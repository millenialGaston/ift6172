(* lexp.ml --- Lambda-expressions: the core language.

Copyright (C) 2011-2019  Free Software Foundation, Inc.

Author: Stefan Monnier <monnier@iro.umontreal.ca>
Keywords: languages, lisp, dependent types.

This file is part of Typer.

Typer is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any
later version.

Typer is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
more details.

You should have received a copy of the GNU General Public License along with
this program.  If not, see <http://www.gnu.org/licenses/>.  *)

module U = Util
module L = List
module SMap = U.SMap
open Fmt

open Sexp
open Pexp

open Myers
open Grammar

(* open Unify *)
module S = Subst

type vname = U.vname
type vref = U.vref
type meta_id = int             (* Identifier of a meta variable.  *)

type label = symbol

(*************** Elaboration to Lexp *********************)

(* The scoping of `Let` is tricky:
 *
 * Since it's a recursive let, the definition part of each binding is
 * valid in the "final" scope which includes all the new bindings.
 *
 * But the type of each binding is not defined in that same scope.  Instead
 * it's defined in the scope of all the previous bindings.
 *
 * For exemple the type of the second binding of such a Let is defined in
 * the scope of the surrounded context extended with the first binding.
 * And the type of the 3rd binding is defined in the scope of the
 * surrounded context extended with the first and the second bindings.  *)

type ltype = lexp
 and subst = lexp S.subst
 and lexp =
   | Imm of sexp                        (* Used for strings, ...  *)
   | Sort of U.location * int
   | Builtin of symbol * ltype
   | Var of vref
   | Susp of lexp * subst  (* Lazy explicit substitution: e[σ].  *)
   (* This "Let" allows recursion.  *)
   | Let of U.location * (vname * lexp * ltype) list * lexp
   | Arrow of vname * ltype * U.location * ltype
   | Lambda of vname * ltype * lexp
   | Call of lexp * lexp list (* Curried call.  *)
   | Inductive of U.location * ((vname * ltype) list) SMap.t
   | Cons of lexp * symbol (* = Type info * ctor_name  *)
   | Case of U.location * lexp
             * ltype (* The type of the return value of all branches *)
             * (U.location * vname list * lexp) SMap.t
             * (vname * lexp) option               (* Default.  *)

type varbind =
  | Variable
  | ForwardRef
  | LetDef of U.db_offset * lexp

(* Scope level is used to detect "out of scope" metavars.
 * See http://okmij.org/ftp/ML/generalization.html
 * The ctx_length keeps track of the length of the lctx in which the
 * metavar is meant to be defined.  *)
type scope_level = int
type ctx_length = int

type constraints  = (lexp * lexp) list

let dummy_scope_level = 0
let impossible = Imm Sexp.dummy_epsilon

let builtin_size = ref 0

(********************** Hash-consing **********************)

(* let hc_table : (lexp, lexp) Hashtbl.t = Hashtbl.create 1000
 * let hc (e : lexp) : lexp =
 *   try Hashtbl.find hc_table e
 *   with Not_found -> Hashtbl.add hc_table e e; e *)

module WHC = Weak.Make (struct type t = lexp
                                (* Using (=) instead of `compare` results
                                 * in an *enormous* slowdown.  Apparently
                                 * `compare` checks == before recursing
                                 * but (=) doesn't?  *)
                                let equal x y = (compare x y = 0)
                                let hash = Hashtbl.hash
                         end)
let hc_table : WHC.t = WHC.create 1000
let hc : lexp -> lexp = WHC.merge hc_table


let mkImm s                    = hc (Imm s)
let mkSort (l, s)              = hc (Sort (l, s))
let mkBuiltin (v, t)           = hc (Builtin (v, t))
let mkVar v                    = hc (Var v)
let mkLet (l, ds, e)           = hc (Let (l, ds, e))
let mkArrow (v, t1, l, t2)     = hc (Arrow (v, t1, l, t2))
let mkLambda (v, t, e)         = hc (Lambda (v, t, e))
let mkInductive (l, cs)         = hc (Inductive (l, cs))
let mkCons (t, n)              = hc (Cons (t, n))
let mkCase (l, e, rt, bs, d)   = hc (Case (l, e, rt, bs, d))
let mkCall (f, es)
  = match f, es with
  | Call (f', es'), _ -> hc (Call (f', es' @ es))
  | _, [] -> f
  | _ -> hc (Call (f, es))

(********* Helper functions to use the Subst operations  *********)
(* This basically "ties the knot" between Subst and Lexp.
 * Maybe it would be cleaner to just move subst.ml into lexp.ml
 * and be done with it.  *)

(* FIXME: We'd like to make this table "weak" to avoid memory leaks,
 * but Weak.Make doesn't cut it because we need to index with a pair
 * that is transient and hence immediately GC'd.  *)
let hcs_table : ((lexp * subst), lexp) Hashtbl.t = Hashtbl.create 1000

(* When computing the type of "load"ed modules
 * we end up building substitutions of the form
 *
 *     ((Susp e3 (((Susp e2 (e1 · id)) · e1 · id)
 *                · e1 · id))
 *      · ((Susp e2 (e1 · id)) · e1 · id)
 *      · e1 · id)
 *
 * with 2^n size (but lots of sharing).  So it's indispensible
 * to memoize the computation to avoid the exponential waste of time.
 *
 * This shows up because of the dependent type of `let`:
 *
 *    let z = e₃ in e                :   τ[e₃/z]
 *    let y = e₂ in let z = e₃ in e  :   (τ[e₃/z])[e₂/y] = τ[(e₃[e₂/y])/z,e₂/y]
 *    let x = e₁ in let y = e₂ in let z = e₃ in e
 *      :   (τ[(e₃[e₂/y])/z,e₂/y])[e₁/x]
 *        = τ[(e₃[(e₂[e₁/x])/y,e₁/x])/z,(e₂[e₁/x])/y,e₁/x]
 *      ...
 *)

let rec list_filter names names' = match names' with
  | name::names' -> if List.mem name names
                  then list_filter names names'
                  else name::list_filter names names'
  | [] -> []
                                                 
let rec mkSusp e s =
  if S.identity_p s then e else
    (* We apply the substitution eagerly to some terms.
     * There's no deep technical rason for that:
     * it just seemed like a good idea to do it eagerly when it's easy.  *)
    match e with
    | Imm _ -> e
    | Builtin _ -> e
    | Susp (e, s') -> mkSusp_memo e (scompose s' s)
    | Var ((l,names),i)
      -> (match slookup s (l,names) i with
         | Var ((_l,names'),i')
           -> mkVar ((l,names' @ list_filter names' names), i')
         | e -> e)
    | _ -> hc (Susp (e, s))
and mkSusp_memo e s
  = if Hashtbl.mem hcs_table (e, s)
    then Hashtbl.find hcs_table (e, s)
    else let res = mkSusp e s in
         Hashtbl.add hcs_table (e, s) res;
         res
and scompose s1 s2 = S.compose mkSusp_memo s1 s2
and slookup s l v = S.lookup (fun l i -> mkVar (l, i))
                             (fun e o -> mkSusp e (S.shift o))
                             s l v

let oname2names on = match on with
  | (l, None) -> (l, [])
  | (l, Some n) -> (l, [n])

let ssink = S.sink (fun l i -> mkVar (oname2names l, i))

(* Shift by a negative amount!  *)
let rec sunshift n =
  if n = 0 then S.identity
  else (assert (n >= 0);
        S.cons impossible (sunshift (n - 1)))

let _ = assert (S.identity_p (scompose (S.shift 5) (sunshift 5)))

(* The quick test below seemed to indicate that about 50% of the "sink"s
 * are applied on top of another "sink" and hence cound be combined into
 * a single "Lift^n" constructor.  Doesn't seem high enough to justify
 * the complexity of adding a `Lift` to `subst`.
 *)
(* let sink_count_total = ref 0
 * let sink_count_optimizable = ref 0
 *
 * let ssink l s =
 *   sink_count_total := 1 + !sink_count_total;
 *   (match s with
 *    | S.Cons (Var (_, 0), (S.Identity o | S.Cons (_, _, o)), 0) when o > 0
 *      -> sink_count_optimizable := 1 + !sink_count_optimizable
 *    | _ -> ());
 *   if ((!sink_count_total) mod 10000) = 0 then
 *     (print_string ("Optimizable = "
 *                    ^ (string_of_int ((100 * !sink_count_optimizable)
 *                                      / !sink_count_total))
 *                    ^ "%\n");
 *      if !sink_count_total > 100000 then
 *        (sink_count_total := !sink_count_total / 2;
 *         sink_count_optimizable := !sink_count_optimizable / 2));
 *   S.sink (fun l i -> mkVar (l, i)) l s *)


let rec lexp_location e =
  match e with
  | Sort (l,_) -> l
  | Imm s -> sexp_location s
  | Var ((l,_),_) -> l
  | Builtin ((l, _), _) -> l
  | Let (l,_,_) -> l
  | Arrow (_,_,l,_) -> l
  | Lambda ((l,_),_,_) -> l
  | Call (f,_) -> lexp_location f
  | Inductive (l,_) -> l
  | Cons (_,(l,_)) -> l
  | Case (l,_,_,_,_) -> l
  | Susp (e, _) -> lexp_location e
  (* | Susp (_, e) -> lexp_location e *)


(********* Normalizing a term *********)

let vdummy = (U.dummy_location, [])
let maybename n = match n with None -> "<anon>" | Some v -> v
let firstname n = match n with [] -> "<anon>" | v::_ -> v
let sname (l,n) = (l, maybename n)

let rec push_susp e s =            (* Push a suspension one level down.  *)
  match e with
  | Imm _ -> e
  | Sort _ -> e
  | Builtin _ -> e

  | Let (l, defs, e)
    -> let s' = L.fold_left (fun s (v, _, _) -> ssink v s) s defs in
      let rec loop s defs = match defs with
        | [] -> []
        | (v, def, ty) :: defs
          -> (v, mkSusp def s', mkSusp ty s) :: loop (ssink v s) defs in
      mkLet (l, loop s defs, mkSusp e s')
  | Arrow (v, t1, l, t2)
    -> mkArrow (v, mkSusp t1 s, l, mkSusp t2 (ssink v s))
  | Lambda (v, t, e) -> mkLambda (v, mkSusp t s, mkSusp e (ssink v s))
  | Call (f, args) -> mkCall (mkSusp f s,
                             L.map (fun arg -> mkSusp arg s) args)
  | Inductive (l, cases)
    -> let ncases = SMap.map (fun args
                             -> let (_, ncase)
                                 = L.fold_left (fun (s, nargs) (v, t)
                                                -> (ssink v s,
                                                   (v, mkSusp t s)
                                                   :: nargs))
                                               (s, []) args in
                               L.rev ncase)
                            cases in
      mkInductive (l, ncases)
  | Cons (it, name) -> Cons (mkSusp it s, name)
  | Case (l, e, ret, cases, default)
    -> mkCase (l, mkSusp e s, mkSusp ret s,
              SMap.map (fun (l, cargs, e)
                        -> let s' = L.fold_left
                                     (fun s ov -> ssink ov s)
                                     s cargs in
                          (l, cargs, mkSusp e s'))
                       cases,
              match default with
              | None -> default
              | Some (v,e) -> Some (v, mkSusp e (ssink v s)))
  (* Susp should never appear around Var/Susp because mkSusp
   * pushes the subst into them eagerly.  IOW if there's a Susp(Var..)
   * it's because some chunk of code should use mkSusp
   * rather than Susp.
   * But we still have to handle them here, since push_susp is called
   * in many other cases than just when we bump into a Susp.  *)
  | Susp (e,s') -> push_susp e (scompose s' s)
  | Var _ -> nosusp (mkSusp e s)

and nosusp e =                  (* Return `e` with no outermost `Susp`.  *)
  match e with
    | Susp(e, s) -> push_susp e s
    | _ -> e


(* Get rid of `Susp`ensions.  *)
let clean e =
  let rec clean s e = match e with
    | Imm _ -> e
    | Sort (l, _) -> e
    | Builtin _ -> e
    | Let (l, defs, e)
      -> let s' = L.fold_left (fun s (v, _, _) -> ssink v s) s defs in
        let (_,ndefs) = L.fold_left (fun (s,ndefs) (v, def, ty)
                                     -> (ssink v s,
                                        (v, clean s' def, clean s ty) :: ndefs))
                                  (s, []) defs in
        mkLet (l, ndefs, clean s' e)
    | Arrow (v, t1, l, t2)
      -> mkArrow (v, clean s t1, l, clean (ssink v s) t2)
    | Lambda (v, t, e) -> mkLambda (v, clean s t, clean (ssink v s) e)
    | Call (f, args) -> mkCall (clean s f,
                               L.map (fun arg -> clean s arg) args)
    | Inductive (l, cases)
      -> let ncases = SMap.map (fun args
                               -> let (_, ncase)
                                   = L.fold_left (fun (s, nargs) (v, t)
                                                  -> (ssink v s,
                                                     (v, clean s t)
                                                     :: nargs))
                                       (s, []) args in
                                 L.rev ncase)
                       cases in
        mkInductive (l, ncases)
    | Cons (it, name) -> Cons (clean s it, name)
    | Case (l, e, ret, cases, default)
      -> mkCase (l, clean s e, clean s ret,
                SMap.map (fun (l, cargs, e)
                          -> let s' = L.fold_left
                                       (fun s ov -> ssink ov s)
                                       s cargs in
                            (l, cargs, clean s' e))
                         cases,
                match default with
                | None -> default
                | Some (v,e) -> Some (v, clean (ssink v s) e))
    | Susp (e, s') -> clean (scompose s' s) e
    | Var _ -> if S.identity_p s then e
              else clean S.identity (mkSusp e s)
  in clean S.identity e

let sdatacons = Symbol (U.dummy_location, "##datacons")
let stypecons = Symbol (U.dummy_location, "##typecons")

(* ugly printing (sexp_print (pexp_unparse (lexp_unparse e))) *)
let rec lexp_unparse lxp =
  match lxp with
    | Susp _ as e -> lexp_unparse (nosusp e)
    | Imm (sexp) -> sexp
    | Builtin ((l,name), _) -> Symbol (l, "##" ^ name)
    (* FIXME: Add a Sexp syntax for debindex references.  *)
    | Var ((loc, name), _) -> Symbol (loc, firstname name)
    | Cons (t, (l, name))
      -> Node (sdatacons,
              [lexp_unparse t; Symbol (l, name)])
    | Lambda (vdef, ltp, body)
      -> let l = lexp_location lxp in
        let st = lexp_unparse ltp in
        Node (Symbol (l, "lambda_->_"),
              [Node (Symbol (l, "_:_"), [Symbol (sname vdef); st]);
               lexp_unparse body])
    | Arrow ((l,oname), ltp1, loc, ltp2)
      -> let ut1 = lexp_unparse ltp1 in
        Node (Symbol (loc, "_->_"),
              [(match oname with None -> ut1
                               | Some v -> Node (Symbol (l, "_:_"),
                                                [Symbol (l,v); ut1]));
               lexp_unparse ltp2])

    | Let (loc, ldecls, body)
      -> (* (vdef * lexp * ltype) list *)
       let sdecls = List.fold_left
                      (fun acc (vdef, lxp, ltp)
                       -> Node (Symbol (U.dummy_location, "_=_"),
                               [Symbol (sname vdef); lexp_unparse ltp])
                         :: Node (Symbol (U.dummy_location, "_=_"),
                                  [Symbol (sname vdef); lexp_unparse lxp])
                         :: acc)
                      [] ldecls in
       Node (Symbol (loc, "let_in_"),
             [Node (Symbol (U.dummy_location, "_;_"), sdecls);
              lexp_unparse body])

    | Call(lxp, largs)
      -> let sargs = List.map lexp_unparse largs in
        Node (lexp_unparse lxp, sargs)

    | Inductive(loc, ctors) ->
       Node (stypecons,
             List.map
               (fun (name, types)
                -> Node (Symbol (loc, name),
                        List.map
                          (fun arg ->
                            match arg with
                            | ((_,None), t) -> lexp_unparse t
                            | (s, t)
                              -> let (l,_) as id = sname s in
                                Node (Symbol (l, "_:_"),
                                      [Symbol id; lexp_unparse t]))
                          types))
               (SMap.bindings ctors))

    | Case (loc, target, bltp, branches, default) ->
       let bt = lexp_unparse bltp in
       let pbranch
         = List.map (fun (str, (loc, args, bch))
                     -> match args with
                       | [] -> Ppatsym (loc, Some str), lexp_unparse bch
                       | _  ->
                          (* FIXME: Rather than a Pcons we'd like to refer
                           * to an existing binding with that value!  *)
                          (Ppatcons (Node (sdatacons,
                                           [bt; Symbol (loc, str)]),
                                     args),
                           lexp_unparse bch))
             (SMap.bindings branches) in

       let pbranch = match default with
         | Some (v,dft) -> (Ppatsym v,
                           lexp_unparse dft)::pbranch
         | None -> pbranch
       in let e = lexp_unparse target in
          Node (Symbol (loc, "case_"),
                e :: List.map
                      (fun (pat, branch) ->
                        Node (Symbol (pexp_pat_location pat, "_=>_"),
                              [pexp_u_pat pat; branch]))
                      pbranch)

    | Sort (l, 0) -> Symbol (l, "Type")
    | Sort (l, 1) -> Symbol (l, "Kind")
    | Sort (l, n)
      -> Symbol (l, "##Type_" ^ string_of_int n)

(* FIXME: ¡Unify lexp_print and lexp_string!  *)
and lexp_string lxp = sexp_string (lexp_unparse lxp)

and subst_string s = match s with
  | S.Identity o -> "↑" ^ string_of_int o
  | S.Cons (l, s, 0) -> lexp_name l ^ " · " ^ subst_string s
  | S.Cons (l, s, o)
    -> "(↑"^ string_of_int o ^ " " ^ subst_string (S.cons l s) ^ ")"

and lexp_name e =
  match e with
    | Imm    _ -> lexp_string e
    | Var    _ -> lexp_string e
    | Let    _ -> "let"
    | Arrow  _ -> "Arrow"
    | Lambda _ -> "lambda"
    | Call   _ -> "Call"
    | Cons   _ -> "datacons"
    | Case   _ -> "case"
    | Inductive _ -> "typecons"
    | Susp      _ -> "Susp"
    | Builtin   (_, _) -> "Builtin"
    | Sort      _ -> "Sort"

(* ------------------------------------------------------------------------- *)
(*                                   Printing                                *)

(*  Printing Context
 * ========================================== *)

type print_context_value =
  | Bool of bool
  | Int of int
  | Expr of lexp option
  | Predtl of grammar        (* precedence table *)

type print_context = print_context_value SMap.t

let pretty_ppctx =
  List.fold_left (fun map (key, v) -> SMap.add key v map)
    SMap.empty
    [("pretty"        , Bool (true) ); (* print with new lines and indents   *)
     ("print_type"    , Bool (true) ); (* print inferred Type                *)
     ("print_dbi"     , Bool (false)); (* print dbi index                    *)
     ("indent_size"   , Int  (2)    ); (* indent step                        *)
     ("color"         , Bool (true) ); (* use console color to display hints *)
     ("separate_decl" , Bool (true) ); (* print newline between declarations *)
     ("indent_level"  , Int  (0)    ); (* current indent level               *)
     ("parent"        , Expr (None) ); (* parent expression                  *)
     ("col_max"       , Int  (80)   ); (* col_size + col_ofsset <= col_max   *)
     ("col_size"      , Int  (0)    ); (* current column size                *)
     ("col_ofsset"    , Int  (0)    ); (* if col does not start at 0         *)
     ("print_erasable", Bool (false));
     ("print_implicit", Bool (false));
     ("grammar"       , Predtl (default_grammar))]

(* debug_ppctx is a ref so we can modify it in the REPL *)
let debug_ppctx = ref (
  List.fold_left (fun map (key, v) -> SMap.add key v map)
    pretty_ppctx
    [("pretty"        , Bool (false) );
     ("print_dbi"     , Bool (true)  );
     ("print_erasable", Bool (true));
     ("print_implicit", Bool (true));
     ("separate_decl" , Bool (false) );])

let smap_bool s ctx =
  match SMap.find s ctx with Bool b -> b | _ -> failwith "Unreachable"
and smap_int s ctx =
  match SMap.find s ctx with Int i -> i | _ -> failwith "Unreachable"
and smap_lexp s ctx =
  match SMap.find s ctx with Expr e -> e | _ -> failwith "Unreachable"
and smap_predtl s ctx =
  match SMap.find s ctx with Predtl tl -> tl | _ -> failwith "Unreachable"

let pp_pretty = smap_bool "pretty"
let pp_type = smap_bool "print_type"
let pp_dbi = smap_bool "print_dbi"
let pp_size = smap_int "indent_size"
let pp_color = smap_bool "color"
let pp_decl = smap_bool "separate_decl"
let pp_indent = smap_int "indent_level"
let pp_parent = smap_lexp "parent"
let pp_grammar = smap_predtl "grammar"
let pp_colsize = smap_int "col_size"
let pp_colmax = smap_int "col_max"
let pp_erasable = smap_bool "print_erasable"
let pp_implicit = smap_bool "print_implicit"

let set_col_size p ctx = SMap.add "col_size" (Int p) ctx
let add_col_size p ctx = set_col_size ((pp_colsize ctx) + p) ctx
let reset_col_size ctx = set_col_size 0 ctx
let set_parent p ctx = SMap.add "parent" (Expr (Some p)) ctx
let add_indent ctx i = SMap.add "indent_level" (Int ((pp_indent ctx) + i)) ctx

let pp_append_string buffer ctx str =
  let n = (String.length str) in
    Buffer.add_string buffer str;
    add_col_size n ctx
let pp_newline buffer ctx =
  Buffer.add_char buffer '\n';
  reset_col_size ctx

let is_binary_op str =
  let len = String.length str in
  let c1 = String.get str 0 in
  let cn = String.get str (len - 1) in
    if (c1 = '_') && (cn = '_') && (len > 2) then true else false

let get_binary_op_name name =
  assert (((String.length name) - 2) >= 1);
  String.sub name 1 ((String.length name) - 2)

let rec get_precedence expr ctx =
  let lkp name = SMap.find name (pp_grammar ctx) in
  match expr with
    | Lambda _ -> lkp "lambda"
    | Case _ -> lkp "case"
    | Let _ -> lkp "let"
    | Arrow (_, _, _, _) -> lkp "->"
    | Call (exp, _) -> get_precedence exp ctx
    | Builtin ((_, name), _)  when is_binary_op name ->
      lkp (get_binary_op_name name)
    | Var ((_, name::_), _) when is_binary_op name ->
      lkp (get_binary_op_name name)
    | _ -> None, None

(*  Printing Functions
 * ========================================== *)

let rec lexp_print  e = print_string (lexp_string e)
and     lexp_string e = lexp_cstring (!debug_ppctx) e

(* Context Print *)
and lexp_cprint ctx e  = print_string (lexp_cstring ctx e)
and lexp_cstring ctx e = lexp_str ctx e

(* Implementation *)
and lexp_str ctx (exp : lexp) : string =

    let ctx             = set_parent exp ctx in
    let inter_ctx       = add_indent ctx 1 in
    let lexp_str'        = lexp_str ctx in
    let lexp_stri idt e = lexp_str (add_indent ctx idt) e in

    let pretty = pp_pretty ctx in
    let color  = pp_color ctx in
    let indent = pp_indent ctx in
    let isize  = pp_size ctx in

    (* colors *)
      let red     = if color then red     else "" in
      let green   = if color then green   else "" in
      let yellow  = if color then yellow  else "" in
      let magenta = if color then magenta else "" in
      let cyan    = if color then cyan    else "" in
      let reset   = if color then reset   else "" in

    let make_indent idt = if pretty then
      (make_line ' ' ((idt + indent) * isize)) else "" in

    let newline = if pretty then "\n" else " " in
    let nl = newline in

    let keyword str  = magenta ^ str ^ reset in
    let error str    = red     ^ str ^ reset in
    let tval str     = yellow  ^ str ^ reset in
    let fun_call str = cyan    ^ str ^ reset in

    let index idx =
      let str = if pp_dbi ctx
                then ("[" ^ (string_of_int idx) ^ "]")
                else "" in
      if idx < 0 then error str
      else green ^ str ^ reset in

    let get_name fname = match fname with
      | Builtin ((_, name), _) -> name,  0
      | Var((_, name::_), idx)     -> name, idx
      | Lambda _                  -> "__",  0
      | Cons _                    -> "__",  0
      | _                         -> "__", -1  in

    match exp with
        | Imm(value) -> (match value with
            | String (_, s) -> tval ("\"" ^ s ^ "\"")
            | Integer(_, s) -> tval (string_of_int s)
            | Float  (_, s) -> tval (string_of_float s)
            | e -> sexp_string e)

        | Susp (e, s) -> lexp_str ctx (push_susp e s)

        | Var ((loc, name), idx) -> firstname name ^ (index idx) ;

        | Let (_, decls, body)   ->
            (* Print first decls without indent *)
            let h1, decls, idt_lvl =
                match lexp_str_decls inter_ctx decls with
                    | h1::decls -> h1, decls, 2
                    | _ -> "", [], 1 in

            let decls = List.fold_left (fun str elem ->
              str ^ nl ^ (make_indent 1) ^ elem ^ " ") h1 decls in

            let n = String.length decls in
            (* remove last newline *)
            let decls = if (n > 0) then
                          String.sub decls 0 (n - 2)
                        else decls in

            (keyword "let ") ^ decls ^ (keyword " in ") ^ newline ^
                (make_indent idt_lvl) ^ (lexp_stri idt_lvl body)

        | Arrow((_, Some name), tp, loc, expr) ->
            "(" ^ name ^ " : " ^ (lexp_str' tp) ^ ") -> " ^ (lexp_str' expr)

        | Arrow((_, None), tp, loc, expr) ->
           "(" ^ (lexp_str' tp) ^ " -> " ^ (lexp_str' expr) ^ ")"

        | Lambda((loc, name), ltype, lbody) ->
            let arg = "(" ^ maybename name ^ " : " ^ (lexp_str' ltype) ^ ")" in

            (keyword "lambda ") ^ arg ^ " ->" ^ newline ^
                (make_indent 1) ^ (lexp_stri 1 lbody)

        | Cons(t, (_, ctor_name)) ->
            (keyword "datacons ") ^ (lexp_str' t) ^ " " ^ ctor_name

        | Call(fname, args) ->
          let name, idx = get_name fname in
          let binop_str op lhs rhs =
            "(" ^ (lexp_str' lhs) ^ op ^ (index idx)
            ^ " " ^ (lexp_str' rhs) ^ ")" in

          let print_arg str lxp = str ^ " " ^ (lexp_str' lxp) in
          (match args with
           | [lhs; rhs]  when is_binary_op name
             -> binop_str (" " ^ (get_binary_op_name name)) lhs rhs

           | _ -> let args = List.fold_left print_arg "" args in
                 "(" ^ (lexp_str' fname) ^ args ^ ")")

        | Inductive (_, ctors)
          -> (keyword "typecons") ^ newline
            ^ (lexp_str_ctor ctx ctors)

        | Case (_, target, _ret, map, dflt)
          -> let str = (keyword "case ") ^ (lexp_str' target) in
            let arg_str arg
              = List.fold_left (fun str v
                                -> match v with
                                  | (_, None) -> str ^ " _"
                                  | (_, Some n) -> str ^ " " ^ n)
                  "" arg in

            let str
              = SMap.fold (fun k (_, arg, exp) str
                           -> str ^ nl ^ (make_indent 1)
                             ^ "| " ^ (fun_call k) ^ (arg_str arg)
                             ^ " => " ^ (lexp_stri 1 exp))
                  map str in

            (match dflt with
             | None -> str
             | Some (v, df) ->
                str ^ nl ^ (make_indent 1)
                ^ "| " ^ (match v with (_, None) -> "_"
                                     | (_, Some name) -> name)
                ^ " => " ^ (lexp_stri 1 df))

        | Builtin ((_, name), _) -> "##" ^ name

        | Sort (l, 0) -> "Type"
        | Sort (l, 1) -> "Kind"
        | Sort (l, n) -> "##Type_" ^ string_of_int n

and lexp_str_ctor ctx ctors =

  let pretty = pp_pretty ctx in
  let make_indent idt = if pretty then (make_line ' ' ((idt + (pp_indent ctx)) * (pp_size ctx))) else "" in
  let newline = (if pretty then "\n" else " ") in

  SMap.fold (fun key value str
             -> let str = str ^ newline ^ (make_indent 1) ^ "(" ^ key in
               let str = List.fold_left (fun str (_, arg)
                                         -> str ^ " " ^ (lexp_str ctx arg))
                                        str value in
               str ^ ")")
            ctors ""

and lexp_str_decls ctx decls =

    let lexp_str' = lexp_str ctx in
    let sepdecl = (if pp_decl ctx then "\n" else "") in

    let type_str name lxp = (if pp_type ctx then (
         name ^ " : " ^ (lexp_str' lxp) ^ ";") else "") in

    let ret = List.fold_left
                (fun str ((_, name), lxp, ltp)
                 -> let name = maybename name in
                   let str = if pp_type ctx then (type_str name ltp)::str else str in
                   (name ^ " = " ^ (lexp_str' lxp) ^ ";" ^ sepdecl)::str)
                [] decls in
    List.rev ret

(** Syntactic equality (i.e. without β).  *******)

let rec eq e1 e2 =
  e1 == e2 ||
    match (e1, e2) with
    | (Imm (Integer (_, i1)), Imm (Integer (_, i2))) -> i1 = i2
    | (Imm (Float (_, x1)), Imm (Float (_, x2))) -> x1 = x2
    | (Imm (String (_, s1)), Imm (String (_, s2))) -> s1 = s2
    | (Imm s1, Imm s2) -> s1 = s2
    | (Sort (_, s1), Sort (_, s2)) -> s1 = s2
    | (Builtin ((_, name1), _), Builtin ((_, name2), _)) -> name1 = name2
    | (Var (_, i1), Var (_, i2)) -> i1 = i2
    | (Susp (e1, s1), e2) -> eq (push_susp e1 s1) e2
    | (e1, Susp (e2, s2)) -> eq e1 (push_susp e2 s2)
    | (Let (_, defs1, e1), Let (_, defs2, e2))
      -> eq e1 e2 && List.for_all2 (fun (_, e1, t1) (_, e2, t2)
                                  -> eq t1 t2 && eq e1 e2)
                                 defs1 defs2
    | (Arrow (_, t11, _, t21), Arrow (_, t12, _, t22))
      -> eq t11 t12 && eq t21 t22
    | (Lambda (_, t1, e1), Lambda (_, t2, e2))
      -> eq t1 t2 && eq e1 e2
    | (Call (e1, as1), Call (e2, as2))
      -> eq e1 e2 && List.for_all2 eq as1 as2
    | (Inductive (_, cases1), Inductive (_, cases2))
      -> SMap.equal (List.for_all2 (fun (_, e1) (_, e2) -> eq e1 e2))
          cases1 cases2
    | (Cons (t1, (_, l1)), Cons (t2, (_, l2))) -> eq t1 t2 && l1 = l2
    | (Case (_, e1, r1, cases1, def1), Case (_, e2, r2, cases2, def2))
      -> eq e1 e2 && eq r1 r2
        && SMap.equal (fun (_, fields1, e1) (_, fields2, e2)
                      -> eq e1 e2 && List.for_all2 (fun _ _ -> true)
                                                 fields1 fields2)
                     cases1 cases2
        && (match (def1, def2) with
          | (Some (_, e1), Some (_, e2)) -> eq e1 e2
          | _ -> def1 = def2)
    | _ -> false

and subst_eq s1 s2 =
  s1 == s2 ||
    match (s1, s2) with
    | (S.Identity o1, S.Identity o2) -> o1 = o2
    | (S.Cons (e1, s1, o1), S.Cons (e2, s2, o2))
      -> if o1 = o2 then
          eq e1 e2 && subst_eq s1 s2
        else if o1 > o2 then
          let o = o1 - o2 in
          eq (mkSusp e1 (S.shift o)) e2
          && subst_eq (S.mkShift s1 o) s2
        else
          let o = o2 - o1 in
          eq e1 (mkSusp e2 (S.shift o))
          && subst_eq s1 (S.mkShift s2 o)
    | _ -> false

