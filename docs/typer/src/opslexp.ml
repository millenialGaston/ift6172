(* opslexp.ml --- Operations on Lexps

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
module SMap = U.SMap
module IMap = U.IMap
(* open Lexer *)
open Sexp
module P = Pexp
(* open Myers *)
(* open Grammar *)
open Lexp
module E = Elexp
module L = Lexp
module M = Myers

(* open Unify *)
module S = Subst
(* module L = List *)
module DB = Debruijn

let error_tc = Log.log_error ~section:"TC"
let warning_tc = Log.log_warning ~section:"TC"

(* `conv_erase` is supposed to be safe according to the ICC papers. *)
let conv_erase = true          (* Makes conv ignore erased terms. *)

(* The safety of `impredicative_erase` is unknown.  But I like the idea.  *)
let impredicative_erase = true (* Allows erasable args to be impredicative. *)

(* Lexp context *)

let lookup_type  = DB.lctx_lookup_type
let lookup_value = DB.lctx_lookup_value

(** Extend a substitution S with a (mutually recursive) set
 * of definitions DEFS.
 * This is rather tricky.  E.g. for
 *
 *     (x₁ = e1; x₂ = e₂)
 *
 * Where x₁ will be DeBruijn #1 and x₂ will be DeBruijn #0,
 * we want a substitution of the form
 *
 *     (let x₂ = e₂ in e₂) · (let x₁ = e₁; x₂ = e₂ in e₁) · Id
 *
 * Because we want #2 in both e₂ and e₁ to refer to the nearest variable in
 * the surrouding context, but the substitution for #0 (defined here as
 * `let x₂ = e₂ in e₂`) will be interpreted in the remaining context,
 * which already provides "x₁".
 *)
(* FXIME: This creates an O(N^2) tree from an O(N) `let`!  *)
let rec lexp_defs_subst l s defs = match defs with
  | [] -> s
  | (_, lexp, _) :: defs'
    -> lexp_defs_subst l (S.cons (mkLet (l, defs, lexp)) s) defs'

(** Convert a lexp_context into a substitution.  *)

let rec lctx_to_subst lctx =
  match DB.lctx_view lctx with
  | DB.CVempty -> Subst.identity
  | DB.CVlet (_, LetDef (_, e), _, lctx)
    -> let s = lctx_to_subst lctx in
       L.scompose (S.substitute e) s
  | DB.CVlet (v, _, _, lctx)
    -> let s = lctx_to_subst lctx in
       (* Here we decide to keep those vars in the target domain.
        * Another option would be to map them to `L.impossible`,
        * hence making the target domain be empty (i.e. making the substitution
        * generate closed results).  *)
       L.ssink v s
  | DB.CVfix (defs, lctx)
    -> let s1 = lctx_to_subst lctx in
       let s2 = lexp_defs_subst DB.dloc S.identity
                                (List.rev defs) in
       L.scompose s2 s1

(* Take an expression `e` that is "closed" relatively to context lctx
 * and return an equivalent expression valid in the empty context.
 * By "closed" I mean that it only refers to elements of the context which
 * are LetDef.  *)
let lexp_close lctx e =
  (* There are many different ways to skin this cat.
   * This is definitely not the best one:
   * - it inlines all the definitions everywhere they're used
   * - It turns the lctx (of O(log N) access time) into a subst
   *   (of O(N) access time)
   * Oh well!  *)
  L.clean (mkSusp e (lctx_to_subst lctx))


(** Reduce to weak head normal form.
 * WHNF implies:
 * - Not a Let.
 * - Not a let-bound variable.
 * - Not a Susp.
 * - Not a Call (Lambda _).
 * - Not a Call (Call _).
 * - Not a Call (_, []).
 * - Not a Case (Cons _).
 * FIXME: This should be memoized!
 *
 * BEWARE: As a general rule lexp_whnf should not be used on actual *code*
 * but only on *types*.  If you must use it on code, be sure to use its
 * return value as little as possible since WHNF will inherently introduce
 * call-by-name behavior.  *)
let lexp_whnf e (ctx : DB.lexp_context) : lexp =
  let rec lexp_whnf e (ctx : DB.lexp_context) : lexp =
  match e with
  | Var v -> (match lookup_value ctx v with
             | None -> e
             (* We can do this blindly even for recursive definitions!
              * IOW the risk of inf-looping should only show up when doing
              * things like full normalization (e.g. lexp_conv_p).  *)
             | Some e' -> lexp_whnf e' ctx)
  | Susp (e, s) -> lexp_whnf (push_susp e s) ctx
  | Call (e, []) -> lexp_whnf e ctx
  | Call (f, ((arg::args) as xs)) ->
     (match lexp_whnf f ctx with
      | Lambda (_, _, body) ->
         (* Here we apply whnf to the arg eagerly to kind of stay closer
          * to the idea of call-by-value, although in this context
          * we can't really make sure we always reduce the arg to a value.  *)
         lexp_whnf (mkCall (push_susp body (S.substitute (lexp_whnf arg ctx)),
                            args))
                   ctx
      | Call (f', xs1) -> mkCall (f', List.append xs1 xs)
      | _ -> e)                 (* Keep `e`, assuming it's more readable!  *)
  | Case (l, e, rt, branches, default) ->
     let e' = lexp_whnf e ctx in
     let reduce name aargs =
       try
         let (_, _, branch) = SMap.find name branches in
         let (subst, _)
           = List.fold_left
               (fun (s,d) arg ->
                 (S.cons (L.mkSusp (lexp_whnf arg ctx) (S.shift d)) s,
                  d + 1))
               (S.identity, 0)
               aargs in
         lexp_whnf (push_susp branch subst) ctx
       with Not_found
            -> match default
              with | Some (v,default)
                     -> lexp_whnf (push_susp default (S.substitute e')) ctx
                   | _ -> Log.log_error ~section:"WHNF" ~loc:l
                                     ("Unhandled constructor " ^
                                        name ^ "in case expression");
                         mkCase (l, e, rt, branches, default) in
     (match e' with
      | Cons (_, (_, name)) -> reduce name []
      | Call (Cons (_, (_, name)), aargs) -> reduce name aargs
      | _ -> mkCase (l, e, rt, branches, default))

  (* FIXME: I'd really prefer to use "native" recursive substitutions, using
   *   ideally a trick similar to the db_offsets in lexp_context!  *)
  | Let (l, defs, body)
    -> lexp_whnf (push_susp body (lexp_defs_subst l S.identity defs)) ctx

  | e -> e

  in lexp_whnf e ctx


(** A very naive implementation of sets of pairs of lexps.  *)
type set_plexp = (lexp * lexp) list
let set_empty : set_plexp = []
let set_member_p (s : set_plexp) (e1 : lexp) (e2 : lexp) : bool
  = assert (e1 == Lexp.hc e1); (* Make sure `e1` and `e2` have been ... *)
    assert (e2 == Lexp.hc e2); (* ... properly hash-cons'd!  *)
    try let _ = List.find (fun (e1', e2')
                           -> L.eq e1 e1' && L.eq e2 e2')
                  s
        in true
    with Not_found -> false
let set_add (s : set_plexp) (e1 : lexp) (e2 : lexp) : set_plexp
  = (* assert (not (set_member_p s e1 e2)); *)
    ((e1, e2) :: s)
let set_shift_n (s : set_plexp) (n : U.db_offset)
  = List.map (let s = S.shift n in
              fun (e1, e2) -> (Lexp.push_susp e1 s, Lexp.push_susp e2 s))
             s
let set_shift s : set_plexp = set_shift_n s 1

(********* Testing if two types are "convertible" aka "equivalent"  *********)

(* Returns true if e₁ and e₂ are equal (upto alpha/beta/...).  *)
let rec conv_p' (ctx : DB.lexp_context) (vs : set_plexp) e1 e2 : bool =
  let e1' = lexp_whnf e1 ctx in
  let e2' = lexp_whnf e2 ctx in
  e1' == e2' ||
    let changed = not (e1 == e1' && e2 == e2') in
    if changed && set_member_p vs e1' e2' then true else
    let vs' = if changed then set_add vs e1' e2' else vs in
    let conv_p = conv_p' ctx vs' in
    match (e1', e2') with
    | (Imm (Integer (_, i1)), Imm (Integer (_, i2))) -> i1 = i2
    | (Imm (Float (_, i1)), Imm (Float (_, i2))) -> i1 = i2
    | (Imm (String (_, i1)), Imm (String (_, i2))) -> i1 = i2
    | (Sort (_, s1), Sort (_, s2)) -> s1 == s2
    | (Builtin ((_, s1), _), Builtin ((_, s2), _)) -> s1 = s2
    | (Var (_, v1), Var (_, v2)) -> v1 = v2
    | (Arrow (vd1, t11, _, t12), Arrow (vd2, t21, _, t22))
      -> conv_p t11 t21
        && conv_p' (DB.lexp_ctx_cons ctx vd1 Variable t11) (set_shift vs')
                  t12 t22
    | (Lambda (l1, t1, e1), Lambda (l2, t2, e2))
      -> (conv_erase || conv_p t1 t2)
        && conv_p' (DB.lexp_ctx_cons ctx l1 Variable t1)
                  (set_shift vs')
                  e1 e2
    | (Call (f1, args1), Call (f2, args2))
      -> let rec conv_arglist_p args1 args2 : bool =
          List.fold_left2
            (fun eqp t1 t2 -> eqp && conv_p t1 t2)
            true args1 args2 in
        conv_p f1 f2 && conv_arglist_p args1 args2
    | (Inductive (_, cases1), Inductive (_, cases2))
      -> let rec conv_fields ctx vs fields1 fields2 =
          match fields1, fields2 with
          | ([], []) -> true
          | ((vd1,t1)::fields1, (vd2,t2)::fields2)
            -> conv_p' ctx vs t1 t2
              && conv_fields (DB.lexp_ctx_cons ctx vd1 Variable t1)
                            (set_shift vs)
                            fields1 fields2
          | _,_ -> false in
        SMap.equal (conv_fields ctx vs') cases1 cases2
    | (Cons (t1, (_, l1)), Cons (t2, (_, l2))) -> l1 = l2 && conv_p t1 t2
    (* FIXME: Various missing cases, such as Case.  *)
    | (_, _) -> false

let conv_p (ctx : DB.lexp_context) e1 e2
  = if e1 == e2 then true
    else conv_p' ctx set_empty e1 e2

(********* Testing if a lexp is properly typed  *********)

type sort_compose_result
  = SortResult of ltype
  | SortK1NotType
  | SortK2NotType

let sort_compose ctx l k1 k2 =
  (* BEWARE!  Technically `k2` can refer to `v`, but this should only happen
   * if `v` is a TypeLevel, and in that case sort_compose
   * should ignore `k2` and return TypeOmega anyway.  *)
  let k2 = mkSusp k2 (S.substitute impossible) in
  match (lexp_whnf k1 ctx, lexp_whnf k2 ctx) with
  | (Sort (_, s1), Sort (_, s2)) -> SortResult (mkSort (l, max s1 s2))
  | (Sort (_, _), _) -> SortK2NotType
  | (_, _) -> SortK1NotType

(* "check ctx e" should return τ when "Δ ⊢ e : τ"  *)
let rec check'' ctx e =
  let check = check'' in
  let assert_type ctx e t t' =
    if conv_p ctx t t' then ()
    else (error_tc ~loc:(lexp_location e)
                     ("Type mismatch for "
                      ^ lexp_string (L.clean e) ^ " : "
                      ^ lexp_string (L.clean t) ^ " != "
                      ^ lexp_string (L.clean t'));
          (* Log.internal_error "Type mismatch" *)) in
  let check_type ctx t =
    let s = check ctx t in
    (match lexp_whnf s ctx with
    | Sort _ -> ()
    | _ -> error_tc ~loc:(lexp_location t)
                      ("Not a proper type: " ^ lexp_string t));
    (* FIXME: return the `sort` rather than the surrounding `lexp`!  *)
    s in

  match e with
  | Imm (Float (_, _)) -> DB.type_float
  | Imm (Integer (_, _)) -> DB.type_int
  | Imm (String (_, _)) -> DB.type_string
  | Imm (Block (_, _, _) | Symbol _ | Node (_, _))
    -> (error_tc ~loc:(lexp_location e) "Unsupported immediate value!";
       DB.type_int)
  | Sort (l, s) -> mkSort (l, s + 1)
  | Builtin (_, t)
    -> let _ = check_type Myers.nil t in
      t
  | Var (((l, name), idx) as v)
    -> lookup_type ctx v
  | Susp (e, s) -> check ctx (push_susp e s)
  | Let (l, defs, e)
    -> let _ =
        List.fold_left (fun ctx (v, e, t)
                        -> (let _ = check_type ctx t in
                           DB.lctx_extend ctx v ForwardRef t))
                       ctx defs in
      let nctx = DB.lctx_extend_rec ctx defs in
      (* FIXME: Termination checking!  Positivity-checker!  *)
      let _ = List.fold_left (fun n (v, e, t)
                              -> assert_type
                                  nctx e
                                  (push_susp t (S.shift n))
                                  (check nctx e);
                                n - 1)
                             (List.length defs) defs in
      mkSusp (check nctx e)
             (lexp_defs_subst l S.identity defs)
  | Arrow (v, t1, l, t2)
    -> (let k1 = check_type ctx t1 in
       let nctx = DB.lexp_ctx_cons ctx v Variable t1 in
       let k2 = check_type nctx t2 in
       match sort_compose ctx l k1 k2 with
       | SortResult k -> k
       | SortK1NotType
         -> (error_tc ~loc:(lexp_location t1)
              "Not a proper type";
            mkSort (l, 99))
       | SortK2NotType
         -> (error_tc ~loc:(lexp_location t2)
              "Not a proper type";
            mkSort (l, 99)))
  | Lambda (((l,_) as v), t, e)
    -> (let _k = check_type ctx t in
       mkArrow (v, t, l,
                check (DB.lctx_extend ctx v Variable t)
                      e))
  | Call (f, args)
    -> let ft = check ctx f in
      List.fold_left
        (fun ft arg
         -> let at = check ctx arg in
           match lexp_whnf ft ctx with
           | Arrow (v, t1, l, t2)
             -> assert_type ctx arg t1 at;
               mkSusp t2 (S.substitute arg)
           | _ -> (error_tc ~loc:(lexp_location arg)
                              ("Calling a non function (type = "
                               ^ lexp_string ft ^ ")!");
                  ft))
        ft args
  | Inductive (l, cases)
    -> let level
        = SMap.fold
            (fun _ case level ->
              let (level, _, _) =
                List.fold_left
                  (fun (level, ictx, n) (v, t) ->
                    ((match lexp_whnf (check_type ictx t)
                              ictx with
                      | Sort (_, level')
                        -> max level level'
                      | tt -> error_tc ~loc:(lexp_location t)
                               ~print_action:(fun _ ->
                                 DB.print_lexp_ctx ictx; print_newline ()
                               )
                               ("Field type "
                                ^ lexp_string t
                                ^ " is not a Type! ("
                                ^ lexp_string tt ^")");
                             level),
                     DB.lctx_extend ictx v Variable t,
                     n + 1))
                  (level, ctx, 0)
                  case in
              level)
            cases 0 in
      mkSort (l, level)
  | Case (l, e, ret, branches, default)
    -> let etype = lexp_whnf (check ctx e) ctx in
      (match etype with
       | Inductive (_, constructors)
         -> SMap.iter
            (fun name (l, vdefs, branch)
             -> let fieldtypes = SMap.find name constructors in
               let rec mkctx ctx s vdefs fieldtypes =
                 match vdefs, fieldtypes with
                 | [], [] -> ctx
                 (* FIXME: If ak is Aerasable, make sure the var only
                  * appears in type annotations.  *)
                 | vdef::vdefs, (vdef', ftype)::fieldtypes
                   -> mkctx (DB.lexp_ctx_cons ctx vdef Variable (mkSusp ftype s))
                           (S.cons (Var (oname2names vdef, 0))
                                   (S.mkShift s 1))
                           vdefs fieldtypes
                 | _,_ -> (error_tc ~loc:l
                                      "Wrong number of args to constructor!";
                          ctx) in
               let nctx = mkctx ctx S.identity vdefs fieldtypes in
               assert_type nctx branch
                           (mkSusp ret (S.shift (List.length fieldtypes)))
                           (check nctx branch))
            branches;
          let diff = SMap.cardinal constructors - SMap.cardinal branches in
          (match default with
           | Some (v, d)
             -> if diff <= 0 then
                 warning_tc ~loc:l "Redundant default clause";
               let nctx = (DB.lctx_extend ctx v (LetDef (0, e)) etype) in
               assert_type nctx d (mkSusp ret (S.shift 1))
                           (check nctx d)
           | None
             -> if diff > 0 then
                 error_tc ~loc:l ("Non-exhaustive match: "
                                     ^ string_of_int diff ^ " cases missing"))
       | _ -> error_tc ~loc:l "Case on a non-inductive type!");
      ret
  | Cons (t, (l, name))
    -> (match lexp_whnf t ctx with
       | Inductive (l, constructors)
         -> (try
              let fieldtypes = SMap.find name constructors in
              let rec fieldargs ftypes =
                match ftypes with
                | [] -> let nargs = List.length fieldtypes in
                       mkSusp t (S.shift nargs)
                | (vd, ftype) :: ftypes
                  -> mkArrow (vd, ftype, lexp_location ftype,
                             fieldargs ftypes) in
              fieldargs fieldtypes
            with Not_found
                 -> (error_tc ~loc:l
                                ("Constructor \"" ^ name ^ "\" does not exist");
                    DB.type_int))
       | _ -> (error_tc ~loc:(lexp_location e)
                          ("Cons of a non-inductive type: "
                           ^ lexp_string t);
              DB.type_int))

let check' ctx e =
  let res = check'' ctx e in
    (Log.stop_on_error (); res)

let check = check'

(** Compute the set of free variables.  **)

let rec list_union l1 l2 = match l1 with
  | [] -> l2
  | (x::l1) -> list_union l1 (if List.mem x l2 then l2 else (x::l2))

module LMap
  (* Memoization table.  FIXME: Ideally the keys should be "weak", but
   * I haven't found any such functionality in OCaml's libs.  *)
  = Hashtbl.Make
      (struct type t = lexp let hash = Hashtbl.hash let equal = (==) end)
let fv_memo = LMap.create 1000

let fv_empty = (DB.set_empty)
let fv_union (fv1) (fv2)
  = (DB.set_union fv1 fv2)
let fv_sink n (fvs) = (DB.set_sink n fvs)
let fv_hoist n (fvs) = (DB.set_hoist n fvs)
let fv_erase (fvs) = (fvs)

let rec fv (e : lexp) : (DB.set) =
  let fv' e = match e with
    | Imm _ -> fv_empty
    | Sort (_, _) -> fv_empty
    | Builtin _ -> fv_empty
    | Var (_, i) -> (DB.set_singleton i)
    | Susp (e, s) -> fv (push_susp e s)
    | Let (_, defs, e)
      -> let len = List.length defs in
        let (fvs, _)
          = List.fold_left (fun (fvs, o) (_, e, t)
                            -> (fv_union fvs (fv_union (fv_erase
                                                         (fv_sink o (fv t)))
                                                      (fv e)),
                               o - 1))
                           (fv e, len) defs in
        fv_hoist len fvs
    | Arrow (_, t1, _, t2) -> fv_union (fv t1) (fv_hoist 1 (fv t2))
    | Lambda (_, t, e) -> fv_union (fv_erase (fv t)) (fv_hoist 1 (fv e))
    | Call (f, args)
      -> List.fold_left (fun fvs arg -> fv_union fvs (fv arg))
                       (fv f) args
    | Inductive (_, cases)
      -> SMap.fold
          (fun _ fields s
           -> fv_union
               s
               (fv_hoist (List.length fields)
                  (List.fold_left (fun s (_, t)
                                   -> fv_sink 1 (fv_union s (fv t)))
                     fv_empty fields)))
          cases fv_empty
    | Cons (t, _) -> fv_erase (fv t)
    | Case (_, e, t, cases, def)
      -> let s = fv_union (fv e) (fv_erase (fv t)) in
        let s = match def with
          | None -> s
          | Some (_, e) -> fv_union s (fv_hoist 1 (fv e)) in
        SMap.fold (fun _ (_, fields, e) s
                   -> fv_union s (fv_hoist (List.length fields) (fv e)))
                  cases s
  in
  try LMap.find fv_memo e
  with Not_found
       -> let r = fv' e in
         LMap.add fv_memo e r;
         r

(** Finding the type of a expression.  **)
(* This should never signal any warning/error.  *)

let rec get_type ctx e =
  match e with
  | Imm (Float (_, _)) -> DB.type_float
  | Imm (Integer (_, _)) -> DB.type_int
  | Imm (String (_, _)) -> DB.type_string
  | Imm (Block (_, _, _) | Symbol _ | Node (_, _)) -> DB.type_int
  | Builtin (_, t) -> t
  | Sort (l, s) -> mkSort (l, s + 1)
  | Var (((_, name), idx) as v) -> lookup_type ctx v
  | Susp (e, s) -> get_type ctx (push_susp e s)
  | Let (l, defs, e)
    -> let nctx = DB.lctx_extend_rec ctx defs in
      mkSusp (get_type nctx e) (lexp_defs_subst l S.identity defs)
  | Arrow (v, t1, l, t2)
    (* FIXME: Use `check` here but silencing errors?  *)
    -> (let k1 = get_type ctx t1 in
       let nctx = DB.lexp_ctx_cons ctx v Variable t1 in
       let k2 = get_type nctx t2 in
       match sort_compose ctx l k1 k2 with
       | SortResult k -> k
       | _ -> mkSort (l, 99))
  | Lambda (((l,_) as v), t, e)
    -> (mkArrow (v, t, l,
                get_type (DB.lctx_extend ctx v Variable t)
                         e))
  | Call (f, args)
    -> let ft = get_type ctx f in
      List.fold_left
        (fun ft arg
         -> match lexp_whnf ft ctx with
           | Arrow (v, t1, l, t2)
             -> mkSusp t2 (S.substitute arg)
           | _ -> ft)
        ft args
  | Inductive (l, cases)
    (* FIXME: Use `check` here but silencing errors?  *)
    -> let level
        = SMap.fold
            (fun _ case level ->
              let (level, _, _) =
                List.fold_left
                  (fun (level, ictx, n) (v, t) ->
                    ((match lexp_whnf (get_type ictx t) ictx with
                      | Sort (_, level')
                        -> max level level'
                      | tt -> level),
                     DB.lctx_extend ictx v Variable t,
                     n + 1))
                  (level, ctx, 0)
                  case in
              level)
            cases 0 in
      mkSort (l, level)
  | Case (l, e, ret, branches, default) -> ret
  | Cons (t, (l, name))
    -> (match lexp_whnf t ctx with
       | Inductive (l, constructors)
         -> (try
              let fieldtypes = SMap.find name constructors in
              let rec fieldargs ftypes =
                match ftypes with
                | [] -> let nargs = List.length fieldtypes in
                       mkSusp t (S.shift nargs)
                | (vd, ftype) :: ftypes
                  -> mkArrow (vd, ftype, lexp_location ftype,
                             fieldargs ftypes) in
              fieldargs fieldtypes
            with Not_found -> DB.type_int)
       | _ -> DB.type_int)

(*********** Type erasure, before evaluation.  *****************)

let rec erase_type (lxp: L.lexp): E.elexp =

    match lxp with
        | L.Imm(s)           -> E.Imm(s)
        | L.Builtin(v, _)    -> E.Builtin(v)
        | L.Var(v)           -> E.Var(v)
        | L.Cons(_, s)       -> E.Cons(s)
        | L.Lambda (vdef, _, body) ->
          E.Lambda (vdef, erase_type body)

        | L.Let(l, decls, body)       ->
            E.Let(l, (clean_decls decls), (erase_type body))

        | L.Call(fct, args) ->
            E.Call((erase_type fct), (filter_arg_list args))

        | L.Case(l, target, _, cases, default) ->
            E.Case(l, (erase_type target), (clean_map cases),
                                         (clean_maybe default))

        | L.Susp(l, s)                -> erase_type (L.push_susp l s)

        (* To be thrown out *)
        | L.Arrow _                   -> E.Type lxp
        | L.Sort _                    -> E.Type lxp
        (* Still useful to some extent.  *)
        | L.Inductive(l, _) -> E.Type lxp

and filter_arg_list lst =
  let rec filter_arg_list lst acc =
    match lst with
    | lxp::tl
      -> let acc = (erase_type lxp)::acc in
        filter_arg_list tl acc
    | [] -> List.rev acc in
  filter_arg_list lst []

and clean_decls decls =
  List.map (fun (v, lxp, _) -> (v, (erase_type lxp))) decls

and clean_maybe lxp =
  match lxp with
  | Some (v, lxp) -> Some (v, erase_type lxp)
  | None -> None

and clean_map cases =
  let clean_arg_list lst =
    let rec clean_arg_list lst acc =
      match lst with
      | var::tl
        -> let acc = var::acc in
          clean_arg_list tl acc
      | [] -> List.rev acc in
    clean_arg_list lst [] in

  SMap.map (fun (l, args, expr)
            -> (l, (clean_arg_list args), (erase_type expr)))
    cases


(* opslexp.ml ends here.  *)
