(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2019  Free Software Foundation, Inc.
 *
 *   Author: Pierre Delaunay <pierre.delaunay@hec.ca>
 *   Keywords: languages, lisp, dependent types.
 *
 *   This file is part of Typer.
 *
 *   Typer is free software; you can redistribute it and/or modify it under the
 *   terms of the GNU General Public License as published by the Free Software
 *   Foundation, either version 3 of the License, or (at your option) any
 *   later version.
 *
 *   Typer is distributed in the hope that it will be useful, but WITHOUT ANY
 *   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 *   FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 *   more details.
 *
 *   You should have received a copy of the GNU General Public License along
 *   with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * ---------------------------------------------------------------------------
 *
 * Description:
 *
 * Elaborate Sexp expression into Lexp.
 * This includes type inference, and macro expansion.
 *
 * While elaboration will discover most type errors, strictly speaking
 * this phase does not need to perform any checks, and it can instead presume
 * that the code is well-behaved.  The real type checks (and totality
 * checks) are performed later in OL.check.
 *
 * -------------------------------------------------------------------------- *)

open Util
open Fmt

open Prelexer
open Lexer

open Sexp
open Pexp
open Lexp

open Env
open Debruijn
module DB = Debruijn
module M = Myers
module EV = Eval

open Grammar
module BI = Builtin

module OL = Opslexp
module EL = Elexp

(* dummies *)
let dloc = dummy_location

let parsing_internals = ref false
let btl_folder =
  try Sys.getenv "TYPER_BUILTINS"
  with Not_found -> "./btl"

let fatal = Log.log_fatal ~section:"ELAB"
let error = Log.log_error ~section:"ELAB"
let warning = Log.log_warning ~section:"ELAB"
let info = Log.log_info ~section:"ELAB"

let indent_line str =
  "        > " ^ str
let print_indent_line str =
  print_endline (indent_line str)
let print_details to_name to_str elem =
  print_indent_line ((to_name elem) ^ ": " ^ (to_str elem))
let lexp_print_details lexp () =
  print_details lexp_name lexp_string lexp
let value_print_details value () =
  print_details value_name value_string value

let lexp_error loc lexp =
  error ~loc ~print_action:(lexp_print_details lexp)
let lexp_fatal loc lexp =
  fatal ~loc ~print_action:(lexp_print_details lexp)
let value_fatal loc value =
  fatal ~loc ~print_action:(value_print_details value)

(** Type info returned by elaboration.  *)
type sform_type =
  | Checked       (* Checked that the expression has the requested type.  *)
  | Inferred of ltype            (* Hasn't looked as the requested type.  *)
  | Lazy    (* Hasn't looked as the requested type, nor inferred a type.  *)

type special_forms_map =
  (elab_context -> location -> sexp list -> ltype option
   -> (lexp * sform_type)) SMap.t

let special_forms : special_forms_map ref = ref SMap.empty
let type_special_form = BI.new_builtin_type "Special-Form" type0

let add_special_form (name, func) =
  BI.add_builtin_cst name (mkBuiltin ((dloc, name), type_special_form));
  special_forms := SMap.add name func (!special_forms)

let get_special_form name =
  SMap.find name (!special_forms)

(* Used for sform_load because sform are
 * added before default context's function. *)
let sform_default_ectx = ref empty_elab_context

(* The prefix `elab_check_` is used for functions which do internal checking
 * (i.e. errors signalled here correspond to internal errors rather than
 * to errors in the user's code).  *)

let elab_check_sort (ctx : elab_context) lsort var ltp =
  match (try OL.lexp_whnf lsort (ectx_to_lctx ctx)
         with e ->
           info ~print_action:(fun _ -> lexp_print lsort; print_newline ())
             ~loc:(lexp_location lsort)
             "Exception during whnf of sort:";
           raise e) with
  | Sort (_, _) -> () (* All clear!  *)
  | _ -> let lexp_string e = lexp_string (L.clean e) in
        let typestr = lexp_string ltp ^ " : " ^ lexp_string lsort in
        match var with
        | (l, None) -> lexp_error l ltp
                        ("`" ^ typestr ^ "` is not a proper type")
        | (l, Some name)
          -> lexp_error l ltp
                       ("Type of `" ^ name ^ "` is not a proper type: "
                        ^ typestr)

let elab_check_proper_type (ctx : elab_context) ltp var =
  try elab_check_sort ctx (OL.check (ectx_to_lctx ctx) ltp) var ltp
  with e -> match e with
            | Log.Stop_Compilation _ -> raise e
            | _ ->
               info
                 ~print_action:(fun _ ->
                   print_lexp_ctx (ectx_to_lctx ctx); print_newline ()
                 )
                 ~loc:(lexp_location ltp)
                 ("Exception while checking type `" ^ (lexp_string ltp) ^ "`"
                  ^ (match var with
                     | (_, None) -> ""
                     | (_, Some name)
                       -> " of var `" ^ name ^ "`"));
               raise e

let elab_check_def (ctx : elab_context) var lxp ltype =
  let lctx = ectx_to_lctx ctx in
  let loc = lexp_location lxp in

  let lexp_string e = lexp_string (L.clean e) in
  let ltype' = try OL.check lctx lxp
    with e -> match e with
      | Log.Stop_Compilation _ -> raise e
      | _ ->
         info
           ~print_action:(fun _ ->
             lexp_print_details lxp ();
             print_lexp_ctx (ectx_to_lctx ctx);
             print_newline ()
           )
           ~loc
           "Error while type-checking";
         raise e in
  if (try OL.conv_p (ectx_to_lctx ctx) ltype ltype'
      with e ->
        info ~print_action:(lexp_print_details lxp)
          ~loc
          ("Exception while conversion-checking types: "
           ^ lexp_string ltype ^ " and " ^ lexp_string ltype');
        raise e)
  then
    elab_check_proper_type ctx ltype var
  else
    fatal
      ~print_action:(fun _ ->
        List.iter print_indent_line [
            (match var with (_, Some n) -> n | _ -> "<anon>")
            ^ " = " ^ lexp_string lxp ^ " !: " ^ lexp_string ltype;
            "                    because";
            lexp_string ltype' ^ " != " ^ lexp_string ltype
      ])
      ~loc
      "Type check error: ¡¡ctx_define error!!"

let ctx_extend (ctx: elab_context) (var : vname) def ltype =
  elab_check_proper_type ctx ltype var;
  ectx_extend ctx var def ltype

let ctx_define (ctx: elab_context) var lxp ltype =
  elab_check_def ctx var lxp ltype;
  ectx_extend ctx var (LetDef (0, lxp)) ltype

let ctx_define_rec (ctx: elab_context) decls =
  let nctx = ectx_extend_rec ctx decls in
  let _ = List.fold_left (fun n (var, lxp, ltp)
                          -> elab_check_proper_type
                              nctx (push_susp ltp (S.shift n)) var;
                            n - 1)
                         (List.length decls)
                         decls in
  let _ = List.fold_left (fun n (var, lxp, ltp)
                          -> elab_check_def nctx var lxp
                                           (push_susp ltp (S.shift n));
                            n - 1)
                         (List.length decls)
                         decls in
  nctx

(*  The main job of lexp (currently) is to determine variable name (index)
 *  and to regroup type specification with their variable
 *
 *  elab_context is composed of two environment: senv and env.
 *  the senv environment is used to find the correct debruijn index
 *  while the env environment is used to save variable information.
 *  the env environment look a lot like the runtime environment that will be
 *  used in the eval section.
 *
 *  While most of the time senv and env will be synchronised it is
 *  possible for env to hold more variables than senv since senv is a map
 *  which does not allow multiple definition while env does.
 *
 *)

(*
 *      Type Inference
 * --------------------- *)
(* Parsing a Pexp into an Lexp is really "elaboration", i.e. it needs to
 * infer the types and perform macro-expansion.
 *
 * More specifically, we do it with 2 mutually recursive functions:
 * - `check` takes a Pexp along with its expected type and return an Lexp
 *   of that type (hopefully)
 * - `infer` takes a Pexp and infers its type (which it returns along with
 *   the Lexp).
 * This is the idea of "bidirectional type checking", which minimizes
 * the amount of "guessing" and/or annotations.  Since we infer types anyway
 * it doesn't really reduce the amount of type annotations for us, but it
 * reduces the amount of inference and checking, i.e. it reduces the number of
 * metavars we create/instantiate/dereference as well as the number of call to
 * the unification algorithm.
 * Basically guessing/annotations is only needed at those few places where the
 * code is not fully-normalized, which in normal programs is only in "let"
 * definitions.
 *)

let mkDummy_type ctx loc = DB.type_string

let sdform_define_operator (ctx : elab_context) loc sargs _ot : elab_context =
  match sargs with
  | [String (_, name); l; r]
    -> let level s = match s with
        | Symbol (_, "") -> None
        | Integer (_, n) -> Some n
        | _ -> sexp_error (sexp_location s) "Expecting an integer or ()"; None in
      let (grm, a, b, c) = ctx in
      (SMap.add name (level l, level r) grm, a, b, c)
  | [o; _; _]
    -> sexp_error (sexp_location o) "Expecting a string"; ctx
  | _
    -> sexp_error loc "define-operator expects 3 argument"; ctx

let sform_dummy_ret ctx loc =
  (mkImm (String (loc,"#error#dummy#")),
   Inferred DB.type_string)

let elab_varref ctx (loc, name)
  = try
      let idx = senv_lookup name ctx in
      let id = (loc, [name]) in
      let lxp = mkVar (id, idx) in
      let ltp = env_lookup_type ctx (id, idx) in
      (lxp, Inferred ltp)
  with Senv_Lookup_Fail xs ->
    (let relateds =
       if ((List.length xs) > 0) then
         ". Did you mean: " ^ (String.concat " or " xs) ^" ?"
       else "" in
     sexp_error loc ("The variable: `" ^ name ^
                       "` was not declared" ^ relateds);
     sform_dummy_ret ctx loc)

let elab_p_id ((l,name) : symbol) : vname =
  (l, match name with "_" -> None | _ -> Some name)

(* Infer or check, as the case may be.  *)
let rec elaborate ctx se ot =
  match se with
  (* Rewrite SYM to `typer-identifier SYM`.  *)
  | Symbol ((loc, name) as id)
    -> if not (name = "typer-identifier") then
        elaborate ctx (Node (Symbol (loc, "typer-identifier"), [se])) ot
      (* Break the inf-recursion!  *)
      else elab_varref ctx id

  (* Rewrite IMM to `typer-immediate IMM`.  *)
  | (Integer _ | Float _ | String _ | Block _)
    -> let l = sexp_location se in
      elaborate ctx (Node (Symbol (l, "typer-immediate"), [se])) ot

  | Node (se, []) -> elaborate ctx se ot

  | Node (func, args)
    -> let (f, t) as ft = infer func ctx in
      if (OL.conv_p (ectx_to_lctx ctx) t type_special_form) then
        elab_special_form ctx f args ot
      else if (OL.conv_p (ectx_to_lctx ctx) t
                         (BI.get_predef "Macro" ctx)) then
        elab_macro_call ctx f args ot
      else
        (* FIXME: I'd like to do something like:
         *    elaborate ctx (Node (Symbol (l, "typer-funcall"), func::args)) ot
         * but that forces `typer-funcall` to elaborate `func` a second time!
         * Maybe I should only elaborate `func` above if it's a symbol
         * (and maybe even use `elaborate_varref` rather than indirecting
         * through `typr-identifier`)?  *)
        elab_call ctx ft args

and infer (p : sexp) (ctx : elab_context): lexp * ltype =
  match elaborate ctx p None with
  | (_, Checked) -> fatal ~loc:(sexp_location p) "`infer` got Checked!"
  | (e, Lazy) -> (e, OL.get_type (ectx_to_lctx ctx) e)
  | (e, Inferred t) -> (e, t)

and elab_special_form ctx f args ot =
  let loc = lexp_location f in
  match OL.lexp_whnf f (ectx_to_lctx ctx) with
  | Builtin ((_, name), _) ->
     (* Special form.  *)
     (get_special_form name) ctx loc args ot

  | _ -> lexp_error loc f ("Unknown special-form: " ^ lexp_string f);
        sform_dummy_ret ctx loc

and infer_type pexp ectx var =
  (* We could also use lexp_check with an argument of the form Sort (...),
   * except that we don't know which universe level it will be.  *)
  let t, s = infer pexp ectx in
  (match OL.lexp_whnf s (ectx_to_lctx ectx) with
   | Sort (_, _) -> () (* All clear!  *)
   | _ ->
      let lexp_string e = lexp_string (L.clean e) in
      let typestr = lexp_string t ^ " : " ^ lexp_string s in
      match var with
      | (l, None) -> lexp_error l t
                      ("`" ^ typestr ^ "` is not a proper type")
      | (l, Some name)
        -> lexp_error l t
            ("Type of `" ^ name ^ "` is not a proper type: "
             ^ typestr));
  t

and lexp_let_decls declss (body: lexp) ctx =
  List.fold_right (fun decls lxp -> mkLet (dloc, decls, lxp))
                  declss body

and unify_with_arrow ctx tloc lxp var aty
  = let (l, _) = var in
    let arg = mkDummy_type ctx l in
    let nctx = ectx_extend ctx var Variable arg in
    lexp_error tloc lxp ("Type " ^ lexp_string lxp
                         ^ " is not a function type");
    (arg, mkDummy_type nctx l)

and check (p : sexp) (t : ltype) (ctx : elab_context): lexp =
  let (e, ot) = elaborate ctx p (Some t) in
  match ot with
  | Checked -> e
  | _ -> let inferred_t = match ot with Inferred t -> t
                                      | _ -> OL.get_type (ectx_to_lctx ctx) e in
        check_inferred ctx e inferred_t t

and check_inferred ctx e inferred_t t =
  (match OL.conv_p (ectx_to_lctx ctx) inferred_t t with
   | false
     -> lexp_error (lexp_location e) e
                  ("Type mismatch!  Context expected `"
                   ^ lexp_string t ^ "` but expression has type `"
                   ^ lexp_string inferred_t ^ "`")
   | true -> ());
  e

(* Lexp.case can sometimes be inferred, but we prefer to always check.  *)
and check_case rtype (loc, target, ppatterns) ctx =
  (* Helpers *)

  let pat_string p = sexp_string (pexp_u_pat p) in

    let uniqueness_warn pat =
      warning ~loc:(pexp_pat_location pat)
              ("Pattern " ^ pat_string pat
               ^ " is a duplicate.  It will override previous pattern.") in

    let check_uniqueness pat name map =
      if SMap.mem name map then uniqueness_warn pat in

    (* get target and its type *)
    let tlxp, tltp = infer target ctx in
    (* FIXME: We need to be careful with whnf: while the output is "equivalent"
     * to the input, it's not necessarily as readable/efficient.
     * So try to reuse the "non-whnf" form whenever possible.  *)
    let constructors = match OL.lexp_whnf tltp (ectx_to_lctx ctx) with
      (* FIXME: Check that it's `Inductive' only after performing Unif.unify
       * with the various branches, so that we can infer the type
       * of the target from the type of the patterns.  *)
      | Inductive (_, constructors) -> constructors
      | _ -> lexp_error (sexp_location target) tlxp
                       ("Can't `case` on objects of this type: "
                        ^ lexp_string tltp);
            SMap.empty in

    (*  Read patterns one by one *)
    let fold_fun (lbranches, dflt) (pat, pexp) =

      let add_default v =
        (if dflt != None then uniqueness_warn pat);
        let nctx = ctx_extend ctx v Variable tltp in
        let rtype' = mkSusp rtype (S.shift (M.length (ectx_to_lctx nctx)
                                            - M.length (ectx_to_lctx ctx))) in
        let lexp = check pexp rtype' nctx in
        lbranches, Some (v, lexp) in

      let add_branch pctor pargs =
        let loc = sexp_location pctor in
        match pctor with
        | Symbol (_, cons_name) when SMap.mem cons_name constructors
          -> let _ = check_uniqueness pat cons_name lbranches in
            let cargs = SMap.find cons_name constructors in

            let subst = S.identity in
            let rec make_nctx ctx   (* elab context.  *)
                              s     (* Pending substitution.  *)
                              pargs (* Pattern arguments.  *)
                              cargs (* Constructor arguments.  *)
                              acc = (* Accumulated result.  *)
              match (pargs, cargs) with
              | ([], []) -> ctx, List.rev acc
              | _::_, []
                -> sexp_error loc "Too many pattern args to the constructor";
                  make_nctx ctx s [] [] acc
              | (var::pargs, (_, fty)::cargs)
                -> let nctx = ctx_extend ctx var Variable (mkSusp fty s) in
                  make_nctx nctx (ssink var s) pargs cargs
                            (var::acc)
              | [], (fname, fty)::cargs
                -> let var = (loc, None) in
                  let nctx = ctx_extend ctx var Variable (mkSusp fty s) in
                  sexp_error loc
                    ("Missing pattern for field"
                     ^ (match fname with (_, Some n) -> " `" ^ n ^ "`"
                                       | _ -> ""));
                  make_nctx nctx (ssink var s) [] cargs
                            (var::acc) in
            let nctx, fargs = make_nctx ctx subst pargs cargs [] in
            let rtype' = mkSusp rtype
                                (S.shift (M.length (ectx_to_lctx nctx)
                                          - M.length (ectx_to_lctx ctx))) in
            let lexp = check pexp rtype' nctx in
            SMap.add cons_name (loc, fargs, lexp) lbranches,
            dflt
        | _ -> sexp_error loc "Not a constructor"; lbranches, dflt
      in

      match pat with
      | Ppatsym ((_, None) as var) -> add_default var
      | Ppatsym ((l, Some name) as var)
        -> if SMap.mem name constructors then
            add_branch (Symbol (l, name)) []
          else add_default var (* A named default branch.  *)

      | Ppatcons (pctor, pargs) -> add_branch pctor pargs in

    let (lpattern, dflt) =
        List.fold_left fold_fun (SMap.empty, None) ppatterns in

    mkCase (loc, tlxp, rtype, lpattern, dflt)

and elab_macro_call ctx func args ot =
  let sxp = match lexp_expand_macro (lexp_location func)
                                    func args ctx ot with
    | Vsexp (sxp) -> sxp
    | v -> value_fatal (lexp_location func) v
            "Macros should return a Sexp" in
  elaborate ctx sxp ot

(*  Identify Call Type and return processed call.  *)
and elab_call ctx (func, ltp) (sargs: sexp list) =

  let rec handle_fun_args largs sargs ltp =
    let ltp' = OL.lexp_whnf ltp (ectx_to_lctx ctx) in
    match sargs, ltp' with
    | [], _
      -> largs, ltp

    | sarg :: sargs, _
      -> let (arg_type, ret_type) = match ltp' with
          | Arrow (_, arg_type, _, ret_type)
            -> (arg_type, ret_type)
          | _ -> unify_with_arrow ctx (sexp_location sarg)
                                 ltp' (dloc, None) None in
        let larg = check sarg arg_type ctx in
        handle_fun_args (larg :: largs) sargs
                        (L.mkSusp ret_type (S.substitute larg)) in

  let (largs, ret_type) = handle_fun_args [] sargs ltp in
  (mkCall (func, List.rev largs), Inferred ret_type)

(*  Parse inductive type definition.  *)
and lexp_parse_inductive ctors ctx =

  let make_args (args:(vname * sexp) list) ctx
      : (vname * ltype) list =
    let nctx = ectx_new_scope ctx in
    let rec loop args acc ctx =
          match args with
          | [] -> List.rev acc
          | (var, exp)::tl
            -> let lxp = infer_type exp ctx var in
              let nctx = ectx_extend ctx var Variable lxp in
              loop tl ((var, lxp)::acc) nctx in
    loop args [] nctx in

  List.fold_left
    (fun lctors ((_, name), args) ->
      SMap.add name (make_args args ctx) lctors)
    SMap.empty ctors

and track_fv rctx lctx e =
  let (fvs) = OL.fv e in
  let nc = EV.not_closed rctx fvs in
  if nc = [] then
    "a bug"
  else let tfv i =
         let name = match Myers.nth i rctx with
           | ((_, Some n),_) -> n
           | _ -> "<anon>" in
         match Myers.nth i lctx with
         | (_, LetDef (o, e), _)
           -> let drop = i + 1 - o in
             if drop <= 0 then
               "somevars[" ^ string_of_int i ^ "-" ^ string_of_int o ^ "]"
             else
               name ^ " ("
               ^ track_fv (Myers.nthcdr drop rctx)
                          (Myers.nthcdr drop lctx)
                          (L.clean e)
               ^ ")"
         | _ -> name
       in String.concat " " (List.map tfv nc)

and lexp_eval ectx e =
  let e = L.clean e in
  let ee = OL.erase_type e in
  let rctx = EV.from_ectx ectx in

  if not (EV.closed_p rctx (OL.fv e)) then
    lexp_error (lexp_location e) e
               ("Expression `" ^ lexp_string e ^ "` is not closed: "
                ^ track_fv rctx (ectx_to_lctx ectx) e);

  try EV.eval ee rctx
  with exc ->
    let eval_trace = fst (EV.get_trace ()) in
    info ~print_action:(fun _ -> EV.print_eval_trace (Some eval_trace))
      "Exception happened during evaluation:";
    raise exc

and lexp_expand_macro loc macro_funct sargs ctx (ot : ltype option)
    : value_type =

  (* Build the function to be called *)
  let macro_expand = BI.get_predef "Macro_expand" ctx in
  (* FIXME: Rather than remember the lexp of "expand_macro" in predef,
   * we should remember its value so we don't have to re-eval it everytime.  *)
  let macro_expand = lexp_eval ctx macro_expand in
  (* FIXME: provide `ot` (the optional expected type) for non-decl macros.  *)
  let macro = lexp_eval ctx macro_funct in
  let args = [macro; BI.o2v_list sargs] in

  (* FIXME: Make a proper `Var`.  *)
  EV.eval_call loc (EL.Var ((DB.dloc, ["expand_macro"]), 0)) ([], [])
               macro_expand args

(* Print each generated decls *)
(* and sexp_decls_macro_print sxp_decls =
 *   match sxp_decls with
 *     | Node (Symbol (_, "_;_"), decls) ->
 *       List.iter (fun sxp -> sexp_decls_macro_print sxp) decls
 *     | e -> sexp_print e; print_string "\n" *)

and lexp_decls_macro (loc, mname) sargs ctx: sexp =
  try let lxp, ltp = infer (Symbol (loc, mname)) ctx in

      (* FIXME: Check that (conv_p ltp Macro)!  *)
      let ret = lexp_expand_macro loc lxp sargs ctx None in
      match ret with
      | Vsexp (sexp) -> sexp
      | _ -> fatal ~loc ("Macro `" ^ mname ^ "` should return a Sexp")

  with e ->
    fatal ~loc ("Macro `" ^ mname ^ "` not found")

and lexp_check_decls (ectx : elab_context) (* External context.  *)
                     (nctx : elab_context) (* Context with type declarations. *)
                     (defs : (symbol * sexp) list)
    : (vname * lexp * ltype) list * elab_context =
  (* Preserve the new operators added to nctx.  *)
  let ectx = let (_,   a, b, c) = ectx in
             let (grm, _, _, _) = nctx in
             (grm, a, b, c) in
  let (declmap, nctx)
    = List.fold_right
                  (fun ((l, vname), pexp) (map, nctx) ->
                    let i = senv_lookup vname nctx in
                    assert (i < List.length defs);
                    match Myers.nth i (ectx_to_lctx nctx) with
                    | (v', ForwardRef, t)
                      -> let adjusted_t = push_susp t (S.shift (i + 1)) in
                        let e = check pexp adjusted_t nctx in
                        let (grm, ec, lc, sl) = nctx in
                        let d = (v', LetDef (i + 1, e), t) in
                        (IMap.add i ((l, Some vname), e, t) map,
                         (grm, ec, Myers.set_nth i d lc, sl))
                    | _ -> Log.internal_error "Defining same slot!")
                  defs (IMap.empty, nctx) in
  let decls = List.rev (List.map (fun (_, d) -> d) (IMap.bindings declmap)) in
  decls, ctx_define_rec ectx decls

and lexp_decls_1
      (sdecls : sexp list)
      (ectx : elab_context)                       (* External ctx.  *)
      (nctx : elab_context)                       (* New context.  *)
      (pending_decls : location SMap.t)           (* Pending type decls. *)
      (pending_defs : (symbol * sexp) list)       (* Pending definitions. *)
    : (vname * lexp * ltype) list * sexp list * elab_context =

  let rec lexp_decls_1 sdecls ectx nctx pending_decls pending_defs =
  match sdecls with
  | [] -> (if not (SMap.is_empty pending_decls) then
            let (s, loc) = SMap.choose pending_decls in
              error ~loc ("Variable `" ^ s ^ "` declared but not defined!")
          else
            assert (pending_defs == []));
         [], [], nctx

  | Symbol (_, "") :: sdecls
    -> lexp_decls_1 sdecls ectx nctx pending_decls pending_defs

  | Node (Symbol (_, ("_;_" (* | "_;" | ";_" *))), sdecls') :: sdecls
    -> lexp_decls_1 (List.append sdecls' sdecls)
                   ectx nctx pending_decls pending_defs

  | Node (Symbol (loc, "_:_"), args) :: sdecls
    (* FIXME: Move this to a "special form"!  *)
    -> (match args with
       | [Symbol (loc, vname); stp]
         -> let ltp = infer_type stp nctx (loc, Some vname) in
           if SMap.mem vname pending_decls then
             (* Don't burp: take'em all and unify!  *)
             let pt_idx = senv_lookup vname nctx in
             (* Take the previous type annotation.  *)
             let pt = match Myers.nth pt_idx (ectx_to_lctx nctx) with
               | (_, ForwardRef, t) -> push_susp t (S.shift (pt_idx + 1))
               | _ -> Log.internal_error "Var not found at its index!" in
             (* Unify it with the new one.  *)
             let _ = match OL.conv_p (ectx_to_lctx nctx) ltp pt with
              | false
                -> lexp_error loc ltp
                             ("New type annotation `"
                              ^ lexp_string ltp ^ "` incompatible with previous `"
                              ^ lexp_string pt ^ "`")
              | true -> () in
             lexp_decls_1 sdecls ectx nctx pending_decls pending_defs
           else if List.exists (fun ((_, vname'), _) -> vname = vname')
                               pending_defs then
             (error ~loc ("Variable `" ^ vname ^ "` already defined!");
              lexp_decls_1 sdecls ectx nctx pending_decls pending_defs)
           else lexp_decls_1 sdecls ectx
                             (ectx_extend nctx (loc, Some vname) ForwardRef ltp)
                             (SMap.add vname loc pending_decls)
                             pending_defs
       | _ -> error ~loc "Invalid type declaration syntax";
             lexp_decls_1 sdecls ectx nctx pending_decls pending_defs)

  | Node (Symbol (l, "_=_") as head, args) :: sdecls
    (* FIXME: Move this to a "special form"!  *)
    -> (match args with
      | [Symbol ((l, vname)); sexp]
           when SMap.is_empty pending_decls
        -> assert (pending_defs == []);
          (* Used to be true before we added define-operator.  *)
          (* assert (ectx == nctx); *)
          let (lexp, ltp) = infer sexp nctx in
          let var = (l, Some vname) in
          (* Lexp decls are always recursive, so we have to shift by 1 to
           * account for the extra var (ourselves).  *)
          [(var, mkSusp lexp (S.shift 1), ltp)], sdecls,
          ctx_define nctx var lexp ltp

      | [Symbol (l, vname); sexp]
        -> if SMap.mem vname pending_decls then
            let decl_loc = SMap.find vname pending_decls in
            let v = ({file = l.file;
                      line = l.line;
                      column = l.column;
                      docstr = String.concat "\n" [decl_loc.docstr; l.docstr]},
                     vname) in
            let pending_decls = SMap.remove vname pending_decls in
            let pending_defs = ((v, sexp) :: pending_defs) in
            if SMap.is_empty pending_decls then
              let nctx = ectx_new_scope nctx in
              let decls, nctx = lexp_check_decls ectx nctx pending_defs in
              decls, sdecls, nctx
            else
              lexp_decls_1 sdecls ectx nctx pending_decls pending_defs

          else
            (error ~loc:l ("`" ^ vname ^ "` defined but not declared!");
             lexp_decls_1 sdecls ectx nctx pending_decls pending_defs)

      | [Node (Symbol s, args) as d; body]
        -> (* FIXME: Make it a macro (and don't hardcode `lambda_->_`)!  *)
         lexp_decls_1 ((Node (head,
                              [Symbol s;
                               Node (Symbol (sexp_location d, "lambda_->_"),
                                     [sexp_u_list args; body])]))
                       :: sdecls)
                      ectx nctx pending_decls pending_defs

      | _ -> error ~loc:l "Invalid definition syntax";
            lexp_decls_1 sdecls ectx nctx pending_decls pending_defs)

  | Node (Symbol (l, "define-operator"), args) :: sdecls
    (* FIXME: Move this to a "special form"!  *)
    -> lexp_decls_1 sdecls ectx (sdform_define_operator nctx l args None)
                   pending_decls pending_defs

  | Node (Symbol ((l, _) as v), sargs) :: sdecls
    -> (* expand macro and get the generated declarations *)
     let sdecl' = lexp_decls_macro v sargs nctx in
     lexp_decls_1 (sdecl' :: sdecls) ectx nctx
                  pending_decls pending_defs

  | sexp :: sdecls
    -> error ~loc:(sexp_location sexp) "Invalid declaration syntax";
      lexp_decls_1 sdecls ectx nctx pending_decls pending_defs

  in (EV.set_getenv nctx;
      let res = lexp_decls_1 sdecls ectx nctx pending_decls pending_defs in
        (Log.stop_on_error (); res))

and lexp_p_decls (sdecls : sexp list) (ctx : elab_context)
    : ((vname * lexp * ltype) list list * elab_context) =
  let impl sdecls ctx = match sdecls with
    | [] -> [], ectx_new_scope ctx
    | _ -> let decls, sdecls, nctx = lexp_decls_1 sdecls ctx ctx SMap.empty [] in
      let declss, nnctx = lexp_p_decls sdecls nctx in
      decls :: declss, nnctx in
  let res = impl sdecls ctx in (Log.stop_on_error (); res)

and lexp_parse_all (p: sexp list) (ctx: elab_context) : lexp list =
  let res = List.map (fun pe -> let e, _ = infer pe ctx in e) p in
    (Log.stop_on_error (); res)

and lexp_parse_sexp (ctx: elab_context) (e : sexp) : lexp =
  let e, _ = infer e ctx in (Log.stop_on_error (); e)

(* --------------------------------------------------------------------------
 *  Special forms implementation
 * -------------------------------------------------------------------------- *)

and sform_declexpr ctx loc sargs ot =
  match List.map (lexp_parse_sexp ctx) sargs with
  | [Var((_, vn), vi)]
    -> (match DB.env_lookup_expr ctx ((loc, vn), vi) with
       | Some lxp -> (lxp, Lazy)
       | None -> error ~loc "no expr available";
                sform_dummy_ret ctx loc)
  | _ -> error ~loc "declexpr expects one argument";
        sform_dummy_ret ctx loc


let sform_decltype ctx loc sargs ot =
  match List.map (lexp_parse_sexp ctx) sargs with
  | [Var((_, vn), vi)]
    -> (DB.env_lookup_type ctx ((loc, vn), vi), Lazy)
  | _ -> error ~loc "decltype expects one argument";
        sform_dummy_ret ctx loc

let builtin_value_types : ltype option SMap.t ref = ref SMap.empty

let sform_built_in ctx loc sargs ot =
  match !parsing_internals, sargs with
  | true, [String (_, name)]
    -> (match ot with
       | Some ltp
         -> let ltp' = OL.lexp_close (ectx_to_lctx ctx) ltp in
           let bi = mkBuiltin ((loc, name), ltp') in
           if not (SMap.mem name (!EV.builtin_functions)) then
             sexp_error loc ("Unknown built-in `" ^ name ^ "`");
           BI.add_builtin_cst name bi;
           (bi, Checked)
       | None -> error ~loc "Built-in's type not provided by context!";
                sform_dummy_ret ctx loc)

  | true, _ -> error ~loc "Wrong Usage of `Built-in`";
              sform_dummy_ret ctx loc

  | false, _ -> error ~loc "Use of `Built-in` in user code";
               sform_dummy_ret ctx loc

let sform_datacons ctx loc sargs ot =
  match sargs with
  | [t; Symbol ((sloc, cname) as sym)]
    -> let idt, _ = infer t ctx in
      (mkCons (idt, sym), Lazy)

  | [_;_] -> sexp_error loc "Second arg of ##constr should be a symbol";
            sform_dummy_ret ctx loc
  | _ -> sexp_error loc "##constr requires two arguments";
        sform_dummy_ret ctx loc

let elab_datacons_arg s = match s with
  | Node (Symbol (_, "_:_"), [Symbol s; t])
    -> (elab_p_id s, t)
  | _ -> ((sexp_location s, None), s)

let elab_typecons_arg arg : (vname * sexp) =
  match arg with
  | Node (Symbol (_, "_:_"), [Symbol (l,name); e])
    -> ((l, Some name), e)
  | _ -> sexp_error ~print_action:(fun _ -> sexp_print arg; print_newline ())
           (sexp_location arg)
           "Unrecognized formal arg";
         ((sexp_location arg, None), arg)

let sform_typecons ctx loc sargs ot =
  let ctors
    = List.fold_right
        (fun case pcases
         -> match case with
           (* read Constructor name + args => Type ((Symbol * args) list) *)
           | Node (Symbol s, cases)
             -> (s, List.map elab_datacons_arg cases)::pcases
           (* This is a constructor with no args *)
           | Symbol s -> (s, [])::pcases

           | _ -> sexp_error (sexp_location case)
                   "Unrecognized constructor declaration";
                 pcases)
        sargs [] in

  let map_ctor = lexp_parse_inductive ctors ctx in
  (mkInductive (loc, map_ctor), Lazy)

let sform_hastype ctx loc sargs ot =
  match sargs with
  | [se; st] -> let lt = infer_type st ctx (loc, None) in
               let le = check se lt ctx in
               (le, Inferred lt)
  | _ -> sexp_error loc "##_:_ takes two arguments";
        sform_dummy_ret ctx loc

let sform_arrow ctx loc sargs ot =
  match sargs with
  | [st1; st2]
    -> let (v, st1) = match st1 with
        | Node (Symbol (_, "_:_"), [Symbol v; st1]) -> (elab_p_id v, st1)
        | _ -> ((sexp_location st1, None), st1) in
      let lt1 = infer_type st1 ctx v in
      let nctx = ectx_extend ctx v Variable lt1 in
      let lt2 = infer_type st2 nctx (sexp_location st2, None) in
      (mkArrow (v, lt1, loc, lt2), Lazy)
  | _ -> sexp_error loc "##_->_ takes two arguments";
        sform_dummy_ret ctx loc

let sform_immediate ctx loc sargs ot =
  match sargs with
  | [(String _) as se]  -> mkImm (se), Inferred DB.type_string
  | [(Integer _) as se] -> mkImm (se), Inferred DB.type_int
  | [(Float _) as se]   -> mkImm (se), Inferred DB.type_float
  | [Block (sl, pts, el)]
    -> let grm = ectx_get_grammar ctx in
      let tokens = lex default_stt pts in
      let (se, _) = sexp_parse_all grm tokens None in
      elaborate ctx se ot
  | [se]
    -> (sexp_error loc ("Non-immediate passed to ##typer-immediate");
       sform_dummy_ret ctx loc)
  | _
    -> (sexp_error loc ("Too many args to ##typer-immediate");
       sform_dummy_ret ctx loc)


let sform_identifier ctx loc sargs ot =
  match sargs with
  | [Symbol (l,name)]
       when String.length name >= 1 && String.get name 0 == '#'
    -> if String.length name > 2 && String.get name 1 == '#' then
        let name = string_sub name 2 (String.length name) in
        try let (e,t) = SMap.find name (! BI.lmap) in
            (e, Inferred t)
        with Not_found
             -> sexp_error l ("Unknown builtin `" ^ name ^ "`");
               sform_dummy_ret ctx loc
      else (sexp_error l ("Invalid special identifier `" ^ name ^ "`");
            sform_dummy_ret ctx loc)

  (* Normal identifier.  *)
  | [Symbol id] -> elab_varref ctx id

  | [se]
    -> (sexp_error loc ("Non-symbol passed to ##typer-identifier");
       sform_dummy_ret ctx loc)

  | _
    -> (sexp_error loc ("Too many args to ##typer-identifier");
       sform_dummy_ret ctx loc)

let rec sform_lambda ctx loc sargs ot' =
  match sargs with
  | [sargs; sbody]
    -> let sargs = sexp_p_list sargs ["_:_"] in
      let rec do_all_args sargs ctx ot = match sargs with
        | [] -> elaborate ctx sbody ot
        | sarg :: sargs
          -> let (arg, ost1) = match sarg with
              | Node (Symbol (_, "_:_"), [Symbol arg; st])
                -> (elab_p_id arg, Some st)
              | Symbol arg -> (elab_p_id arg, None)
              | _ -> sexp_error (sexp_location sarg)
                      "Unrecognized lambda argument";
                    ((dummy_location, None), None) in

            let olt1 = match ost1 with
              | Some st -> Some (infer_type st ctx arg)
              | _ -> None in

            let mklam lt1 olt2 =
              let nctx = ectx_extend ctx arg Variable lt1 in
              let (lbody, alt) = do_all_args sargs nctx olt2 in
              (mkLambda (arg, lt1, lbody),
               match alt with
               | Inferred lt2 -> Inferred (mkArrow (arg, lt1, loc, lt2))
               | _ -> alt) in

            (match ot with
             | None -> mklam (match olt1 with
                             | Some lt1 -> lt1
                             | None -> mkDummy_type (ectx_to_lctx ctx) loc)
                        None
             (* Read var type from the provided type *)
             | Some t
               -> match OL.lexp_whnf t (ectx_to_lctx ctx) with
                 | Arrow ((l, v), lt1, _, lt2)
                   -> (match olt1 with
                      | None -> ()
                      | Some lt1'
                        -> if not (OL.conv_p (ectx_to_lctx ctx) lt1 lt1')
                          then lexp_error (lexp_location lt1') lt1'
                                 ("Type mismatch!  Context expected `"
                                  ^ lexp_string lt1 ^ "`"));
                     (* Apply a "dummy" substitution which replace #0 with #0
                      * in order to account for the fact that `arg` and `v`
                      * might not be the same name!  *)
                     let vn = oname2names arg in
                     let s = S.cons (mkVar (vn, 0)) (S.shift 1) in
                     mklam lt1 (Some (mkSusp lt2 s))
                     (* mklam lt1 (Some lt2) *)

                 | lt
                   -> let (lt1, lt2) = unify_with_arrow ctx loc lt arg olt1
                     in mklam lt1 (Some lt2)) in
      do_all_args sargs ctx ot'

  | _ -> sexp_error loc ("##lambda_->_ takes two arguments");
        sform_dummy_ret ctx loc

let rec sform_case ctx loc sargs ot = match sargs with
  | [Node (Symbol (_, "_|_"), se :: scases)]
    -> let parse_case branch = match branch with
        | Node (Symbol (_, "_=>_"), [pat; code])
          -> (pexp_p_pat pat, code)
        | _ -> let l = (sexp_location branch) in
              sexp_error l "Unrecognized simple case branch";
              (Ppatsym (l, None), Symbol (l, "?")) in
      let pcases = List.map parse_case scases in
      let t = match ot with
        | Some t -> t
        | None -> mkDummy_type (ectx_to_lctx ctx) loc in
      let le = check_case t (loc, se, pcases) ctx in
      (le, match ot with Some _ -> Checked | None -> Inferred t)

  (* In case there are no branches, pretend there was a | anyway.  *)
  | [e] -> sform_case ctx loc [Node (Symbol (loc, "_|_"), sargs)] ot
  | _ -> sexp_error loc "Unrecognized case expression";
        sform_dummy_ret ctx loc

let sform_letin ctx loc sargs ot = match sargs with
  | [sdecls; sbody]
    -> let declss, nctx = lexp_p_decls [sdecls] ctx in
      (* FIXME: Use `elaborate`.  *)
      let bdy, ltp = infer sbody (ectx_new_scope nctx) in
      let s = List.fold_left (OL.lexp_defs_subst loc) S.identity declss in
      (lexp_let_decls declss bdy nctx,
       Inferred (mkSusp ltp s))
  | _ -> sexp_error loc "Unrecognized let_in_ expression";
        sform_dummy_ret ctx loc

let sform_debruijn ctx loc sargs ot =
  match sargs with
  | [Integer (l,i)]
    -> if i < 0 || i > get_size ctx then
        (sexp_error l "##DeBruijn index out of bounds";
         sform_dummy_ret ctx loc)
      else
        let lxp = mkVar ((loc, []), i) in (lxp, Lazy)
  | _ -> (sexp_error loc "##DeBruijn expects one integer argument";
         sform_dummy_ret ctx loc)

(*  Only print var info *)
let lexp_print_var_info ctx =
    let ((m, _), env, _) = ctx in
    let n = Myers.length env in

    for i = 0 to n - 1 do (
        let (_, (_, name), exp, tp) = Myers.nth i env in
        print_int i; print_string " ";
        print_string name; (*   name must match *)
        print_string " = ";
         (match exp with
             | None -> print_string "<var>"
             | Some exp -> lexp_print exp);
        print_string ": ";
        lexp_print tp;
        print_string "\n")
    done

let in_pervasive = ref true

(* Register special forms.  *)
let register_special_forms () =
  List.iter add_special_form
            [
              ("Built-in",      sform_built_in);
              ("DeBruijn",      sform_debruijn);
              ("typer-identifier", sform_identifier);
              ("typer-immediate", sform_immediate);
              ("datacons",      sform_datacons);
              ("typecons",      sform_typecons);
              ("_:_",           sform_hastype);
              ("lambda_->_",    sform_lambda);
              ("_->_",          sform_arrow);
              ("case_",         sform_case);
              ("let_in_",       sform_letin);
              (* FIXME: These should be functions!  *)
              ("decltype",      sform_decltype);
              ("declexpr",      sform_declexpr);
            ]

(*      Default context with builtin types
 * --------------------------------------------------------- *)

let dynamic_bind r v body =
  let old = !r in
  try r := v;
      let res = body () in
      r := old;
      res
  with e -> r := old; raise e

(* Make lxp context with built-in types *)
let default_ectx
  = try let _ = register_special_forms () in

    (* Read BTL files *)
    let read_file file_name elctx =
      let pres = prelex_file file_name in
      let sxps = lex default_stt pres in
      let nods = sexp_parse_all_to_list (ectx_get_grammar elctx)
                                        sxps (Some ";") in
      let _, lctx = lexp_p_decls nods elctx
      in lctx in

    (* Register predef *)
    let register_predefs elctx =
      try List.iter (fun name ->
            let idx = senv_lookup name elctx in
            let v = mkVar ((dloc, [name]), idx) in
              BI.set_predef name v) BI.predef_names;
      with Senv_Lookup_Fail _ ->
        warning "Predef not found"; in

    (* Empty context *)
    let lctx = empty_elab_context in
    let lctx = SMap.fold (fun key (e, t) ctx
                          -> if String.get key 0 = '-' then ctx
                            else ctx_define ctx (dloc, Some key) e t)
                         (!BI.lmap) lctx in

    (* read base file *)
    let lctx = dynamic_bind parsing_internals true
                            (fun ()
                             -> read_file (btl_folder ^ "/builtins.typer")
                                          lctx) in
    let _ = register_predefs lctx in

    (* Does not work, not sure why
    let files = ["list.typer"; "quote.typer"; "type.typer"] in
    let lctx = List.fold_left (fun lctx file_name ->
      read_file (btl_folder ^ "/" ^ file_name) lctx) lctx files in *)


    builtin_size := get_size lctx;
    let ectx = dynamic_bind in_pervasive true
                 (fun () -> read_file (btl_folder ^ "/pervasive.typer") lctx) in
    let _ = sform_default_ectx := ectx in
    ectx
  with e ->
    error "Compilation stopped in default context";
    Log.print_and_clear_log ();
    raise e

let default_rctx = EV.from_ectx default_ectx

(*      String Parsing
 * --------------------------------------------------------- *)

let lexp_expr_str str ctx =
  try let tenv = default_stt in
      let grm = ectx_get_grammar ctx in
      let limit = Some ";" in
      let pxps = sexp_parse_str str tenv grm limit in
      let lexps = lexp_parse_all pxps ctx in
      List.iter (fun lxp -> ignore (OL.check (ectx_to_lctx ctx) lxp))
        lexps;
      lexps
  with Log.Stop_Compilation s -> []

let lexp_decl_str str ctx =
  try let tenv = default_stt in
      let grm = ectx_get_grammar ctx in
      let limit = Some ";" in
      let sdecls = sexp_parse_str str tenv grm limit in
      lexp_p_decls sdecls ctx
  with Log.Stop_Compilation s -> ([],ctx)


(*  Eval String
 * --------------------------------------------------------- *)
(* Because we cant include Elab in eval.ml *)

let eval_expr_str str lctx rctx =
  try let lxps = lexp_expr_str str lctx in
      let elxps = List.map OL.erase_type lxps in
      EV.eval_all elxps rctx false
  with Log.Stop_Compilation s -> []

let eval_decl_str str lctx rctx =
  let prev_lctx, prev_rctx = lctx, rctx in
    try
      let lxps, lctx = lexp_decl_str str lctx in
      let elxps = (List.map OL.clean_decls lxps) in
          (EV.eval_decls_toplevel elxps rctx), lctx
    with Log.Stop_Compilation s -> (prev_rctx, prev_lctx)

