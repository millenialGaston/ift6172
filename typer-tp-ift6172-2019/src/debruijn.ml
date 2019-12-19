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
 *      Description:
 *          Specifies recursive data structure for DeBruijn indexing
 *          methods starting with '_' are considered private and should not
 *          elsewhere in the project
 *
 * ---------------------------------------------------------------------------*)

module Str = Str

open Util
open Lexp
module L = Lexp
module M = Myers
open Fmt

module S = Subst

let fatal = Log.log_fatal ~section:"DEBRUIJN"

(* Handling scoping/bindings is always tricky.  So it's always important
 * to keep in mind for *every* expression which is its context.
 *
 * In particular, this holds true as well for those expressions that appear
 * in the context.  Traditionally for dependently typed languages we expect
 * the context's rules to say something like:
 *
 *      ⊢ Γ    Γ ⊢ τ:Type
 *      —————————————————
 *          ⊢ Γ,x:τ
 *
 * Which means that we expect (τ) expressions in the context to be typed
 * within the *rest* of that context.
 *
 * This also means that when we look up a binding in the context, we need to
 * adjust the result, since we need to use it in the context where we looked
 * it up, which is different from the context where it was defined.
 *
 * More concretely, this means that lookup(Γ, i) should return an expression
 * where debruijn indices have been shifted by "i".
 *
 * This is nice for "normal bindings", but there's a complication in the
 * case of recursive definitions.  Typically, this is handled by using
 * something like a μx.e construct, which works OK for the theory but tends
 * to become rather inconvenient in practice for mutually recursive
 * definitions.  So instead, we annotate the recursive binding with
 * a "recursion_offset" (of type `db_offset`) to say that rather than being
 * defined in "the rest of the context", they're defined in a slightly larger
 * context that includes "younger" bindings.
 *)


(*  Type definitions
 * ---------------------------------- *)

let dloc   = dummy_location
let type0  = mkSort (dloc, 0)
let type1   = mkSort (dloc, 1)
let type2   = mkSort (dloc, 2)
let type_int = mkBuiltin ((dloc, "Int"), type0)
let type_integer = mkBuiltin ((dloc, "Integer"), type0)
let type_float = mkBuiltin ((dloc, "Float"), type0)
let type_string = mkBuiltin ((dloc, "String"), type0)
let type_elabctx = mkBuiltin ((dloc, "Elab_Context"), type0)

(* easier to debug with type annotations *)
type env_elem = (vname * varbind * ltype)
type lexp_context = env_elem M.myers

type db_ridx = int (* DeBruijn reverse index (i.e. counting from the root).  *)

(*  Map variable name to its distance in the context *)
type senv_length = int  (* it is not the map true length *)
type senv_type = senv_length * (db_ridx SMap.t)

type lctx_length = db_ridx

type meta_scope
  = scope_level       (* Integer identifying a level.  *)
    * lctx_length     (* Length of ctx when the scope is added.  *)
    * (meta_id SMap.t ref) (* Metavars already known in this scope.  *)

(* This is the *elaboration context* (i.e. a context that holds
 * a lexp context plus some side info.  *)
type elab_context
  = Grammar.grammar * senv_type * lexp_context * meta_scope

let get_size (ctx : elab_context)
  = let (_, (n, _), lctx, _) = ctx in
    assert (n = M.length lctx); n

let ectx_to_grm (ectx : elab_context) : Grammar.grammar =
  let (grm,_, _, _) = ectx in grm

  (* Extract the lexp context from the context used during elaboration.  *)
let ectx_to_lctx (ectx : elab_context) : lexp_context =
  let (_,_, lctx, _) = ectx in lctx

let ectx_to_scope_level ((_, _, _, (sl, _, _)) : elab_context) : scope_level
  = sl

let ectx_local_scope_size ((_, (n, _), _, (_, slen, _)) as ectx) : int
  = get_size ectx - slen

(*  Public methods: DO USE
 * ---------------------------------- *)

let empty_senv = (0, SMap.empty)
let empty_lctx = M.nil

let empty_elab_context : elab_context
  = (Grammar.default_grammar, empty_senv, empty_lctx,
     (0, 0, ref SMap.empty))

(* senv_lookup caller were using Not_found exception *)
exception Senv_Lookup_Fail of (string list)
let senv_lookup_fail relateds = raise (Senv_Lookup_Fail relateds)

(* Return its current DeBruijn index.  *)
let senv_lookup (name: string) (ctx: elab_context): int =
  let (_, (n, map), _, _) = ctx in
  try n - (SMap.find name map) - 1
  with Not_found
       -> let get_related_names (n : db_ridx) name map =
           let r = Str.regexp (".*"^name^".*") in
           let search r = SMap.fold (fun name _ names
                                     -> if (Str.string_match r name 0) then
                                         name::names
                                       else
                                         names)
                                    map [] in
           if ((String.sub name 0 1) = "_" ||
                 (String.sub name ((String.length name) - 1) 1) = "_") &&
                ((String.length name) > 1) then
             search r
           else [] in

         senv_lookup_fail (get_related_names n name map)

let lexp_ctx_cons (ctx : lexp_context) d v t =
  assert (let offset = match v with | LetDef (o, _) -> o | _ -> 0 in
          offset >= 0
          && (ctx = M.nil
             || match M.car ctx with
               | (_, LetDef (previous_offset, _), _)
                 -> previous_offset >= 0 (* General constraint.  *)
                   (* Either `ctx` is self-standing (doesn't depend on us),
                    * or it depends on us (and maybe other bindings to come), in
                    * which case we have to depend on the exact same bindings.  *)
                   && (previous_offset <= 1
                      || previous_offset = 1 + offset)
               | _ -> true));
  M.cons (d, v, t) ctx

let lctx_extend (ctx : lexp_context) (def: vname) (v: varbind) (t: lexp) =
  lexp_ctx_cons ctx def v t

let env_extend_rec (ctx: elab_context) (def: vname) (v: varbind) (t: lexp) =
  let (loc, oname) = def in
  let (grm, (n, map), env, sl) = ctx in
  let nmap = match oname with None -> map | Some name -> SMap.add name n map in
  (grm, (n + 1, nmap),
   lexp_ctx_cons env def v t,
   sl)

let ectx_extend (ctx: elab_context) (def: vname) (v: varbind) (t: lexp) = env_extend_rec ctx def v t

let lctx_extend_rec (ctx : lexp_context) (defs: (vname * lexp * ltype) list) =
  let (ctx, _) =
    List.fold_left
      (fun (ctx, recursion_offset) (def, e, t) ->
        lexp_ctx_cons ctx def (LetDef (recursion_offset, e)) t,
        recursion_offset - 1)
      (ctx, List.length defs) defs in
  ctx

let ectx_extend_rec (ctx: elab_context) (defs: (vname * lexp * ltype) list) =
  let (grm, (n, senv), lctx, sl) = ctx in
  let senv', _ = List.fold_left
                   (fun (senv, i) ((_, oname), _, _) ->
                     (match oname with None -> senv
                                     | Some name -> SMap.add name i senv),
                     i + 1)
                   (senv, n) defs in
  (grm, (n + List.length defs, senv'), lctx_extend_rec lctx defs, sl)

let ectx_new_scope (ectx : elab_context) : elab_context =
  let (grm, senv, lctx, (scope, _, rmmap)) = ectx in
  (grm, senv, lctx, (scope + 1, Myers.length lctx, ref (!rmmap)))

let ectx_get_scope (ectx : elab_context) : meta_scope =
  let (_, _, _, sl) = ectx in sl

let ectx_get_grammar (ectx : elab_context) : Grammar.grammar =
  let (grm, _, _, _) = ectx in grm

let env_lookup_by_index index (ctx: lexp_context): env_elem =
  Myers.nth index ctx

(*  Print context  *)
let print_lexp_ctx_n (ctx : lexp_context) start =
    let n = (M.length ctx) - 1 in

    print_string (make_title " LEXP CONTEXT ");

    make_rheader [
        (Some ('l',  7), "INDEX");
        (Some ('l',  4), "OFF");
        (Some ('l', 10), "NAME");
        (Some ('l', 42), "VALUE:TYPE")];

    print_string (make_sep '-');

    (* it is annoying to print according to SMap order *)
    (* let's use myers list order *)
    let rec extract_names (lst: lexp_context) acc =
        let names = ref [] in
        for i = start to n do
          let name = match (M.nth (n - i) lst) with
            | ((_, Some name), _, _) -> name
            | _ -> "" in
              names := name::!names
        done; !names in

    let ord = extract_names ctx [] in

    let rec print idx ord =
        match ord with
            | [] -> ()
            | hd::tl ->(

        print_string "    | ";  lalign_print_int (n - idx - 1) 7;
        print_string    " | ";

        let ptr_str = "    |         |      |            | " in

        try let r, name, exp, tp =
              match env_lookup_by_index (n - idx - 1) ctx with
                | ((_, name), LetDef (r, exp), tp) -> r, name, Some exp, tp
                | ((_, name), _, tp) -> 0, name, None, tp in

            (*  Print env Info *)
            lalign_print_int r 4;
            print_string " | ";
            lalign_print_string (maybename name) 10; (*   name must match *)
            print_string " | ";

            let _ = match exp with
                | None -> print_string "<var>"
                | Some exp -> (
                  let str = lexp_str (!debug_ppctx) exp in
                    let str = (match str_split str '\n' with
                        | hd::tl -> print_string hd; tl
                        | _ -> []) in

                      List.iter (fun elem ->
                        print_string ("\n" ^ ptr_str ^ elem)) str) in

            print_string (": "); lexp_print tp; print_string "\n";

            print (idx + 1) tl

        with Not_found ->
            (print_string "Not_found  |\n"; print (idx + 1) tl)) in

    print (start - 1) ord; print_string (make_sep '=')


(* Only print user defined variables *)
let print_lexp_ctx (ctx : lexp_context) =
  print_lexp_ctx_n ctx !L.builtin_size

(* Dump the whole context *)
let dump_lexp_ctx (ctx : lexp_context) =
  print_lexp_ctx_n ctx 0

(* generic lookup *)
let lctx_lookup (ctx : lexp_context) (v: vref): env_elem  =
    let ((loc, enames), dbi) = v in

    try(let ret = (Myers.nth dbi ctx) in
        let _ = match (ret, enames) with
          | (((_, Some name), _, _), _::_)
             (* Check if names match *)
            -> let rec checknames names = match names with
                | ename::names
                  -> if ename = name then () else checknames names
                | []
                  -> fatal ~loc ~print_action:(fun _ ->
                        print_lexp_ctx ctx; print_newline ())
                      ("DeBruijn index " ^ string_of_int dbi
                       ^ " refers to wrong name.  "
                       ^ "Expected: `"
                       ^ List.fold_left (fun str ename
                                         -> str ^ " " ^ ename)
                           "" enames
                       ^ "` got `" ^ name ^ "`") in
              checknames enames
          | _ -> () in

        ret)
    with
      Not_found -> fatal ~loc ("DeBruijn index "
                             ^ string_of_int dbi ^ " of `" ^ firstname enames
                             ^ "` out of bounds!")

let lctx_lookup_type (ctx : lexp_context) (vref : vref) : lexp =
  let (_, i) = vref in
  let (_, _, t) = lctx_lookup ctx vref in
  mkSusp t (S.shift (i + 1))

let lctx_lookup_value (ctx : lexp_context) (vref : vref) : lexp option =
  let (_, i) = vref in
  match lctx_lookup ctx vref with
  | (_, LetDef (o, v), _) -> Some (push_susp v (S.shift (i + 1 - o)))
  | _ -> None

let env_lookup_type ctx (v : vref): lexp =
  lctx_lookup_type (ectx_to_lctx ctx) v

    (* mkSusp ltp (S.shift (idx + 1)) *)

let env_lookup_expr ctx (v : vref): lexp option =
  lctx_lookup_value (ectx_to_lctx ctx) v

type lct_view =
  | CVempty
  | CVlet of vname * varbind * ltype * lexp_context
  | CVfix of (vname * lexp * ltype) list * lexp_context

let rec lctx_view lctx =
  match lctx with
  | Myers.Mnil -> CVempty
  | Myers.Mcons ((loname, LetDef (1, def), t), lctx, _, _)
    -> let rec loop i lctx defs =
        match lctx with
        | Myers.Mcons ((loname, LetDef (o, def), t), lctx, _, _)
             when o = i
          -> loop (i + 1) lctx ((loname, def, t) :: defs)
        | _ -> CVfix (defs, lctx) in
      loop 2 lctx [(loname, def, t)]
  | Myers.Mcons ((_, LetDef (o, def), _), _, _, _) when o > 1
    -> fatal "Unexpected lexp_context shape!"
  | Myers.Mcons ((loname, odef, t), lctx, _, _)
    -> CVlet (loname, odef, t, lctx)

(**          Sets of DeBruijn indices          **)

type set = db_offset * unit IMap.t

let set_empty = (0, IMap.empty)

let set_mem i (o, m) = IMap.mem (i - o) m

let set_set i (o, m) = (o, IMap.add (i - o) () m)
let set_reset i (o, m) = (o, IMap.remove (i - o) m)

let set_singleton i = (0, IMap.singleton i ())

(* Adjust a set for use in a deeper scope with `o` additional bindings.  *)
let set_sink o (o', m) = (o + o', m)

(* Adjust a set for use in a higher scope with `o` fewer bindings.  *)
let set_hoist o (o', m) =
  let newo = o' - o in
  let (_, _, newm) = IMap.split (-1 - newo) m
  in (newo, newm)

let set_union (o1, m1) (o2, m2) : set =
  if o1 = o2 then
    (o1, IMap.merge (fun k _ _ -> Some ()) m1 m2)
  else
    let o = o2 - o1 in
    (o1, IMap.fold (fun i2 () m1
                    -> IMap.add (i2 + o) () m1)
                   m2 m1)
