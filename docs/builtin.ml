(* builtin.ml --- Infrastructure to define built-in primitives
 *
 *      Copyright (C) 2016-2019  Free Software Foundation, Inc.
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
 * There are several different issues with how to make the compiler's code
 * interact with code defined in Typer:
 *
 * ** Exporting primitives
 *
 * I.e. how to give a name and a type to a primitive implemented in OCaml
 *
 * There are several conflicting desires, here: we'd generally want the name,
 * the type (and the association) to be close to the primitive's definition, so
 * that adding a new primitive doesn't require changes in many files.
 *
 * But it's also good to have the type written in some Typer file, both for
 * the convenience of writing the code in Typer syntax with typer-mode support,
 * and also because error messages can easily refer to that file, so it can be
 * used for user-documentation.
 *
 * ** Importing definitions
 *
 * Sometimes we want some part of the core to be defined in Typer and used
 * from OCaml.  Examples are the type `Macro` along with the `expand-macro`
 * function or the type Bool/true/false used with various primitives.
 *
 * ** Intertwined dependencies
 *
 * The various importing/exporting might need to be interlaced.  Some exported
 * functions's types will want to refer to imported types, while some imported
 * definitions may want to refer to exported definitions.  So we'd like to be
 * able to do them in "any" order.
 *
 * ---------------------------------------------------------------------------*)

open Util

open Sexp   (* Integer/Float *)
open Pexp   (* arg_kind *)
module L = Lexp
module OL = Opslexp
open Lexp

module DB = Debruijn
module E = Env

let log_raise_error ?loc msg =
  Log.log_error ~section:"BUILT-IN" ?loc msg;
  Log.internal_error msg

let predef_names = [
    "cons";                     (* FIXME: Should be used but isn't!  *)
    "nil";                      (* FIXME: Should be used but isn't!  *)
    "true";
    "false";
    "Macro";
    "Macro_expand";
]

(* FIXME: Actually, we should map the predefs to *values* since that's
 * where they're really needed!  *)
let predef_map : lexp SMap.t ref
  (* Pre-fill "Macro" with a dummy value, to avoid errors while reading
   * the builtins.typer file.  *)
  = ref (SMap.add "Macro" impossible SMap.empty)

let get_predef (name: string) (ctx: DB.elab_context) : lexp =
  try let r = (DB.get_size ctx) - !builtin_size - 0 in
      let p = SMap.find name (!predef_map) in
      mkSusp p (S.shift r)
  with Not_found -> log_raise_error ("\""^ name ^ "\" was not predefined")

let set_predef name lexp
  = predef_map := SMap.add name lexp (!predef_map)

(*                Builtin types               *)
let dloc    = DB.dloc

let op_binary t = mkArrow ((dloc, None), t, dloc,
                           mkArrow ((dloc, None), t, dloc, t))

let o2l_bool ctx b = get_predef (if b then "true" else "false") ctx

(* Typer list as seen during runtime.  *)
let o2v_list lst =
  (* FIXME: We're not using predef here.  This will break if we change
   * the definition of `List` in builtins.typer.  *)
  List.fold_left (fun tail elem
                  -> E.Vcons ((dloc, "cons"), [E.Vsexp (elem); tail]))
                 (E.Vcons ((dloc, "nil"), []))
                 (List.rev lst)


(* Typer list to Ocaml list *)
let v2o_list v =
  (* FIXME: We're not using predef here.  This will break if we change
   * the definition of `List` in builtins.typer.  *)
  let rec v2o_list acc v =
    match v with
    | E.Vcons ((_, "cons"), [hd; tl]) -> v2o_list (hd::acc) tl
    | E.Vcons ((_, "nil"), []) -> List.rev acc
    | _ -> log_raise_error ~loc:(E.value_location v) (
               "Failed to convert the " ^ E.value_name v ^ " with value :\n"
               ^ E.value_string v ^ "\n to a list.") in
  v2o_list [] v

(* Map of lexp builtin elements accessible via (## <name>).  *)
let lmap = ref (SMap.empty : (lexp * ltype) SMap.t)

let add_builtin_cst (name : string) (e : lexp)
  = let map = !lmap in
    assert (not (SMap.mem name map));
    let t = OL.check Myers.nil e in
    lmap := SMap.add name (e, t) map

let new_builtin_type name kind =
  let t = mkBuiltin ((dloc, name), kind) in
  add_builtin_cst name t;
  t

let register_builtin_csts () =
  add_builtin_cst "Type" DB.type0;
  add_builtin_cst "Kind" DB.type1;
  add_builtin_cst "Int" DB.type_int;
  add_builtin_cst "Integer" DB.type_integer;
  add_builtin_cst "Float" DB.type_float;
  add_builtin_cst "String" DB.type_string;
  add_builtin_cst "Elab_Context" DB.type_elabctx

let register_builtin_types () =
  let _ = new_builtin_type "Sexp" DB.type0 in
  let _ = new_builtin_type
            "Ref" (mkArrow ((dloc, None),
                            DB.type0, dloc, DB.type0)) in
  let _ = new_builtin_type
            "Array" (mkArrow ((dloc, None),
                            DB.type0, dloc, DB.type0)) in
  let _ = new_builtin_type "FileHandle" DB.type0 in
  ()

let _ = register_builtin_csts ();
        register_builtin_types ()
