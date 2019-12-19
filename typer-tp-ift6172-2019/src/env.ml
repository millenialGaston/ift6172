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
 *          Implements runtime environment
 *
 * --------------------------------------------------------------------------- *)

open Fmt        (*  make_title, table util *)

open Sexp

open Elexp
module M = Myers
module L = Lexp
module BI = Big_int
module DB = Debruijn

let dloc = Util.dummy_location

let fatal = Log.log_fatal ~section:"ENV"
let warning = Log.log_warning ~section:"ENV"

let str_idx idx = "[" ^ (string_of_int idx) ^ "]"

type value_type =
    | Vint of int
    | Vinteger of BI.big_int
    | Vstring of string
    | Vcons of symbol * value_type list
    | Vbuiltin of string
    | Vfloat of float
    | Closure of vname * elexp * runtime_env
    | Vsexp of sexp             (* Values passed to macros.  *)
    (* Unable to eval during macro expansion, only throw if the value is used *)
    | Vundefined
    | Vtype of L.lexp           (* The lexp value can't be trusted.  *)
    | Vin of in_channel
    | Vout of out_channel
    | Vref of (value_type ref)
    | Velabctx of DB.elab_context
    | Varray of (value_type array)

 (*  Runtime Environ *)
 and runtime_env = (vname * (value_type ref)) M.myers

let rec value_equal a b =
  match a, b with
    | Vint (i1), Vint (i2)          -> i1 = i2
    | Vinteger (i1), Vinteger (i2)  -> BI.eq_big_int i1 i2
    | Vstring (s1), Vstring (s2)    -> s1 = s2
    | Vbuiltin (s1), Vbuiltin (s2)  -> s1 = s2
    | Vfloat (f1), Vfloat (f2)      -> f1 = f2
    | Vsexp (a), Vsexp (b)          -> sexp_equal a b
    | Vin (c1), Vin (c2)            -> c1 = c2
    | Vout (c1), Vout (c2)          -> c2 = c2
    | Vundefined, _ | _, Vundefined -> warning "Vundefined"; false
    | Vtype e1, Vtype e2            -> warning "Vtype"; false

    | Closure (s1, b1, ctx1), Closure (s2, b2, ctx2)
      -> warning "Closure";
         if (s1 != s2) then false else true

    | Vcons ((_, ct1), a1), Vcons ((_, ct2), a2)
      -> if not (ct1 = ct2) then false else
           not (List.exists2
                  (fun a b -> not (value_equal a b))
                  a1 a2)

    | Vref (v1), Vref (v2) -> value_equal (!v1) (!v2) (* FIXME: Really?  *)

    | Velabctx (e1), Velabctx (e2) -> (e1 = e2)

    | Varray (a1), Varray (a2) -> (a1 = a2)

    | _ -> false

let rec value_eq_list a b =
  match a, b with
    | [], [] -> true
    | v1::vv1, v2::vv2 -> value_equal v1 v2 && value_eq_list vv1 vv2
    | _ -> false

let value_location (vtp: value_type) =
    match vtp with
        | Vcons ((loc, _), _) -> loc
        | Closure (_, lxp, _) -> elexp_location lxp
        (* location info was lost or never existed *)
        | _ -> dloc

let rec value_name v =
  match v with
    | Vin   _ -> "Vin"
    | Vout  _ -> "Vout"
    | Vint  _ -> "Vint"
    | Vinteger _ -> "Vinteger"
    | Vsexp  _ -> "Vsexp"
    | Vtype  _ -> "Vtype"
    | Vcons  _ -> "Vcons"
    | Vfloat _ -> "Vfloat"
    | Vundefined -> "Vundefined"
    | Vstring  _ -> "Vstring"
    | Closure  _ -> "Closure"
    | Vbuiltin _ -> "Vbuiltin"
    | Vref v -> ("Vref of "^(value_name (!v)))
    | Velabctx _ -> ("Velabctx")
    | Varray _ -> ("Varray")

let rec value_string v =
  match v with
    | Vin   _ -> "in_channel"
    | Vout  _ -> "out_channel"
    | Vundefined -> "<undefined!>"
    | Vstring  s -> "\"" ^ s ^ "\""
    | Vbuiltin s -> s
    | Vint     i -> string_of_int i
    | Vinteger i -> BI.string_of_big_int i
    | Vfloat   f -> string_of_float f
    | Vsexp    s -> sexp_string s
    | Vtype    e -> L.lexp_string e
    | Closure  ((_, s), elexp, _) -> "(lambda " ^ L.maybename s ^ " -> " ^ (elexp_string elexp) ^ ")"
    | Vcons    ((_, s), lst)
      -> let args = List.fold_left
                      (fun str v -> str ^ " " ^ value_string v)
                      "" lst in
         "(" ^ s ^ args ^ ")"
    | Vref     (v) -> ("Ref of "^(value_string (!v)))
    | Velabctx _ -> ("Velabctx")
    | Varray a -> if ( (Array.length a) = 0 )
      then "[]"
      else ( let
        str = (Array.fold_left
          (fun str v -> (str^(value_string v)^";")) "" a)
      in ("["^(String.sub str 0 ((String.length str) - 1))^"]") )

let value_print (vtp: value_type) = print_string (value_string vtp)

let make_runtime_ctx = M.nil

let get_rte_size (ctx: runtime_env): int = M.length ctx

let get_rte_variable names (idx: int)
                     (ctx: runtime_env): value_type =
    try (
        let (defname, ref_cell) = (M.nth idx ctx) in
        let x = !ref_cell in
    match (defname, names) with
    | ((_, Some n1), (_, ((_::_) as names)))
      -> let rec checkname ns = match ns with
          | n2::ns
            -> if n2 = n1 then x
              else checkname ns
          | []
            -> fatal
                ("Variable lookup failure. Expected: \""
                 ^ List.fold_left (fun str name
                                   -> str ^ " " ^ name)
                     "" names
                 ^ "[" ^ (string_of_int idx) ^ "]" ^ "\" got \"" ^ n1 ^ "\"")
        in checkname names
    | _ -> x)
    with Not_found ->
        let (_, ns) = names in
        fatal ("Variable lookup failure. Var: \"" ^
            L.firstname ns ^ "\" idx: " ^ (str_idx idx))

let add_rte_variable (name:vname) (x: value_type) (ctx: runtime_env)
    : runtime_env =
  let valcell = ref x in
  M.cons (name, valcell) ctx

let set_rte_variable idx name (v: value_type) (ctx : runtime_env) =
    let (n, ref_cell) = (M.nth idx ctx) in

    (match (n, name) with
     | ((_, Some n1), (_, Some n2))
       -> if (n1 != n2) then
            fatal ("Variable's Name must Match: " ^ n1 ^ " vs " ^ n2)
     | _ -> ());

    ref_cell := v

(* Select the n first variable present in the env *)
let nfirst_rte_var n ctx =
    let rec loop i acc =
        if i < n then
            loop (i + 1) ((get_rte_variable L.vdummy i ctx)::acc)
        else
            List.rev acc in
    loop 0 []

let print_myers_list l print_fun start =
    let n = (M.length l) - 1 in
    print_string (make_title " ENVIRONMENT ");
    make_rheader [(None, "INDEX");
        (None, "VARIABLE NAME"); (Some ('l', 48), "VALUE")];
    print_string (make_sep '-');

    for i = start to n do
    print_string "    | ";
        ralign_print_int (n - i) 5;
        print_string " | ";
        print_fun (M.nth (n - i) l);
    done;
    print_string (make_sep '=')

let print_rte_ctx_n (ctx: runtime_env) start =
  print_myers_list
    ctx
    (fun (n, vref) ->
      let g = !vref in
      let _ =
        match n with
        | (_, Some m) -> lalign_print_string m 12; print_string "  |  "
        | _ -> print_string (make_line ' ' 12); print_string "  |  " in

      value_print g; print_string "\n") start

(* Only print user defined variables *)
let print_rte_ctx ctx =
  print_rte_ctx_n ctx (!L.builtin_size)

(* Dump the whole context *)
let dump_rte_ctx ctx =
  print_rte_ctx_n ctx 0
