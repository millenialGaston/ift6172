(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2018  Free Software Foundation, Inc.
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
 *          utest library utility.  Tests register themselves
 *
 * --------------------------------------------------------------------------- *)


module U = Util
open Fmt

module StringMap =
    Map.Make (struct type t = string let compare = String.compare end)


type test_fun = (unit -> int)
type tests = (test_fun) StringMap.t
type sections = ((tests) StringMap.t) * string list

let success () = 0
let failure () = (-1)

(*
 *  SECTION NAME - TEST NAME   - FUNCTION (() -> int)
 *      "Let"    - "Base Case" - (fun () -> success )
 *      "Let"    - "Recursive"
 *      "Lambda" - "Base Case"
 *      "Lambda" - "Nested"
 *)
let global_sections = ref StringMap.empty
let insertion_order = ref []
let ret_code = ref 0
let number_test = ref 0

(*  Exception *)
exception Unexpected_result of string

(*  Argument Parsing                        *)
(* ---------------------------------------- *)

(*
 *  0: Nothing
 *  1: Print:            (x/N) file_test .................... pass
 *  2: Print Each composing Test
 *  3: use debug
 *)
let global_verbose_lvl = ref 0
let global_sample_dir = ref ""
let global_fsection = ref ""
let global_ftitle = ref ""

let set_verbose lvl =
    global_verbose_lvl := lvl;
    Log.set_typer_log_level (if lvl >= 3 then Log.Debug else Log.Nothing)

let arg_defs = [
    ("--verbose=",
     Arg.Int set_verbose, " Set verbose level");
    ("--samples=",
     Arg.String (fun g -> global_sample_dir := g), " Set sample directory");
    (* Allow users to select which test to run *)
    ("--fsection=",
     Arg.String (fun g -> global_fsection := U.string_uppercase g),
     " Set test filter");
    ("--ftitle=",
     Arg.String (fun g -> global_ftitle := U.string_uppercase g),
     " Set test filter");
  ]

let must_run_section str =
  !global_fsection = ""
  || U.string_uppercase str = !global_fsection

let must_run_title str =
  !global_ftitle = ""
  || U.string_uppercase str = !global_ftitle

let parse_args () = Arg.parse arg_defs (fun s -> ()) ""


(* Utest printing function                  *)
(* ---------------------------------------- *)
let ut_string vb msg = if vb <= (!global_verbose_lvl) then print_string msg else ()
let ut_string2 = ut_string 2


(* Value Checking                                           *)
(*      USAGE: expect_something_type value expected_value   *)
(*          return success() if match else failure ()       *)
let unexpected_throw sk tk e =
    ut_string2 (red ^ "[   FAIL] " ^ sk ^ " - " ^ tk ^ "\n");
    ut_string2        "[       ]     UNEXPECTED THROW:\n";
    ut_string2        "[       ]     ----------------------------- Callstack (20): -----------------------------------------\n";
    ut_string2        ("[       ]     " ^ (Printexc.raw_backtrace_to_string (Printexc.get_callstack 20)));
    ut_string2        "[       ]     ---------------------------------------------------------------------------------------\n";
    ut_string2        "[       ]     ----------------------------- Backtrace: ----------------------------------------------\n";
    ut_string2        ("[       ]     " ^ (Printexc.get_backtrace ()) ^ "\n");
    ut_string2        "[       ]     ---------------------------------------------------------------------------------------\n";
    ut_string2        "[       ]  "; ut_string2 ((Printexc.to_string e) ^ "\n" ^ reset)

let _expect_equal_t to_string value expect =
    if value = expect then
        success ()
    else(
        ut_string2 (red ^ "[       ]     EXPECTED: " ^ (to_string expect)^ "\n");
        ut_string2 (      "[       ]          GOT: " ^ (to_string value) ^ "\n" ^ reset);
        failure ())

let expect_equal_int   = _expect_equal_t string_of_int
let expect_equal_float = _expect_equal_t string_of_float
let expect_equal_str   = _expect_equal_t (fun g -> g)


let add_section sname =
    try
        StringMap.find sname (!global_sections)
    with
        Not_found ->
            insertion_order := sname::(!insertion_order);
            (StringMap.empty, ref [])

(* USAGE *)
(*
 *   (add_test "LET" "Base Case" (fun () ->
 *      let r = eval_string "let a = 2; b = 3; in a + b;" in
 *      let v = (get_int r) in
 *          if v = 5 then success () else failure ()))
 *
 *  sname: Section Name
 *  tname: Test Name
 *  tfun : test function (unit -> int)
 *)
let add_test sname tname tfun =

    (* Does Section Exist ? *)
    let (tmap, lst) = add_section sname in

    try let _ = StringMap.find tname tmap in
        ut_string2 "TEST ALREADY EXISTS"
    with
        Not_found ->

    lst := tname::(!lst);

    (* add test *)
    let ntmap = StringMap.add tname tfun tmap in
        global_sections := StringMap.add sname (ntmap, lst) (!global_sections);

    number_test := (!number_test + 1)

(*  sk  : Section Key
 *  tmap: test_name -> tmap
 *  tk  : Test Key                  *)
let for_all_tests sk tmap tk =
    if (must_run_title tk) then (
    let tv = StringMap.find tk tmap in
    flush stdout;
    try
        let r = tv () in
            if r = 0 then(
                ut_string2 (green ^ "[     OK] " ^ sk ^ " - " ^ tk ^ "\n" ^ reset))
            else(
                ut_string2 (red ^ "[   FAIL] " ^ sk ^ " - " ^ tk ^ "\n" ^ reset);
                ret_code := failure ())
    with e ->
        ret_code := failure ();
        unexpected_throw sk tk e) else ()

let for_all_sections sk =
    let tmap, tst = StringMap.find sk (!global_sections) in

    if (must_run_section sk) then(
        ut_string2 ("[RUN    ] " ^ sk ^ " \n");
        tst := List.rev (!tst);
        List.iter (for_all_tests sk tmap) (!tst))

    else ()

(* Run all *)
let run_all () =
    parse_args ();

    insertion_order := List.rev (!insertion_order);

    (* iter over all sections *)
    List.iter for_all_sections (!insertion_order);

    (* return success or failure *)
    exit !ret_code
