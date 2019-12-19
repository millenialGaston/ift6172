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
 *          print out each compilation' steps
 *
 * --------------------------------------------------------------------------- *)

(* Utilities *)
open Util
open Fmt
open Debug

(* ASTs *)
open Sexp
open Pexp
open Lexp

(* AST reader *)
open Prelexer
open Lexer
open Eval
module EL = Elexp
module OL = Opslexp

(* definitions *)
open Grammar
open Builtin

(* environments *)
open Debruijn
open Env

let dloc = dummy_location
let dummy_decl = Imm(String(dloc, "Dummy"))

let discard v = ()

(*          Argument parsing        *)
let arg_print_options = ref SMap.empty
let arg_files = ref []
let debug_arg = ref 0

let add_p_option name () =
    debug_arg := (!debug_arg) + 1;
    arg_print_options := SMap.add name true (!arg_print_options)

let get_p_option name =
    try let _ = SMap.find name (!arg_print_options) in
        true
    with
        Not_found -> false

(*
    pretty ?        (print with new lines and indents)
    indent level
    print_type?     (print inferred Type)
    print_index     (print dbi index)
    separate decl   (print extra newline between declarations)
    indent size      4
    highlight       (use console color to display hints)
*)

let format_mode = ref false
let ppctx  = ref pretty_ppctx
let format_dest = ref ""
let write_file = ref false

let mod_ctx name v = let f ctx = ctx := SMap.add name v !ctx in
                     f ppctx; f debug_ppctx

let set_print_type v ()     = mod_ctx "print_type"  (Bool v)
let set_print_index v ()    = mod_ctx "print_dbi"   (Bool v)
let set_print_indent_size v = mod_ctx "indent_size" (Int v)
let set_highlight v ()      = mod_ctx "color"       (Bool v)
let set_print_pretty v ()   = mod_ctx "pretty"      (Bool v)

let output_to_file str =
    write_file := true;
    format_dest := str;
    set_highlight false ()


let arg_defs = [
    (* format *)
    ("--format",
        Arg.Unit (fun () -> format_mode := true), " format a typer source code");
    ("-fmt-type=on",
        Arg.Unit (set_print_type true), " Print type info");
    ("-fmt-pretty=on",
        Arg.Unit (set_print_pretty true), " Print with indentation");
    ("-fmt-pretty=off",
        Arg.Unit (set_print_pretty false), " Print expression in one line");
    ("-fmt-type=off",
        Arg.Unit (set_print_type false), " Don't print type info");
    ("-fmt-index=on",
        Arg.Unit (set_print_index true), " Print DBI index");
    ("-fmt-index=off",
        Arg.Unit (set_print_index false), " Don't print DBI index");
    ("-fmt-indent-size",
        Arg.Int set_print_indent_size, " Indent size");
    ("-fmt-highlight=on",
        Arg.Unit (set_highlight true), " Enable Highlighting for typer code");
    ("-fmt-highlight=off",
        Arg.Unit (set_highlight false), " Disable Highlighting for typer code");
    ("-fmt-file",
        Arg.String output_to_file, " Output formatted code to a file");

    ("-typecheck",
        Arg.Unit (add_p_option "typecheck"), " Enable type checking");

    (*  Debug *)
    ("-pretok",
        Arg.Unit (add_p_option "pretok"), " Print pretok debug info");
    ("-tok",
        Arg.Unit (add_p_option "tok"), " Print tok debug info");
    ("-sexp",
        Arg.Unit (add_p_option "sexp"), " Print sexp debug info");
    ("-pexp",
        Arg.Unit (add_p_option "pexp"), " Print pexp debug info");
    ("-lexp",
        Arg.Unit (add_p_option "lexp"), " Print lexp debug info");
    ("-lctx",
        Arg.Unit (add_p_option "lctx"), " Print lexp context");
    ("-rctx",
        Arg.Unit (add_p_option "rctx"), " Print runtime context");
    ("-all",
        Arg.Unit (fun () ->
            add_p_option "pretok" ();
            add_p_option "tok" ();
            add_p_option "sexp" ();
            add_p_option "pexp" ();
            add_p_option "lexp" ();
            add_p_option "lctx" ();
            add_p_option "rctx" ();),
        " Print all debug info");
]

let parse_args () =
  Arg.parse arg_defs (fun s -> arg_files:= s::!arg_files) ""

let make_default () =
    arg_print_options := SMap.empty;
    add_p_option "sexp" ();
    add_p_option "pexp" ();
    add_p_option "lexp" ()


let format_source () =
    print_string (make_title " ERRORS ");

    let filename = List.hd (!arg_files) in
    let pretoks = prelex_file filename in
    let toks = lex default_stt pretoks in
    let nodes = sexp_parse_all_to_list (ectx_to_grm Elab.default_ectx)
                                       toks (Some ";") in
    let ctx = Elab.default_ectx in
    let lexps, _ = Elab.lexp_p_decls nodes ctx in

    print_string (make_sep '-'); print_string "\n";

    let result = lexp_str_decls (!ppctx) (List.flatten lexps) in

    if (!write_file) then (
        print_string ("    " ^ " Writing output file: " ^ (!format_dest) ^ "\n");
        let file = open_out (!format_dest) in

        List.iter (fun str -> output_string file str) result;

        flush_all ();
        close_out file;

    ) else (List.iter (fun str ->
        print_string str; print_string "\n") result;)

let main () =
    parse_args ();

    let arg_n = Array.length Sys.argv in

    let usage =
        "\n  Usage:   " ^ Sys.argv.(0) ^ " <file_name> [options]\n" in

    (*  Print Usage *)
    if arg_n == 1 then
        (Arg.usage (Arg.align arg_defs) usage)

    else if (!format_mode) then (
        format_source ()
    )
    else(
        (if (!debug_arg) = 0 then make_default ());

        let filename = List.hd (!arg_files) in

        (* get pretokens*)
        print_string yellow;
        let pretoks = prelex_file filename in
        print_string reset;

        (if (get_p_option "pretok") then(
            print_string (make_title " PreTokens");
            debug_pretokens_print_all pretoks; print_string "\n"));

        (* get sexp/tokens *)
        print_string yellow;
        let toks = lex default_stt pretoks in
        print_string reset;

        (if (get_p_option "tok") then(
            print_string (make_title " Base Sexp");
            debug_sexp_print_all toks; print_string "\n"));

        (* get node sexp  *)
        print_string yellow;
        let nodes = sexp_parse_all_to_list (ectx_to_grm Elab.default_ectx)
                                           toks (Some ";") in
        print_string reset;

        (if (get_p_option "sexp") then(
            print_string (make_title " Node Sexp ");
            debug_sexp_print_all nodes; print_string "\n"));

        (* Parse All Declaration *)
        print_string yellow;
        print_string reset;

        (* get lexp *)
        let octx = Elab.default_ectx in

        (* debug lexp parsing once merged *)
        print_string yellow;
        let lexps, nctx = try Elab.lexp_p_decls nodes octx
          with e ->
            print_string reset;
            raise e in
        print_string reset;

        (* use the new way of parsing expr *)
        let ctx = nctx in
        let flexps = List.flatten lexps in

        (if (get_p_option "lexp-merge-debug") then(
          List.iter (fun ((l, s), lxp, ltp) ->
            lalign_print_string (maybename s) 20;
            lexp_print ltp; print_string "\n";

            lalign_print_string (maybename s) 20;
            lexp_print lxp; print_string "\n";

            ) flexps));

        (* get typecheck context *)
        (if (get_p_option "typecheck") then(
            print_string (make_title " TYPECHECK ");

            let cctx = ectx_to_lctx ctx in
            (* run type check *)
            List.iter (fun (_, lxp, _)
                       -> let _ = OL.check cctx lxp in ())
                      flexps;

            print_string ("    " ^ (make_line '-' 76));
            print_string "\n";));

        (if (get_p_option "lexp") then(
            print_string (make_title " Lexp ");
            debug_lexp_decls flexps; print_string "\n"));

        (if (get_p_option "lctx") then(
           print_lexp_ctx (ectx_to_lctx nctx); print_string "\n"));

        (* Type erasure *)
        let clean_lxp = List.map OL.clean_decls lexps in

        (* Eval declaration *)
        let rctx = Elab.default_rctx in
        print_string yellow;
        let rctx = (try eval_decls_toplevel clean_lxp rctx;
            with e ->
                print_string reset;
                print_rte_ctx (!global_eval_ctx);
                print_eval_trace None;
                raise e) in
        print_string reset;

        (if (get_p_option "rctx") then(
            print_rte_ctx rctx; print_string "\n"));

        (* Eval Each Expression *)
        print_string (make_title " Eval Print ");

        (try
            (* Check if main is present *)
            let main = (senv_lookup "main" nctx) in

            (* get main body *)
            let body = (get_rte_variable (dloc, ["main"]) main rctx) in

            (* eval main *)
                print_eval_result 1 body

        with
            Not_found -> ()
        )
    )

let _ = main ()
