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
 *          Provide helper functions to print out extracted
 *                      Pretoken, Sexp, pexp and lexp
 *
 * --------------------------------------------------------------------------- *)

(* removes some warnings *)
open Util
open Fmt

open Prelexer
open Lexer

open Sexp
open Pexp
open Lexp

open Debruijn
open Grammar

(* Print aPretokens *)
let rec debug_pretokens_print pretoken =
    print_string " ";
    let print_info msg loc =
        print_string msg;
        print_string "["; loc_print loc; print_string "]\t" in

    match pretoken with
        | Preblock(loc, pts,_)
         -> print_info "Preblock:  " loc;
            print_string "{";   pretokens_print pts;    print_string " }"

        | Pretoken(loc, str)
         -> print_info "Pretoken:  " loc;
                print_string ("'" ^ str ^ "'");

        | Prestring(loc, str)
         -> print_info "Prestring: " loc;
            print_string ("\"" ^ str ^ "\"")

(* Print a List of Pretokens *)
let rec debug_pretokens_print_all pretokens =
  List.iter (fun pt -> debug_pretokens_print pt; print_string "\n") pretokens

(* Sexp Print *)
let rec debug_sexp_print sexp =
  let print_info msg loc =
    print_string msg;
    print_string "["; loc_print loc; print_string "]\t" in
  match sexp with
    | Symbol(_, "")
        -> print_string "Epsilon  "  (* "ε" *)

    | Block(loc, pts, _)
        -> print_info "Block:   " loc;
           print_string "{"; pretokens_print pts; print_string " }"

    | Symbol(loc, name)
        -> print_info "Symbol:  " loc; print_string name

    | String(loc, str)
        -> print_info "String:  " loc;
           print_string "\""; print_string str; print_string "\""

    | Integer(loc, n)
        -> print_info "Integer: " loc;   print_int n

    | Float(loc, x)
        -> print_info "Float:   " loc;   print_float x

    | Node(f, args)
        -> print_info "Node:    " (sexp_location f);
            sexp_print f; print_string " [";
                List.iter (fun sexp -> print_string " "; sexp_print sexp)
                                 args;
            print_string "]"

(* Print a list of sexp *)
let debug_sexp_print_all tokens =
  List.iter (fun pt ->
         print_string " ";
         debug_sexp_print pt;
         print_string "\n";)
    tokens


(* Print a Pexp with debug info *)
let debug_pexp_print ptop =
    print_string " ";
    let l = sexp_location ptop in
    let print_info msg loc pex =
        print_string msg; print_string "[";
        loc_print loc;
        print_string "]\t";
        sexp_print pex in
    print_info (sexp_name ptop) l ptop

let debug_lexp_decls decls =
    let sep = " : " in
    List.iter (fun e ->
            let ((loc, name), lxp, ltp) = e in

            print_string " ";
            lalign_print_string (lexp_name lxp) 15;
            print_string "["; loc_print loc; print_string "]";

            let str = lexp_str_decls (!debug_ppctx) [e] in

            (* First col size = 15 + 1 + 2 + 3 + 5 + 6
             *                = 32                          *)

            let str = match str with
                | fst::tl -> print_string (sep ^ fst); print_string "\n"; tl
                | _ -> [] in

            (* inefficient but makes things pretty iff -fmt-pretty=on *)
            let str = List.flatten (List.map (fun g -> str_split g '\n') str) in

            let str = match str with
                | scd::tl ->
                    print_string " FILE: ";
                    lalign_print_string loc.file 25;
                    print_string (sep ^ scd); print_string "\n"; tl
                | _ -> [] in

            List.iter (fun g ->
                print_string ((make_line ' ' 32) ^ sep);
                print_string g; print_string "\n")
                str;

        ) decls
