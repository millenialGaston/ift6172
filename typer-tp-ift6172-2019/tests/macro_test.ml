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
 * --------------------------------------------------------------------------- *)

open Util
open Utest_lib

open Sexp
open Lexp

open Eval       (* reset_eval_trace *)

open Builtin
open Env


(* default environment *)
let ectx = Elab.default_ectx
let rctx = Elab.default_rctx

let _ = (add_test "MACROS" "macros base" (fun () ->

    (* define 'lambda x -> x * x' using macros *)
    let dcode = "
    my_fun = lambda (x : List Sexp) ->
        let hd = (case x
          | cons hd tl => hd
          | nil => Sexp_symbol \"x\") : Sexp
        in (Sexp_node (Sexp_symbol \"_*_\")
                      (cons Sexp hd (cons Sexp hd (nil Sexp))));

    sqr = macro my_fun;
    " in

    let rctx, ectx = Elab.eval_decl_str dcode ectx rctx in

    let ecode = "(lambda (x : Int) -> sqr 3) 5;" in

    let ret = Elab.eval_expr_str ecode ectx rctx in

        match ret with
            | [Vint(r)] -> expect_equal_int r (3 * 3)
            | _ -> failure ())
)

let _ = (add_test "MACROS" "macros decls" (fun () ->
    let dcode = "
      decls-impl = lambda (x : List Sexp) ->
        let chain-decl : Sexp -> Sexp -> Sexp;
            chain-decl a b = Sexp_node (Sexp_symbol \"_;_\") (cons Sexp a (cons Sexp b (nil Sexp))) in

        let make-decl : String -> Int -> Sexp;
            make-decl name val =
          (Sexp_node (Sexp_symbol \"_=_\") (cons Sexp (Sexp_symbol name) (cons Sexp (Sexp_integer (Int->Integer val)) (nil Sexp)))) in

        let d1 = make-decl \"a\" 1 in
        let d2 = make-decl \"b\" 2 in
          (chain-decl d1 d2);

      my-decls = macro decls-impl;

      my-decls Nat;" in

    let rctx, ectx = Elab.eval_decl_str dcode ectx rctx in

    let ecode = "a; b;" in

    let ret = Elab.eval_expr_str ecode ectx rctx in

        match ret with
            | [Vint(a); Vint(b)] ->
                if (a = 1 && b = 2) then success () else failure ()

            | _ -> failure ())
)


(* run all tests *)
let _ = run_all ()
