(* pexp.ml --- Proto lambda-expressions, half-way between Sexp and Lexp.

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

open Util
open Sexp   (* Symbol *)
open Lexer
open Grammar

let pexp_error loc = Log.log_error ~section:"PEXP" ~loc

(*************** The Pexp Parser *********************)

(*  This is Dangerously misleading since pvar is NOT pexp but Pvar is *)
type pvar = symbol
(* type sort = Type | Ext *)
(* type tag = string *)

type ppat =
  | Ppatsym of vname (* A named default pattern, or a 0-ary constructor.  *)
  | Ppatcons of sexp * vname list

let pexp_pat_location e = match e with
  | Ppatsym (l,_) -> l
  | Ppatcons (e, _) -> sexp_location e

let pexp_u_formal_arg (arg : pvar * sexp option) =
  match arg with
  | (s, None) -> Symbol s
  | (((l,_) as s), t)
    -> Node (Symbol (l, ":"),
            [Symbol s; match t with Some e -> e
                                  | None -> Symbol (l, "_")])

let pexp_p_pat_arg (s : sexp) = match s with
  | Symbol (l , n) -> (l, match n with "_" -> None | _ -> Some n)
  | _ -> let loc = sexp_location s in
        pexp_error loc "Unknown pattern arg";
        (loc, None)

let pexp_u_pat_arg ((l, oname) : vname) : sexp =
  Symbol (l, match oname with None -> "_" | Some n -> n)

let pexp_p_pat (s : sexp) : ppat = match s with
  | Symbol (l, n) -> Ppatsym (l, match n with "_" -> None | _ -> Some n)
  | Node (c, args)
    -> Ppatcons (c, List.map pexp_p_pat_arg args)
  | _ -> let l = sexp_location s in
        pexp_error l "Unknown pattern"; Ppatsym (l, None)

let pexp_u_pat (p : ppat) : sexp = match p with
  | Ppatsym (l, None) -> Symbol (l, "_")
  | Ppatsym (l, Some n) -> Symbol (l, n)
  | Ppatcons (c, args) -> Node (c, List.map pexp_u_pat_arg args)
