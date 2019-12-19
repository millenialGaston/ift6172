(* subst.ml --- Substitutions for Lexp

Copyright (C) 2016-2019  Free Software Foundation, Inc.

Author: Stefan Monnier <monnier@iro.umontreal.ca>

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

(* Implementation of the subsitution calculus.
 *
 * As a general rule, try not to use the constructors of the `subst'
 * datatype, but use the following entry points instead.
 * Constructor functions:
 * - S.identity
 * - S.cons
 * - S.mkShift
 * - S.shift
 * - S.compose
 * - S.substitute
 * - S.sink
 * Destructor functions:
 * - S.identity_p
 * - S.lookup
 *
 * This implementation is generic (i.e. can be used with various datatypes
 * implementing the associated lambda-calculus), which is the reason for
 * the added complexity of arguments like `mkVar` and `mkShift` to `S.lookup`.
 * So in general, you'll want to use Lexp.scompose and Lexp.slookup
 * for those functions.
 *)

(* There are many different ways to do an explicit substitution system.
 * See for example:
 *     Implementation of Explicit Substitutions:
 *     from λσ to the Suspension Calculus.
 *     Vincent Archambault-Bouffard and Stefan Monnier.  HOR'2016.
 *     http://www.iro.umontreal.ca/~monnier/HOR-2016.pdf
 *
 * We mostly follow the above article, which we summarize here.
 * We start from Abadi's calculs which looks like:
 *
 *     e ::= #0       % Reference to dbi_index 0
 *           e₁ e₂
 *           (λ e)
 *           e[s]     % Application of a substitution
 *
 *     s ::= id       % identity substitution
 *           e . s    % replace #0 with `e` and use `s` for the rest
 *           s₁ ∘ s₂  % Composition (apply s₁ *first* and then s₂!).
 *           ↑        % dbi_index = dbi_index + 1
 *
 * But we make it more practical by using instead:
 *
 *     e ::= #i       % Reference to dbi_index `i`
 *           e₁ e₂
 *           (λ e)
 *           e[s]     % Application of a substitution
 *
 *     s ::= id       % identity substitution
 *           e . s    % replace #0 by `e` and use `s` for the rest
 *           s ↑n     % like Abadi's "s ∘ (↑ⁿ)"
 *
 * And the composition ∘ is defined as a function rather than a constructor.
 *
 * And we have the propagation rules:
 *
 *     #i[s]        ==>   lookup i s
 *     (e₁ e₂)[s]   ==>   (e₁[s]) (e₂[s])
 *     (λ e)[s]     ==>   λ(e[#0 · (s ↑1)])
 *     e[s₁][s₂]    ==>   e[s₁ ∘ s₂]
 *
 * We also have beta rules:
 *
 *     (λ e₁) e₂    ==>   e₁[e₂·id]
 *
 * To which we can add (as an optimisation to avoid using `compose`):
 *
 *     (λ e₁)[s] e₂ ==>   e₁[e₂·s]
 *
 * Merging rules:
 *
 *    (s ↑n₂) ↑n₁         ==>  s ↑(n₁+n₂)                    {part of m1}
 *    s₁ ∘ id             ==>  s₁                            {m2}
 *    s₁ ∘ s₂ ↑n          ==>  (s₁ ∘ s₂) ↑n                  {part of m1}
 *    id ∘ s              ==>  s                             {m3}
 *    s₁ ↑n ∘ e·s₂        ==>  s₁ ↑(n-1) ∘ s₂                {m4 & m5}
 *    e·s₁ ∘ s₂           ==>  (e[s₂])·(s₁ ∘ s₂)             {m6}
 *
 *)

(* We define here substitutions which take a variable within a source context
 * Δₛ and should return an expression valid in target context Δₜ.
 *
 * The current implementation only handles a very limited subset of such
 * substitutions.  One of the many limitations is that we can only encode
 * substitutions which map variables to variables.
 *)

type db_index = int             (* DeBruijn index.  *)
type db_offset = int            (* DeBruijn index offset.  *)

(* Substitution, i.e. a mapping from db_index to 'a
 * In practice, 'a is always lexp, but we keep it as a parameter:
 * - for better modularity of the code.
 * - to break a mutual dependency between the Lexp and the Subst modules.  *)
type 'a subst = (* lexp subst *)
  | Identity of db_offset            (* Identity o      ≡  id ∘ ↑ₒ        *)
  | Cons of 'a * 'a subst * db_offset  (* Cons (e, s, o)  ≡  (e · s) ∘ ↑ₒ   *)
            (* Myers's extra pointers down the list:
             *     * int * 'a subst * db_offset *)
(* Lift (n,m) increases indices≥N by M.
   * IOW, it takes variables from a source context Δₛ₁Δₛ₂ to a destination
   * context Δₛ₁ΔₜΔₛ₂ where Δₛ₂ has size N and Δₜ has size M.  *)
  (* | Lift of db_index * db_offset *)

(* Build Myers's "stack" element.  *)
(* let mkCons e s o = match s with
 *   | Cons (_, _, _, sk1, Cons (_, _, _, sk2, s2, o2), o1) when sk1 >= sk2
 *     -> Cons (e, s, o, sk1 + sk2 + 1, s2, o1 + o2 + o)
 *   | _ -> Cons (e, s, o, 1, s, o) *)

(* Apply a substitution to a single variable.  *)
let lookup (mkVar : 'b -> db_index -> 'a)
          (mkShift: 'a -> db_offset -> 'a)
          (s: 'a subst) (l : 'b) (v:db_index) : 'a =
  let rec lookup' (o:db_offset) (s: 'a subst) (v:db_index) : 'a =
    match s with
    | Identity o' -> mkVar l (v + o + o')
    (* Use Myers's fastlane when applicable:
     * | Cons (_, _, _, sk, s, o') when v >= sk -> lookup' (o + o') s (v - sk) *)
    | Cons (e, s, o') -> let o = o + o' in
                        if v > 0 then lookup' o s (v - 1)
                        else mkShift e o
  in lookup' 0 s v

let mkShift s (m:db_offset) =
  if m>0 then
    match s with Identity o -> Identity (o + m)
               | Cons (e, s, o) -> Cons (e, s, o + m)
  else s

(* A substitution which adds M to every deBruijn index.
 * I.e. one that takes variables from a context Δₛ to an extended
 * context ΔₛΔₜ where Δₜ has size M.  *)
let shift (m:db_offset) = Identity m

(* Return a substitution which replaces #0 with `e` and then applies `s`
 * to the rest.  *)
let cons e s = Cons (e, s, 0)

(* The trivial substitution which doesn't do anything.  *)
let identity = Identity 0

(* Test if a substitution is trivial.  The "_p" stands for "predicate".  *)
let identity_p s = match s with | Identity o -> o = 0 | _ -> false

(* Compose two substitutions.  This implements the merging rules.
 * Returns s₁ ∘ s₂  (i.e. s₁ is applied before s₂) *)
let compose (mkSusp : 'a -> 'a subst -> 'a)
      (s1: 'a subst) (s2: 'a subst) : 'a subst =
  (* There is a bit of flexibility in what we return, in the sense
   * that some shifts can be pushed more or less down.  Here we
   * want the shifts to float as far outside as possible.  *)
  let rec compose' (s1: 'a subst) (s2: 'a subst) : 'a subst =
    match s1 with
    | Identity o1
      -> let rec compose_id o1 s o = match s with
          | Identity o2 -> Identity (o + o1 + o2)
          | Cons (e2, s2, o2) (* , sk2, s2', o2'  *)
            -> (* Myers's fastlane:
               * if o1 >= sk2 then compose_id (o1 - sk2) s2' (o + o2') *)
             if o1 > 0 then compose_id (o1 - 1) s2 (o + o2)
             else Cons (e2, s2, o + o2)
        in compose_id o1 s2 0
    | Cons (e1, s1, o1)
      -> let rec compose_cons o1 s o = match s with
          | Identity o2 -> Cons (e1, s1, o + o1 + o2)
          | Cons (e2, s2, o2) (* , sk2, s2', o2'  *)
            -> (* Myers's fastlane:
               * if o1 >= sk2 then compose_cons (o1 - sk1) s2' (o + o2')  *)
             if o1 > 0 then compose_cons (o1 - 1) s2 (o + o2)
             else 
               (* Pull out o2's shift and compose the two Cons.  *)
               let s' = cons e2 s2 in
               Cons (mkSusp e1 s', compose' s1 s', o + o2)
        in compose_cons o1 s2 0
  in compose' s1 s2

(* Adjust a substitution for use under one more binder.
 * I.e. take a substitution from Δs to Δₜ and return a substitution
 * from Δs,x to Δₜ,x.
 * Also known as `lift`.  *)
let sink (mkVar : 'b -> db_index -> 'a) (l:'b) (s:'a subst) =
  cons (mkVar l 0) (mkShift s 1)

(* Return a substitution which replaces #0 with `e`.  *)
let substitute e = cons e identity
