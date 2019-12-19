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
 *          Simple interpreter
 *
 * --------------------------------------------------------------------------- *)

open Util
open Fmt

open Sexp
open Pexp       (* Arg_kind *)
open Lexp       (* Varbind *)

open Elexp
open Builtin
open Grammar
open Debruijn
open Env
open Printf
module OL = Opslexp

module Lexer = Lexer      (* lex *)
module Prelexer = Prelexer (* prelex_string *)


type eval_debug_info = elexp list * elexp list

let dloc = dummy_location
let global_eval_trace = ref ([], [])
let global_eval_ctx = ref make_runtime_ctx
(* let eval_max_recursion_depth = ref 23000 *)

let builtin_functions
  = ref (SMap.empty : ((location -> eval_debug_info
                        -> value_type list -> value_type)
                       (* The primitive's arity.  *)
                       * int) SMap.t)

let add_builtin_function name f arity =
  builtin_functions := SMap.add name (f, arity) (!builtin_functions)

let append_eval_trace trace (expr : elexp) =
  let (a, b) = trace in
  let r = expr::a, b in
    global_eval_trace := r; r

let append_typer_trace trace (expr : elexp) =
  let (a, b) = trace in
  let r = (a, expr::b) in
    global_eval_trace := r; r

let get_trace () = !global_eval_trace

let rec_depth trace =
  let (a, b) = trace in
    List.length b

(* eval error are always fatal *)
let error loc ?print_action msg =
    Log.log_error ~section:"EVAL" ~loc ?print_action msg;
    Log.internal_error msg

let fatal loc msg = Log.log_fatal ~section:"EVAL" ~loc msg
let warning loc msg = Log.log_warning ~section:"EVAL" ~loc msg

(*  Print a message that look like this:
 *
 * [Ln   8, cl   6] ./samples/error.typer
 *   [X] Fatal     EVAL     MESSAGE
 *       > ....
 *       > ....
 *
 *)

let debug_messages error_type loc message messages =
  let msg = List.fold_left (fun str msg ->
    str ^ "\n        > " ^ msg) message messages in
      error_type loc (msg ^ "\n")

let root_string () =
  let a, _ = !global_eval_trace in
  match List.rev a with
    | [] -> ""
    | e::_ -> elexp_string e

let debug_message error_type type_name type_string loc expr message =
  debug_messages error_type loc
    message [
      (type_name expr) ^ ": " ^ (type_string expr);
      "Root: " ^ (root_string ());
    ]

(* Print value name followed by the value in itself, finally throw an exception *)
let value_fatal = debug_message fatal value_name value_string
let value_error = debug_message (error ?print_action:None) value_name value_string
let elexp_fatal = debug_message fatal elexp_name elexp_string


(* FIXME: We're not using predef here.  This will break if we change
 * the definition of `Bool` in builtins.typer.  *)
let ttrue = Vcons ((dloc, "true"), [])
let tfalse = Vcons ((dloc, "false"), [])
let o2v_bool b = if b then ttrue else tfalse

(* FIXME: This should be the unit value!  *)
let tunit = Vcons ((dloc, "unit"), [])

let ddummy = (U.dummy_location, None)

(* I'm using a ref because I think register_builtin_functions
   get called after the default_ctx is created in elab.
   Another solution could be to define a function in elaboration step
   and then undefine it. The thing is elab_context may not exist at runtime
   so I must save it somewhere if the Elab.* function persist. *)
let macro_monad_elab_context = ref empty_elab_context

let set_getenv (ectx : elab_context) = macro_monad_elab_context := ectx

(*
 *                  Builtins
 *)
(* Builtin of builtin * string * ltype *)
let add_binary_iop name f =
  let name = "Int." ^ name in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vint (v); Vint (w)] -> Vint (f v w)
    | _ -> error loc ("`" ^ name ^ "` expects 2 Int arguments") in
  add_builtin_function name f 2

let _ = add_binary_iop "+"  (+);
        add_binary_iop "-"  (-);
        add_binary_iop "*" ( * );
        add_binary_iop "/"  (/);

        add_binary_iop "mod"  (mod);
        add_binary_iop "and"  (land);
        add_binary_iop "or"  (lor);
        add_binary_iop "lsl" (lsl);
        add_binary_iop "lsr" (lsr);
        add_binary_iop "asr"(asr);
        add_binary_iop "xor"  (lxor)

let add_binary_bool_iop name f =
  let name = "Int." ^ name in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vint v; Vint w] -> o2v_bool (f v w)
    | _ -> error loc ("`" ^ name ^ "` expects 2 Int arguments") in
  add_builtin_function name f 2

let _ = add_binary_bool_iop "<"  (<);
        add_binary_bool_iop ">"  (>);
        add_binary_bool_iop "="  (=);
        add_binary_bool_iop ">="  (>=);
        add_binary_bool_iop "<="  (<=)

let _ =
  let name = "Int." ^ "not" in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vint v] -> Vint(lnot v)
    | _ -> error loc ("`" ^ name ^ "` expects 1 Int argument") in
  add_builtin_function name f 1

(* True integers (aka Z).  *)

let add_binary_biop name f =
  let name = "Integer." ^ name in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vinteger v; Vinteger w] -> Vinteger (f v w)
    | _ -> error loc ("`" ^ name ^ "` expects 2 Integer arguments") in
  add_builtin_function name f 2

let _ = add_binary_biop "+"  BI.add_big_int;
        add_binary_biop "-"  BI.sub_big_int;
        add_binary_biop "*"  BI.mult_big_int;
        add_binary_biop "/"  BI.div_big_int

let add_binary_bool_biop name f =
  let name = "Integer." ^ name in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vinteger v; Vinteger w] -> o2v_bool (f v w)
    | _ -> error loc ("`" ^ name ^ "` expects 2 Integer arguments") in
  add_builtin_function name f 2

let _ = add_binary_bool_biop "<"  BI.lt_big_int;
        add_binary_bool_biop ">"  BI.gt_big_int;
        add_binary_bool_biop "="  BI.eq_big_int;
        add_binary_bool_biop ">=" BI.ge_big_int;
        add_binary_bool_biop "<=" BI.le_big_int;
        let name = "Int->Integer" in
        add_builtin_function
          name
          (fun loc (depth : eval_debug_info) (args_val: value_type list)
           -> match args_val with
             | [Vint v] -> Vinteger (BI.big_int_of_int v)
             | _ -> error loc ("`" ^ name ^ "` expects 1 Int argument"))
          1

(* Floating point numers.  *)

let add_binary_fop name f =
  let name = "Float." ^ name in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vfloat v; Vfloat w] -> Vfloat (f v w)
    | _ -> error loc ("`" ^ name ^ "` expects 2 Float arguments") in
  add_builtin_function name f 2

let _ = add_binary_fop "+"  (+.);
        add_binary_fop "-"  (-.);
        add_binary_fop "*" ( *. );
        add_binary_fop "/"  (/.)

let add_binary_bool_fop name f =
  let name = "Float." ^ name in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vfloat v; Vfloat w] -> o2v_bool (f v w)
    | _ -> error loc ("`" ^ name ^ "` expects 2 Float arguments") in
  add_builtin_function name f 2

let _ = add_binary_bool_fop "<"  (<);
        add_binary_bool_fop ">"  (>);
        add_binary_bool_fop "="  (=);
        add_binary_bool_fop ">="  (>=);
        add_binary_bool_fop "<="  (<=)

let _ = let name = "Float." ^ "trunc" in
  let f loc (depth : eval_debug_info) (args_val : value_type list) =
    match args_val with
    | [Vfloat v] -> Vfloat ( snd (modf v) )
    | _ -> error loc ("`" ^ name ^ "` expects 1 Float argument") in
  add_builtin_function name f 1

let make_symbol loc depth args_val  = match args_val with
  | [Vstring str] -> Vsexp (Symbol (loc, str))
  | _ -> error loc "Sexp.symbol expects one string as argument"

let make_node loc depth args_val = match args_val with
  | [Vsexp (op); lst] ->
     let args = v2o_list lst in

     let s = List.map (fun g -> match g with
                                | Vsexp(sxp)  -> sxp
                                | _ ->
                                   (* print_rte_ctx ctx; *)
                                   value_error loc g "Sexp.node expects `List Sexp` second as arguments") args in

     Vsexp (Node (op, s))

  | _  -> error loc "Sexp.node expects a `Sexp` and a `List Sexp`"


let make_string loc depth args_val  = match args_val with
  | [Vstring str] -> Vsexp (String (loc, str))
  | _ -> error loc "Sexp.string expects one string as argument"

let make_integer loc depth args_val = match args_val with
  | [Vinteger n] -> Vsexp (Integer (loc, BI.int_of_big_int n))
  | _ -> error loc "Sexp.integer expects one integer as argument"

let make_float loc depth args_val   = match args_val with
  | [Vfloat x] -> Vsexp (Float (loc, x))
  | _ -> error loc "Sexp.float expects one float as argument"

let make_block loc depth args_val   = match args_val with
  (* From what would we like to make a block? *)
  | [Vstring str] -> Vsexp (Block (loc, (Prelexer.prelex_string str), loc))
  | _ -> error loc "Sexp.block expects one string as argument"

let reader_parse loc depth args_val  = match args_val with
  | [Velabctx ectx; Vsexp (Block (_,toks,_))] ->
      let grm = ectx_get_grammar ectx in
      o2v_list (sexp_parse_all_to_list grm (Lexer.lex default_stt toks) (Some ";"))
  | [Velabctx _; s] -> (warning loc "Reader.parse do nothing without a Block"; s)
  | _   -> error loc "Reader.parse expects an ElabContext and a Block as argument"

let string_eq loc depth args_val = match args_val with
  | [Vstring s1; Vstring s2] -> o2v_bool (s1 = s2)
  | _ -> error loc "String.= expects 2 strings"

(* need either a character type or builtin string operation *)
let string_concat loc depth args_val = match args_val with
  | [Vstring s1; Vstring s2] -> Vstring (s1 ^ s2)
  | _ -> error loc "String.concat expects 2 strings"

let string_sub loc depth args_val = match args_val with
  | [Vstring s; Vint start; Vint len] -> Vstring (String.sub s start len)
  | _ -> error loc "String.sub expects 1 string and 2 ints"

let sexp_eq loc depth args_val = match args_val with
  | [Vsexp (s1); Vsexp (s2)] -> o2v_bool (sexp_equal s1 s2)
  | _ -> error loc "Sexp.= expects 2 sexps"

let sexp_debug_print loc depth args_val = match args_val with
  | [Vsexp (s1)]
    -> let tstr = sexp_name s1
      in print_string ("\n\t"^tstr^" : ["^(sexp_string s1)^"]\n\n")
       ; Vsexp (s1)
  | _ -> error loc "Sexp.debug_print expects 1 sexps"

let file_open loc depth args_val = match args_val with
  | [Vstring (file); Vstring (mode)] ->
     (* open file *) (* return a file handle *)
     (match mode with
      | "r" -> Vin (open_in file)
      | "w" -> Vout (open_out file)
      | _ -> error loc "wrong open mode")

  | _ -> error loc "File.open expects 2 strings"

let file_read loc depth args_val = match args_val with
  (* FIXME: Either rename it to "readline" and drop the second arg,
   * or actually pay attention to the second arg.  *)
  | [Vin channel; Vint n] -> Vstring (input_line channel)
  | _ -> error loc ~print_action:(fun _ ->
            List.iter (fun v -> value_print v; print_newline ()) args_val;
          )
          "File.read expects an in_channel. Actual arguments:"

let file_write loc depth args_val = match args_val with
  | [Vout channel; Vstring msg]
    -> (fprintf channel "%s" msg;
       tunit)
  | _ -> error loc ~print_action:(fun _ ->
            List.iter (fun v -> value_print v; print_newline ()) args_val;
          )
          "File.write expects an out_channel and a string. Actual arguments:"

let rec eval lxp (ctx : Env.runtime_env) (trace : eval_debug_info): (value_type) =

    let trace = append_eval_trace trace lxp in
    let eval' lxp ctx = eval lxp ctx trace in

    (* This creates an O(N^2) cost for deep recursion because rec_depth
     * uses `length` on the stack trace.  *)
    (* (if (rec_depth trace) > (!eval_max_recursion_depth) then
     *     fatal (elexp_location lxp) "Recursion Depth exceeded"); *)

    (* Save current trace in a global variable. If an error occur,
       we will be able to retrieve the most recent trace and context *)
    global_eval_ctx := ctx;
    global_eval_trace := trace;

    match lxp with
        (*  Leafs           *)
        (* ---------------- *)
        | Imm(Integer (_, i))       -> Vint i
        | Imm(String (_, s))        -> Vstring s
        | Imm(Float (_, n))         -> Vfloat n
        | Imm(sxp)                  -> Vsexp sxp
        | Cons (label)              -> Vcons (label, [])
        | Lambda (n, lxp)           -> Closure (n, lxp, ctx)
        | Builtin ((_, str))        -> Vbuiltin str

        (* Return a value stored in env *)
        | Var((loc, name), idx) as e
          -> eval_var ctx e ((loc, name), idx)

        (*  Nodes           *)
        (* ---------------- *)
        | Let(_, decls, inst)
          -> let nctx = eval_decls decls ctx trace in
            eval' inst nctx

        (* Function call *)
        | Call (f, args)
          -> eval_call (elexp_location f) f trace
                      (eval f ctx trace)
                      (List.map (fun e -> eval e ctx trace) args)

        (* Case *)
        | Case (loc, target, pat, dflt)
          -> (eval_case ctx trace loc target pat dflt)

        (* FIXME: Here, we'd want to apply `ctx` to `e`, but we can't
         * apply a runtime-ctx to a lexp!
         * E.g. say we have `λt ≡> Ind (arg : t)`: by the time we get here,
         * Our `Type` carries `Ind (arg : t)` but `t` is not in `ctx`!
         * So we should either use an elexp instead of a lexp,
         * or somehow recover a lexp-ctx from the runtime-ctx (maybe
         * with extra info that `Type` could carry),
         * or find another trick.
         *
         * We could replace erasable arguments (like t above) with a Metavar,
         * but the other issue of converting Values back to Lexps remains!
         *
         * Hence, the `e` carried by `Vtype` is just indicative and not
         * something we can use.  *)
        | Type e -> Vtype e


and eval_var ctx lxp v =
    let (name, idx) = v in
    try get_rte_variable name idx ctx
    with e ->
      elexp_fatal (fst name) lxp
        ("Variable: " ^ L.firstname (snd name) ^ (str_idx idx) ^ " was not found ")

(* unef: unevaluated function (to make the trace readable) *)
and eval_call loc unef i f args =
  match f, args with
  (* return result of eval *)
  | _, [] -> f

  | Vcons (n, fields), _
    -> Vcons (n, List.append fields args)

  | Closure (x, e, ctx), v::vs
    -> let rec bindargs e vs ctx = match (vs, e) with
       | (v::vs, Lambda (x, e))
         (* "Uncurry" on the fly.  *)
         -> bindargs e vs (add_rte_variable x v ctx)
       | ([], _) ->
        let trace = append_typer_trace i unef in
        eval e ctx trace
       | _ -> eval_call loc unef i (eval e ctx i) vs in
     bindargs e vs (add_rte_variable x v ctx)

  | Vbuiltin (name), args
    -> (try let (builtin, arity) = SMap.find name !builtin_functions in
           let nargs = List.length args in
           if nargs = arity then
             builtin loc i args        (* Fast common case.  *)
           else if nargs > arity then
             let rec split n vs acc = match (n, vs) with
               | 0, _ -> let v = eval_call loc unef i f (List.rev acc) in
                        eval_call loc unef i v vs
               | _, (v::vs) -> split (n - 1) vs (v::acc)
               | _ -> error loc "Impossible!"
             in split nargs args []
           else
             let rec buildctx args ctx = match args with
               | [] -> ctx
               | arg::args -> buildctx args (add_rte_variable ddummy arg ctx) in
             let rec buildargs n =
               if n >= 0
               then (Var (vdummy, n))::buildargs (n - 1)
               else [] in
             let rec buildbody n =
               if n > 0 then
                 Lambda (ddummy, buildbody (n - 1))
               else Call (Builtin (dloc, name), buildargs (arity - 1)) in
             Closure (ddummy,
                      buildbody (arity - nargs - 1),
                      buildctx args Myers.nil)

        with
        | Not_found ->
           error loc ("Requested Built-in `" ^ name ^ "` does not exist")
        (* | e ->
         *    warning loc ("Exception thrown from primitive `" ^ name ^"`");
         *    raise e *))

  | Vtype e, _
   (* We may call a Vlexp e.g. for "x = Map Int String".
    * FIXME: The arg will sometimes be a Vlexp but not always, so this is
    * really just broken!  *)
    -> Vtype (L.mkCall (e, [(Var (vdummy, -1))]))
  | _ -> value_fatal loc f "Trying to call a non-function!"

and eval_case ctx i loc target pat dflt =
    (* Eval target *)
    let v = eval target ctx i in

    (* extract constructor name and arguments *)
    let ctor_name, args = match v with
        | Vcons((_, cname), args)  -> cname, args
        | _ -> value_error loc v ("Target `" ^ elexp_string target
                                 ^ "` is not a Constructor") in

    (*  Get working pattern *)
    try let (_, pat_args, exp) = SMap.find ctor_name pat in
        (* build context (List.fold2 has problem with some cases)  *)
        (* This is more robust                                     *)
        let rec fold2 nctx pats args =
            match pats, args with
            | pat::pats, arg::args
              -> let nctx = add_rte_variable pat arg nctx in
                fold2 nctx pats args
            (* Errors: those should not happen but they might  *)
            (* List.fold2 would complain. we print more info   *)
            | _::_, [] -> warning loc "a) Eval::Case Pattern Error"; nctx
            | [], _::_ -> warning loc "b) Eval::Case Pattern Error"; nctx
            (* Normal case *)
            | [], [] -> nctx in

        let nctx = fold2 ctx pat_args args in
            eval exp nctx i

    (* Run default *)
    with Not_found -> (match dflt with
        | Some (var, lxp)
          -> eval lxp (add_rte_variable var v ctx) i
        | _ -> error loc "Match Failure")

and build_arg_list args ctx i =
    (*  eval every args *)
    let arg_val = List.map (fun (k, e) -> eval e ctx i) args in

    (*  Add args inside context *)
    List.fold_left (fun c v -> add_rte_variable ddummy v c) ctx arg_val

and eval_decls (decls: (vname * elexp) list)
               (ctx: runtime_env) i: runtime_env =

    let n = (List.length decls) - 1 in

    (* Read declarations once and push them *)
    let nctx = List.fold_left (fun ctx (name, _) ->
      add_rte_variable name Vundefined ctx) ctx decls in

    List.iteri (fun idx (name, lxp) ->
      let v = eval lxp nctx i in
      let offset = n - idx in
        ignore (set_rte_variable offset name v nctx)) decls;

        nctx

(* -------------------------------------------------------------------------- *)
(*              Builtin Implementation  (Some require eval)                   *)

(* Sexp -> (Sexp -> List Sexp -> Sexp) -> (String -> Sexp) ->
    (String -> Sexp) -> (Int -> Sexp) -> (Float -> Sexp) -> (List Sexp -> Sexp)
        ->  Sexp *)
and sexp_dispatch loc depth args =
    let eval a b = eval a b depth in
    let sxp, nd, ctx_nd,
            sym, ctx_sym,
            str, ctx_str,
             it, ctx_it,
            flt, ctx_flt,
            blk, ctx_blk = match args with
      (* FIXME: Don't match against `Closure` to later use `eval`, instead
       * pass the value to "funcall".  *)
        | [_typ; sxp; Closure(_, nd,  ctx_nd); Closure(_, sym, ctx_sym);
                Closure(_, str, ctx_str); Closure(_, it, ctx_it);
                Closure(_, flt, ctx_flt); Closure(_, blk, ctx_blk)] ->
            sxp, nd, ctx_nd, sym, ctx_sym, str, ctx_str, it, ctx_it,
            flt, ctx_flt, blk, ctx_blk
        | _ ->  error loc "sexp_dispatch expects 8 arguments" in

    let sxp = match sxp with
        | Vsexp(sxp)   -> sxp
        | _ -> value_fatal loc sxp "sexp_dispatch expects a Sexp as 2nd arg" in

    match sxp with
        | Node    (op, s)    ->(
            let rctx = ctx_nd in
            let rctx = add_rte_variable ddummy (Vsexp(op)) rctx in
            let rctx = add_rte_variable ddummy (o2v_list s) rctx in
                match eval nd rctx with
                    | Closure(_, nd, _) -> eval nd rctx
                    | _ -> error loc "Node has 2 arguments")

        | Symbol  (_ , s)    ->
             let rctx = ctx_sym in
             eval sym (add_rte_variable ddummy (Vstring s) rctx)
        | String  (_ , s)    ->
             let rctx = ctx_str in
             eval str (add_rte_variable ddummy (Vstring s) rctx)
        | Integer (_ , i)    ->
             let rctx = ctx_it in
             eval it (add_rte_variable ddummy (Vinteger (BI.big_int_of_int i))
                        rctx)
        | Float   (_ , f)    ->
             let rctx = ctx_flt in
             eval flt (add_rte_variable ddummy (Vfloat f) rctx)
        | Block   (_ , _, _) as b ->
             (* I think this code breaks what Blocks are. *)
             (* We delay parsing but parse with default_stt and default_grammar... *)
             (*let toks = Lexer.lex default_stt s in
             let s = sexp_parse_all_to_list default_grammar toks (Some ";") in*)
             let rctx = ctx_blk in
             eval blk (add_rte_variable ddummy (Vsexp b) rctx)

(* -------------------------------------------------------------------------- *)
and print_eval_result i lxp =
    print_string "     Out[";
    ralign_print_int i 2;
    print_string "] >> ";
    value_print lxp; print_string "\n";

and print_typer_trace' trace =

  let trace = List.rev trace in

  print_string (Fmt.make_title "Typer Trace");
  print_string (Fmt.make_sep '-');

  let _ = List.iteri (fun i expr ->
    print_string "    ";
    Fmt.print_ct_tree i; print_string "+- ";
    print_string ((elexp_string expr) ^ "\n")) trace in

  print_string (Fmt.make_sep '=')

and print_typer_trace trace =
  match trace with
    | Some t -> print_typer_trace' t
    | None -> let (a, b) = !global_eval_trace in
      print_typer_trace' b

and print_trace title trace default =
  (* If no trace is provided take the most revent one *)
  let trace = match trace with
    | Some trace -> trace
    | None -> default in

  (* Trace is upside down by default *)
  let trace = List.rev trace in

  (* Now eval trace and elab trace are the same *)
  let print_trace = (fun type_name type_string type_loc i expr ->
    (* Print location info *)
    print_string ("    [" ^ (loc_string (type_loc expr)) ^ "] ");

    (* Print call trace visualization *)
    Fmt.print_ct_tree i; print_string "+- ";

    (* Print element *)
    print_string ((type_name expr) ^ ": " ^ (type_string expr) ^ "\n")
  ) in

  let elexp_trace = print_trace elexp_name elexp_string elexp_location in

  (* Print the trace*)
  print_string (Fmt.make_title title);
  print_string (Fmt.make_sep '-');
  let _ = List.iteri elexp_trace trace in
  print_string (Fmt.make_sep '=')

and print_eval_trace trace =
    let (a, b) = !global_eval_trace in
      print_trace " EVAL TRACE " trace a

let float_to_string loc depth args_val = match args_val with
  | [Vfloat x] -> Vstring (string_of_float x)
  | _ -> error loc "Float->String expects one Float argument"

let int_to_string loc depth args_val = match args_val with
  | [Vint x] -> Vstring (string_of_int x)
  | _ -> error loc "Int->String expects one Int argument"

let integer_to_string loc depth args_val = match args_val with
  | [Vinteger x] -> Vstring (BI.string_of_big_int x)
  | _ -> error loc "Integer->String expects one Integer argument"

let sys_exit loc depth args_val = match args_val with
  | [Vint n] -> exit n
  | _ -> error loc "Sys.exit takes a single Int argument"

let arity0_fun loc _ _ = error loc "Called a 0-arity function!?"
let nop_fun loc _ vs = match vs with
  | [v] -> v
  | _ -> error loc "Wrong number of argument to nop"

let ref_make loc depth args_val = match args_val with
  | [_typ; v] -> Vref (ref v)
  | _ -> error loc "Ref.make takes a single value as argument"

let ref_read loc depth args_val = match args_val with
  | [_typ; Vref (v)] -> !v
  | _ -> error loc "Ref.read takes a single Ref as argument"

let ref_write loc depth args_val = match args_val with
  | [_typ; value; Vref (actual)] -> actual := value; tunit
  | _ -> error loc "Ref.write takes a value and a Ref as argument"

let gensym
  = let count = ref 0 in
    (fun loc depth args_val
     -> match args_val with
       | [v]
         -> (count := ((!count) + 1);
            Vsexp (Symbol (dloc,(" %gensym% no "^(string_of_int (!count))
                                 ^" "))))
       | _ -> error loc "gensym takes a Unit as argument")

let getenv loc depth args_val = match args_val with
  | [v] -> Velabctx !macro_monad_elab_context
  | _ -> error loc "getenv takes a single Unit as argument"

let debug_doc loc depth args_val = match args_val with
  | [Vstring name; Velabctx ectx]
    -> (try let idx  = senv_lookup name ectx in
            let elem = lctx_lookup (ectx_to_lctx ectx)
                                   (((dummy_location, [name]), idx)) in
            match elem with
            | ((l,_),_,_) -> Vstring (l.docstr)
        with _ -> Vstring "element not found")
  | _ -> error loc "Elab.debug_doc takes a String and an Elab_Context as arguments"

let is_bound loc depth args_val = match args_val with
  | [Vstring name; Velabctx ectx]
    -> o2v_bool (try (ignore (senv_lookup name ectx); true)
                with Senv_Lookup_Fail _ -> false)
  | _ -> error loc "Elab.isbound takes an Elab_Context and a String as arguments"

let constructor_p name ectx =
  try let idx = senv_lookup name ectx in
      (* Use `lexp_whnf` so that `name` can be indirectly
       * defined as a constructor
       * (e.g. as in `let foo = cons in case foo x xs | ...`  *)
      match OL.lexp_whnf (mkVar ((dummy_location, [name]), idx))
              (ectx_to_lctx ectx) with
      | Cons _ -> true           (* It's indeed a constructor!  *)
      | _ -> false
  with Senv_Lookup_Fail _ -> false

let nth_ctor_arg name nth ectx =
  let find_nth ctors = match (smap_find_opt name ctors) with
    | Some args ->
       (match (List.nth args nth) with
        | ((_, Some n), _) -> n
        | _ -> "_"
        | exception (Failure _) -> "_" )
    | _ -> "_" in
  try let idx = senv_lookup name ectx in
    match OL.lexp_whnf (mkVar ((dummy_location, [name]), idx))
        (ectx_to_lctx ectx) with
      | Cons (Var v, _) -> (  match (env_lookup_expr ectx v) with
                                | Some (Inductive (_, ctors)) ->
                                  find_nth ctors
                                | _ -> "_"  )
      | _ -> "_"
  with Senv_Lookup_Fail _ -> "_"

let ctor_arg_pos name arg ectx =
  let rec find_opt xs n = match xs with
    | [] -> None
    | ((_, Some x), _)::xs -> if x = arg then Some n else find_opt xs (n + 1)
    | _::xs -> find_opt xs (n + 1) in
  let find_arg ctors = match (smap_find_opt name ctors) with
                            | (Some args) ->
                              ( match (find_opt args 0) with
                                  | None -> (-1)
                                  | Some n -> n )
                            | _ -> (-1) in
  try let idx = senv_lookup name ectx in
    match OL.lexp_whnf (mkVar ((dummy_location, [name]), idx))
        (ectx_to_lctx ectx) with
      | Cons (Var v, _) -> (  match (env_lookup_expr ectx v) with
                                | Some (Inductive (_, ctors)) ->
                                  find_arg ctors
                                | _ -> (-1)  )
      | _ -> (-1)
  with Senv_Lookup_Fail _ -> (-1)

let is_constructor loc depth args_val = match args_val with
  | [Vstring name; Velabctx ectx] -> o2v_bool (constructor_p name ectx)
  | _ -> error loc "Elab.isconstructor takes a String and an Elab_Context as arguments"

let nth_arg loc depth args_val = match args_val with
  | [Vstring t; Vint nth; Velabctx ectx] -> Vstring (nth_ctor_arg t nth ectx)
  | _ -> error loc "Elab.nth-arg takes a String, an Int and an Elab_Context as arguments"

let arg_pos loc depth args_val = match args_val with
  | [Vstring t; Vstring a; Velabctx ectx] -> Vint (ctor_arg_pos t a ectx)
  | _ -> error loc "Elab.arg-pos takes two String and an Elab_Context as arguments"

let array_append loc depth args_val = match args_val with
  | [_typ; v; Varray a] ->
    Varray (Array.append (Array.map (fun v -> v) a) (Array.make 1 v))
  | _ -> error loc "Array.append takes a value followed by an Array as arguments"

let array_create loc depth args_val = match args_val with
  | [_typ; Vint len; v] -> Varray (Array.make len v)
  | _ -> error loc "Array.make takes an Int and a value and as arguemnts"

let array_length loc depth args_val = match args_val with
  | [_typ; Varray a] -> Vint (Array.length a)
  | _ -> error loc "Array.length takes an Array as argument"

let array_set loc depth args_val = match args_val with
  | [_typ; Vint idx; v; Varray a] -> if (idx > (Array.length a) || idx < 0)
    then
      (warning loc "Array.set index out of bounds (array unchanged)";
      (Varray a))
    else
      let copy = (Array.map (fun v -> v) a) in
      (Array.set copy idx v; Varray copy)
  | _ -> error loc "Array.set takes an Int, a value and an Array as arguments"

let array_get loc depth args_val = match args_val with
  | [_typ; dflt; Vint idx; Varray a] -> if (idx >= (Array.length a)) || (idx < 0)
    then
      dflt
    else
      Array.get a idx
  | _ -> error loc "Array.get takes a default value, an Int and an Array as arguments"


(*  Vundefined is used in array_empty because we have no default value
    ("array_create 0 0" has a default value v (Vint 0)).
*)
let array_empty loc depth args_val = match args_val with
  | [_typ] -> Varray (Array.make 0 Vundefined)
  | _ -> error loc "Array.empty takes a type as single argument"

let test_fatal loc depth args_val = match args_val with
  | [Vstring section; Vstring msg]
    -> Log.print_entry
        (Log.mkEntry Log.Fatal ~kind:"(Unit test fatal)" ~loc ~section msg);
      Log.user_error msg
  | _ -> error loc "Test.fatal takes two String as argument"

let test_warning loc depth args_val = match args_val with
  | [Vstring section; Vstring msg]
    -> Log.print_entry
        (Log.mkEntry Log.Warning ~kind:"(Unit test warning)" ~loc ~section msg);
      tunit
  | _ -> error loc "Test.warning takes two String as argument"

let test_info loc depth args_val = match args_val with
  | [Vstring section; Vstring msg]
    -> Log.print_entry
        (Log.mkEntry Log.Info ~kind:"(Unit test Info)" ~loc ~section msg);
      tunit
  | _ -> error loc "Test.info takes two String as argument"

let test_location loc depth args_val = match args_val with
  | [_] -> Vstring (loc.file ^ ":" ^ string_of_int loc.line
                             ^ ":" ^ string_of_int loc.column)
  | _ -> error loc "Test.location takes a Unit as argument"

let test_true loc depth args_val = match args_val with
  | [Vstring name; Vcons ((dloc, b), [])]
    -> if b = "true" then
        (print_string ("[  OK] "^name^"\n");
         ttrue)
      else
        (print_string ("[FAIL] "^name^"\n");
         tfalse)
  | _ -> error loc "Test.true takes a String and a Bool as argument"

let test_false loc depth args_val = match args_val with
  | [Vstring name; Vcons ((dloc, b), [])]
    -> if b = "false" then
        (print_string ("[  OK] "^name^"\n");
         ttrue)
      else
        (print_string ("[FAIL] "^name^"\n");
         tfalse)
  | _ -> error loc "Test.false takes a String and a Bool as argument"

let test_eq loc depth args_val = match args_val with
  | [_typ; Vstring name; v0; v1]
    -> if Env.value_equal v0 v1 then
        (print_string ("[  OK] "^name^"\n");
         ttrue)
      else
        (print_string ("[FAIL] "^name^"\n");
         tfalse)
  | _ -> error loc "Test.eq takes a String and two values as argument"

let test_neq loc depth args_val = match args_val with
  | [_typ; Vstring name; v0; v1]
    -> if Env.value_equal v0 v1 then
        (print_string ("[FAIL] "^name^"\n");
         tfalse)
      else
        (print_string ("[  OK] "^name^"\n");
         ttrue)
  | _ -> error loc "Test.neq takes a String and two values as argument"

let typelevel_succ loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vint v] -> Vint(v + 1)
    | _ -> error loc ("`Typlevel.succ` expects 1 TypeLevel argument")
let typelevel_lub loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vint v1; Vint v2] -> Vint(max v1 v2)
    | _ -> error loc ("`Typlevel.⊔` expects 2 TypeLevel argument2")

let register_builtin_functions () =
  List.iter (fun (name, f, arity) -> add_builtin_function name f arity)
            [
              ("Sexp.block"    , make_block, 1);
              ("Sexp.symbol"   , make_symbol, 1);
              ("Sexp.string"   , make_string, 1);
              ("Sexp.integer"  , make_integer, 1);
              ("Sexp.float"    , make_float, 1);
              ("Sexp.node"     , make_node, 2);
              ("Sexp.dispatch" , sexp_dispatch, 8);
              ("Reader.parse" , reader_parse,2);
              ("String.="      , string_eq, 2);
              ("String.concat" , string_concat, 2);
              ("String.sub"    , string_sub, 3);
              ("Sexp.="        , sexp_eq, 2);
              ("Sexp.debug_print", sexp_debug_print, 1);
              ("Float->String" , float_to_string, 1);
              ("Int->String"   , int_to_string, 1);
              ("Integer->String", integer_to_string, 1);
              ("Sys.exit"      , sys_exit, 1);
              ("File.open"     , file_open, 2);
              ("File.read"     , file_read, 2);
              ("File.write"    , file_write, 2);
              ("Ref.make"      , ref_make, 2);
              ("Ref.read"      , ref_read, 2);
              ("Ref.write"     , ref_write, 3);
              ("gensym"        , gensym, 1);
              ("Elab.getenv"   , getenv, 1);
              ("Elab.debug-doc", debug_doc, 2);
              ("Elab.isbound"  , is_bound, 2);
              ("Elab.isconstructor", is_constructor, 2);
              ("Elab.nth-arg"  , nth_arg, 3);
              ("Elab.arg-pos"  , arg_pos, 3);
              ("Array.append"  , array_append,3);
              ("Array.create"  , array_create,3);
              ("Array.length"  , array_length,2);
              ("Array.set"     , array_set,4);
              ("Array.get"     , array_get,4);
              ("Array.empty"   , array_empty,2);
              ("Test.fatal"    , test_fatal,2);
              ("Test.warning"  , test_warning,2);
              ("Test.info"     , test_info,2);
              ("Test.location" , test_location,1);
              ("Test.true"     , test_true,2);
              ("Test.false"    , test_false,2);
              ("Test.eq"       , test_eq,4);
              ("Test.neq"      , test_neq,4);
            ]
let _ = register_builtin_functions ()

let builtin_constant v loc depth args_val = match args_val with
  (* FIXME: Dummy arg because we currently can't define a Builtin
   * *constant* (except for cases like Eq.refl where the contant is not
   * actually used).  *)
  | [_] -> v ()
  | _ -> error loc "Builtin almost-constant takes a unit argument"

let register_builtin_constants () =
  List.iter (fun (name, v) -> add_builtin_function name (builtin_constant v) 1)
            [
              ("File.stdout", (fun () -> Vout stdout));
              ("Sys.cpu_time", (fun () -> Vfloat (Sys.time ())))
            ]
let _ = register_builtin_constants ()

let eval lxp ctx = eval lxp ctx ([], [])

let debug_eval lxp ctx =
    try eval lxp ctx
    with e -> (
      let ectx = !global_eval_ctx in
      let eval_trace = fst (get_trace ()) in
      Log.log_info ~section:"EVAL" ~print_action:(fun _ ->
          print_rte_ctx ectx;
          print_eval_trace (Some eval_trace)
        )
        "Exception occured during evaluation in the following context:";
      raise e)

let eval_decls decls ctx = eval_decls decls ctx ([], [])

let eval_decls_toplevel (decls: (vname * elexp) list list) ctx =
  (* Add toplevel decls function *)
  List.fold_left (fun ctx decls -> eval_decls decls ctx)
                 ctx decls

(*  Eval a list of lexp *)
let eval_all lxps rctx silent =
    let evalfun = if silent then eval else debug_eval in
    List.map (fun g -> evalfun g rctx) lxps


module CMap
  (* Memoization table.  FIXME: Ideally the keys should be "weak", but
   * I haven't found any such functionality in OCaml's libs.  *)
  = Hashtbl.Make
      (struct type t = lexp_context let hash = Hashtbl.hash let equal = (==) end)
let ctx_memo = CMap.create 1000

let not_closed rctx ((o, vm) : DB.set) =
  IMap.fold (fun i () nc -> let i = i + o in
                         let (_, rc) = Myers.nth i rctx in
                         match !rc with Vundefined -> i::nc | _ -> nc)
            vm []

let closed_p rctx (fvs) =
  not_closed rctx fvs = []

let from_lctx (lctx: lexp_context): runtime_env =
  (* FIXME: We should use `eval` with disabled side effects!  *)
  let rec from_lctx' (lctx: lexp_context): runtime_env =
    match lctx_view lctx with
    | CVempty -> Myers.nil
    | CVlet (loname, def, _, lctx)
      -> let rctx = from_lctx lctx in
         Myers.cons (loname,
                     ref (match def with
                          | LetDef (_, e)
                            -> let e = L.clean e in
                               if closed_p rctx (OL.fv e) then
                                 eval (OL.erase_type e) rctx
                               else Vundefined
                          | _ -> Vundefined))
                    rctx
    | CVfix (defs, lctx)
      -> let fvs = List.fold_left
                     (fun fvs (_, e, _)
                      -> OL.fv_union fvs (OL.fv (L.clean e)))
                     OL.fv_empty
                     defs in
         let rctx = from_lctx lctx in
         let (nrctx, evs, alldefs)
           = List.fold_left (fun (rctx, evs, alldefs) (loname, e, _)
                             -> let rc = ref Vundefined in
                                let nrctx = Myers.cons (loname, rc) rctx in
                                (nrctx, (e, rc)::evs, alldefs))
                            (rctx, [], true) defs in
         let _ =
           (* FIXME: Evaluate those defs that we can, even if not all defs
            * are present!  *)
           if alldefs && closed_p rctx (OL.fv_hoist (List.length defs) fvs) then
             List.iter (fun (e, rc) -> rc := eval (OL.erase_type e) nrctx) evs
           else () in
         nrctx
  and from_lctx lctx =
    try CMap.find ctx_memo lctx
    with Not_found
         -> let r = from_lctx' lctx in
            CMap.add ctx_memo lctx r;
            r
  in from_lctx lctx

(* build a rctx from a ectx.  *)
let from_ectx (ctx: elab_context): runtime_env =
  from_lctx (ectx_to_lctx ctx)
