(* log.ml --- User Errors/Warnings log for Typer.  -*- coding: utf-8 -*-

Copyright (C) 2019  Free Software Foundation, Inc.

Author: Jean-Alexandre Barszcz <jalex_b@hotmail.com>
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

(* LOGGING LEVELS *)

type log_level = Nothing | Fatal | Error | Warning | Info | Debug

let int_of_level lvl =
  match lvl with
  | Nothing -> -1 (* We might not want to print anything during testing *)
  | Fatal -> 0 | Error -> 1 | Warning -> 2 | Info -> 3 | Debug -> 4

let level_of_int i =
  match i with
  | _ when i < 0  -> Nothing
  | 0 -> Fatal | 1 -> Error | 2 -> Warning | 3 -> Info
  | _ -> Debug

let string_of_level lvl =
  match lvl with
  | Nothing -> "Nothing"
  | Fatal -> "Fatal"
  | Error -> "Error"
  | Warning -> "Warning"
  | Info -> "Info"
  | Debug -> "Debug"

let level_of_string str =
  match Util.string_uppercase str with
  | "NOTHING" -> Nothing
  | "FATAL" -> Fatal
  | "ERROR" -> Error
  | "WARNING" -> Warning
  | "INFO" -> Info
  | "DEBUG" -> Debug
  | _ -> invalid_arg ("`"^str^"` is not a logging level")

let level_color lvl =
  match lvl with
  | Nothing -> None
  | Fatal -> Some Fmt.red
  | Error -> Some Fmt.red
  | Warning -> Some Fmt.yellow
  | Info -> Some Fmt.cyan
  | Debug -> Some Fmt.magenta

(* LOGGING CONFIGURATION *)

type log_config = {
    mutable level : log_level;
    mutable print_at_log : bool;
    mutable print_in_reverse : bool;
    mutable color : bool;
  }

let typer_log_config : log_config = {
    level = Warning;
    print_at_log = false;
    print_in_reverse = false;
    color = true;
  }

(* LOG DEFINITION *)

type log_entry = {
    level : log_level;
    kind : string option;
    section : string option;
    print_action : (unit -> unit) option;
    loc : location option;
    msg : string;
  }

type log = log_entry list

let empty_log = []

let typer_log = ref empty_log

(* PRIVATE OPERATIONS *)

let mkEntry level ?kind ?section ?print_action ?loc msg =
  {level; kind; section; print_action; loc; msg}

let log_push (entry : log_entry) =
  typer_log := entry::(!typer_log)

let string_of_location (loc : location) =
  (loc.file ^ ":"
   ^ string_of_int loc.line ^ ":"
   ^ string_of_int loc.column ^ ":")

let maybe_color_string color_opt str =
  match color_opt with
  | Some color -> Fmt.color_string color str
  | None -> str

let string_of_log_entry {level; kind; section; loc; msg} =
  let color = if typer_log_config.color then (level_color level) else None in
  let parens s = "(" ^ s ^ ")" in
  (option_default "" (option_map string_of_location loc)
   ^ maybe_color_string color (option_default (string_of_level level) kind) ^ ":"
   ^ option_default "" (option_map parens section) ^ " "
   ^ msg)

let print_entry entry =
  print_endline (string_of_log_entry entry);
  match entry.print_action with
  | Some f -> f ()
  | None -> ()

let log_entry (entry : log_entry) =
  if (entry.level <= typer_log_config.level)
  then (
    log_push entry;
    if (typer_log_config.print_at_log)
    then
      (print_entry entry;
       flush stdout)
  )

let count_msgs (lvlp : log_level -> bool) =
  let count_step count {level} =
    if lvlp level then count + 1 else count
  in
  List.fold_left count_step 0 !typer_log

let error_count () = count_msgs (fun level -> level <= Error)
let warning_count () = count_msgs (fun level -> level = Warning)

(* PUBLIC INTERFACE *)

let set_typer_log_level lvl =
  typer_log_config.level <- lvl

let set_typer_log_level_str str =
  try set_typer_log_level (level_of_int (int_of_string str))
  with
    _ -> set_typer_log_level (level_of_string str)

let increment_log_level () =
  typer_log_config.level
  |> int_of_level
  |> (+) 1
  |> level_of_int
  |> set_typer_log_level

let clear_log () = typer_log := empty_log

let print_log () =
  let reverse = typer_log_config.print_in_reverse in
  let l = if reverse then !typer_log else List.rev !typer_log in
  List.iter print_entry l

let print_and_clear_log () =
  print_log (); clear_log ()

let log_msg level ?kind ?section ?print_action ?loc msg =
  log_entry (mkEntry level ?kind ?section ?print_action ?loc msg)

exception Internal_error of string
let internal_error s = raise (Internal_error s)

exception User_error of string
let user_error s = raise (User_error s)

exception Stop_Compilation of string
let stop_compilation s = raise (Stop_Compilation s)

let log_fatal ?section ?print_action ?loc m =
  log_msg Fatal ~kind:"[X] Fatal    " ?section ?print_action ?loc m;
  internal_error "Compiler Fatal Error"
let log_error = log_msg Error ?kind:None
let log_warning = log_msg Warning ?kind:None
let log_info = log_msg Info ?kind:None
let log_debug = log_msg Debug ?kind:None

let stop_on_error () =
  let count = error_count () in
  if (0 < count) then
    stop_compilation
      ("Compiler stopped after: "^(string_of_int count)^" errors\n")

let stop_on_warning () =
  stop_on_error ();
  let count = warning_count () in
  if (0 < count) then
    stop_compilation
      ("Compiler stopped after: "^(string_of_int count)^" warnings\n")

(* Compiler Internal Debug print *)
let debug_msg expr =
    if Debug <= typer_log_config.level then (print_string expr; flush stdout)

let not_implemented_error () = internal_error "not implemented"
