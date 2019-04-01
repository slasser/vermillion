open Lexer
open Lexing
open Printf
open Token

module V  = Vermillion
module G  = JsonLL1Grammar
       
let strOf (t : token) : string =
  match t with
  | INT i -> "INT"
  | FLOAT f -> "FLOAT"
  | STRING s -> "STRING"
  | TRUE -> "TRUE"
  | FALSE -> "FALSE"
  | NULL -> "NULL"
  | LEFT_BRACE -> "{"
  | RIGHT_BRACE -> "}"
  | LEFT_BRACK -> "["
  | RIGHT_BRACK -> "]"
  | COLON -> ":"
  | COMMA -> ","
  | EOF -> "EOF"

let benchmark (f : 'a -> 'b) (x : 'a) : float * 'b =
  let start = Unix.gettimeofday () in
  let res = f x in
  let stop = Unix.gettimeofday () in
  let time = stop -. start
  in (time, res)

let run_gen_json_parser lexbuf =
  benchmark (JsonParser.top Lexer.read) lexbuf

let run_generated_json_tokenizer_and_ll1_parser lexbuf =
  match V.parseTableOf G.g with
  | Some tbl ->
     let (lextime, ts) = benchmark (JsonTokenizer.top Lexer.read) lexbuf in
     let ts' = List.map (fun t -> G.explode (strOf t)) ts in
     let (parsetime, e) = benchmark (V.parse_wrapper tbl (NT G.g.start)) ts' in
     (lextime, parsetime, e)
  | None ->
     print_string "no valid parse table";
     exit 1

let sum_floats fs =
  List.fold_right (+.) fs 0.0
          
let record_menhir_json_parser_times dirname =
  let parse_file fname =
    let () = Printf.printf "%s\n" fname in
    let inx = open_in (dirname ^ "/" ^ fname) in
    let lexbuf = Lexing.from_channel inx in
    let (time, o) = run_gen_json_parser lexbuf in
    let () = Printf.printf "Menhir parser time: %fs\n" time in
    let () = (match o with
              | Some v -> print_string "menhir success\n"
              | None -> print_string "menhir fail\n") in
    let () = close_in inx in
    time
  in
  let avg_trials (n : int) fname =
    let rec run_trials n =
      if n <= 0 then [] else parse_file fname :: run_trials (n - 1)
    in  sum_floats (run_trials n) /. (Float.of_int n)
  in
  List.map (avg_trials 10) (List.sort String.compare (Array.to_list (Sys.readdir dirname)))

let record_ll1_parser_times dirname =
  let parse_file fname =
    let () = Printf.printf "%s\n" fname in
    let inx = open_in (dirname ^ "/" ^ fname) in
    let lexbuf = Lexing.from_channel inx in
    let (lextime, parsetime, e) =
      run_generated_json_tokenizer_and_ll1_parser lexbuf in
    let () = Printf.printf "Menhir tokenizer time: %fs\n" lextime in
    let () = Printf.printf "LL(1) parser time: %fs\n" parsetime in
    let () = Printf.printf "Total: %fs\n" (lextime +. parsetime) in
    let () = (match e with
              | Inl pf -> print_string "LL(1) fail\n"
              | Inr (tr, ts') ->
                 print_string "LL(1) success\n";
                 Printf.printf "%d\n" (G.tree_size tr)) in
    (lextime, parsetime)
  in
  let avg_trials (n : int) fname =
    let rec run_trials n =
      if n <= 0 then [] else parse_file fname :: run_trials (n - 1)
    in
    let (lextimes, parsetimes) = List.split (run_trials n) in
    (sum_floats lextimes /. (Float.of_int n), sum_floats parsetimes /. (Float.of_int n))
  in
  List.map (avg_trials 10) (List.sort String.compare (Array.to_list (Sys.readdir dirname)))
             
let main dirname =
  let menhir_parser_times = record_menhir_json_parser_times dirname in
  let ll1_lex_and_parse_times = record_ll1_parser_times dirname in
  List.iter (fun (m, (vl, vp)) -> Printf.printf "%f %f %f %f\n" m vl vp (vl +. vp))
    (List.combine menhir_parser_times ll1_lex_and_parse_times)

let () = main "data"
