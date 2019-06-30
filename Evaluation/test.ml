open Lexing
open Printf
open VermillionJsonParser

let char_list_of_string (s : string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in  exp (String.length s - 1) []

let rec nat_of_int' (i : int) : nat =
  if i = 0 then O else S (nat_of_int' (i - 1))
       
let nat_of_int (i : int) : nat =
  if i < 0 then 
    raise (Invalid_argument "i can't be negative") 
  else 
    nat_of_int' i

let nat_of_float (f : float) : nat =
  nat_of_int (int_of_float f)

let print_char_list cs = List.iter (fun c -> print_string (Char.escaped c)) cs

let rec str_of_nat n = match n with | O -> "O" | S n' -> "S" ^ str_of_nat n'

let sum_floats (fs : float list) : float =
  List.fold_right (+.) fs 0.0

let str_of_float_list fs = "[" ^ String.concat "," (List.map string_of_float fs) ^ "]"

let str_of_int_list is   = "[" ^ String.concat "," (List.map string_of_int is) ^ "]"

let filenames_in_dir (dirname : string) : string list =
  List.sort String.compare (List.map (fun s -> dirname ^ "/" ^ s) 
                                     (Array.to_list (Sys.readdir dirname)))

let file_sizes (fnames : string list) : int list =
  List.map (fun fname -> (Unix.stat fname).st_size) fnames

let simplyTypedTokenOfMenhirToken (t : JsonTokenizer.token) : simply_typed_token =
  match t with
  | INT i       -> StInt (nat_of_int i)
  | FLOAT f     -> StFloat (nat_of_float f)
  | STRING s    -> StStr (char_list_of_string s)
  | TRUE        -> StTru
  | FALSE       -> StFls
  | NULL        -> StNull
  | LEFT_BRACE  -> StLeftBrace
  | RIGHT_BRACE -> StRightBrace
  | LEFT_BRACK  -> StLeftBrack
  | RIGHT_BRACK -> StRightBrack
  | COLON       -> StColon
  | COMMA       -> StComma
  | EOF         -> failwith "Vermillion doesn't treat EOF as a token"

let benchmark (f : 'a -> 'b) (x : 'a) : float * 'b =
  let start = Unix.gettimeofday () in
  let res = f x in
  let stop = Unix.gettimeofday () in
  let time = stop -. start
  in (time, res)

let run_menhir_parser lexbuf =
  benchmark (JsonParser.top Mlexer.mread) lexbuf
          
let record_menhir_parser_times (fnames : string list) =
  let parse_file fname =
    let () = Printf.printf "%s\n" fname  in
    let inx = open_in fname              in
    let lexbuf = Lexing.from_channel inx in
    let (time, o) = run_menhir_parser lexbuf in
    let () = Printf.printf "Menhir parser time: %fs\n" time in
    let () = (match o with
              | Some v -> print_string "menhir success\n"
              | None   -> print_string "menhir fail\n") in
    let () = close_in inx in
    time
  in
  let avg_trials (n : int) fname =
    let rec run_trials n =
      if n <= 0 then [] else parse_file fname :: run_trials (n - 1)
    in  sum_floats (run_trials n) /. (float_of_int n)
  in
  List.map (avg_trials 10) fnames

let vtoken_of_mtoken t =
  depTokenOfSimplyTypedToken (simplyTypedTokenOfMenhirToken t)

let run_menhir_tokenizer_and_vermillion_parser lexbuf =
  match PG.parseTableOf jsonGrammar with
  | Inr tbl ->
     let (lextime, ts) = benchmark (JsonTokenizer.top Vlexer.vread) lexbuf in
     let ts' = List.map vtoken_of_mtoken ts                              in
     let (parsetime, vres) = benchmark (PG.parse tbl (NT jsonGrammar.start)) ts'   in
     (lextime, parsetime, vres)
  | Inl msg ->
     print_char_list msg;
     exit 1

let record_menhir_tokenizer_and_vermillion_parser_times fnames =
  let parse_file fname =
    let () = Printf.printf "%s\n" fname in
    let inx = open_in fname in
    let lexbuf = Lexing.from_channel inx in
    let (lextime, parsetime, e) =
      run_menhir_tokenizer_and_vermillion_parser lexbuf in
    let () = Printf.printf "Menhir tokenizer time: %fs\n" lextime in
    let () = Printf.printf "Vermillion parser time: %fs\n" parsetime in
    let () = Printf.printf "Total: %fs\n" (lextime +. parsetime) in
    let () = (match e with
              | Inl (Error (m, x, ts')) -> print_char_list m
              | Inl (Reject (m, ts')) -> print_char_list m
              | Inr (v, r)            -> 
                 print_string "LL(1) success\n") in
    (lextime, parsetime)
  in
  let avg_trials (n : int) fname =
    let rec run_trials n =
      if n <= 0 then [] else parse_file fname :: run_trials (n - 1)
    in
    let (lextimes, parsetimes) = List.split (run_trials n) in
    (sum_floats lextimes /. (float_of_int n), sum_floats parsetimes /. (float_of_int n))
  in
  List.map (avg_trials 10) fnames

let main (data_dir : string) (out_f : string) : unit =
  (* First, collect the results *)
  let fnames = filenames_in_dir data_dir                           in
  let menhir_parser_times = record_menhir_parser_times fnames in
  let ll1_lex_and_parse_times = record_menhir_tokenizer_and_vermillion_parser_times fnames     in
  let (ll1_lex, ll1_parse) = List.split ll1_lex_and_parse_times    in
  (* Next, format the results *)
  let json_str =
    Printf.sprintf "{\"file_sizes\" : %s,\n\"menhir_parser_times\" : %s,\n\"ll1_lexer_times\" : %s,\n\"ll1_parser_times\" : %s}\n"
                    (str_of_int_list   (file_sizes fnames))
                    (str_of_float_list menhir_parser_times)
                    (str_of_float_list ll1_lex)
                    (str_of_float_list ll1_parse) in
  (* Finally, write the results file *)
  let () = print_string json_str                  in
  let out_c = open_out out_f                      in
  output_string out_c json_str
               
let () = main Sys.argv.(1) Sys.argv.(2)

