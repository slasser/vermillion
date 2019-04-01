module V = Vermillion

(* i must be non-negative *)
let rec natOf (i : int) : V.nat =
  if i = 0 then V.O else V.S (natOf (i - 1))
                             
let value  = natOf 0
let pairs  = natOf 1
let pairs' = natOf 2
let pair   = natOf 3
let elts   = natOf 4
let elts'  = natOf 5

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let lEFTBRACE = explode "{"
let rIGHTBRACE = explode "}"
let lEFTBRACK = explode "["
let rIGHTBRACK = explode "]"
let cOMMA = explode ","
let sTRING = explode "STRING"
let cOLON = explode ":"
let iNT = explode "INT"
let fLOAT = explode "FLOAT"
let tRUE = explode "TRUE"
let fALSE = explode "FALSE"
let nULL = explode "NULL"

let g : V.grammar =
  { start = value
  ; productions =
      [ (value, [T lEFTBRACE; NT pairs; T rIGHTBRACE])
      ; (value, [T lEFTBRACK; NT elts; T rIGHTBRACK])
      ; (value, [T sTRING])
      ; (value, [T iNT])
      ; (value, [T fLOAT])
      ; (value, [T tRUE])
      ; (value, [T fALSE])
      ; (value, [T nULL])
          
      ; (pairs, [])
      ; (pairs, [NT pair; NT pairs'])
          
      ; (pairs', [])
      ; (pairs', [T cOMMA; NT pair; NT pairs'])

      ; (pair, [T sTRING; T cOLON; NT value])

      ; (elts, [])
      ; (elts, [NT value; NT elts'])

      ; (elts', [])
      ; (elts', [T cOMMA; NT value; NT elts'])
      ]
  }

let rec count_nts (t:V.tree) : int =
  match t with
  | Leaf _ -> 0
  | Node (_, f) -> 1 + (count_nts' f)
and count_nts' (f:V.tree list) : int =
  match f with
  | [] -> 0
  | t :: f' -> (count_nts t + count_nts' f')

let rec tree_size (t:V.tree) : int =
  match t with
  | Leaf _ -> 1
  | Node (_, f) -> 1 + (forest_size f)
and forest_size (f:V.tree list) : int =
  match f with
  | [] -> 0
  | t :: f' -> (tree_size t + forest_size f')
