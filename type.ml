type typ = Bool | Int | Rat | Undefined | Pointeur of typ | NamedTyp of string | Struct of (typ * string) list

let rec string_of_type t = 
  match t with
  | Bool ->  "Bool"
  | Int  ->  "Int"
  | Rat  ->  "Rat"
  | Pointeur t -> "* "^(string_of_type t)
  | Undefined -> "Undefined"
  | NamedTyp n -> n
  | Struct lnt -> (List.fold_left (fun chaine (t,n) -> chaine ^ " " ^ (string_of_type t) ^ " " ^ n) "{" lnt ) ^ " }"


let rec est_compatible t1 t2 =
  match t1, t2 with
  | Bool, Bool -> true
  | Int, Int -> true
  | Rat, Rat -> true 
  | Pointeur a, Pointeur b -> (est_compatible a b) ||
    (match a,b with
    (* Pointeur null *)
    | _, Undefined -> true
    | _ -> false)
  | Struct ltn1, Struct ltn2 -> est_compatible_list (List.map (fst) ltn1) (List.map (fst) ltn2)
  | _ -> false 

and est_compatible_list lt1 lt2 =
  try
    List.for_all2 est_compatible lt1 lt2
  with Invalid_argument _ -> false

let%test _ = est_compatible Bool Bool
let%test _ = est_compatible Int Int
let%test _ = est_compatible Rat Rat
let%test _ = not (est_compatible Int Bool)
let%test _ = not (est_compatible Bool Int)
let%test _ = not (est_compatible Int Rat)
let%test _ = not (est_compatible Rat Int)
let%test _ = not (est_compatible Bool Rat)
let%test _ = not (est_compatible Rat Bool)
let%test _ = not (est_compatible Undefined Int)
let%test _ = not (est_compatible Int Undefined)
let%test _ = not (est_compatible Rat Undefined)
let%test _ = not (est_compatible Bool Undefined)
let%test _ = not (est_compatible Undefined Int)
let%test _ = not (est_compatible Undefined Rat)
let%test _ = not (est_compatible Undefined Bool)

(* Pointeurs *)
let%test _ = (est_compatible (Pointeur Int) (Pointeur Int))
let%test _ = (est_compatible (Pointeur Int) (Pointeur Undefined))
let%test _ = (not (est_compatible (Pointeur Int) (Pointeur Bool)))
let%test _ = not (est_compatible (Pointeur Int) Rat)



let%test _ = est_compatible_list [] []
let%test _ = est_compatible_list [Int ; Rat] [Int ; Rat]
let%test _ = est_compatible_list [Bool ; Rat ; Bool] [Bool ; Rat ; Bool]
let%test _ = not (est_compatible_list [Int] [Int ; Rat])
let%test _ = not (est_compatible_list [Int] [Rat ; Int])
let%test _ = not (est_compatible_list [Int ; Rat] [Rat ; Int])
let%test _ = not (est_compatible_list [Bool ; Rat ; Bool] [Bool ; Rat ; Bool ; Int])

let rec getTaille t =
  match t with
  | Int -> 1
  | Bool -> 1
  | Rat -> 2
  | Undefined -> 0
  | Pointeur _ -> 1
  | Struct ltn -> List.fold_left (fun taille (t,n) -> taille + getTaille t) 0 ltn
  
let%test _ = getTaille Int = 1
let%test _ = getTaille Bool = 1
let%test _ = getTaille Rat = 2
