open Compilateur
open Exceptions

(* Changer le chemin d'accès du jar. *)
let runtamcmde = "java -jar ../../runtam.jar"
(* let runtamcmde = "java -jar /mnt/n7fs/.../tools/runtam/runtam.jar" *)

(* Execute the TAM code obtained from the rat file and return the ouptut of this code *)
let runtamcode cmde ratfile =
  let tamcode = compiler ratfile in
  let (tamfile, chan) = Filename.open_temp_file "test" ".tam" in
  output_string chan tamcode;
  close_out chan;
  let ic = Unix.open_process_in (cmde ^ " " ^ tamfile) in
  let printed = input_line ic in
  close_in ic;
  Sys.remove tamfile;    (* à commenter si on veut étudier le code TAM. *)
  String.trim printed

(* Compile and run ratfile, then print its output *)
let runtam ratfile =
  print_string (runtamcode runtamcmde ratfile)

exception ErreurNonDetectee

let%expect_test "test-add-aff-int" =
  runtam "../../fichiersRat/test-add-aff/test-add-aff-int.rat";
  [%expect{| 7 |}]

let%expect_test "test-add-aff-rat" =
  runtam "../../fichiersRat/test-add-aff/test-add-aff-rat.rat";
  [%expect{| [9/2] |}]

let%expect_test "test-add-aff-reference" =
  runtam "../../fichiersRat/test-add-aff/test-add-aff-reference.rat";
  [%expect{| 7 |}]

let%expect_test "test-add-aff-pointeur" =
  try let _ = runtam "../../fichiersRat/test-add-aff/test-add-aff-pointeur.rat"
  in raise ErreurNonDetectee 
  with 
  | TypeInattendu _ -> ();
  [%expect{| |}]

let%expect_test "test-add-aff-incompatible" =
  try let _ = runtam "../../fichiersRat/test-add-aff/test-add-aff-incompatible.rat"
  in raise ErreurNonDetectee 
  with 
  | TypeInattendu _ -> ();
  [%expect{| |}]
  