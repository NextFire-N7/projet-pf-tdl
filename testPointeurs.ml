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

let%expect_test "test-definition-bool" =
  runtam "../../fichiersRat/test-pointeurs/test-definition-bool.rat";
  [%expect{| false |}]

let%expect_test "test-definition-int" =
  runtam "../../fichiersRat/test-pointeurs/test-definition-int.rat";
  [%expect{| 5 |}]

let%expect_test "test-definition-rat" =
  runtam "../../fichiersRat/test-pointeurs/test-definition-rat.rat";
  [%expect{| [5/2] |}]

let%expect_test "test-definition-null" =
  runtam "../../fichiersRat/test-pointeurs/test-definition-null.rat";
  [%expect{| 0 |}]

let%expect_test "test-mauvaise-definition" =
  try let _ = runtam "../../fichiersRat/test-pointeurs/test-mauvaise-definition.rat"
  in raise ErreurNonDetectee 
  with 
  | TypeInattendu _ -> ();
  [%expect{| |}]

let%expect_test "test-acces-statique" =
  runtam "../../fichiersRat/test-pointeurs/test-acces-statique.rat";
  [%expect{| 5 |}]

let%expect_test "test-mauvaise-deref" =
  try let _ = runtam "../../fichiersRat/test-pointeurs/test-mauvaise-deref.rat"
  in raise ErreurNonDetectee 
  with 
  | DereferenceNonPointeur _ -> ();
  [%expect{| |}]
  
let%expect_test "test-pointeur-pointeur" =
  runtam "../../fichiersRat/test-pointeurs/test-pointeur-pointeur.rat";
  [%expect{| 5 |}]

let%expect_test "test-acces-dynamique" =
  runtam "../../fichiersRat/test-pointeurs/test-acces-dynamique.rat";
  [%expect{| 7 |}]

let%expect_test "test-param-fonction" =
  runtam "../../fichiersRat/test-pointeurs/test-param-fonction.rat";
  [%expect{| true10 |}]