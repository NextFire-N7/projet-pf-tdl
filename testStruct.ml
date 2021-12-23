open Compilateur
open Exceptions

(* Changer le chemin d'accès du jar. *)
let runtamcmde = "java -jar ../../runtam.jar"
(* let runtamcmde = "java -jar /mnt/n7fs/.../tools/runtam/runtam.jar" *)

(* Execute the TAM code obtained from the rat file and return the ouptut of this code *)
let runtamcode cmde ratfile =
  let tamcode = compiler ratfile in
  let tamfile, chan = Filename.open_temp_file "test" ".tam" in
  output_string chan tamcode;
  close_out chan;
  let ic = Unix.open_process_in (cmde ^ " " ^ tamfile) in
  let printed = input_line ic in
  close_in ic;
  Sys.remove tamfile;
  (* à commenter si on veut étudier le code TAM. *)
  String.trim printed

(* Compile and run ratfile, then print its output *)
let runtam ratfile = print_string (runtamcode runtamcmde ratfile)

let%expect_test "exemple1" =
  runtam "../../fichiersRat/test-struct/exemple1.rat";
  [%expect {| 3[1/4] |}]

let%expect_test "exemple2" =
  runtam "../../fichiersRat/test-struct/exemple2.rat";
  [%expect {| 4835 |}]

let%expect_test "exemple3" =
  runtam "../../fichiersRat/test-struct/exemple3.rat";
  [%expect {| 12 |}]

let%expect_test "exemple4-double-decl" =
  try runtam "../../fichiersRat/test-struct/exemple4-double-decl.rat"
  with DoubleDeclaration "y" -> ()

let%expect_test "exemple5-double-decl" =
  try runtam "../../fichiersRat/test-struct/exemple5-double-decl.rat"
  with DoubleDeclaration "x" -> ()

let%expect_test "exemple6" =
  runtam "../../fichiersRat/test-struct/exemple6.rat";
  [%expect {| 3 |}]

let%expect_test "exemple7-mauvaise-util" =
  try runtam "../../fichiersRat/test-struct/exemple7-mauvaise-util.rat"
  with MauvaiseUtilisationIdentifiant "x" -> ()

let%expect_test "exemple8-bonus" =
  runtam "../../fichiersRat/test-struct/exemple8-bonus.rat";
  [%expect {| 123 |}]
