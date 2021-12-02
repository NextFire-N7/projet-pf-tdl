module PasseCodeRatToTam :
  Passe.Passe with type t1 = Ast.AstPlacement.programme and type t2 = string =
struct
  open Tds
  open Exceptions
  open Ast
  open Type

  type t1 = Ast.AstPlacement.programme

  type t2 = string

  (* AstTds.expression -> (AstType.Expression * typ) = <fun> *)
  (* Paramètre:
       - expr: AstTds.expression = l'expression dont on souhaite vérifier le typage
     Retour: (AstType.expression * typ)
       - La nouvelle expression (principalement les nouveaux appels et nouveaux opérateurs
       - Le type réel de l'expression après analyse
       - Exceptions si les types attendus pour les diverses expressions ne correspondent pas aux types réels obtenus
  *)
  let rec generer_code_expression expr =
    match expr with
    | AstType.AppelFonction (ia, le) -> ""
    | AstType.Ident x ->
        "LOADL " ^ string_of_type (get_type x) ^ " @" ^ get_nom x
    | AstType.Booleen b -> if b then "LOADL 1" else "LOADL 0"
    | AstType.Entier i -> "LOADL " ^ string_of_int i
    | AstType.Unaire (u, e) -> 
      let code_u = (match u with 
      | Numerateur -> "POP (0) 1" 
      | Denominateur -> "POP (1) 1")
    in generer_code_expression e ^ code_u 
    | AstType.Binaire (b, e1, e2) -> let code_b = (match b with 
    | Fraction -> "POP (0) 1" 
    | PlusInt -> "POP (1) 1"
    | PlusRat -> ""
    | MultInt -> ""
    | MultRat -> ""
    | EquBool -> ""
    | EquInt -> ""
    | InfInt -> "")
  in generer_code_expression e1 ^ generer_code_expression e2 ^ code_b

  (* analyse_type_instruction : typ option -> AstTds.instruction -> AstType.instruction *)
  (* Paramètre tf : le type de retour de la fonction le cas échéant *)
  (* Paramètre i : l'instruction à analyser *)
  (* Vérifie le bon typage des identifiants, fait de la résolution de surcharge
     et tranforme l'instruction en une instruction de type AstType.instruction *)
  (* Erreur si mauvaise utilisation des identifiants *)
  let rec generer_code_instruction i =
    match i with
    | AstType.Declaration (ia, e) ->
      let taille = Int.to_string (getTaille (get_type ia)) in
      let adresse = Int.to_string (get_adresse ia) in
        "PUSH " ^ taille ^ ";"
        ^ generer_code_expression e ^ ";"
        ^ "STORE(" ^ taille ^ ")" ^ adresse ^ "[" ^ reg ^ "]" ^
    | AstType.Affectation (ia, e) -> ""
    | AstType.AffichageInt e -> ""
    | AstType.AffichageRat e -> ""
    | AstType.AffichageBool e -> ""
    | AstType.Conditionnelle (e, bt, be) -> ""
    | AstType.TantQue (e, b) -> ""
    | AstType.Retour e -> ""
    | AstType.Empty -> ""

  (* analyse_type_bloc : typ option -> AstTds.bloc -> AstType.bloc *)
  (* Paramètre tf : type de retour de la fonction le cas échéant *)
  (* Paramètre li : liste d'instructions à analyser *)
  (* Vérifie le bon typage des identifiants et tranforme le bloc
     en un bloc de type AstType.bloc *)
  (* Erreur si mauvais typage des identifiants *)
  and generer_code_bloc li =
    List.fold_right (fun (i, c) -> generer_code_instruction i ^ c) li ""

  (* analyse_type_fonction : AstTds.fonction -> AstType.fonction *)
  (* Paramètre : la fonction à analyser *)
  (* Vérifie le bon typage des identifiants et tranforme la fonction
     en une fonction de type AstType.fonction *)
  (* Erreur si mauvais typage des identifiants *)
  let generer_code_fonction (AstPlacement.Fonction (ia, lp, li)) = ()

  (* analyser : AstTds.Programme -> AstType.Programme *)
  (* Paramètre : le programme à analyser *)
  (* Vérifie le bon typage des identifiants et tranforme le programme
     en un programme de type AstType.Programme *)
  (* Erreur si mauvais typage des identifiants *)
  let analyser (AstPlacement.Programme (fonctions, prog)) = "HALT"
end
