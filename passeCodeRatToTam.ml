module PasseCodeRatToTam :
  Passe.Passe with type t1 = Ast.AstPlacement.programme and type t2 = string =
struct
  open Tds
  open Exceptions
  open Ast
  open Type
  open Code

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
    let code =
      match expr with
      | AstType.AppelFonction (ia, le) ->
          List.fold_left (fun c e -> c^generer_code_expression e) "" le ^
          "CALL (LB) " ^ get_nom ia
      | AstType.Ident x ->
          let str_taille, str_add, reg = get_var_data x in
          "LOAD (" ^ str_taille ^ ") " ^ str_add ^ "[" ^ reg ^ "]"
      | AstType.Booleen b -> if b then "LOADL 1" else "LOADL 0"
      | AstType.Entier i -> "LOADL " ^ string_of_int i
      | AstType.Unaire (u, e) ->
          let code_u =
            match u with
            | Numerateur -> "POP (0) 1"
            | Denominateur -> "POP (1) 1"
          in
          generer_code_expression e ^ code_u
      | AstType.Binaire (b, e1, e2) ->
          let code_b =
            match b with
            | Fraction -> ""
            | PlusInt -> "SUBR IAdd"
            | PlusRat -> "CALL (LB) RAdd"
            | MultInt -> "SUBR IMul"
            | MultRat -> "CALL (LB) RMul"
            | EquBool -> "SUBR IEq"
            | EquInt -> "SUBR IEq"
            | InfInt -> "SUBR ILss"
          in
          generer_code_expression e1 ^ generer_code_expression e2 ^ code_b
    in
    code ^ "\n"

  (* analyse_type_instruction : typ option -> AstTds.instruction -> AstType.instruction *)
  (* Paramètre tf : le type de retour de la fonction le cas échéant *)
  (* Paramètre i : l'instruction à analyser *)
  (* Vérifie le bon typage des identifiants, fait de la résolution de surcharge
     et tranforme l'instruction en une instruction de type AstType.instruction *)
  (* Erreur si mauvaise utilisation des identifiants *)
  let rec generer_code_instruction i taille_retour taille_params =
    let code, taille =
      match i with
      | AstType.Declaration (ia, e) ->
          let taille_int = get_taille ia in
          let taille, addr, reg = get_var_data ia in
          "PUSH " ^ taille ^ "\n" ^
          generer_code_expression e ^
          "STORE (" ^ taille ^ ") " ^ addr ^ "[" ^ reg ^ "]", taille_int
      | AstType.Affectation (ia, e) ->
          let taille, addr, reg = get_var_data ia in
          generer_code_expression e ^
          "STORE (" ^ taille ^ ") " ^ addr ^ "[" ^ reg ^ "]", 0
      | AstType.AffichageInt e -> 
          generer_code_expression e ^
          "SUBR IOut", 0
      | AstType.AffichageRat e ->
          generer_code_expression e ^
          "CALL (LB) ROut", 0
      | AstType.AffichageBool e -> 
          generer_code_expression e ^
          "SUBR BOut", 0
      | AstType.Conditionnelle (e, bt, be) ->
          let etiqelse = getEtiquette () in
          let etiqfin = getEtiquette () in
          generer_code_expression e ^ "JUMPIF (0) " ^ etiqelse ^ "\n" ^
          generer_code_bloc bt taille_retour taille_params ^
          "JUMP " ^ etiqfin ^ "\n" ^
          etiqelse ^ "\n" ^
          generer_code_bloc be taille_retour taille_params ^
          etiqfin, 0
      | AstType.TantQue (e, b) ->
          let etiqdeb = getEtiquette () in
          let etiqfin = getEtiquette () in
          etiqdeb ^ "\n" ^
          generer_code_expression e ^
          "JUMPIF (0) " ^ etiqfin ^ "\n" ^
          generer_code_bloc b taille_retour taille_params ^
          "JUMP " ^ etiqdeb ^ "\n" ^
          etiqfin, 0
      | AstType.Retour e ->
          generer_code_expression e ^ "\n" ^ 
          "RETURN (" ^ string_of_int taille_retour ^ ") " ^ string_of_int taille_params, 0
      | AstType.Empty -> "", 0
    in
    code ^ "\n", taille

  (* analyse_type_bloc : typ option -> AstTds.bloc -> AstType.bloc *)
  (* Paramètre tf : type de retour de la fonction le cas échéant *)
  (* Paramètre li : liste d'instructions à analyser *)
  (* Vérifie le bon typage des identifiants et tranforme le bloc
     en un bloc de type AstType.bloc *)
  (* Erreur si mauvais typage des identifiants *)
  and generer_code_bloc li taille_retour taille_params =
    let code, taille = List.fold_right
      (fun i (c, t) -> 
        let code, taille = (generer_code_instruction i taille_retour taille_params) in 
        code ^ c, t + taille)
      li ("", 0)
    in code ^ "POP (0) " ^ string_of_int taille ^ "\n"

  (* analyse_type_fonction : AstTds.fonction -> AstType.fonction *)
  (* Paramètre : la fonction à analyser *)
  (* Vérifie le bon typage des identifiants et tranforme la fonction
     en une fonction de type AstType.fonction *)
  (* Erreur si mauvais typage des identifiants *)
  let generer_code_fonction (AstPlacement.Fonction (ia, lp, li)) =
    get_nom ia ^ "\n" ^
    generer_code_bloc li (get_taille ia) (List.fold_right (fun param taille -> (get_taille param)+taille) lp 0) ^
    "HALT\n"

  (* analyser : AstTds.Programme -> AstType.Programme *)
  (* Paramètre : le programme à analyser *)
  (* Vérifie le bon typage des identifiants et tranforme le programme
     en un programme de type AstType.Programme *)
  (* Erreur si mauvais typage des identifiants *)
  let analyser (AstPlacement.Programme (fonctions, prog)) = 
    getEntete () ^
    List.fold_right (fun f c -> generer_code_fonction f ^ c) fonctions "" ^
    "main\n" ^
    generer_code_bloc prog 0 0 ^
    "HALT"
end
