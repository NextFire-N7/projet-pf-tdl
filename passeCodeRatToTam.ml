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

  let generer_code_affectable modif aff =
    let rec generer_code_affectable_int modif aff =
      match aff with
      | AstTds.Deref a ->
          let code, taille = generer_code_affectable_int false a in
          if modif then (code ^ "\n" ^ "STOREI (" ^ string_of_int taille ^ ")", 0)
          else (code ^ "\n" ^ "LOADI (" ^ string_of_int taille ^ ")", 1)
      | AstTds.Ident ia -> (
          match info_ast_to_info ia with
          | InfoConst (_, v) ->
              if modif then failwith "on a foiré le typage"
              else ("LOADL " ^ string_of_int v, 0)
          | InfoVar (_, t, _, _) ->
              (* on récupère des données sur la variable *)
              let str_taille, str_add, reg = get_var_data ia in
              (* Et on la charge sur la stack *)
              let code =
                if modif then
                  "STORE (" ^ str_taille ^ ") " ^ str_add ^ "[" ^ reg ^ "]"
                else "LOAD (" ^ str_taille ^ ") " ^ str_add ^ "[" ^ reg ^ "]"
              in
              (code, getTaille t)
          | _ -> failwith "on a foiré le typage")
    in
    let code, _ = generer_code_affectable_int modif aff in
    code

  (* AstType.expression -> string = <fun> *)
  (* Paramètres:
       - expr: AstTds.expression = l'expression dont on souhaite vérifier le typage
     Retour: string = Le code généré par l'expression
  *)
  let rec generer_code_expression expr =
    let code =
      match expr with
      | AstType.AppelFonction (ia, le) ->
          (* Pour appeler une fonction, on génère le code des expressions formant les paramètres*)
          List.fold_left (fun c e -> c^generer_code_expression e) "" le ^
          (* puis on appelle la fonction *)
          "CALL (LB) " ^ get_nom ia
      | AstType.Affectable aff -> generer_code_affectable false aff
      | AstType.Null -> "SUBR MVoid"
      | AstType.New t ->
          "LOADL " ^ string_of_int (getTaille t) ^ "\n" ^
          "SUBR MAlloc"
      | AstType.Adresse ia ->
          let _, str_add, reg = get_var_data ia in
          "LOADA " ^  str_add ^ "[" ^ reg ^ "]"
      (* En fonction du résultat du booleén, on charge 1 ou 0 sur la stack *)
      | AstType.Booleen b -> if b then "LOADL 1" else "LOADL 0"
      (* De même, on charge la valeur de l'entier *)
      | AstType.Entier i -> "LOADL " ^ string_of_int i
      | AstType.Unaire (u, e) ->
          let code_u =
            match u with
            (* Si l'on souhaite garder le numérateur, on enlève le dénominateur (valeur sur le dessus de la stack) *)
            | Numerateur -> "POP (0) 1"
            (* Inversement poru le dénominateur *)
            | Denominateur -> "POP (1) 1"
          in
          generer_code_expression e ^ code_u
      | AstType.Binaire (b, e1, e2) ->
          let code_b =
            match b with
            (* Pour Fraction, les deux valeurs sont déjà chargées dans le bon ordre sur la stack, rien n'est à faire. *)
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

  (* generer_code_instruction : AstType.instruction -> int -> int -> string * int *)
  (* Paramètre i : l'instruction à générer *)
  (* Paramètre taille_retour : taille du résultat si fonction *)
  (* Paramètre taille_params : taille des paramètres si fonction *)
  (* Génère le code TAM associé à l'instruction et renvoie aussi la taille de la déclaration
  le cas échéant (à pop à la fin du bloc) *)
  let rec generer_code_instruction i taille_retour taille_params =
    let code, taille =
      match i with
      | AstType.Declaration (ia, e) ->
          let taille_int = get_taille ia in
          (* get_var_data renvoie la taille, l'adresse et le registre de la variable sous forme de strings *)
          let taille, addr, reg = get_var_data ia in
          (* Réservation dans le stack *)
          "PUSH " ^ taille ^ "\n" ^
          (* code de l'expr *)
          generer_code_expression e ^
          (* Store du résultat de l'expression dans l'espace alloué précédement *)
          "STORE (" ^ taille ^ ") " ^ addr ^ "[" ^ reg ^ "]", taille_int
      | AstType.Affectation (aff, e) ->
          (* code de l'expr *)
          generer_code_expression e ^
          (* puis store *)
          generer_code_affectable true aff, 0
      | AstType.AffichageInt e ->
          (* code de l'expr *)
          generer_code_expression e ^
          (* puis affichage entier *)
          "SUBR IOut", 0
      | AstType.AffichageRat e ->
          (* code de l'expr *)
          generer_code_expression e ^
          (* puis affichage rationnel (callable défini en header) *)
          "CALL (LB) ROut", 0
      | AstType.AffichageBool e ->
          (* code de l'expr *)
          generer_code_expression e ^
          (* puis affichage booléen *)
          "SUBR BOut", 0
      | AstType.Conditionnelle (e, bt, be) ->
          (* génération d'étiquettes uniques pour le else et le end *)
          let etiqelse = getEtiquette () in
          let etiqfin = getEtiquette () in
          (* code de la condition et jump dans le else si false *)
          generer_code_expression e ^ "JUMPIF (0) " ^ etiqelse ^ "\n" ^
          (* code du bloc then *)
          generer_code_bloc bt taille_retour taille_params ^
          (* jump vers le end *)
          "JUMP " ^ etiqfin ^ "\n" ^
          (* else *)
          etiqelse ^ "\n" ^
          (* code du bloc else *)
          generer_code_bloc be taille_retour taille_params ^
          (* end *)
          etiqfin, 0
      | AstType.TantQue (e, b) ->
          (* génération d'étiquettes uniques pour le debut et la fin de la boucle *)
          let etiqdeb = getEtiquette () in
          let etiqfin = getEtiquette () in
          (* début boucle *)
          etiqdeb ^ "\n" ^
          (* code de la condition et jump dans la fin si false *)
          generer_code_expression e ^
          "JUMPIF (0) " ^ etiqfin ^ "\n" ^
          (* code du bloc *)
          generer_code_bloc b taille_retour taille_params ^
          (* jump inconditionnel vers le debut *)
          "JUMP " ^ etiqdeb ^ "\n" ^
          (* fin de la boucle *)
          etiqfin, 0
      | AstType.Retour e ->
          (* code de l'expr *)
          generer_code_expression e ^ "\n" ^
          (* puis retour *)
          "RETURN (" ^ string_of_int taille_retour ^ ") " ^ string_of_int taille_params, 0
      | AstType.Empty -> "", 0
    in
    code ^ "\n", taille

  (* generer_code_bloc : AstType.bloc -> int -> int -> t2(=string) *)
  (* Paramètres
      - li = liste d'instructions *)
  (*  - taille_retour = taille du type de retour (utile pour l'instruction return) *)
  (*  - taille_params = taille de la liste de paramètres de la fonction (utile pour l'instruction return)*)
  (* Génère le code correspondant au bloc, et retire du stack les nouvelles variables déclarées *)
  and generer_code_bloc li taille_retour taille_params =
    (* On récupère le code généré ainsi que la taille des nouvelles variables push sur le stack *)
    let code, taille = List.fold_right
      (fun i (c, t) ->
        (* Pour chaque instruction, on récupère le code ansi que la taille allouée sur le stack *)
        let code, taille = (generer_code_instruction i taille_retour taille_params) in
        code ^ c, t + taille)
      li ("", 0)
    in code ^
    (* Si des variables ont été déclarées, il est nécessaire de les enlever su stack à la fin du bloc (sortie du scope)*)
    (if taille > 0 then ("POP (0) " ^ string_of_int taille) else "") ^
    "\n"

  (* generer_code_fonction : AstPlacement.fonction -> string *)
  (* Paramètre : la fonction à analyser *)
  (* Génère le code de la fonction *)
  let generer_code_fonction (AstPlacement.Fonction (ia, lp, li)) =
    (* Saut de ligne pour mieux formater le fichier en language TAM *)
    "\n" ^
    (* étiquette qui porte le nom de la fonction *)
    get_nom ia ^ "\n" ^
    (* code de la fonction *)
    generer_code_bloc li (get_taille ia) (List.fold_right (fun param taille -> (get_taille param)+taille) lp 0) ^
    (* HALT pour éviter les problèmes avec les fonctions sans retour *)
    "HALT\n"

  (* analyser : AstPlacement.Programme -> string *)
  (* Paramètre : le programme à analyser *)
  (* Génère tout le code du programme compilé en language machine TAM *)
  let analyser (AstPlacement.Programme (fonctions, prog)) =
    (* On place les headers *)
    getEntete () ^
    (* On code les fonctions *)
    List.fold_right (fun f c -> generer_code_fonction f ^ c) fonctions "" ^
    (* Début du main *)
    "main\n" ^
    (* Code du main *)
    generer_code_bloc prog 0 0 ^
    (* Fin du programme principal *)
    "HALT"
end
