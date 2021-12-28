module PasseTypeRat :
  Passe.Passe
    with type t1 = Ast.AstTds.programme
     and type t2 = Ast.AstType.programme = struct
  open Tds
  open Exceptions
  open Ast
  open AstType
  open Type

  type t1 = Ast.AstTds.programme
  type t2 = Ast.AstType.programme

  (* AstTds.affectable -> (AstType.affectable * typ) = <fun> *)
  (* Paramètre:
         - a: AstTds.affectable = l'affectable
     Retour:
         - AstType.affectable = le même affectable
         - typ = le type de l'affectable
     Raise:
         - DereferenceNonPointeur t = Si l'on tente de déréférencer un type t autre que Pointeur
  *)
  let rec analyse_type_affectable a =
    let t =
      match a with
      | AstTds.Deref a -> (
          (* On récupère le type réel de l'affectable déréférencé *)
          let _, taff = analyse_type_affectable a in
          match taff with
          (* On déréférence le pointeur *)
          | Pointeur t -> t
          (* Si ce n'est pas un pointeur, on renvoir une erreur *)
          | _ -> raise (DereferenceNonPointeur taff))
      (* Si c'est un identifiant, on retourne le type de l'identifiant. *)
      | AstTds.Ident ia | AstTds.Acces (_, ia) -> get_type ia
    in
    (a, t)

  let rec analyse_type_declaration t ia =
    modifier_type_info t ia;
    match info_ast_to_info ia with
    | InfoStruct (_, _, _, _, li) -> (
        match t with
        | Struct lc ->
            let _ =
              List.map2 (fun (t, _) ia -> analyse_type_declaration t ia) lc li
            in
            ()
        | _ -> ())
    | _ -> ()

  (* AstTds.expression -> (AstType.Expression * typ) = <fun> *)
  (* Paramètre:
       - expr: AstTds.expression = l'expression dont on souhaite vérifier le typage
     Retour: (AstType.expression * typ)
       - La nouvelle expression (principalement les nouveaux appels et nouveaux opérateurs
       - Le type réel de l'expression après analyse
     Throws:
       - Exceptions si les types attendus pour les diverses expressions ne correspondent pas aux types réels obtenus
  *)
  let rec analyse_type_expression expr =
    match expr with
    | AstTds.AppelFonction (ia, le) ->
        (* Pour chaque paramètre, on récupère le couple (nouvelle expression * type réel) *)
        let nlet = List.map analyse_type_expression le in
        (* On récupère le type de retour de la fonction... *)
        let tr = get_type ia in
        (* ... ainsi que le type attendu de ses paramètres *)
        let tpara = get_types_params ia in
        let nle = List.map fst nlet in
        let nlt = List.map snd nlet in
        (* Si les types sont conformes, on peut continuer et le type de l'expression est le type de retour de la fonction. *)
        if List.for_all2 (fun t1 t2 -> est_compatible t1 t2) tpara nlt then
          (AppelFonction (ia, nle), tr)
        else raise (TypesParametresInattendus (nlt, tpara))
    | AstTds.Affectable aff ->
        let naff, taff = analyse_type_affectable aff in
        (Affectable naff, taff)
    | AstTds.Null -> (Null, Pointeur Undefined)
    | AstTds.New t -> (New t, Pointeur t)
    | AstTds.Adresse ia ->
        let t = get_type ia in
        (Adresse ia, Pointeur t)
    | AstTds.Booleen b -> (Booleen b, Bool)
    | AstTds.Entier i -> (Entier i, Int)
    | AstTds.Unaire (u, e) ->
        (* Les seuls opérateurs unaires travaillent sur un Rat et retournent un Int *)
        let n_unaire =
          match u with
          (* On retourne le nouvel opérateur unaire *)
          | AstSyntax.Numerateur -> Numerateur
          | AstSyntax.Denominateur -> Denominateur
        in
        let ne, te = analyse_type_expression e in
        (* On vérifie la compatibilité des types. *)
        if est_compatible te Rat then (Unaire (n_unaire, ne), Int)
        else raise (TypeInattendu (te, Rat))
    | AstTds.Binaire (f, e1, e2) ->
        let ne1, te1 = analyse_type_expression e1 in
        let ne2, te2 = analyse_type_expression e2 in
        let n_binaire, tr =
          (*TODO: est_compatible *)
          (* Pour chaque binaire, on gère la surcharge en comparant les types autorisés des surcharges *)
          match (f, te1, te2) with
          | AstSyntax.Fraction, Int, Int -> (Fraction, Rat)
          | AstSyntax.Plus, Int, Int -> (PlusInt, Int)
          | AstSyntax.Plus, Rat, Rat -> (PlusRat, Rat)
          | AstSyntax.Mult, Int, Int -> (MultInt, Int)
          | AstSyntax.Mult, Rat, Rat -> (MultRat, Rat)
          | AstSyntax.Equ, Int, Int -> (EquInt, Bool)
          | AstSyntax.Equ, Bool, Bool -> (EquBool, Bool)
          | AstSyntax.Inf, Int, Int -> (InfInt, Bool)
          | _ -> raise (TypeBinaireInattendu (f, te1, te2))
        in
        (Binaire (n_binaire, ne1, ne2), tr)
    | AstTds.StructExpr le ->
        let nlet = List.map analyse_type_expression le in
        ( StructExpr (List.map fst nlet),
          Struct (List.map (fun (_, t) -> (t, "")) nlet) )

  (* analyse_type_instruction : typ option -> AstTds.instruction -> AstType.instruction *)
  (* Paramètre tf : le type de retour de la fonction le cas échéant *)
  (* Paramètre i : l'instruction à analyser *)
  (* Vérifie le bon typage des identifiants, fait de la résolution de surcharge
     et tranforme l'instruction en une instruction de type AstType.instruction *)
  (* Erreur si mauvaise utilisation des identifiants *)
  let rec analyse_type_instruction tf i =
    match i with
    | AstTds.Declaration (t, ia, e) ->
        analyse_type_declaration t ia;
        (* Crash si le type de l'expression n'est pas compatible avec celui déclaré *)
        let ne, te = analyse_type_expression e in
        if est_compatible t te then Declaration (ia, ne)
        else raise (TypeInattendu (te, t))
    | AstTds.Affectation (aff, e) ->
        let ne, te = analyse_type_expression e in
        let naff, taff = analyse_type_affectable aff in
        (* Crash si le type de l'expression n'est pas compatible avec celui déclaré *)
        if est_compatible taff te then Affectation (naff, ne)
        else raise (TypeInattendu (te, taff))
    | AstTds.Affichage e -> (
        let ne, te = analyse_type_expression e in
        match te with
        (* résolution de surcharge *)
        | Int -> AstType.AffichageInt ne
        | Rat -> AstType.AffichageRat ne
        | Bool -> AstType.AffichageBool ne
        | _ -> raise (TypeInattendu (te, Bool)))
    | AstTds.Conditionnelle (e, bt, be) ->
        let ne, te = analyse_type_expression e in
        (* Crash si le type de l'expression n'est pas compatible avec un booléen *)
        if not (est_compatible te Bool) then raise (TypeInattendu (te, Bool))
        else
          let nbt = analyse_type_bloc tf bt in
          let nbe = analyse_type_bloc tf be in
          Conditionnelle (ne, nbt, nbe)
    | AstTds.TantQue (e, b) ->
        let ne, te = analyse_type_expression e in
        (* Crash si le type de l'expression n'est pas compatible avec un booléen *)
        if not (est_compatible te Bool) then raise (TypeInattendu (te, Bool))
        else
          let nb = analyse_type_bloc tf b in
          TantQue (ne, nb)
    | AstTds.Retour e -> (
        let ne, te = analyse_type_expression e in
        match tf with
        (* Crash si il y a un retour hors fonction (tf = None) *)
        | None -> raise RetourDansMain
        | Some t ->
            (* Dans le cas contraire, crash si le type de l'expression de retour
               n'est pas compatible avec le type déclaré *)
            if est_compatible t te then Retour ne
            else raise (TypeInattendu (te, t)))
    | AstTds.Empty -> Empty
    | AstTds.AddAff (aff, e) ->
        let ne, te = analyse_type_expression e in
        let naff, taff = analyse_type_affectable aff in
        (* Crash si le type de l'expression n'est pas compatible avec celui déclaré *)
        if est_compatible taff te then
          (* Seuls quelques types peuvent être additionnés *)
          match est_compatible taff with
          | f when f Int -> AddAffEntier (naff, ne)
          | f when f Rat -> AddAffRat (naff, ne)
          | _ -> raise (TypeInattendu (te, taff))
        else raise (TypeInattendu (te, taff))

  (* analyse_type_bloc : typ option -> AstTds.bloc -> AstType.bloc *)
  (* Paramètre tf : type de retour de la fonction le cas échéant *)
  (* Paramètre li : liste d'instructions à analyser *)
  (* Vérifie le bon typage des identifiants et tranforme le bloc
     en un bloc de type AstType.bloc *)
  (* Erreur si mauvais typage des identifiants *)
  and analyse_type_bloc tf li = List.map (analyse_type_instruction tf) li

  (* analyse_type_fonction : AstTds.fonction -> AstType.fonction *)
  (* Paramètre : la fonction à analyser *)
  (* Vérifie le bon typage des identifiants et tranforme la fonction
     en une fonction de type AstType.fonction *)
  (* Erreur si mauvais typage des identifiants *)
  let analyse_type_fonction (AstTds.Fonction (t, ia, lp, li)) =
    (* On enregistre le type attendu des paramètres *)
    let _ = List.map (fun (t, ia) -> analyse_type_declaration t ia) lp in
    (* type des paramètes *)
    let ltp = List.map fst lp in
    (* info_ast des paramètres *)
    let liap = List.map snd lp in
    (* On enregistre le type de retour dans l'info de la fonction *)
    modifier_type_fonction_info t ltp ia;
    (* On analyse le bloc de la fonction en précisant le type de retour attendu *)
    let nli = analyse_type_bloc (Some t) li in
    Fonction (ia, liap, nli)

  (* analyser : AstTds.Programme -> AstType.Programme *)
  (* Paramètre : le programme à analyser *)
  (* Vérifie le bon typage des identifiants et tranforme le programme
     en un programme de type AstType.Programme *)
  (* Erreur si mauvais typage des identifiants *)
  let analyser (AstTds.Programme (fonctions, prog)) =
    (* Analyse des fonction *)
    let nf = List.map analyse_type_fonction fonctions in
    (* Analyse du bloc principal, aucun type de retour attendu *)
    let nb = analyse_type_bloc None prog in
    Programme (nf, nb)
end
