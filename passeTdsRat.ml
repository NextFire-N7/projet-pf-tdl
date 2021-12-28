(* Module de la passe de gestion des identifiants *)
module PasseTdsRat :
  Passe.Passe
    with type t1 = Ast.AstSyntax.programme
     and type t2 = Ast.AstTds.programme = struct
  open Tds
  open Exceptions
  open Ast
  open AstTds
  open Type

  type t1 = Ast.AstSyntax.programme
  type t2 = Ast.AstTds.programme

  let analyse_tds_affectable tds modif a =
    let analyse_tds_affectable_acces (n, ia) c =
      match info_ast_to_info ia with
      | InfoStruct (_, _, _, _, lc) -> (
          let iopt =
            List.find_opt
              (fun i ->
                match info_ast_to_info i with
                | InfoVar (n, _, _, _) | InfoStruct (n, _, _, _, _) -> n = c
                | _ -> failwith "hmm")
              lc
          in
          match iopt with
          | Some iaa -> Acces (Ident ia, iaa)
          | None -> raise (MauvaiseUtilisationIdentifiant n))
      | _ -> raise (MauvaiseUtilisationIdentifiant n)
    in
    let rec analyse_tds_affectable_int tds modif a c =
      match a with
      | AstSyntax.Deref a -> Deref (analyse_tds_affectable_int tds modif a c)
      | AstSyntax.Ident n -> (
          match chercherGlobalement tds n with
          | None -> raise (IdentifiantNonDeclare n)
          | Some ia -> (
              match c with
              | Some c -> analyse_tds_affectable_acces (n, ia) c
              | None -> (
                  match info_ast_to_info ia with
                  | InfoVar _ | InfoStruct _ -> Ident ia
                  | InfoConst _ ->
                      if modif then raise (MauvaiseUtilisationIdentifiant n)
                      else Ident ia
                  | _ -> raise (MauvaiseUtilisationIdentifiant n))))
      | AstSyntax.Acces (a, c) ->
          analyse_tds_affectable_int tds modif a (Some c)
    in
    analyse_tds_affectable_int tds modif a None

  let rec analyse_tds_type tds lstr t =
    match t with
    | Pointeur t ->
        let t, nlstr = analyse_tds_type tds lstr t in
        (Pointeur t, nlstr)
    | NamedTyp n -> (
        match chercherGlobalement tds n with
        | None -> raise (TypeNonDeclare n)
        | Some ia -> (
            match info_ast_to_info ia with
            | InfoTyp (_, t) -> analyse_tds_type tds lstr t
            | _ -> raise (MauvaiseUtilisationIdentifiant n)))
    | Struct lc ->
        (* Analyse des champs de la structure *)
        let nlc, nlstr =
          List.fold_left
            (fun (lc, lstr) (t, c) ->
              let nt, nlstr = analyse_tds_type tds lstr t in
              ((nt, c) :: lc, nlstr))
            ([], lstr) lc
        in
        (* On remet la struct dans le bon sens *)
        let nlc = List.rev nlc in
        (* Analyse de la structure *)
        let nnlstr = analyse_tds_struct nlstr nlc in
        (Struct nlc, nnlstr)
    | _ -> (t, lstr)

  and analyse_tds_struct lstr lc =
    (* Obtenir toutes les structures déjà définies qui ont
       un champ en commun avec la nouvelle structure à analyser *)
    let matching =
      List.filter
        (List.exists (fun n -> List.exists (fun (_, c) -> n = c) lc))
        lstr
    in
    match matching with
    (* Aucun résultat: aucune structure jusqu'à présent n'a utilisé
       un nom de champ présent dans la nouvelle structure => valide *)
    | [] ->
        let nstruct =
          List.fold_left
            (fun lc (_, c) ->
              (* vérif qu'il n'y a pas deux champs avec le même nom *)
              if List.exists (fun n -> n = c) lc then
                raise (DoubleDeclaration c)
              else c :: lc)
            [] lc
        in
        (* on remet la struct dans le bon sens *)
        let nstruct = List.rev nstruct in
        nstruct :: lstr
    (* Dans le cas contraire on regarde si la nouvelle structure est identique à l'une déjà déclarée *)
    | _ -> (
        (* On enlève celles qui ont un nombre de champs différent (donc forcément pas identiques) *)
        let meme_taille =
          List.filter (fun str -> List.length str = List.length lc) matching
        in
        (* et on essaie de trouver celle identique, ordre compris *)
        let struct_opt =
          List.find_opt
            (List.for_all2 (fun (_, c1) c2 -> c1 = c2) lc)
            meme_taille
        in
        match struct_opt with
        | Some _ -> lstr
        | None -> raise (DoubleDeclaration "todo"))

  (* analyse_tds_expression : AstSyntax.expression -> AstTds.expression *)
  (* Paramètre tds : la table des symboles courante *)
  (* Paramètre e : l'expression à analyser *)
  (* Vérifie la bonne utilisation des identifiants et tranforme l'expression
     en une expression de type AstTds.expression *)
  (* Erreur si mauvaise utilisation des identifiants *)
  let rec analyse_tds_expression tds e =
    match e with
    | AstSyntax.AppelFonction (name, el) -> (
        (* On cherche si la fonction est déjà définie *)
        match chercherGlobalement tds name with
        (* Ah ben non elle est pas def *)
        | None -> raise (IdentifiantNonDeclare name)
        | Some ia -> (
            (* Qqch porte bien ce nom, est-ce une fonction ? *)
            match info_ast_to_info ia with
            | InfoFun _ ->
                AppelFonction (ia, List.map (analyse_tds_expression tds) el)
            | _ -> raise (MauvaiseUtilisationIdentifiant name)))
    | AstSyntax.Affectable affectable ->
        Affectable (analyse_tds_affectable tds false affectable)
    | AstSyntax.Booleen value -> Booleen value
    | AstSyntax.Entier value -> Entier value
    | AstSyntax.Unaire (op, exp) -> Unaire (op, analyse_tds_expression tds exp)
    | AstSyntax.Binaire (op, exp1, exp2) ->
        Binaire
          (op, analyse_tds_expression tds exp1, analyse_tds_expression tds exp2)
    (* Pointeurs *)
    | AstSyntax.Null -> Null
    | AstSyntax.Adresse name -> (
        (* On cherche si la fonction est déjà définie *)
        match chercherGlobalement tds name with
        (* Ah ben non elle est pas def *)
        | None -> raise (IdentifiantNonDeclare name)
        | Some ia -> (
            (* Qqch porte bien ce nom, est-ce une fonction ? *)
            match info_ast_to_info ia with
            | InfoVar _ | InfoStruct _ -> Adresse ia
            | _ -> raise (MauvaiseUtilisationIdentifiant name)))
    | AstSyntax.New typ -> New typ
    | AstSyntax.StructExpr le ->
        StructExpr (List.map (analyse_tds_expression tds) le)

  let rec creer_info_ast t n =
    let info =
      match t with
      | Struct lc ->
          InfoStruct
            (n, Undefined, 0, "", List.map (fun (t, c) -> creer_info_ast t c) lc)
      | _ -> InfoVar (n, Undefined, 0, "")
    in
    info_to_info_ast info

  (* analyse_tds_instruction : AstSyntax.instruction -> tds -> AstTds.instruction *)
  (* Paramètre tds : la table des symboles courante *)
  (* Paramètre i : l'instruction à analyser *)
  (* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
     en une instruction de type AstTds.instruction *)
  (* Erreur si mauvaise utilisation des identifiants *)
  let rec analyse_tds_instruction tds lstr i =
    match i with
    | AstSyntax.Declaration (t, n, e) -> (
        if List.exists (List.mem n) lstr then raise (DoubleDeclaration n)
        else
          match chercherLocalement tds n with
          | None ->
              (* L'identifiant n'est pas trouvé dans la tds locale,
                 il n'a donc pas été déclaré dans le bloc courant *)
              (* Analyse du type *)
              let nt, nlstr = analyse_tds_type tds lstr t in
              (* Vérification de la bonne utilisation des identifiants dans l'expression *)
              (* et obtention de l'expression transformée *)
              let ne = analyse_tds_expression tds e in
              (* Création de l'information associée à l'identfiant *)
              (* Création du pointeur sur l'information *)
              let ia = creer_info_ast nt n in
              (* Ajout de l'information (pointeur) dans la tds *)
              ajouter tds n ia;
              (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information
                 et l'expression remplacée par l'expression issue de l'analyse *)
              (Declaration (nt, ia, ne), nlstr)
          | Some _ ->
              (* L'identifiant est trouvé dans la tds locale,
                 il a donc déjà été déclaré dans le bloc courant *)
              raise (DoubleDeclaration n))
    | AstSyntax.Affectation (aff, e) ->
        let naff = analyse_tds_affectable tds true aff in
        let ne = analyse_tds_expression tds e in
        (Affectation (naff, ne), lstr)
    | AstSyntax.Constante (n, v) -> (
        match chercherLocalement tds n with
        | None ->
            (* L'identifiant n'est pas trouvé dans la tds locale,
               il n'a donc pas été déclaré dans le bloc courant *)
            (* Ajout dans la tds de la constante *)
            ajouter tds n (info_to_info_ast (InfoConst (n, v)));
            (* Suppression du noeud de déclaration des constantes devenu inutile *)
            (Empty, lstr)
        | Some _ ->
            (* L'identifiant est trouvé dans la tds locale,
               il a donc déjà été déclaré dans le bloc courant *)
            raise (DoubleDeclaration n))
    | AstSyntax.Affichage e ->
        (* Vérification de la bonne utilisation des identifiants dans l'expression *)
        (* et obtention de l'expression transformée *)
        let ne = analyse_tds_expression tds e in
        (* Renvoie du nouvel affichage où l'expression remplacée par l'expression issue de l'analyse *)
        (Affichage ne, lstr)
    | AstSyntax.Conditionnelle (c, t, e) ->
        (* Analyse de la condition *)
        let nc = analyse_tds_expression tds c in
        (* Analyse du bloc then *)
        let tast, nlstr = analyse_tds_bloc tds lstr t in
        (* Analyse du bloc else *)
        let east, nnlstr = analyse_tds_bloc tds nlstr e in
        (* Renvoie la nouvelle structure de la conditionnelle *)
        (Conditionnelle (nc, tast, east), nnlstr)
    | AstSyntax.TantQue (c, b) ->
        (* Analyse de la condition *)
        let nc = analyse_tds_expression tds c in
        (* Analyse du bloc *)
        let bast, nlstr = analyse_tds_bloc tds lstr b in
        (* Renvoie la nouvelle structure de la boucle *)
        (TantQue (nc, bast), nlstr)
    | AstSyntax.Retour e ->
        (* Analyse de l'expression *)
        let ne = analyse_tds_expression tds e in
        (Retour ne, lstr)
    | AstSyntax.AddAff (aff, exp) ->
        let naff = analyse_tds_affectable tds true aff in
        let ne = analyse_tds_expression tds exp in
        (AddAff (naff, ne), lstr)
    | AstSyntax.TypedefLocal (n, t) -> (
        (* Vérif double déclaration *)
        match chercherLocalement tds n with
        | Some _ -> raise (DoubleDeclaration n)
        | None ->
            (* Enregistrement du type nommé dans la tds *)
            let nt, nlstr = analyse_tds_type tds lstr t in
            let i = InfoTyp (n, nt) in
            let ia = info_to_info_ast i in
            ajouter tds n ia;
            (* Le noeud ne sert plus *)
            (Empty, nlstr))

  (* analyse_tds_bloc : AstSyntax.bloc -> AstTds.bloc *)
  (* Paramètre tds : la table des symboles courante *)
  (* Paramètre li : liste d'instructions à analyser *)
  (* Vérifie la bonne utilisation des identifiants et tranforme le bloc
     en un bloc de type AstTds.bloc *)
  (* Erreur si mauvaise utilisation des identifiants *)
  and analyse_tds_bloc tds lstr li =
    (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale
       pointant sur la table du bloc parent *)
    let tdsbloc = creerTDSFille tds in
    (* Analyse des instructions du bloc avec la tds du nouveau bloc
       Cette tds est modifiée par effet de bord *)
    let nli, nlstr =
      List.fold_left
        (fun (li, lstr) i ->
          let ni, nlstr = analyse_tds_instruction tdsbloc lstr i in
          (ni :: li, nlstr))
        ([], lstr) li
    in
    (* afficher_locale tdsbloc ; *)
    (* décommenter pour afficher la table locale *)
    (* On remet les instructions dans l'ordre *)
    (List.rev nli, nlstr)

  (* analyse_tds_fonction : AstSyntax.fonction -> AstTds.fonction *)
  (* Paramètre tds : la table des symboles courante *)
  (* Paramètre : la fonction à analyser *)
  (* Vérifie la bonne utilisation des identifiants et tranforme la fonction
     en une fonction de type AstTds.fonction *)
  (* Erreur si mauvaise utilisation des identifiants *)
  let analyse_tds_fonction maintds lstr (AstSyntax.Fonction (t, n, lp, li)) =
    match chercherLocalement maintds n with
    | None ->
        (* L'identifiant n'est pas trouvé dans la tds locale,
           il n'a donc pas été déclaré dans le bloc courant *)

        (* Création d'une nouvelle tds pour les paramètres locaux *)
        let tdsparam = creerTDSFille maintds in
        (* Création des informations liés aux paramètres, et ajout dans la tds *)
        let nlp, lstr =
          let nlp_inner_fun (lp, lstr) (t, n) =
            (* analyse du type du paramètre *)
            let nt, nlstr = analyse_tds_type tdsparam lstr t in
            let _ =
              (* On vérifie que la paramètre n'a pas été déclaré précédemment *)
              match chercherLocalement tdsparam n with
              | Some _ -> raise (DoubleDeclaration n)
              | None -> ()
            in
            let ia = creer_info_ast nt n in
            ajouter tdsparam n ia;
            ((nt, ia) :: lp, nlstr)
          in
          List.fold_left nlp_inner_fun ([], lstr) lp
        in
        (* On remet la liste des params dans l'ordre *)
        let nlp = List.rev nlp in
        (* Création de l'information associée à l'identfiant *)
        let info = InfoFun (n, Undefined, List.map fst nlp) in
        (* Création du pointeur sur l'information *)
        let ia = info_to_info_ast info in
        (* Ajout du pointeur dans la TDS (pour la récursivité)*)
        let _ = ajouter maintds n ia in
        (* Vérification de la bonne utilisation des identifiants dans le bloc d'instructions *)
        (* et obtention du bloc transformé *)
        let nli, lstr = analyse_tds_bloc tdsparam lstr li in
        (* Renvoie de la nouvelle fonction où les informations liés
           à la fonction et ses paramètres ont été ajoutés à la tds*)
        (* analyse du type du return *)
        let nt, lstr = analyse_tds_type tdsparam lstr t in
        (Fonction (nt, ia, nlp, nli), lstr)
    | Some _ ->
        (* L'identifiant est trouvé dans la tds locale,
           il a donc déjà été déclaré dans le bloc courant *)
        raise (DoubleDeclaration n)

  (* analyser : AstSyntax.ast -> AstTds.ast *)
  (* Paramètre : le programme à analyser *)
  (* Vérifie la bonne utilisation des identifiants et tranforme le programme
     en un programme de type AstTds.ast *)
  (* Erreur si mauvaise utilisation des identifiants *)
  let analyser (AstSyntax.Programme (typedefs, fonctions, prog)) =
    let tds = creerTDSMere () in
    (* rajout des types nommés en haut de la tds *)
    let lstr =
      List.fold_left
        (fun lstr (AstSyntax.TypedefGlobal (n, t)) ->
          match chercherGlobalement tds n with
          | Some _ -> raise (DoubleDeclaration n)
          | None ->
              (* Résolution du type de base *)
              let nt, nlstr = analyse_tds_type tds lstr t in
              let i = InfoTyp (n, nt) in
              let ia = info_to_info_ast i in
              ajouter tds n ia;
              nlstr)
        [] typedefs
    in
    let nf, nlstr =
      List.fold_left
        (fun (lf, lstr) f ->
          let nf, nlstr = analyse_tds_fonction tds lstr f in
          (nf :: lf, nlstr))
        ([], lstr) fonctions
    in
    (* On remet les fonctions dans l'ordre *)
    let nf = List.rev nf in
    let nb, _ = analyse_tds_bloc tds nlstr prog in
    Programme (nf, nb)
end
