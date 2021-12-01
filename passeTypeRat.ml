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

  (* AstTds.expression -> (AstType.Expression * typ) = <fun> *)
  let rec analyse_type_expression expr =
    match expr with
    | AstTds.AppelFonction (ia, le) ->
        let nlet = List.map analyse_type_expression le in
        let tr = get_type_retour ia in
        let tpara = get_types_params ia in
        let nle = List.map fst nlet in
        let nlt = List.map snd nlet in
        if tpara = nlt then (AppelFonction (ia, nle), tr)
        else raise (TypesParametresInattendus (nlt, tpara))
    | AstTds.Ident info -> (Ident info, get_type info)
    | AstTds.Booleen b -> (Booleen b, Bool)
    | AstTds.Entier i -> (Entier i, Int)
    | AstTds.Unaire (u, e) ->
        let n_unaire =
          match u with
          | AstSyntax.Numerateur -> Numerateur
          | AstSyntax.Denominateur -> Denominateur
        in
        let ne, te = analyse_type_expression e in
        if te = Rat then (Unaire (n_unaire, ne), Int)
        else raise (TypeInattendu (te, Rat))
    | AstTds.Binaire (f, e1, e2) ->
        let ne1, te1 = analyse_type_expression e1 in
        let ne2, te2 = analyse_type_expression e2 in
        let n_binaire, tr =
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

  let rec analyse_type_instruction tf i =
    match i with
    | AstTds.Declaration (t, ia, e) ->
        modifier_type_info t ia;
        let ne, te = analyse_type_expression e in
        if t = te then Declaration (ia, ne) else raise (TypeInattendu (te, t))
    | AstTds.Affectation (ia, e) ->
        let ne, te = analyse_type_expression e in
        let t = get_type ia in
        if t = te then Affectation (ia, ne) else raise (TypeInattendu (te, t))
    | AstTds.Affichage e -> (
        let ne, te = analyse_type_expression e in
        match te with
        | Int -> AstType.AffichageInt ne
        | Rat -> AstType.AffichageRat ne
        | Bool -> AstType.AffichageBool ne
        | _ -> raise (TypeInattendu (te, Bool)))
    | AstTds.Conditionnelle (e, bt, be) ->
        let ne, te = analyse_type_expression e in
        if te != Bool then raise (TypeInattendu (te, Bool))
        else
          let nbt = analyse_type_bloc tf bt in
          let nbe = analyse_type_bloc tf be in
          Conditionnelle (ne, nbt, nbe)
    | AstTds.TantQue (e, b) ->
        let ne, te = analyse_type_expression e in
        if te != Bool then raise (TypeInattendu (te, Bool))
        else
          let nb = analyse_type_bloc tf b in
          TantQue (ne, nb)
    | AstTds.Retour e -> (
        let ne, te = analyse_type_expression e in
        match tf with
        | None -> raise RetourDansMain
        | Some t -> if t = te then Retour ne else raise (TypeInattendu (te, t)))
    | AstTds.Empty -> Empty

  and analyse_type_bloc tf li = List.map (analyse_type_instruction tf) li

  let analyse_type_fonction (AstTds.Fonction (t, ia, lp, li)) =
    let _ = List.map (fun (t, ia) -> modifier_type_info t ia) lp in
    let ltp = List.map fst lp in
    let liap = List.map snd lp in
    modifier_type_fonction_info t ltp ia;
    let nli = analyse_type_bloc (Some t) li in
    Fonction (ia, liap, nli)

  let analyser (AstTds.Programme (fonctions, prog)) =
    let nf = List.map analyse_type_fonction fonctions in
    let nb = analyse_type_bloc None prog in
    Programme (nf, nb)
end
