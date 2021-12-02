module PassePlacementRat :
  Passe.Passe
    with type t1 = Ast.AstType.programme
     and type t2 = Ast.AstPlacement.programme = struct
  open Tds
  open Exceptions
  open Ast
  open AstPlacement
  open Type

  type t1 = Ast.AstType.programme

  type t2 = Ast.AstPlacement.programme

  let rec analyse_placement_instruction reg dep i =
    let inc =
      match i with
      | AstType.Declaration (ia, _) ->
          modifier_adresse_info dep reg ia;
          getTaille (get_type ia)
      | AstType.Conditionnelle (_, bt, be) ->
          analyse_placement_bloc reg dep bt;
          analyse_placement_bloc reg dep be;
          0
      | AstType.TantQue (_, b) ->
          analyse_placement_bloc reg dep b;
          0
      | _ -> 0
    in
    dep + inc

  and analyse_placement_bloc reg dep li =
    match li with
    | [] -> ()
    | i :: q ->
        let ndep = analyse_placement_instruction reg dep i in
        analyse_placement_bloc reg ndep q

  let rec analyse_placement_fonction (AstType.Fonction (ia, liap, li)) =
    analyse_placement_params 0 (List.rev liap);
    analyse_placement_bloc "LB" 3 li;
    Fonction (ia, liap, li)

  and analyse_placement_params dep lp =
    match lp with
    | [] -> ()
    | ia :: q ->
        let t = getTaille (get_type ia) in
        modifier_adresse_info (dep - t) "LB" ia;
        analyse_placement_params (dep - t) q

  let analyser (AstType.Programme (fonctions, prog)) =
    let nf = List.map analyse_placement_fonction fonctions in
    analyse_placement_bloc "SB" 0 prog;
    Programme (nf, prog)
end
