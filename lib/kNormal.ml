open Syntax

exception KNormal_error of string
exception KNormal_bug of string

let subst_type = Typing.subst_type

module CC = struct
  open Syntax.CC

  (* generate variable string for insert_let *)
  let genvar = 
    let counter = ref 0 in
    let body () =
      let v = !counter in
      counter := v + 1;
      Printf.sprintf "_var%d" !counter
    in body

  let insert_let (f, _) (k: KNorm.k_id -> KNorm.exp * ty) = match f with
    | KNorm.Var (_, x) -> k x
    | _ as f -> 
      let x = genvar () in
      let f', u' = k (x, []) in (* Var以外に自由な型変数への代入などは存在しないので、ここは[]で大丈夫 *)
      let r = KNorm.range_of_exp f' in
      KNorm.LetExp (r, x, [], f, f'), u' (* todo:考える。とりあえず[] *)
      (*多分大丈夫、applicationにしか不要で、(fun x...) vなら既に代入済み、(fun (x:?)...) vならcast済み*)

  let rec k_normalize_exp tyenv = function
    | Var (r, x, tas) -> 
      let TyScheme (tvs, u) = Environment.find x tyenv in 
      let us = List.map (function Ty u -> u | TyNu -> TyDyn) tas in
      let s = Utils.List.zip tvs us in
      let u = subst_type s u in
      KNorm.Var (r, (x, tas)), u
    | IConst (r, i) -> KNorm.IConst (r, i), TyInt
    | BConst (r, b) -> KNorm.BConst (r, b), TyBool
    | UConst r -> KNorm.UConst r, TyUnit
    | BinOp (r, op, f1, f2) -> 
      let _, _, ui = Typing.type_of_binop op in
      let fu1 = k_normalize_exp tyenv f1 in
      let fu2 = k_normalize_exp tyenv f2 in
      insert_let fu1 (fun x -> (insert_let fu2 (fun y -> KNorm.BinOp (r, op, x, y), ui)))
    | IfExp (r, f1, f2, f3) ->
      let fu11, fu12, op_b, ord_b = cond_if tyenv f1 in
      let f2', u2 = k_normalize_exp tyenv f2 in
      let f3', u3 = k_normalize_exp tyenv f3 in
      let former, later = if ord_b then f2', f3' else f3', f2' in
      let u = Typing.meet u2 u3 in
      if op_b then insert_let fu11 (fun x -> (insert_let fu12 (fun y -> KNorm.IfEqExp (r, x, y, former, later), u)))
      else insert_let fu11 (fun x -> (insert_let fu12 (fun y -> KNorm.IfLteExp (r, x, y, former, later), u)))
    | FunExp (r, x, u, f) -> 
      let f', u' = k_normalize_exp (Environment.add x (TyScheme ([], u)) tyenv) f in
      KNorm.FunExp (r, x, u, f'), TyFun (u, u')
    | FixExp (r, x, y, u1, u2, f) ->
      let f', u' = k_normalize_exp (Environment.add y (TyScheme ([], u1)) (Environment.add x (TyScheme ([], TyFun (u1, u2))) tyenv)) f in
      KNorm.FixExp (r, x, y, u1, u2, f'), TyFun (u1, u')
    | AppExp (r, f1, f2) ->
      let _, u1 as fu1 = k_normalize_exp tyenv f1 in 
      let fu2 = k_normalize_exp tyenv f2 in
      begin match u1 with
        | TyFun (_, u12) -> 
          insert_let fu1 (fun x -> (insert_let fu2 (fun y -> KNorm.AppExp (r, x, y), u12)))
        | _ -> raise @@ KNormal_bug "app: not fun application"
      end
    | CastExp (r, f, u1, u2, p) ->
      let f, _ = k_normalize_exp tyenv f in
      KNorm.CastExp (r, f, u1, u2, p), u2
    | LetExp (r, x, tvs, f1, f2) -> 
      let f1', u1 = k_normalize_exp tyenv f1 in
      let f2', u2 = k_normalize_exp (Environment.add x (TyScheme (tvs, u1)) tyenv) f2 in
      KNorm.LetExp (r, x, tvs, f1', f2'), u2
  and cond_if tyenv = function
    | BinOp (r, op, f1, f2) -> 
      let fu1 = k_normalize_exp tyenv f1 in
      let fu2 = k_normalize_exp tyenv f2 in
      begin match op with
        | Eq -> fu1, fu2, true, true
        | Neq -> fu1, fu2, true, false
        | Lt -> cond_if tyenv (IfExp (r, BinOp (r, Lte, f1, f2), IfExp (r, BinOp (r, Eq, f1, f2), BConst (r, false), BConst (r, true)), BConst (r, false)))
        | Lte -> fu1, fu2, false, true
        | Gt -> fu1, fu2, false, false
        | Gte -> cond_if tyenv (IfExp (r, BinOp (r, Lte, f1, f2), IfExp (r, BinOp (r, Eq, f1, f2), BConst (r, true), BConst (r, false)), BConst (r, true)))
        | _ -> raise @@ KNormal_bug "if-cond type should bool"
      end
    | Var (r, _, _) | BConst (r, _) | IfExp (r, _, _, _) | AppExp (r, _, _) | LetExp (r, _, _, _, _) | CastExp (r, _, _, _, _) as f ->
      let fu = k_normalize_exp tyenv f in 
      fu, (KNorm.BConst (r, true), TyBool), true, true
    | IConst _ | UConst _ | FunExp _ | FixExp _ -> raise @@ KNormal_bug "if-cond type should bool"

  let k_normalize_program tyenv = function
    | Exp f -> let f, u = k_normalize_exp tyenv f in KNorm.Exp f, u
    | LetDecl (x, tvs, f) -> let f, u = k_normalize_exp tyenv f in KNorm.LetDecl (x, tvs, f), u
end