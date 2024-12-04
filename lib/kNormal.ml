open Syntax
open Format

exception KNormal_error of string
exception KNormal_bug of string

let subst_type = Typing.subst_type

(* generate variable string for insert_let *)
let counter = ref 0
let genvar x = 
  let v = !counter in
  counter := v + 1;
  Printf.sprintf "%s.%d" x !counter

module CC = struct
  open Syntax.CC

  (* alpha : 変数の名前が被らないように付け替える *)
  let rec alpha_exp idenv = function
    | Var (r, x, tas) -> Var (r, Environment.find x idenv, tas)
    | IConst _ | BConst _ | UConst _ as f -> f
    | BinOp (r, op, f1, f2) -> BinOp (r, op, alpha_exp idenv f1, alpha_exp idenv f2)
    | IfExp (r, f1, f2, f3) ->
      IfExp (r, alpha_exp idenv f1, alpha_exp idenv f2, alpha_exp idenv f3)
    | FunExp (r, x, u, f) -> 
      let newx = genvar x in
      FunExp (r, newx, u, alpha_exp (Environment.add x newx idenv) f)
    | FixExp _ -> raise @@ KNormal_error "FixExp should not be alpha_exp's argument"
    | AppExp (r, f1, f2) -> AppExp (r, alpha_exp idenv f1, alpha_exp idenv f2)
    | CastExp (r, f1, u1, u2, p) ->
      CastExp (r, alpha_exp idenv f1, u1, u2, p)
    | LetExp (r, x, tvs, FixExp (r', x', y, u1, u2, f1), f2) -> 
      assert (x = x');
      let newx = genvar x in
      let idenv = Environment.add x newx idenv in
      let newy = genvar y in
      LetExp (r, newx, tvs, FixExp (r', newx, newy, u1, u2, alpha_exp (Environment.add y newy idenv) f1), alpha_exp idenv f2)
    | LetExp (r, x, tvs, f1, f2) -> 
      let newx = genvar x in
      LetExp (r, newx, tvs, alpha_exp idenv f1, alpha_exp (Environment.add x newx idenv) f2)

  let alpha_program idenv = function
    | Exp f -> Exp (alpha_exp idenv f), idenv
    | LetDecl (x, tvs, FixExp (r', x', y, u1, u2, f)) ->
      assert (x = x');
      let newx = genvar x in
      let idenv = Environment.add x newx idenv in
      let newy = genvar y in
      LetDecl (newx, tvs, FixExp (r', newx, newy, u1, u2, alpha_exp (Environment.add y newy idenv) f)), idenv
    | LetDecl (x, tvs, f) -> 
      let newx = genvar x in
      LetDecl (newx, tvs, alpha_exp idenv f), Environment.add x newx idenv

  let insert_let (f, u) (k: id -> KNorm.exp * ty) = match f with
    | KNorm.Var x -> k x
    | _ as f -> 
      let x = genvar "_var" in
      let f', u' = k x in (* Var以外に自由な型変数への代入などは存在しないので、ここは[]で大丈夫 *)
      KNorm.LetExp (x, u, f, f'), u' (* todo:考える。とりあえず[] *)
      (*多分大丈夫、applicationにしか不要で、(fun x...) vなら既に代入済み、(fun (x:?)...) vならcast済み*)

  let rec k_normalize_exp tyenv = function
    | Var (_, x, tas) -> 
      let TyScheme (tvs, u) = Environment.find x tyenv in 
      let us = List.map (function Ty u -> u | TyNu -> TyDyn) tas in
      let s = Utils.List.zip tvs us in
      let u = subst_type s u in
      if List.length tas = 0 && List.length tvs = 0 then KNorm.Var x, u
      else if List.length tas = List.length tvs then KNorm.AppTy (x, tvs, tas), u
      else raise @@ KNormal_bug "tas and tvs don't have same length"
    | IConst (_, i) -> KNorm.IConst i, TyInt
    | BConst (_, b) -> let i = if b then 1 else 0 in KNorm.IConst i, TyBool
    | UConst _ -> KNorm.UConst, TyUnit
    | BinOp (r, op, f1, f2) as f -> begin match op with
      | Plus -> 
        let _, _, ui = Typing.type_of_binop op in
        let fu1 = k_normalize_exp tyenv f1 in
        let fu2 = k_normalize_exp tyenv f2 in
        insert_let fu1 (fun x -> (insert_let fu2 (fun y -> KNorm.Add (x, y), ui)))
      | Minus ->
        let _, _, ui = Typing.type_of_binop op in
        let fu1 = k_normalize_exp tyenv f1 in
        let fu2 = k_normalize_exp tyenv f2 in
        insert_let fu1 (fun x -> (insert_let fu2 (fun y -> KNorm.Sub (x, y), ui))) 
      | Mult -> 
        let _, _, ui = Typing.type_of_binop op in
        let fu1 = k_normalize_exp tyenv f1 in
        let fu2 = k_normalize_exp tyenv f2 in
        insert_let fu1 (fun x -> (insert_let fu2 (fun y -> KNorm.Mul (x, y), ui)))
      | Div -> 
        let _, _, ui = Typing.type_of_binop op in
        let fu1 = k_normalize_exp tyenv f1 in
        let fu2 = k_normalize_exp tyenv f2 in
        insert_let fu1 (fun x -> (insert_let fu2 (fun y -> KNorm.Div (x, y), ui)))
      | Mod -> 
        let _, _, ui = Typing.type_of_binop op in
        let fu1 = k_normalize_exp tyenv f1 in
        let fu2 = k_normalize_exp tyenv f2 in
        insert_let fu1 (fun x -> (insert_let fu2 (fun y -> KNorm.Mod (x, y), ui)))
      | _ -> k_normalize_exp tyenv (IfExp (r, f, BConst (r, true), BConst (r, false)))
      end
    | IfExp (_, f1, f2, f3) ->
      let fu11, fu12, op_b, ord_b = cond_if tyenv f1 in
      let f2', u2 = k_normalize_exp tyenv f2 in
      let f3', u3 = k_normalize_exp tyenv f3 in
      let former, later = if ord_b then f2', f3' else f3', f2' in
      let u = Typing.meet u2 u3 in
      if op_b then insert_let fu11 (fun x -> (insert_let fu12 (fun y -> KNorm.IfEqExp (x, y, former, later), u)))
      else insert_let fu11 (fun x -> (insert_let fu12 (fun y -> KNorm.IfLteExp (x, y, former, later), u)))
    | FunExp (_, x, u, f) -> 
      let tent_var = genvar "_var" in
      let f, u' = k_normalize_exp (Environment.add x (TyScheme ([], u)) tyenv) f in
      KNorm.LetRecExp (tent_var, TyFun (u, u'), (x, u), f, KNorm.Var tent_var), TyFun (u, u')
    | FixExp _ -> raise @@ KNormal_bug "FixExp should appear in let"
    | AppExp (_, f1, f2) ->
      let _, u1 as fu1 = k_normalize_exp tyenv f1 in 
      let fu2 = k_normalize_exp tyenv f2 in
      begin match u1 with
        | TyFun (_, u12) -> 
          insert_let fu1 (fun x -> (insert_let fu2 (fun y -> KNorm.AppExp (x, y), u12)))
        | _ -> raise @@ KNormal_bug "app: not fun application"
      end
    | CastExp (r, f, u1, u2, p) ->
      let fu = k_normalize_exp tyenv f in
      insert_let fu (fun x -> KNorm.CastExp (r, x, u1, u2, p), u2)
    | LetExp (_, x, tvs, f1, f2) -> 
      begin match f1 with
        | FunExp (_, x', u, f1) ->
          let f1, u1 = k_normalize_exp (Environment.add x' (TyScheme ([], u)) tyenv) f1 in
          let f2, u2 = k_normalize_exp (Environment.add x (TyScheme (tvs, TyFun (u, u1))) tyenv) f2 in
          KNorm.LetRecExp (x, TyFun (u, u1), (x', u), f1, f2), u2
        | FixExp (_, x', y, u, u', f1) ->
          assert (x' = x);
          let f1, u1 = k_normalize_exp (Environment.add y (TyScheme ([], u)) (Environment.add x' (TyScheme ([], TyFun (u, u'))) tyenv)) f1 in
          let f2, u2 = k_normalize_exp (Environment.add x (TyScheme (tvs, TyFun (u, u1))) tyenv) f2 in
          KNorm.LetRecExp (x, TyFun (u, u1), (y, u'), f1, f2), u2
        | _ as f ->
          let f1, u1 = k_normalize_exp tyenv f in
          let f2, u2 = k_normalize_exp (Environment.add x (TyScheme (tvs, u1)) tyenv) f2 in
          KNorm.LetExp (x, u1, f1, f2), u2
      end
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
    | Var _ | BConst _ | IfExp _ | AppExp _ | LetExp _ | CastExp _ as f ->
      let fu = k_normalize_exp tyenv f in 
      fu, (KNorm.IConst 1, TyBool), true, true
    | IConst _ | UConst _ | FunExp _ | FixExp _ -> raise @@ KNormal_bug "if-cond type should bool"

  let k_normalize_program ktyenv = function
    | Exp f -> let f, u = k_normalize_exp ktyenv f in KNorm.Exp f, u, ktyenv
    | LetDecl (x, tvs, f) -> 
      begin match f with
        | FunExp (_, x', u, f) ->
          let f, u' = k_normalize_exp (Environment.add x' (TyScheme ([], u)) ktyenv) f in
          KNorm.LetRecDecl (x, TyFun (u, u'), (x', u), f), TyFun (u, u'), Environment.add x (TyScheme (tvs, TyFun (u, u'))) ktyenv
        | FixExp (_, x', y, u, u', f) ->
          assert (x' = x);
          let f, u'' = k_normalize_exp (Environment.add y (TyScheme ([], u')) (Environment.add x' (TyScheme ([], TyFun (u, u'))) ktyenv)) f in
          KNorm.LetRecDecl (x, TyFun (u, u''), (y, u'), f), TyFun (u, u''), Environment.add x (TyScheme (tvs, TyFun (u, u'))) ktyenv
        | _ as f ->
          let f, u = k_normalize_exp ktyenv f in KNorm.LetDecl (x, u, f), u, Environment.add x (TyScheme (tvs, u)) ktyenv
      end
end

module KNorm = struct
  open Syntax.KNorm

  let find x idenv = try Environment.find x idenv with Not_found -> x

  (* beta : let x = y in ... となっているようなxをyに置き換える *)
  let rec beta_exp idenv = function
    | Var x -> Var (find x idenv)
    | IConst _ | UConst as f -> f
    | Add (x, y) -> Add (find x idenv, find y idenv)
    | Sub (x, y) -> Sub (find x idenv, find y idenv)
    | Mul (x, y) -> Mul (find x idenv, find y idenv)
    | Div (x, y) -> Div (find x idenv, find y idenv)
    | Mod (x, y) -> Mod (find x idenv, find y idenv)
    | IfEqExp (x, y, f1, f2) ->
      IfEqExp (find x idenv, find y idenv, beta_exp idenv f1, beta_exp idenv f2)
    | IfLteExp (x, y, f1, f2) ->
      IfLteExp (find x idenv, find y idenv, beta_exp idenv f1, beta_exp idenv f2)
    | AppExp (x, y) -> AppExp (find x idenv, find y idenv)
    | AppTy (x, tvs, tas) -> AppTy (find x idenv, tvs, tas)
    | CastExp (r, x, u1, u2, p) -> CastExp (r, find x idenv, u1, u2, p)
    | LetExp (x, u, f1, f2) ->
      let f1 = beta_exp idenv f1 in
      begin match f1 with
        | Var x' -> beta_exp (Environment.add x x' idenv) f2
        | f1 -> LetExp (x, u, f1, beta_exp idenv f2)
      end
    | LetRecExp (x, u, arg, f1, f2) ->
      LetRecExp (x, u, arg, beta_exp idenv f1, beta_exp idenv f2)

  let beta_program idenv = function
    | Exp f -> Exp (beta_exp idenv f), idenv
    | LetDecl (x, u, f) ->
      let f = beta_exp idenv f in
      begin match f with
      | Var x' as f -> Exp f, Environment.add x x' idenv
      | f -> LetDecl (x, u, f), idenv
      end
    | LetRecDecl (x, u, arg, f) ->
      LetRecDecl (x, u, arg, beta_exp idenv f), idenv

  (* assoc : let x = (let y = ... in ... ) in ...というようなネストされたletをlet y = ... in let x = ... in ...という形に平たくする *)
  let rec assoc_exp = function
    | IfEqExp (x, y, f1, f2) -> IfEqExp (x, y, assoc_exp f1, assoc_exp f2)
    | IfLteExp (x, y, f1, f2) -> IfLteExp (x, y, assoc_exp f1, assoc_exp f2)
    (*| CastExp (r, f, u1, u2, p) -> CastExp (r, assoc_exp f, u1, u2, p)*)
    | LetExp (x, u, f1, f2) ->
      let rec insert = function
        | LetExp (x', u', f3, f4) -> LetExp (x', u', f3, insert f4)
        | LetRecExp (x', u', arg, f3, f4) -> LetRecExp (x', u', arg, f3, insert f4)
        | f1 -> LetExp (x, u, f1, assoc_exp f2)
      in insert (assoc_exp f1)
    | LetRecExp (x, u, arg, f1, f2) ->
      LetRecExp (x, u, arg, assoc_exp f1, assoc_exp f2)
    | f -> f
  
  let assoc_program = function
    | Exp f -> Exp (assoc_exp f)
    | LetDecl (x, u, f) -> LetDecl (x, u, assoc_exp f)
    | LetRecDecl (x, u, arg, f) -> LetRecDecl (x, u, arg, assoc_exp f)
end

let kNorm_funs ?(debug=false) (ktyenv, alphaenv, betaenv) f = 
  let f, alphaenv = CC.alpha_program alphaenv f in
  if debug then fprintf err_formatter "alpha: %a\n" Pp.CC.pp_program f;
  let f, u, ktyenv = CC.k_normalize_program ktyenv f in
  if debug then fprintf err_formatter "k_normalize: %a\n" Pp.KNorm.pp_program f;
  let f, betaenv = KNorm.beta_program betaenv f in
  if debug then fprintf err_formatter "beta: %a\n" Pp.KNorm.pp_program f;
  let f = KNorm.assoc_program f in
  if debug then fprintf err_formatter "assoc: %a\n" Pp.KNorm.pp_program f;
  f, u, (ktyenv, alphaenv, betaenv)