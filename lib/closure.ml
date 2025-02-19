open Syntax

exception Closure_bug of string
exception Closure_error of string

module KNorm = struct
  open Syntax.KNorm

  let toplevel = ref []

  let tvset = ref TV.empty

  let rec exist_tv l1 l2 = match l2 with
    | h :: t -> if List.mem h l1 then true else exist_tv l1 t
    | [] -> false
  
  let rec ty_tv tvs = function
    | TyInt | TyBool | TyUnit | TyDyn | TyFun (TyDyn, TyDyn) as u -> (u, fun x -> x)
    | TyVar tv as u -> if not (List.mem tv tvs) then (tvset := TV.add tv !tvset; (u, fun x -> x)) else (u, fun x -> x)
    | TyFun (u1, u2) ->
      let u1, ufun1 = ty_tv tvs u1 in
      let u2, ufun2 = ty_tv tvs u2 in
      let newu = Typing.fresh_tyvar () in
      let newtv = begin match newu with
        | TyVar (i, u) -> u := Some (TyFun (u1, u2)); (i, u)
        | _ -> raise @@ Closure_bug "not tyvar was created"
      end in if not (exist_tv (TV.elements (Syntax.ftv_ty u1)) tvs) && not (exist_tv (TV.elements (Syntax.ftv_ty u2)) tvs) then 
        (tvset := TV.add newtv !tvset; (newu, fun x -> ufun1 (ufun2 x)))
      else (newu, fun x -> ufun1 (ufun2 (Cls.SetTy (newtv, x))))

  let ta_tv tvs = function
    | Ty u -> let (u, f) = ty_tv tvs u in (Ty u, f)
    | TyNu -> (TyNu, fun x -> x)

  let tyvar_to_tyarg tvs = 
    let rec ttt l r = match l with
    | tv :: t -> ttt t ((Ty (TyVar tv)) :: r)
    | [] -> r
  in ttt (List.rev tvs) []

  let rec toCls_exp tyenv known tvs = function
    | Var x -> Cls.Var x
    | IConst i -> Cls.Int i
    | UConst -> Cls.Unit
    | Add (x, y) -> Cls.Add (x, y)
    | Sub (x, y) -> Cls.Sub (x, y)
    | Mul (x, y) -> Cls.Mul (x, y)
    | Div (x, y) -> Cls.Div (x, y)
    | Mod (x, y) -> Cls.Mod (x, y)
    | IfEqExp (x, y, f1, f2) -> Cls.IfEq (x, y, toCls_exp tyenv known tvs f1, toCls_exp tyenv known tvs f2)
    | IfLteExp (x, y, f1, f2) -> Cls.IfLte (x, y, toCls_exp tyenv known tvs f1, toCls_exp tyenv known tvs f2)
    | AppExp (x, y) when Cls.V.mem x known -> Cls.AppDir (Cls.to_label x, y)
    | AppExp (x, y) -> Cls.AppCls (x, y)
    | AppTy (x, _, tas) -> 
      let uandf = List.map (ta_tv tvs) tas in
      let rec destruct_uandf l ru rf = match l with
        | (u, f) :: t -> destruct_uandf t (u::ru) (fun x -> rf (f x))
        | [] -> ru, rf 
      in let us, f = destruct_uandf (List.rev uandf) [] (fun x -> x) in
      f (Cls.AppTy (x, List.length tas + List.length tvs, us))
    | CastExp (r, x, u1, u2, p) -> 
      let u1, udeclfun1 = ty_tv tvs u1 in 
      let u2, udeclfun2 = ty_tv tvs u2 in 
      udeclfun1 (udeclfun2 (Cls.Cast (x, u1, u2, r, p)))
    | LetExp (x, u, f1, f2) -> 
      let f1 = toCls_exp tyenv known tvs f1 in
      let f2 = toCls_exp (Environment.add x u tyenv) known tvs f2 in
      Cls.Let (x, u, f1, f2)
    | LetRecExp (x, u, tvs', (y, u'), f1, f2) ->
      let toplevel_backup = !toplevel in
      let tvset_backup = !tvset in
      let new_tvs = tvs' @ tvs in
      let tyenv' = Environment.add x u tyenv in
      let known' = Cls.V.add x known in
      let f1' = toCls_exp (Environment.add y u' tyenv') known' new_tvs f1 in
      let zs = Cls.V.diff (Cls.fv f1') (Cls.V.singleton y) in
      let known', f1' =
        if Cls.V.is_empty zs && List.length new_tvs = 0 then known', f1'
        else (toplevel := toplevel_backup; tvset := tvset_backup;
        let f1' = toCls_exp (Environment.add y u' tyenv') known new_tvs f1 in
        known, f1')
      in let zs = Cls.V.elements (Cls.V.diff (Cls.fv f1') (Cls.V.add x (Cls.V.singleton y))) in
      let zts = List.map (fun z -> (z, Environment.find z tyenv')) zs in
      toplevel := { Cls.name = (Cls.to_label x, u); Cls.tvs = (new_tvs, List.length tvs'); Cls.arg = (y, u'); Cls.formal_fv = zts; Cls.body = f1' } :: !toplevel;
      let f2' = toCls_exp tyenv' known' tvs f2 in
      if Cls.V.mem x (Cls.fv f2') then
        if List.length zs = 0 && List.length new_tvs = 0 then Cls.MakeLabel (x, u, Cls.to_label x, f2')
        else if List.length new_tvs = 0 then Cls.MakeCls (x, u, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, f2')
        else if List.length zs = 0 then Cls.MakePolyLabel (x, u, Cls.to_label x, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
        else Cls.MakePolyCls (x, u, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
      else f2'

  let ini x u (env, vs) = (Environment.add x u env, Cls.V.add x vs)

  let tyenv, venv = 
    ini "print_newline" (TyFun (TyUnit, TyUnit))
    @@ ini "print_bool" (TyFun (TyBool, TyUnit)) 
    @@ ini "print_int" (TyFun (TyInt, TyUnit)) 
    @@ (Environment.empty, Cls.V.empty)

  let toCls_program p =
    toplevel := []; tvset := TV.empty;
    let f = toCls_exp tyenv venv [] p in
    Cls.Prog (!tvset, List.rev !toplevel, f)
end

(*
let quad:int->int = fun (x:int) ->
  let dbl:int->int = fun (_var16:int) ->
    _var16 + _var16
  in (let _var14:int = dbl x in dbl _var14)
in (let _var15:int = 123 in quad _var15)

toplevel:=[]
g [] [] e
  LetFunExp(_,quad,int->int,[],[x,int],e1=LetExp(),e2=LetExp())
  env'=[quad,int->int], known'=[quad]
  g [x,int;quad,int->int] [quad] e1
    LetFunExp(_,dbl,int->int,[],[_var16,int],e1=BinOp(),e2=LetExp())
    env'=[dbl,int->int;x,int;quad,int->int], known'=[dbl,quad]
    g [_var16,int;dbl,int->int;x,int;quad,int->int] [dbl,quad] e1
    e1'=BinOp(_,Plus,_var16,_var16)
    zs=[_var16]-[_var16]=[]
    known'=known', e1'=e1'
    zs=[], zts=[]
    toplevel:={name=(quad,int->int);args=[_var16,int];formal_fv=[];body=e1'}::[]
    g [dbl,int->int;x,int;quad,int->int] [dbl,quad] e2
      LetExp(_,_var14,int,[],e1=AppExp(),e2=AppExp())
      g env known e1=AppDir(_,L(dbl),x)
      g env known e2=AppDir(_,L(dbl),_var14)
    e2'=Let(_,_var14,int,[],AppDir(_,L(dbl),x),AppDir(_,L(dbl),_var14))
  e1'=Let(_,_var14,int,[],AppDir(_,L(dbl),x),AppDir(_,L(dbl),_var14))
  zs=[x]-[x]=[] (*_var14はLetのfv、dblはAppDirの一つ目なので、含まれない*)
  known'=known', e1'=e1'
  zs=[],zts=[]
  toplevel:={name=(dbl,int->int);args=[x,int];formal_fv=[];body=e1'}::!toplevel
  g [quad,int->int] [quad] e2
    LetExp(_,_var15,[],e1=IConst(),e2=AppExp())
    g env known e1=Int(_,123)
    g env known e2=AppDir(_,L(quad),_var15)
  e2'=Let(_,_var15,[],Int(_,123),AppDir(_,L(quad),_var15))
e'=Let(_,_var15,[],Int(_,123),AppDir(_,L(quad),_var15))

let make_adder = fun (x:int) -> 
  let adder = fun (y:int) -> 
    x + y 
  in adder 
in (let _var17 = 3 in (let _var18 = make_adder _var17 in (let _var19 = 7 in _var18 _var19)))

toplevel:=[]
g [] [] e
  LetExp(_,make_adder,[],FunExp(_,x,int,e1=LetExp()),e2=LetExp())
  env'=[make_adder,int->int], known'=[make_adder]
  g [x,int;make_adder,int->int] [make_adder] e1
    LetExp(_,adder,[],FunExp(_,y,int,e1=BinOp()),e2=Var())
    env'=[adder,int->int;x,int;make_adder,int->int], known'=[adder,make_adder]
    g [y,int;adder,int->int;x,int;make_adder,int->int] [adder,make_adder] e1
    e1'=BinOp(_,Plus,x,y)
    zs=[x,y]-[y]=[x]
    g [y,int;adder,int->int;x,int;make_adder,int->int] [make_adder] e1
    e1'=BinOp(_,Plus,x,y)
    known'=known, e1'=e1'
    zs=[x,y]-[adder,y]=[x], zts=[x,int]
    toplevel:={name=(adder,int->int);args=[y,int];formal_fv=[x,int];body=e1'}::[]
    g [adder,int->int;x,int;make_adder,int->int] [make_adder] e2
    e2'=Var(_,adder)
  e1'=MakeCls((adder,int->int),{entry=L(adder);actual_fv=[x]},Var(_,adder))
  zs=[x]-[x]=[] (*adderはMakeClsのfvなので、含まれない*)
  known'=known', e1'=e1'
  zs=[],zts=[]
  toplevel:={name=(make_adder,int->int);args=[x,int];formal_fv=[];body=e1'}::!toplevel
  g [quad,int->int] [quad] e2
    LetExp(_,_var15,[],e1=IConst(),e2=AppExp())
    g env known e1=Int(_,123)
    g env known e2=AppDir(_,quad,_var15)
  e2'=Let(_,_var15,[],Int(_,123),AppDir(_,quad,_var15))
e'=Let(_,_var15,[],Int(_,123),AppDir(_,quad,_var15))
*)
      


  
