open Syntax

exception Closure_bug of string
exception Closure_error of string

module KNorm = struct
  let toplevel = ref []

  let rec toCls_exp tyenv known = function
    | Var x -> Cls.Var x
    | Int i -> Cls.Int i
    | UConst -> Cls.Unit
    | Add (x, y) -> Cls.Add (x, y)
    | Sub (x, y) -> Cls.Sub (x, y)
    | Mul (x, y) -> Cls.Mul (x, y)
    | Div (x, y) -> Cls.Div (x, y)
    | Mod (x, y) -> Cls.Mod (x, y)
    | IfEqExp (x, y, f1, f2) -> Cls.IfEq (x, y, toCls_exp tyenv known f1, toCls_exp tyenv known f2)
    | IfLteExp (x, y, f1, f2) -> Cls.IfLte (x, y, toCls_exp tyenv known f1, toCls_exp tyenv known f2)
    | AppExp (x, y) when V.mem x known -> Cls.AppDir (r, to_label x, y)
    | AppExp (x, y) -> Cls.AppCls (x, y)
    | CastExp (r, x, u1, u2, p) -> Cls.Cast (x, u1, u2, r, p)
    | LetExp (x, u, tvs, f1, f2) -> Cls.Let (x, u, tvs, toCls_exp tyenv f1, toCls_exp (Environment.add x u tyenv) f2)
    | LetRecExp (x, u, tvs, (y, u'), f1, f2) ->
      let toplevel_backup = !toplevel in
      let env' = Environment.add x u tyenv in
      let known' = V.add x known in
      let e1' = toCls_exp (Environment.add y u' tyenv') known' e1 in
      let zs = V.diff (fv e1') (V.singleton y) in
      let known', e1' =
        if V.is_empty zs then known', e1'
        else toplevel := toplevel_backup;
        let e1' = toCls_exp (Environment.add y u' tyenv') known e1 in
        known, e1'
      in let zs = V.elements (V.diff (fv e1') (V.add x (V.singleton y))) in
      let zts = List.map (fun z -> (z, Environment.find z tyenv')) zs in
      toplevel := { name = (to_label x, u); arg = [(y, u')]; formal_fv = zts; body = e1' } :: !toplevel;
      let e2 = toCls_exp env'known' e2 in
      if V.mem x (fv e2) then
        MakeCls (x, u, { entry = to_label x; actual_fv = zs }, e2)
      else e2

  let toCls_program = function
    | Exp f -> Cls.Exp (toCls_exp f)
    | LetDecl (x, tvs, f) -> LetDecl (x, tvs, toCls_exp f)
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
      


  