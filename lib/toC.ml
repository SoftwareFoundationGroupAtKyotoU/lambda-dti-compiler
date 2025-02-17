open Syntax
open Syntax.Cls
open Format
open Utils.Error

exception ToC_bug of string
exception ToC_error of string

(*Utilities*)
(*型のCプログラム表記を出力する関数
  Ground typeとDynamic type以外の型はもともと全てポインタなので&はいらない*)
let c_of_ty = function
  | TyInt -> "&tyint"
  | TyBool -> "&tybool"
  | TyUnit -> "&tyunit"
  | TyDyn -> "&tydyn"
  | TyFun (TyDyn, TyDyn) -> "&tyar"
  | TyFun (_, _) -> raise @@ ToC_bug "tyfun should be eliminated by closure"
  | TyVar (i, { contents = None }) -> "_ty" ^ string_of_int i
  | TyVar (i, { contents = Some _ }) -> "_tyfun" ^ string_of_int i

(*型引数のCプログラム表記を出力する関数*)
let c_of_tyarg = function
  | Ty u -> c_of_ty u
  | TyNu -> "newty()"

(*Castのran_polを記述する関数*)
(*toC_exp Let Castを参照*)
let toC_ran_pol ppf (y, r, p) =
  fprintf ppf "ran_pol %s_r_p = { .filename = %s, .startline = %d, .startchr = %d, .endline = %d, .endchr = %d, .polarity = %d};\n"
    y
    (if r.start_p.pos_fname <> "" then "\"File \\\""^r.start_p.pos_fname^"\\\", \"" else "\"\"")
    r.start_p.pos_lnum
    (r.start_p.pos_cnum - r.start_p.pos_bol)
    r.end_p.pos_lnum
    (r.end_p.pos_cnum - r.end_p.pos_bol)
    (match p with Pos -> 1 | Neg -> 0)

(*自由変数をクロージャに代入するプログラムを記述する関数*)
(*自由変数の個数をカウントする変数*)
let cnt_v = ref 0

let toC_v x ppf v =
  fprintf ppf "%s.f->fundat.closure.fvs[%d] = %s;"
    x
    !cnt_v
    v;
  cnt_v := !cnt_v + 1

let toC_vs ppf (x, vs) =
  cnt_v := 0;
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf fv = pp_print_list (toC_v x) ppf fv ~pp_sep:toC_sep in
  fprintf ppf "%a"
    toC_list vs

(*型引数を代入するプログラムを記述する関数*)
(*型引数の個数をカウントする変数*)
let cnt_ta = ref 0

let toC_ta x ppf u =
  fprintf ppf "%s.f->tas[%d] = %s;"
    x
    !cnt_ta
    (c_of_tyarg u);
  cnt_ta := !cnt_ta + 1

let toC_tas ppf (y, n, x, tas) =
  cnt_ta := 0;
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf ta = pp_print_list (toC_ta x) ppf ta ~pp_sep:toC_sep in
  fprintf ppf "%s.f->tas = (ty**)GC_MALLOC(sizeof(ty*) * %d);\n%a"
    x
    n
    toC_list tas;
  while (!cnt_ta < n) do
    fprintf ppf "\n%s.f->tas[%d] = %s.f->tas[%d];"
      x
      !cnt_ta
      y
      !cnt_ta;
    cnt_ta := !cnt_ta + 1
  done

(*束縛されていない型引数を代入するプログラムを記述する関数*)
let toC_ftas ppf (n, x, ftas) =
  cnt_ta := n;
  if List.length ftas = 0 then fprintf ppf ""
  else let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf fta = pp_print_list (toC_ta x) ppf fta ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list ftas

(* ======================================== *)

(*main関数かどうかを判定*)
let is_main = ref false

let rec toC_exp ppf f = match f with
  | Let (x, u, f1, f2) -> begin match f1 with (* let x = f1 in f2 のとき　f1によって出力するCプログラムを場合分け *) (* 2項目は型なので，現状無くてもよい（MinCamlにはついている）*)
    | Var y -> 
      fprintf ppf "value %s = %s;\n%a" (* let x = y in ... ~> value x = y; ... *) (*これはbeta変換でほとんどなくなるはず...？*)
        x
        y
        toC_exp f2
    | Int i -> 
      fprintf ppf "value %s = { .i_b_u = %d };\n%a" (* let x = n in ... ~> value x = { .i_b_u = n }; ... *)
        x
        i
        toC_exp f2
    | Unit ->
      fprintf ppf "value %s = { .i_b_u = 0 };\n%a" (* let x = () in ... ~> value x = { .i_b_u = 0 }; ...*) (*closure変換でunitもintの0にしてもよいかも？*)
        x
        toC_exp f2
    | Add (y, z) ->
      fprintf ppf "value %s = { .i_b_u = %s.i_b_u + %s.i_b_u };\n%a" (* let x = m + n in ... ~> value x = { .i_b_u = m.i_b_u + n.i_b_u }; ... *)
        x
        y
        z
        toC_exp f2
    | Sub (y, z) ->
      fprintf ppf "value %s = { .i_b_u = %s.i_b_u - %s.i_b_u };\n%a" (*addと同じ*)
        x
        y
        z
        toC_exp f2
    | Mul (y, z) ->
      fprintf ppf "value %s = { .i_b_u = %s.i_b_u * %s.i_b_u };\n%a" (*addと同じ*)
        x
        y
        z
        toC_exp f2
    | Div (y, z) ->
      fprintf ppf "value %s = { .i_b_u = %s.i_b_u / %s.i_b_u };\n%a" (*addと同じ*)
        x
        y
        z
        toC_exp f2
    | Mod (y, z) ->
      fprintf ppf "value %s = { .i_b_u = %s.i_b_u %% %s.i_b_u };\n%a" (*addと同じ*)
        x
        y
        z
        toC_exp f2
    | IfEq _ | IfLte _ as f1 ->
      fprintf ppf "value %s;\n%a%a" (* let x = if ... in f2 ~> value x; Insert(x, f1); f2 *) (*先にxを宣言しておいて，f1の内容を後でxに代入する*)
        x
        toC_exp (Insert (x, f1))
        toC_exp f2
    | AppDir (y, z) ->
      fprintf ppf "value %s = fun_%s(%s);\n%a" (* let x = y z in ... ~> value x = fun_y(z); ...*) (*yが直接適用できる関数のとき*) (*fun_をyにつける*)
        x
        y
        z
        toC_exp f2
    | AppCls (y, z) ->
      fprintf ppf "value %s = app(%s, %s);\n%a" (* let x = y z in ... ~> value x = app(y, z); ...*) (*yがクロージャを用いて適用する関数のとき*) (*app関数にyとzを渡す*) (*yにfunはつけない*)
        x
        y
        z
        toC_exp f2
    | Cast (y, u1, u2, r, p) -> 
      (*
      let x = y:u1=>^(r, p)u2 in ... 
      ~>
      ran_pol y_r_p = { .filename = ~~, .startline = ~~, .startchr = ~~, .endline = ~~, .endchr = ~~, .polarity = ~~};
      value x = cast(y, u1, u2, y_p_r);
      ...
      *)
      (*filenameやrangeの出力形式はUtilsを参照*)
      (*castの処理にはcast関数を用いる*)
      (*型の出力形式は関数c_of_tyによる TODO *)
      let c1, c2 = c_of_ty u1, c_of_ty u2 in
      fprintf ppf "%avalue %s = cast(%s, %s, %s, %s_r_p);\n%a"
        toC_ran_pol (y, r, p)
        x
        y
        c1
        c2
        y
        toC_exp f2
    | AppTy (y, n, tas) -> 
      fprintf ppf "value %s;\n%s.f = (fun*)GC_MALLOC(sizeof(fun));\n*%s.f = *%s.f;\n%a\n%a" (* TODO *)
        x
        x
        x
        y
        toC_tas (y, n, x, tas)
        toC_exp f2
    | SetTy (tv, f) -> toC_exp ppf (SetTy (tv, Let (x, u, f, f2))) (* 型定義を先にやる．Letのuはここで受け継ぐためだけにある*)
    | MakeLabel _ | MakeCls _ | MakePolyLabel _ | MakePolyCls _ | Let _ -> raise @@ ToC_bug "Let or LetRec appears in f1 on let in toC_exp; maybe closure dose not success"
    | Insert _ -> raise @@ ToC_bug "Insert appear in f1 on let in toC_exp"
    (*let x = let rec ~~ in ~ in f2やlet x = Insert(y, f) in f2などの形にはなり得ない
      前者はA正規化，closure変換によって取り除かれているはず
      後者は，toC_exp Insertを見れば分かるはず*)
    end
  | Insert (x, f) -> begin match f with (* letに内包されたif文が出てきたら現れる*) (*すでにxは宣言している*)
    | Var y -> 
      fprintf ppf "%s = %s;\n" (* Insert(x, y) ~> x = y; *)
        x
        y
    | Int i -> 
      fprintf ppf "%s.i_b_u = %d;\n" (* Insert(x, i) ~> x.i_b_u = i; *)
        x
        i
    | Unit -> 
      fprintf ppf "%s.i_b_u = 0;\n" (* Insert(x, ()) ~> x.i_b_u = 0; *)
        x
    | Add (y, z) ->
      fprintf ppf "%s.i_b_u = %s.i_b_u + %s.i_b_u;\n" (* Insert (x, y+z) ~> x.i_b_u = y.i_b_u + z.i_b_u; *)
        x
        y
        z
    | Sub (y, z) ->
      fprintf ppf "%s.i_b_u = %s.i_b_u - %s.i_b_u;\n" (*Addと同じ*)
        x
        y
        z
    | Mul (y, z) ->
      fprintf ppf "%s.i_b_u = %s.i_b_u * %s.i_b_u;\n" (*Addと同じ*)
        x
        y
        z
    | Div (y, z) ->
      fprintf ppf "%s.i_b_u = %s.i_b_u / %s.i_b_u;\n" (*Addと同じ*)
        x
        y
        z
    | Mod (y, z) ->
      fprintf ppf "%s.i_b_u = %s.i_b_u %% %s.i_b_u;\n" (*Addと同じ*)
        x
        y
        z
    | AppDir (y, z) ->
      fprintf ppf "%s = fun_%s(%s);\n" (* Insert(x, y z) ~> x = fun_y(z); *) (*yが直接適用できる関数の場合*)
        x
        y
        z
    | AppCls (y, z) ->
      fprintf ppf "%s = app(%s, %s);\n" (* Insert(x, y z) ~> x = app(y, z); *) (*yがクロージャを用いて適用する関数の場合*)
        x
        y
        z
    | AppTy (y, n, tas) ->
      fprintf ppf "%s.f = (fun*)GC_MALLOC(sizeof(fun));\n*%s.f = *%s.f;\n%a" (* TODO *)
        x
        x
        y        
        toC_tas (y, n, x, tas)
    | Cast (y, u1, u2, r, p) -> (* Letのときと同じ要領でcastを処理する．最後はx = cast(~,~,~,~); *)
      let c1, c2 = c_of_ty u1, c_of_ty u2 in
      fprintf ppf "%a%s = cast(%s, %s, %s, %s_r_p);\n"
        toC_ran_pol (y, r, p)
        x
        y
        c1
        c2
        y
    (*以下は内部にexpがあるので，後者のexpまでinsertを送る
      letはf2のみに，ifはf1,f2の両方にinsertを送る*)
    | Let (y, u, f1, f2) -> toC_exp ppf (Let (y, u, f1, Insert (x, f2)))
    | IfEq (y, z, f1, f2) -> toC_exp ppf (IfEq (y, z, Insert (x, f1), Insert (x, f2)))
    | IfLte (y, z, f1, f2) -> toC_exp ppf (IfLte (y, z, Insert (x, f1), Insert (x, f2)))
    | MakeLabel (y, u, l, f) -> toC_exp ppf (MakeLabel (y, u, l, Insert (x, f)))
    | MakeCls (y, u, c, f) -> toC_exp ppf (MakeCls (y, u, c, Insert (x, f)))
    | MakePolyLabel (y, u, l, tvs, f) -> toC_exp ppf (MakePolyLabel (y, u, l, tvs, Insert (x, f)))
    | MakePolyCls (y, u, c, tvs, f) -> toC_exp ppf (MakePolyCls (y, u, c, tvs, Insert (x, f)))
    | SetTy (tv, f) -> toC_exp ppf (SetTy (tv, Insert (x, f)))
    (*insertはletの一項目には最初の一回しか入らないので，二回insertがかぶさることはない*)
    | Insert _ -> raise @@ ToC_bug "Insert should not be doubled"
    end
  | IfEq (x, y, f1, f2) ->
    (*
    if x = y then f1 else f2
    ~>
    if(x.i_b_u == y.i_b_u) {
      f1
    } else {
      f2
    }
    *)
    (*等価判定はint型を用いて行うので，.i_b_uを取り出す*)
    fprintf ppf "if(%s.i_b_u == %s.i_b_u) {\n%a} else {\n%a}\n"
      x
      y
      toC_exp f1
      toC_exp f2
  | IfLte (x, y, f1, f2) -> (*IfEqと同じ*)
    fprintf ppf "if(%s.i_b_u <= %s.i_b_u) {\n%a} else {\n%a}\n"
      x
      y
      toC_exp f1
      toC_exp f2
  | MakeLabel (_, _, l, f) -> (* TODO *)
    fprintf ppf "%s.f = (fun*)GC_MALLOC(sizeof(fun));\n%s.f->funkind = LABEL;\n%s.f->fundat.label = fun_%s;\n%a"
      l
      l
      l
      l
      toC_exp f
  | MakePolyLabel (_, _, l, { ftvs = ftv; offset = n }, f) -> (*TODO*)
    fprintf ppf "%s.f = (fun*)GC_MALLOC(sizeof(fun));\n%s.f->funkind = POLY_LABEL;\n%s.f->fundat.poly_label = fun_%s;\n%s.f->tas = (ty**)GC_MALLOC(sizeof(ty*) * %d);\n%a%a"
      l
      l
      l
      l
      l
      (List.length ftv + n)
      toC_ftas (n, l, ftv)
      toC_exp f
  | MakeCls (x, _, { entry = _; actual_fv = vs }, f) -> (*TODO*)
    fprintf ppf "%s.f = (fun*)GC_MALLOC(sizeof(fun));\n%s.f->funkind = CLOSURE;\n%s.f->fundat.closure.cls = fun_%s;\n%s.f->fundat.closure.fvs = (value*)GC_MALLOC(sizeof(value) * %d);\n%a\n%a"
      x
      x
      x
      x
      x
      (List.length vs)
      toC_vs (x, vs)
      toC_exp f
  | MakePolyCls (x, _, { entry = _; actual_fv = vs }, { ftvs = ftv; offset = n }, f) -> (*TODO*)
    fprintf ppf "%s.f = (fun*)GC_MALLOC(sizeof(fun));\n%s.f->funkind = POLY_CLOSURE;\n%s.f->fundat.poly_closure.pcls = fun_%s;\n%s.f->fundat.poly_closure.fvs = (value*)GC_MALLOC(sizeof(value) * %d);\n%a\n%s.f->tas = (ty**)GC_MALLOC(sizeof(ty*) * %d);\n%a%a"
      x
      x
      x
      x
      x
      (List.length vs)
      toC_vs (x, vs)
      x
      (List.length ftv + n)
      toC_ftas (n, x, ftv)
      toC_exp f
  | SetTy ((i, { contents = opu }), f) -> begin match opu with (*ここはtoC_tycontentを参照*)
    | None ->
        fprintf ppf "ty *_ty%d = (ty*)GC_MALLOC(sizeof(ty));\n_ty%d->tykind = TYVAR;\n%a"
          i
          i
          toC_exp f
    | Some TyFun (u1, u2) -> 
      fprintf ppf "ty *_tyfun%d = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tykind = TYFUN;\n_tyfun%d->tyfun.left = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tyfun.right = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tyfun.left = %s;\n_tyfun%d->tyfun.right = %s;\n%a"
        i
        i
        i
        i
        i
        (c_of_ty u1)
        i
        (c_of_ty u2)
        toC_exp f
    | Some _ -> raise @@ ToC_bug "not tyfun is in tyvar option"
    end
  (*以下は項の中にexpを含まないので，main関数かどうかを判定してreturn文を変える必要がある．
    main関数ならreturn 0;でプログラムを終える．main関数でなければ，その式自体をreturnする．
    例はmain関数でないとき*)
  | Var x -> (* x ~> return x;*)
    if !is_main then 
      fprintf ppf "%s;\nreturn 0;\n" x
    else 
      fprintf ppf "return %s;\n" x
  | Int i -> (* i ~> value retint = { .i_b_u = i }; return retint; *)
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %d };\nreturn 0;\n" i
    else 
      fprintf ppf "value retint = { .i_b_u = %d };\nreturn retint;\n" i
  | Unit -> (* () ~> value retint = { .i_b_u = 0 }; return retint; *)
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = 0 };\nreturn 0;\n"
    else 
      fprintf ppf "value retint = { .i_b_u = 0 };\nreturn retint;\n"
  | Add (x, y) -> (* x + y ~> value retint = { .i_b_u = x.i_b_u + y.i_b_u }; return retint; *)
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u + %s.i_b_u };\nreturn 0;\n" x y
    else 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u + %s.i_b_u };\nreturn retint;\n" x y
  | Sub (x, y) -> (*Addと同じ*)
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u - %s.i_b_u };\nreturn 0;\n" x y
    else 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u - %s.i_b_u };\nreturn retint;\n" x y
  | Mul (x, y) -> (*Addと同じ*)
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u * %s.i_b_u };\nreturn 0;\n" x y
    else 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u * %s.i_b_u };\nreturn retint;\n" x y
  | Div (x, y) -> (*Addと同じ*)
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u / %s.i_b_u };\nreturn 0;\n" x y
    else 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u / %s.i_b_u };\nreturn retint;\n" x y
  | Mod (x, y) -> (*Addと同じ*)
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u %% %s.i_b_u };\nreturn 0;\n" x y
    else 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u %% %s.i_b_u };\nreturn retint;\n" x y
  | AppDir (x, y) -> (* x y ~> return fun_x(y); *) (*xが直接適用できる関数の場合*)
    if !is_main then 
      fprintf ppf "fun_%s(%s);\nreturn 0;\n"
        x
        y
    else
      fprintf ppf "return fun_%s(%s);\n"
        x
        y
  | AppCls (x, y) -> (* x y ~> return app(x, y); *) (*xがクロージャを利用して適用する関数の場合*)
    if !is_main then 
      fprintf ppf "app(%s, %s);\nreturn 0;\n"
        x
        y
    else
      fprintf ppf "return app(%s, %s);\n"
        x
        y
  | Cast (x, u1, u2, r, p) -> (*letのときと同じように出力．cast関数の返り値をそのまま返す*)
    let c1, c2 = c_of_ty u1, c_of_ty u2 in
    if !is_main then 
      fprintf ppf "%acast(%s, %s, %s, %s_r_p);\nreturn 0;\n"
        toC_ran_pol (x, r, p)
        x
        c1
        c2
        x
    else
      fprintf ppf "%areturn cast(%s, %s, %s, %s_r_p);\n"
        toC_ran_pol (x, r, p)
        x
        c1
        c2
        x
  | AppTy (x, n, tas) -> 
    if !is_main then
      fprintf ppf "value retval;\nretval.f = (fun*)GC_MALLOC(sizeof(fun));\n*retval.f = *%s.f;\n%a\nreturn 0;" (* TODO *)
        x
        toC_tas (x, n, "retval", tas)
    else 
      fprintf ppf "value retval;\nretval.f = (fun*)GC_MALLOC(sizeof(fun));\n*retval.f = *%s.f;\n%a\nreturn retval;\n"
        x
        toC_tas (x, n, "retval", tas)

(* =================================== *)

(*型定義をするCプログラムを記述*)
(*declとしてtyvar = int * ty option refが渡される
  ty option refはcontentsがNoneであればTyVarを，SomeであればTyFunを表すようにしている
  ここで行われる型定義は，プログラム全体で共有される方についてのみである*)
(*型名の前方定義
  型はポインタなので，共有して型を扱うには，まず名前を先に定義する必要がある*)
let toC_tydecl ppf (i, { contents = opu }) =
  match opu with
  | None -> fprintf ppf "ty *_ty%d;" i
  | Some _ -> fprintf ppf "ty *_tyfun%d;" i

let toC_tydecls ppf l = 
  if List.length l = 0 then fprintf ppf ""
  else let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_tydecl ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l

(*型の定義*)
let toC_tycontent ppf (i, { contents = opu }) =
  match opu with
  | None -> (* TyVarはMALLOCした後，tykindをTYVARにする *)
    fprintf ppf "_ty%d = (ty*)GC_MALLOC(sizeof(ty));\n_ty%d->tykind = TYVAR;"
      i
      i
  | Some TyFun (u1, u2) -> 
    (*TyFunはMALLOCしたのち，tykindをTYFUNとする
      さらに，leftとrightをそれぞれMALLOCして，TyFunの二つの型をそれぞれ代入する*)
    fprintf ppf "_tyfun%d = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tykind = TYFUN;\n_tyfun%d->tyfun.left = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tyfun.right = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tyfun.left = %s;\n_tyfun%d->tyfun.right = %s;"
      i
      i
      i
      i
      i
      (c_of_ty u1)
      i
      (c_of_ty u2)
  | Some _ -> raise @@ ToC_bug "not tyfun is in tyvar option"

let toC_tycontents ppf l = 
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_tycontent ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l

(*型定義全体を記述*)
let toC_tys ppf l =
  fprintf ppf "%a%s%a%s"
    toC_tydecls l
    "int set_tys() {\n" (*Cではset_tys()関数内で型の定義を行う．main関数で最初に呼び出す*)
    toC_tycontents l
    "return 0;\n}\n"

(* ================================ *)

(*関数定義をするCプログラムを記述*)
(*関数定義の最初に，自由変数を詰める場所を設ける*)
(*自由変数をカウントする変数*)
let cnt_fv = ref 0

(*引数zsから要素を取り出し，変数名xの値に代入*)
let toC_fv ppf (x, _) =
  fprintf ppf "value %s = zs[%d];"
    x
    !cnt_fv;
  cnt_fv := !cnt_fv + 1

let toC_fvs ppf fvl =
  cnt_fv := 0; (*呼出しごとに0に初期化*)
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf fv = pp_print_list toC_fv ppf fv ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list fvl

(*関数定義の最初に，型変数を詰める場所も設ける*)
(*型変数をカウントする変数*)
let cnt_tv = ref 0

let toC_tv n ppf (i, _) = (* TODO *)
  if !cnt_tv < n then
    (fprintf ppf "ty *_ty%d = (ty*)GC_MALLOC(sizeof(ty));\n_ty%d = tvs[%d];"
      i
      i
      !cnt_tv;
    cnt_tv := !cnt_tv + 1)
  else 
    (fprintf ppf "ty *_ty%d = tvs[%d];"
      i
      !cnt_tv;
    cnt_tv := !cnt_tv + 1)

let toC_tvs ppf (tvl, n) =
  cnt_tv := 0;
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf tv = pp_print_list (toC_tv n) ppf tv ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list tvl
  
(*関数名の前方定義
  再帰関数などに対応するために，関数本体の前に，名前を前方定義する
  ここで定義する内容はfun型の関数自体の定義と，関数が格納されたvalue型の値の二つ
  fundef内のfvl(自由変数のリスト)とtvs(型変数のリスト)に要素が入っているかどうかで関数の型が異なるので，四通りの場合分けが発生する*)
let toC_label ppf { name = (l, _); tvs = (tvs, _); arg = (_, _); formal_fv = fvl; body = _ } = 
  let num = List.length fvl in
  let num' = List.length tvs in
  if num = 0 && num' = 0 then
    fprintf ppf "value fun_%s(value);\nvalue %s;"
      l
      l
  else if num = 0 then
    fprintf ppf "value fun_%s(value, ty**);\nvalue %s;"
      l
      l
  else if num'= 0 then
    fprintf ppf "value fun_%s(value, value*);\nvalue %s;"
      l
      l
  else
    fprintf ppf "value fun_%s(value, value*, ty**);\nvalue %s;"
      l
      l

(*関数本体の定義
  やはり4通りの場合分けが発生*)
let toC_fundef ppf { name = (l, _); tvs = (tvs, n); arg = (x, _); formal_fv = fvl; body = f } = 
  let num = List.length fvl in
  let num' = List.length tvs in
  if num = 0 && num' = 0 then (*自由変数も型変数もない関数は，引数を一つとる関数として定義*)
    fprintf ppf "value fun_%s(value %s) {\n%a}"
      l
      x
      toC_exp f
  else if num = 0 then (*自由変数がない関数は，引数を一つと，型変数リストを受け取る関数として定義*)
    fprintf ppf "value fun_%s(value %s, ty* tvs[%d]) {\n%a%a}"
      l
      x
      num'
      toC_tvs (tvs, n)
      toC_exp f
  else if num' = 0 then (*型変数がない関数は，引数を一つと，自由変数リストを受け取る関数として定義*)
    fprintf ppf "value fun_%s(value %s, value zs[%d]) {\n%a%a}"
      l
      x
      num
      toC_fvs fvl
      toC_exp f
  else (*上記以外の場合は，引数を一つ，自由変数リスト，型変数リストを受け取る関数として定義*)
    fprintf ppf "value fun_%s(value %s, value zs[%d], ty* tvs[%d]) {\n%a%a%a}"
      l
      x
      num
      num'
      toC_tvs (tvs, n)
      toC_fvs fvl
      toC_exp f
  
(*関数定義全体を記述*)
let toC_fundefs ppf toplevel =
  (if List.length toplevel = 0 then pp_print_string ppf ""
  else let toC_sep ppf () = fprintf ppf "\n\n" in
  let toC_list ppf labels = pp_print_list toC_label ppf labels ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n"
    toC_list toplevel;
  let toC_list ppf defs = pp_print_list toC_fundef ppf defs ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n" 
    toC_list toplevel);
  is_main := true (*関数定義が終わったら，main関数に入ることを知らせる*)

(* =================================== *)

(*全体を記述*)
let toC_program ppf (Prog (tvset, toplevel, f)) = 
  is_main := false;
  fprintf ppf "%s\n%a\n%a%s%a%s"
    "#include <gc.h>\n#include \"../lib/cast.h\"\n"
    toC_tys (TV.elements tvset)
    toC_fundefs toplevel
    "int main() {\nstdlib();\nset_tys();\n"
    toC_exp f
    "}"