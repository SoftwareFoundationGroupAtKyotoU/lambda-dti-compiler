open Syntax
open Syntax.Cls
open Format

exception ToC_bug of string
exception ToC_error of string

let is_main = ref false

let tvset = ref V.empty

let rec c_of_ty ppf = function
  | TyInt -> "&tyint"
  | TyBool -> "&tybool"
  | TyUnit -> "&tyunit"
  | TyDyn -> "&tydyn"
  | TyFun (TyDyn, TyDyn) -> "&tyar"
  | TyFun (u1, u2) -> 
    let c1, c2 = c_of_ty ppf u1, c_of_ty ppf u2 in 
    let v = KNormal.genvar "_tyfun" in
    (fprintf ppf "ty %s = { .tykind = TYFUN, .tyfun = { .left = %s, .right = %s } };\n"
      v
      c1
      c2);
    ("&"^v)
  | TyVar (i, _) -> 
    let strtv = "_tv" ^ string_of_int i in
    try 
      V.find strtv !tvset 
    with Not_found -> 
      tvset := V.add strtv !tvset;
      (fprintf ppf "ty *%s = (ty*)malloc(sizeof(ty));\n%s->tykind = TYVAR;\n"
        strtv
        strtv);
      strtv

let cnt_v = ref 0

let toC_v x ppf v =
  fprintf ppf "%s.f.fundat.closure.fvs[%d] = %s;"
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

let rec toC_exp ppf f = match f with
  | Let (x, _, f1, f2) -> begin match f1 with
    | Var y -> 
      fprintf ppf "value %s = %s;\n%a"
        x
        y
        toC_exp f2
    | Int i ->
      fprintf ppf "value %s = { .i_b_u = %d };\n%a"
        x
        i
        toC_exp f2
    | Unit ->
      fprintf ppf "value %s = { .i_b_u = 0 };\n%a"
        x
        toC_exp f2
    | Add (y, z) ->
      fprintf ppf "value %s = { .i_b_u = %s.i_b_u + %s.i_b_u };\n%a"
        x
        y
        z
        toC_exp f2
    | Sub (y, z) ->
      fprintf ppf "value %s = { .i_b_u = %s.i_b_u - %s.i_b_u };\n%a"
        x
        y
        z
        toC_exp f2
    | Mul (y, z) ->
      fprintf ppf "value %s = { .i_b_u = %s.i_b_u * %s.i_b_u };\n%a"
        x
        y
        z
        toC_exp f2
    | Div (y, z) ->
      fprintf ppf "value %s = { .i_b_u = %s.i_b_u / %s.i_b_u };\n%a"
        x
        y
        z
        toC_exp f2
    | Mod (y, z) ->
      fprintf ppf "value %s = { .i_b_u = %s.i_b_u %% %s.i_b_u };\n%a"
        x
        y
        z
        toC_exp f2
    | IfEq _ | IfLte _ as f1 ->
      fprintf ppf "value %s;\n%a%a"
        x
        toC_exp (Insert (x, f1))
        toC_exp f2
    | AppDir (y, z) ->
      fprintf ppf "value %s = fun_%s(%s);\n%a"
        x
        y
        z
        toC_exp f2
    | AppCls (y, z) ->
      fprintf ppf "value %s = app(%s, %s);\n%a"
        x
        y
        z
        toC_exp f2
    | Cast (y, u1, u2, r, p) ->
      let c1, c2 = c_of_ty ppf u1, c_of_ty ppf u2 in
      fprintf ppf "ran_pol %s_p_r = { .filename = %s, .startline = %d, .startchr = %d, .endline = %d, .endchr = %d, .polarity = %d};\nvalue %s = cast(%s, %s, %s, %s_p_r);\n%a"
        y
        (if r.start_p.pos_fname <> "" then "\"File \\\""^r.start_p.pos_fname^"\\\", \"" else "\"\"")
        r.start_p.pos_lnum
        (r.start_p.pos_cnum - r.start_p.pos_bol)
        r.end_p.pos_lnum
        (r.end_p.pos_cnum - r.end_p.pos_bol)
        (match p with Pos -> 1 | Neg -> 0)
        x
        y
        c1
        c2
        y
        toC_exp f2
    | AppTy _ -> raise @@ ToC_error "toC_exp appty is not available : constraint on polymorphism"
    | MakeCls _ | MakeClsLabel _ | Let _ -> raise @@ ToC_bug "Let or LetRec appears in f1 on let in toC_exp; maybe closure dose not success"
    | Insert _ -> raise @@ ToC_bug "Insert appear in f1 on let in toC_exp"
    end
  | IfEq (x, y, f1, f2) ->
    fprintf ppf "if(%s.i_b_u == %s.i_b_u) {\n%a} else {\n%a}\n"
      x
      y
      toC_exp f1
      toC_exp f2
  | IfLte (x, y, f1, f2) ->
    fprintf ppf "if(%s.i_b_u <= %s.i_b_u) {\n%a} else {\n%a}\n"
      x
      y
      toC_exp f1
      toC_exp f2
  | MakeCls (x, _, { entry = _; actual_fv = vs }, f) ->
    fprintf ppf "value %s;\n%s.f.funkind = CLOSURE;\n%s.f.fundat.closure.cls = fun_%s;\n%s.f.fundat.closure.fvs = (value*)malloc(sizeof(value) * %d);\n%a\n%a"
      x
      x
      x
      x
      x
      (List.length vs)
      toC_vs (x, vs)
      toC_exp f
  | MakeClsLabel (_, _, l, f) ->
    fprintf ppf "value %s;\n%s.f.funkind = LABEL;\n%s.f.fundat.label = fun_%s;\n%a"
      l
      l
      l
      l
      toC_exp f
  | Var x -> 
    if !is_main then 
      fprintf ppf "%s;\nreturn 0;\n" x
    else 
      fprintf ppf "return %s;\n" x
  | Int i -> 
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %d };\nreturn 0;\n" i
    else 
      fprintf ppf "value retint = { .i_b_u = %d };\nreturn retint;\n" i
  | Unit ->
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = 0 };\nreturn 0;\n"
    else 
      fprintf ppf "value retint = { .i_b_u = 0 };\nreturn retint;\n"
  | Add (x, y) -> 
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u + %s.i_b_u };\nreturn 0;\n" x y
    else 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u + %s.i_b_u };\nreturn retint;\n" x y
  | Sub (x, y) ->
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u - %s.i_b_u };\nreturn 0;\n" x y
    else 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u - %s.i_b_u };\nreturn retint;\n" x y
  | Mul (x, y) -> 
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u * %s.i_b_u };\nreturn 0;\n" x y
    else 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u * %s.i_b_u };\nreturn retint;\n" x y
  | Div (x, y) -> 
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u / %s.i_b_u };\nreturn 0;\n" x y
    else 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u / %s.i_b_u };\nreturn retint;\n" x y
  | Mod (x, y) -> 
    if !is_main then 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u %% %s.i_b_u };\nreturn 0;\n" x y
    else 
      fprintf ppf "value retint = { .i_b_u = %s.i_b_u %% %s.i_b_u };\nreturn retint;\n" x y
  | AppCls (x, y) ->
    if !is_main then 
      fprintf ppf "app(%s, %s);\nreturn 0;\n"
        x
        y
    else
      fprintf ppf "return app(%s, %s);\n"
        x
        y
  | AppDir (x, y) -> 
    if !is_main then 
      fprintf ppf "fun_%s(%s);\nreturn 0;\n"
        x
        y
    else
      fprintf ppf "return fun_%s(%s);\n"
        x
        y
  | Cast (x, u1, u2, r, p) ->
    let c1, c2 = c_of_ty ppf u1, c_of_ty ppf u2 in
    if !is_main then 
      fprintf ppf "ran_pol %s_p_r = { .filename = %s, .startline = %d, .startchr = %d, .endline = %d, .endchr = %d, .polarity = %d};\ncast(%s, %s, %s, %s_p_r);\nreturn 0;\n"
        x
        (if r.start_p.pos_fname <> "" then "\"File \\\""^r.start_p.pos_fname^"\\\", \"" else "\"\"")
        r.start_p.pos_lnum
        (r.start_p.pos_cnum - r.start_p.pos_bol)
        r.end_p.pos_lnum
        (r.end_p.pos_cnum - r.end_p.pos_bol)
        (match p with Pos -> 1 | Neg -> 0)
        x
        c1
        c2
        x
    else
      fprintf ppf "ran_pol %s_p_r = { .filename = %s, .startline = %d, .startchr = %d, .endline = %d, .endchr = %d, .polarity = %d};\nreturn cast(%s, %s, %s, %s_p_r);\n"
        x
        (if r.start_p.pos_fname <> "" then "\"File \\\""^r.start_p.pos_fname^"\\\", \"" else "\"\"")
        r.start_p.pos_lnum
        (r.start_p.pos_cnum - r.start_p.pos_bol)
        r.end_p.pos_lnum
        (r.end_p.pos_cnum - r.end_p.pos_bol)
        (match p with Pos -> 1 | Neg -> 0)
        x
        c1
        c2
        x
  | Insert (x, f) -> begin match f with
    | Var y -> 
      fprintf ppf "%s = %s;\n"
        x
        y
    | Int i -> 
      fprintf ppf "%s.i_b_u = %d;\n"
        x
        i
    | Unit -> 
      fprintf ppf "%s.i_b_u = 0;\n"
        x
    | Add (y, z) ->
      fprintf ppf "%s.i_b_u = %s.i_b_u + %s.i_b_u;\n"
        x
        y
        z
    | Sub (y, z) ->
      fprintf ppf "%s.i_b_u = %s.i_b_u - %s.i_b_u;\n"
        x
        y
        z
    | Mul (y, z) ->
      fprintf ppf "%s.i_b_u = %s.i_b_u * %s.i_b_u;\n"
        x
        y
        z
    | Div (y, z) ->
      fprintf ppf "%s.i_b_u = %s.i_b_u / %s.i_b_u;\n"
        x
        y
        z
    | Mod (y, z) ->
      fprintf ppf "%s.i_b_u = %s.i_b_u %% %s.i_b_u;\n"
        x
        y
        z
    | AppTy _ -> raise @@ ToC_error "toC_exp appty is not available : constraint on polymorphism"
    | AppCls (y, z) | AppDir (y, z) ->
      fprintf ppf "%s = app(%s, %s);\n"
        x
        y
        z
    | Cast (y, u1, u2, r, p) ->
      let c1, c2 = c_of_ty ppf u1, c_of_ty ppf u2 in
      fprintf ppf "ran_pol %s_p_r = { .filename = %s, .startline = %d, .startchr = %d, .endline = %d, .endchr = %d, .polarity = %d};\n%s = cast(%s, %s, %s, %s_p_r);\n"
        x
        (if r.start_p.pos_fname <> "" then "\"File \\\""^r.start_p.pos_fname^"\\\", \"" else "\"\"")
        r.start_p.pos_lnum
        (r.start_p.pos_cnum - r.start_p.pos_bol)
        r.end_p.pos_lnum
        (r.end_p.pos_cnum - r.end_p.pos_bol)
        (match p with Pos -> 1 | Neg -> 0)
        y
        x
        c1
        c2
        x
    | Let (y, u, f1, f2) -> toC_exp ppf (Let (y, u, f1, Insert (x, f2)))
    | IfEq (y, z, f1, f2) -> toC_exp ppf (IfEq (y, z, Insert (x, f1), Insert (x, f2)))
    | IfLte (y, z, f1, f2) -> toC_exp ppf (IfLte (y, z, Insert (x, f1), Insert (x, f2)))
    | MakeCls (y, u, c, f) -> toC_exp ppf (MakeCls (y, u, c, Insert (x, f)))
    | MakeClsLabel (y, u, l, f) -> toC_exp ppf (MakeClsLabel (y, u, l, Insert (x, f)))
    | Insert _ -> raise @@ ToC_bug "Insert should not be doubled"
    end
  | AppTy _ -> raise @@ ToC_error "toC_exp appty is not available : constraint on polymorphism"

let cnt_fd = ref 0

let toC_fv ppf (x, _) =
  fprintf ppf "value %s = zs[%d];"
    x
    !cnt_fd;
  cnt_fd := !cnt_fd + 1

let toC_fvs ppf fvl =
  cnt_fd := 0;
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf fv = pp_print_list toC_fv ppf fv ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list fvl

let toC_fundef ppf { name = (l, _); arg = (x, _); formal_fv = fvl; body = f} = 
  let num = List.length fvl in
  if num = 0 then
    fprintf ppf "value fun_%s(value %s) {\n%a}"
      l
      x
      toC_exp f
  else
    fprintf ppf "value fun_%s(value %s, value zs[%d]) {\n%a%a}"
      l
      x
      num
      toC_fvs fvl
      toC_exp f

let toC_label ppf { name = (l, _); arg = (_, _); formal_fv = fvl; body = _} = 
  let num = List.length fvl in
  if num = 0 then
    fprintf ppf "value fun_%s(value);"
      l
  else
    fprintf ppf "value fun_%s(value, value*);"
      l

let toC_fundefs ppf toplevel =
  (if List.length toplevel = 0 then pp_print_string ppf ""
  else let toC_sep ppf () = fprintf ppf "\n\n" in
  let toC_list ppf labels = pp_print_list toC_label ppf labels ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n"
    toC_list toplevel;
  let toC_list ppf defs = pp_print_list toC_fundef ppf defs ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n" 
    toC_list toplevel);
  is_main := true

let toC_program ppf (Prog (toplevel, f)) = 
  fprintf ppf "%s\n%a%s%a%s"
    "#include <stdio.h>\n#include <stdlib.h>\n#include \"cast.h\"\n"
    toC_fundefs toplevel
    "int main() {\n"
    toC_exp f
    "}";
  is_main := false; tvset := V.empty