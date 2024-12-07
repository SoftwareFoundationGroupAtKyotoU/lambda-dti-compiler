open Syntax
open Syntax.Cls
open Format

exception ToC_bug of string

let type_of_return = function
  | TyFun (_, u) -> u
  | _ -> raise @@ ToC_bug "not fun type is applied to type_of_return"

let toC_ty ppf = function
  | TyInt -> pp_print_string ppf "int"
  | _ -> raise @@ ToC_bug "toC_ty yet"

let cnt_vs = ref 0

let toC_v ppf (v, x) =
  fprintf ppf "\t%s_.zs[%d] = %s;"
    x
    !cnt_vs
    v;
  cnt_vs := !cnt_vs + 1

let toC_vs ppf vs =
  cnt_vs := 0;
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf v = pp_print_list toC_v ppf v ~pp_sep:toC_sep in
  fprintf ppf "%a"
    toC_list vs

let rec toC_exp ppf f = match f with
  | Var x -> pp_print_string ppf x
  | Int i -> pp_print_int ppf i
  | Add (x, y) -> fprintf ppf "%s + %s" x y
  | Sub (x, y) -> fprintf ppf "%s - %s" x y
  | Mul (x, y) -> fprintf ppf "%s * %s" x y
  | Div (x, y) -> fprintf ppf "%s / %s" x y
  | Mod (x, y) -> fprintf ppf "%s %% %s" x y
  | Let (x, TyInt, f1, (Let _ | MakeCls _ as f2)) ->
    fprintf ppf "\tint %s = %a;\n%a"
      x
      toC_exp f1
      toC_exp f2
  | Let (x, TyInt, f1, f2) ->
    fprintf ppf "\tint %s = %a;\n\treturn %a;"
      x
      toC_exp f1
      toC_exp f2
  | MakeCls (x, _, { entry = _; actual_fv = vs }, (Let _ | MakeCls _ as f)) ->
    fprintf ppf "\tcls_%s_t %s_;\n\t%s_.fun = %s;\n%a\n%a"
      x
      x
      x
      x
      toC_vs (List.map (fun v -> (v, x)) vs)
      toC_exp f
  | MakeCls (x, _, { entry = _; actual_fv = vs }, f) ->
    fprintf ppf "\tcls_%s_t %s_;\n\t%s_.fun = %s;\n%a\n\treturn %a;"
      x
      x
      x
      x
      toC_vs (List.map (fun v -> (v, x)) vs)
      toC_exp f
  | AppCls (x, y) when x = "print_int" ->
    fprintf ppf "printf(\"%%d\\n\", %s)" y
  | AppCls (x, y) -> 
    fprintf ppf "%s_.fun(%s, %s_.zs)"
      x
      y
      x
  | AppDir (x, y) -> fprintf ppf "%s(%s)" x y
  | _ -> raise @@ ToC_bug "toC yet"

let rec toC_exp_main ppf f = match f with
  | Let (x, TyInt, f1, (Let _ | MakeCls _ as f2)) -> 
    fprintf ppf "\tint %s = %a;\n%a"
      x
      toC_exp f1
      toC_exp_main f2
  | Let (x, TyInt, f1, f2) ->
    fprintf ppf "\tint %s = %a;\n\t%a;\n\treturn 0;\n"
      x
      toC_exp f1
      toC_exp f2
  | MakeCls (x, _, { entry = _; actual_fv = vs }, (Let _ | MakeCls _ as f)) -> 
    fprintf ppf "\tcls_%s_t %s_;\n\t%s_.fun = %s;\n%a\n%a"
      x
      x
      x
      x
      toC_vs (List.map (fun v -> (v, x)) vs)
      toC_exp_main f
  | MakeCls (x, _, { entry = _; actual_fv = vs }, f) -> 
    fprintf ppf "\tcls_%s_t %s_;\n\t%s_.fun = %s;\n%a\n\t%a;\n\treturn 0;\n"
      x
      x
      x
      x
      toC_vs (List.map (fun v -> (v, x)) vs)
      toC_exp_main f
  | _ as f -> toC_exp ppf f

let cnt_fd = ref 0

let toC_fv ppf (x, u) =
  begin match u with
    | TyInt ->
      fprintf ppf "\tint %s = zs[%d];"
        x
        !cnt_fd
    | _ -> raise @@ ToC_bug "toC_fv yet"
  end;
  cnt_fd := !cnt_fd + 1

let toC_fvs ppf fvl =
  cnt_fd := 0;
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf fv = pp_print_list toC_fv ppf fv ~pp_sep:toC_sep in
  fprintf ppf "%a"
    toC_list fvl

let toC_fundef ppf { name = (l, ul); arg = (x, ux); formal_fv = fvl; body = f} = 
  let num = List.length fvl in
  if num = 0 then
    match type_of_return ul with
      | TyInt ->
        begin match f with
          | Let _ | MakeCls _ -> 
            fprintf ppf "int %s(%a %s) {\n%a\n}"
              l
              toC_ty ux
              x
              toC_exp f
          | _ -> 
            fprintf ppf "int %s(%a %s) {\n\treturn %a;\n}"
              l
              toC_ty ux
              x
              toC_exp f
        end
      | _ -> raise @@ ToC_bug "toC_fundef yet"
  else 
    match type_of_return ul with
      | TyInt ->
        begin match f with
          | Let _ | MakeCls _ -> 
            fprintf ppf 
              "typedef struct cls_%s_t {\n\tint (*fun)(int, int*);\n\tint arg;\n\tint zs[%d];\n} cls_%s_t;\n\nint %s(%a %s, int zs[%d]) {\n%a\n%a\n}"
              l
              num
              l
              l
              toC_ty ux
              x
              num
              toC_fvs fvl
              toC_exp f
          | _ -> 
            fprintf ppf 
            "typedef struct cls_%s_t {\n\tint (*fun)(int, int*);\n\tint arg;\n\tint zs[%d];\n} cls_%s_t;\n\nint %s(%a %s, int zs[%d]) {\n%a\n\treturn %a;\n}"
              l
              num
              l
              l
              toC_ty ux
              x
              num
              toC_fvs fvl
              toC_exp f
        end
      | _ -> raise @@ ToC_bug "toC_fundef yet"

let toC_fundefs ppf toplevel =
  let toC_sep ppf () = fprintf ppf "\n\n" in
  let toC_list ppf defs = pp_print_list toC_fundef ppf defs ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n"
    toC_list toplevel

let toC_program ppf (Prog (toplevel, f)) = 
  fprintf ppf "%s\n%a%s%a%s"
    "#include <stdio.h>\n"
    toC_fundefs toplevel
    "int main() {\n"
    toC_exp_main f
    "}"
  