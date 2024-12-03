open Format

open OUnit2

open Lambda_dti
open Syntax

let test_cases = List.map (fun l -> List.map (fun (a, b, _, d) -> (a, b, d)) l) Test_cases.tests

let id x = x

let run tyenv kfunenvs kenv program =
  let parse str = Parser.toplevel Lexer.main @@ Lexing.from_string str in
  let e = parse @@ program ^ ";;" in
  let e, u = Typing.ITGL.type_of_program tyenv e in
  let tyenv, e, u = Typing.ITGL.normalize tyenv e u in
  let new_tyenv, f, u' = Typing.ITGL.translate tyenv e in
  assert (Typing.is_equal u u');
  let u'' = Typing.CC.type_of_program tyenv f in
  assert (Typing.is_equal u u'');
  let kf, ku, kfunenvs = KNormal.kNorm_funs kfunenvs f in
  assert (Typing.is_equal u ku);
  try
    let kenv, _, kv = Eval.KNorm.eval_program kenv kf in
    new_tyenv, kfunenvs, kenv, asprintf "%a" Pp.pp_ty2 ku, asprintf "%a" Pp.KNorm.pp_value kv
  with
  | Eval.KBlame (_, Pos) -> tyenv, kfunenvs, kenv, asprintf "%a" Pp.pp_ty2 ku, "blame+"
  | Eval.KBlame (_, Neg) -> tyenv, kfunenvs, kenv, asprintf "%a" Pp.pp_ty2 ku, "blame-"

let test_examples =
  let test i cases =
    (string_of_int i) >:: fun ctxt ->
      ignore @@ List.fold_left
        (fun (tyenv, kfunenvs, kenv) (program, expected_ty, expected_kvalue) ->
           let tyenv, kfunenvs, kenv, actual_kty, actual_kvalue = run tyenv kfunenvs kenv program in
           assert_equal ~ctxt:ctxt ~printer:id expected_ty actual_kty;
           assert_equal ~ctxt:ctxt ~printer:id expected_kvalue actual_kvalue;
           tyenv, kfunenvs, kenv
        )
        (let _, tyenv, kfunenvs, kenv = Stdlib.pervasives in tyenv, kfunenvs, kenv)
        cases
  in
  List.mapi test test_cases

let suite = [
  "test_examples">::: test_examples;
]
