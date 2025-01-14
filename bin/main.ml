open Format
open Lambda_dti

exception Compile_bad of string

let debug = ref false

let programs = ref [] (*Stdlibのために、要変更*)

let opt_file = ref None

let compile_process progs (_, tyenv, kfunenvs, _) = 
  (* Used in all modes *)
  (*let print f = fprintf std_formatter f in*)
  (* Used in debug mode *)
  let print_debug f = Utils.Format.make_print_debug !debug f in
  let rec to_exp ps = match ps with
    | Syntax.ITGL.Exp e :: [] -> e
    | Syntax.ITGL.LetDecl (x, e) :: t -> Syntax.ITGL.LetExp (Utils.Error.dummy_range, x, e, to_exp t)
    | _ -> raise @@ Compile_bad "exp appear in not only last"
  in let e = Syntax.ITGL.Exp (to_exp (List.rev progs)) in
  begin try
    print_debug "\n========== Compilatopn ==========\n";

    (* Type inference *)
    print_debug "***** Typing *****\n";
    let e, u = Typing.ITGL.type_of_program tyenv e in
    print_debug "e: %a\n" Pp.ITGL.pp_program e;
    print_debug "U: %a\n" Pp.pp_ty u;

    (* NOTE: Typing.ITGL.translate and Typing.CC.type_of_program expect
     * normalized input *)
    let tyenv, e, u = Typing.ITGL.normalize tyenv e u in

    (* Translation *)
    print_debug "***** Cast-insertion *****\n";
    let _, f, u' = Typing.ITGL.translate tyenv e in
    print_debug "f: %a\n" Pp.CC.pp_program f;
    print_debug "U: %a\n" Pp.pp_ty u';
    assert (Typing.is_equal u u');
    let u'' = Typing.CC.type_of_program tyenv f in
    assert (Typing.is_equal u u'');

    (* k-Normalization *)
    print_debug "***** kNormal *****\n";
    let kf, ku, _ = KNormal.kNorm_funs kfunenvs f ~debug:!debug in
    print_debug "kf: %a\n" Pp.KNorm.pp_program kf;
    assert (Typing.is_equal u ku);

    let p = match kf with Syntax.KNorm.Exp e -> e | _ -> raise @@ Compile_bad "kf is not exp" in

    print_debug "***** Closure *****\n";
    let p = Closure.KNorm.toCls_program p in
    print_debug "%a\n" Pp.Cls.pp_program p;

    print_debug "***** toC *****\n";
    let c_code = asprintf "%a" ToC.toC_program p in
    print_debug "%s\n" c_code; c_code
    
  with
  | Failure message -> raise @@ Failure message
  | Typing.Type_error message -> raise @@ Typing.Type_error message
  end

let rec read_eval_print lexbuf env tyenv kfunenvs kenv =
  (* Used in all modes *)
  let print f = fprintf std_formatter f in
  (* Used in debug mode *)
  let print_debug f = Utils.Format.make_print_debug !debug f in
  flush stderr;
  flush stdout;
  if lexbuf.Lexing.lex_curr_p.pos_fname = "" then print "# @?";
  begin try
      (* Parsing *)
      print_debug "***** Parser *****\n";
      let e = Parser.toplevel Lexer.main lexbuf in
      print_debug "e: %a\n" Pp.ITGL.pp_program e;
      programs := e :: !programs;

      (* Type inference *)
      (*print_debug "***** Typing *****\n";
      let e, u = Typing.ITGL.type_of_program tyenv e in
      print_debug "e: %a\n" Pp.ITGL.pp_program e;
      print_debug "U: %a\n" Pp.pp_ty u;

      (* NOTE: Typing.ITGL.translate and Typing.CC.type_of_program expect
       * normalized input *)
      let tyenv, e, u = Typing.ITGL.normalize tyenv e u in

      (* Translation *)
      print_debug "***** Cast-insertion *****\n";
      let new_tyenv, f, u' = Typing.ITGL.translate tyenv e in
      print_debug "f: %a\n" Pp.CC.pp_program f;
      print_debug "U: %a\n" Pp.pp_ty u';
      assert (Typing.is_equal u u');
      let u'' = Typing.CC.type_of_program tyenv f in
      assert (Typing.is_equal u u'');

      (* k-Normalization *)
      print_debug "***** kNormal *****\n";
      let kf, ku, kfunenvs = KNormal.kNorm_funs kfunenvs f ~debug:!debug in
      print_debug "kf: %a\n" Pp.KNorm.pp_program kf;
      assert (Typing.is_equal u ku);

      (* Evaluation *)
      (*print_debug "***** Eval *****\n";
      let env, x, v = Eval.CC.eval_program env f ~debug:!debug in
      print_debug "original :: %a : %a = %a\n"
        pp_print_string x
        Pp.pp_ty2 u
        Pp.CC.pp_value v;*)

      (* Evaluation on kNormalized term *)
      print_debug "***** Eval *****\n";
      let kenv, kx, kv = Eval.KNorm.eval_program kenv kf ~debug:!debug in
      print_debug "k-Normal :: ";
      print_debug "%a : %a = %a\n"
        pp_print_string kx
        Pp.pp_ty2 ku
        Pp.KNorm.pp_value kv;*)

      match e, !opt_file with
        | Syntax.ITGL.Exp _, None -> 
            let c_code = compile_process !programs Stdlib.pervasives in
            programs := [];
            let oc = open_out "result_C/stdout.c" in
            Printf.fprintf oc "%s" c_code;
            close_out oc;
            let _ = Sys.command "gcc result_C/stdout.c lib/cast.c -o result/stdout.out" in
            let _ = Sys.command "result/stdout.out" in
            print "\n";
            read_eval_print lexbuf env (*new_*)tyenv kfunenvs kenv
        | _, None -> read_eval_print lexbuf env (*new_*)tyenv kfunenvs kenv
        | Syntax.ITGL.Exp _, Some f -> 
            let c_code = compile_process !programs Stdlib.pervasives in
            programs := [];
            let oc = open_out ("../result_C/"^f^"_out.c") in
            Printf.fprintf oc "%s" c_code;
            close_out oc;
            let _ = Sys.command ("gcc ../result_C/"^f^"_out.c ../lib/cast.c -o ../result/"^f^".out") in
            let _ = Sys.command ("../result/"^f^".out") in
            print "\n"
        | _, _ -> read_eval_print lexbuf env (*new_*)tyenv kfunenvs kenv
        (*| _, Some f ->
            if lexbuf.lex_eof_reached then
              let c_code = compile_process !programs Stdlib.pervasives in
              let oc = open_out ("../result/"^f^"_out.c") in
              Printf.fprintf oc "%s" c_code;
              close_out oc
            else 
              read_eval_print lexbuf env (*new_*)tyenv kfunenvs kenv*)
    with
    | Failure message ->
      print "Failure: %s\n" message;
      Utils.Lexing.flush_input lexbuf
    | Parser.Error -> (* Menhir *)
      let token = Lexing.lexeme lexbuf in
      print "Parser.Error: unexpected token %s\n" token;
      Utils.Lexing.flush_input lexbuf
    | Typing.Type_error message ->
      print "Type_error: %s\n" message
    (*| Eval.Blame (r, p) -> begin
        match p with
        | Pos -> print "Blame on the expression side:\n%a\n" Utils.Error.pp_range r
        | Neg -> print "Blame on the environment side:\n%a\n" Utils.Error.pp_range r
      end*)
    | Eval.KBlame (r, p) -> begin
        match p with
        | Pos -> print "Blame on the expression side:\n%a\n" Utils.Error.pp_range r
        | Neg -> print "Blame on the environment side:\n%a\n" Utils.Error.pp_range r
      end
    | ToC.ToC_error message ->
      print "%s\n" message
  end;
  (match !opt_file with
    | None -> programs := []; read_eval_print lexbuf env tyenv kfunenvs kenv
    | Some _ ->())

let start file =
  let print_debug f = Utils.Format.make_print_debug !debug f in
  opt_file := file;
  print_debug "***** Lexer *****\n";
  let channel, lexbuf = match file with
    | None ->
        print_debug "Reading from stdin\n%!";
        stdin, Lexing.from_channel stdin
    | Some f ->
        print_debug "Reading from file \"%s\"\n%!" f;
        let channel = open_in f in
        let lexbuf = Lexing.from_channel channel in
        lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = f};
        channel, lexbuf
  in
  let env, tyenv, kfunenvs, kenv = Stdlib.pervasives in
  try
    read_eval_print lexbuf env tyenv kfunenvs kenv
  with
    | Lexer.Eof ->
      (* Exiting normally *)
      close_in channel
    | Stdlib.Stdlib_exit i ->
      (* Exiting with the status code *)
      close_in channel;
      exit i
    | e ->
      (* Unexpected error occurs, close the opened channel *)
      close_in_noerr channel;
      raise e

let () =
  let program = Sys.argv.(0) in
  let usage =
    "Interpreter of the ITGL with dynamic type inference\n" ^
    asprintf "Usage: %s <options> [file]\n" program ^
    "Options: "
  in
  let file = ref None in
  let options = Arg.align [
      ("-d", Arg.Set debug, " Enable debug mode");
    ]
  in
  let parse_argv arg = match !file with
    | None -> file := Some arg
    | Some _ -> raise @@ Arg.Bad "error: only one file can be specified"
  in
  Arg.parse options parse_argv usage;
  start !file
