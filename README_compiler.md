# lambda-dti-compiler
## Source
https://github.com/SoftwareFoundationGroupAtKyotoU/lambda-dti-compiler.git

## Requirements
- opam 2.0.0+
- OCaml 4.03.0+
- Dune 2.0.0+ (formerly known as Jbuilder)
- Menhir
- Boehm GC (show below)
- OUnit 2 (optional for running unit tests)

## Installing Bohem GC
Download gc-(version).tar.gz from https://www.hboehm.info/gc/.

Unpack gc-(version).tar.gz and enter the newly created directory.

Install Boehm GC with the following commands:
```console
./configure --prefix=/mnt/c/gc
make
make check
make install
```

## Getting started
In the "/lambda-dti-compiler" directory:
```console
eval $(opam env)
dune build
./_build/default/bin/main.exe
```
Run `$ ./_build/default/bin/main.exe --help` for command line options.

(Optional) Run the following command to install the application:
```
dune install
ldti
```

When you want to input some code file , say "hoge.ml", to ldti, enter sub-directory of "/lambda-dti-compiler" and put the name as argument of "ldti".
```console
# in the "/lambda-dti-compiler" directory
mkdr fuga
cd fuga
ldti hoge.ml
```

## Tips
### Running tests
```console
cd compile_test
./dotests.sh
```

### Debug mode
By enabling the debug mode, our interpreter show various messages to stderr.
```console
ldti -d
```

## Syntax
### Top-level
- Let declaration: `let x ... = e;;`
- Recursion declaration: `let rec f x ... = e;;`
- Expression: `e;;`

### Expressions `e`
- Variables: lowercase alphabet followed by lowercase alphabets, numbers, `_`, or `'`
- Constants:
  - Integers: `0`, `1`, `2`, ...
  - Booleans: `true`, `false`
  - Unit: `()`
- Unary operators for integers: `+`,  `-`
- Binary operators (from higher precedence to lower precedence):
  - Integer multiplication, division, remainder (left): `*`, `/`, `mod`
  - Integer addition, subtraction (left): `+`, `-`
  - Integer comparators (left): `=`, `<>`, `<`, `<=`, `>`, `>=`
  - Boolean and (right): `&&`
  - Boolean or (right): `||`
- Abstraction:
  - Simple: `fun x -> e`
  - Multiple parameters: `fun x y z ... -> e`
  - With type annotations: `fun (x: U1) y (z: U3) ...: U -> e`
- Application: `e1 e2`
- Let expression:
  - Simple: `let x = e1 in e2`
  - Multiple parameters: `let x y z ... = e1 in e2`
  - With type annotations: `let (x:U1) y (z: U3) ... : U ... = e1 in e2`
- Recursion (requires at least one parameter):
  - Simple: `let rec f x = e1 in e2`
  - Multiple parameters: `let rec f x y z ... = e1 in e2`
  - With type annotations: `let rec f (x: U1) y (z: U3) ... : U = e1 in e2`
- If-then-else expression: `if e1 then e2 else e3`
- Sequence of expressions: `e1; e2`
- Type ascription: `(e : U)`

### Types `U`
- Dynamic type: `?`
- Base types: `bool`, `int`, and `unit`
- Function type: `U -> U`
- Type variables: `'a`, `'b`, ...

### Comments
- Simple: `(* comments *)`
- Nested comments: `(* leave comments here (* nested comments are also supported *) *)`

## Standard library
Some useful functions and values are available:
```
# is_bool;;
- : ? -> bool = <fun>
# is_int;;
- : ? -> bool = <fun>
# is_unit;;
- : ? -> bool = <fun>
# is_fun;;
- : ? -> bool = <fun>

# succ;;
- : int -> int = <fun>
# pred;;
- : int -> int = <fun>
# max;;
- : int -> int -> int = <fun>
# min;;
- : int -> int -> int = <fun>
# abs;;
- : int -> int = <fun>
# max_int;;
- : int = 4611686018427387903
# min_int;;
- : int = -4611686018427387904

# not;;
- : bool -> bool = <fun>

# print_bool;;
- : bool -> unit = <fun>
# print_int;;
- : int -> unit = <fun>
# print_newline;;
- : unit -> unit = <fun>

# ignore;;
- : 'a -> unit = <fun>

# exit;;
- : int -> unit = <fun>
```

## Examples
You can check more examples in `sample.ldti` and `test/test_examples.ml`.
```
(* Simple examples which use the dynamic type *)
# (fun (x:?) -> x + 2) 3;;
- : int = 5

# (fun (x:?) -> x + 2) true;;
Blame on the expression side:
line 2, character 14 -- line 2, character 15

# (fun (x:?) -> x) (fun y -> y);;
- : ? = <fun>: ? -> ? => ?

(* DTI: a type of y is instantiated to int *)
# (fun (x:?) -> x 2) (fun y -> y);;
- : ? = 2: int => ?

(* DTI: a type of x is instantiated to X1->X2 where X1 and X2 are fresh,
   then X1 and X2 are instantiated to int *)
# (fun (f:?) -> f 2) ((fun x -> x) ((fun (y:?) -> y) (fun z -> z + 1)));;
- : ? = 3: int => ?

(* DTI: a type of x is instantiated to unit, then raises blame
   because a cast "true: bool => ? => unit" fails *)
# (fun (f:?) -> f (); f true) (fun x -> x);;
Blame on the environment side:
line 6, character 29 -- line 6, character 39

(* Let polymorphism *)
# let id x = x;;
id : 'a -> 'a = <fun>

# let dynid (x:?) = x;;
dynid : ? -> ? = <fun>

(* succ is in the standard library *)
# succ;;
- : int -> int = <fun>

# (fun (f:?) -> f 2) (id (dynid succ));;
- : ? = 3: int => ?

# (fun (f:?) -> f true) (id (dynid succ));;
Blame on the environment side:
line 11, character 33 -- line 11, character 37

(* A polymorphic function which does not behave parametric *)
# let succ_non_para x = 1 + dynid x;;
succ_non_para : 'a -> int = <fun>

(* Returns a value when applied to an interger value *)
# succ_non_para 3;;
- : int = 4

(* Returns a value when applied to a non-interger value *)
# succ_non_para true;;
Blame on the expression side:
line 12, character 26 -- line 12, character 33

(* "let x = v in e" and "e[x:=v]" should behave the same way *)
# (fun x -> 1 + dynid x) 3;;
- : int = 4

(* The following example uses ν during the evaluation *)
# let nu_fun x = ((fun y -> y): ? -> ?) x;;
nu_fun : 'a -> ? = <fun>

(* The following expression is translated into "nu_fun[unit,ν]; nu_fun[int,ν];;"
   and returns a value *)
# nu_fun (); nu_fun 3;;
- : ? = 3: int => ?

(* Recursion *)
# let rec sum (n:?) = if n < 1 then 0 else n + sum (n - 1);;
sum : ? -> int = <fun>

# sum 100;;
- : int = 5050

# sum true;;
Blame on the expression side:
line 18, character 23 -- line 18, character 24

# exit 0;;
```

## Contents
- `bin`: Entry point of the interpreter
- `lib`: Implementation of the calculus
- `test`: Unit tests

