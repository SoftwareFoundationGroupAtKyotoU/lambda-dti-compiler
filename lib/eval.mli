open Syntax
open Utils.Error

exception Blame of range * polarity
exception KBlame of range * polarity

exception Eval_bug of string

module CC : sig
  open Syntax.CC
  
  val eval_program : ?debug:bool -> (tyvar list * value) Environment.t -> program -> (tyvar list * value) Environment.t * id * value
end

module KNorm : sig
  open Syntax.KNorm

  val eval_program : ?debug:bool -> (tyvar list * value) Environment.t -> program -> (tyvar list * value) Environment.t * id * value
end

