Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlIntConv.
Require Import ZArith.
Require Import String.

Require Import OurString.


Module Pp.
  Axiom std_ppcmds: Type.

  Axiom str: caml_string -> std_ppcmds.
  Extract Inlined Constant str => "Pp.str".

  Axiom tab: std_ppcmds.
  Extract Inlined Constant tab => "(Pp.tab ())".

  Axiom fnl: std_ppcmds.
  Extract Inlined Constant fnl => "(Pp.fnl ())".

  Axiom concat: std_ppcmds -> std_ppcmds -> std_ppcmds.
  Extract Inlined Constant concat => "(++)".

  Axiom pp_int: int -> std_ppcmds.
  Extract Inlined Constant pp_int => "Pp.int".
End Pp.
