Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlIntConv.
Require Import Ascii.
Require Import String.

Axiom caml_string: Type.
Extract Inlined Constant caml_string => "string".

Axiom caml_string_eq_dec:
 forall (a b: caml_string),
  {a = b} + {a <> b}.
Extract Inlined Constant caml_string_eq_dec => "(function a -> function b -> a = b)".

Axiom camlstring_of_coqstring: string -> caml_string.
Extract Inlined Constant camlstring_of_coqstring =>
  "(function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)".

Axiom regexp_t: Type.

Axiom regexp: caml_string -> regexp_t.
Extract Inlined Constant regexp => "Str.regexp".

Axiom reg_split: regexp_t -> caml_string -> list caml_string.
Extract Inlined Constant reg_split => "Str.split".

Axiom global_replace: regexp_t -> caml_string -> caml_string -> caml_string.
Extract Inlined Constant global_replace => "Str.global_replace".

Axiom string_match: regexp_t -> caml_string -> int -> bool.
Extract Inlined Constant string_match => "Str.string_match".