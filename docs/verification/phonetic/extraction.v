(** * OCaml Extraction for Phonetic Rewrite Rules *)

Require Import String List Ascii QArith.
Require Import PhoneticRewrites.rewrite_rules.
Require Import PhoneticRewrites.zompist_rules.

(** ** Extraction Configuration *)

(** Extract to OCaml *)
Require Extraction.
Extraction Language OCaml.

(** Configure extraction for standard library types *)
(** Use standard Coq extraction for most types to avoid type errors *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

(** Note: nat, ascii, and Q will use default Coq extraction *)
(** This ensures type safety, though nat will be a custom OCaml type *)

(** ** Main Extraction *)

(** Note: Extraction will output to the current directory *)
(** The Makefile will handle moving files to extracted/ if needed *)

(** Extract the core phonetic rewrite system *)

(** Import the modules to make names available *)
Import PhoneticRewrites.rewrite_rules.
Import PhoneticRewrites.zompist_rules.ZompistRules.

(** Use Recursive Extraction to automatically pull in all dependencies *)
Recursive Extraction zompist_rule_set apply_rules_seq.

(** End of extraction *)
