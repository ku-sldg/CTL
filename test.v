Require Import temporal_logic.
Require Import my_tactics.

(*
Proof goals:
- keys are secure
  - up to effectiveness of measurements
  - either provably private/separated, or detectably exposed
- attestation evidence is trustworthy
  - i.e., measurements accurately reflect state of system
  - based on: 
    - security of keys and AMs (no deliberate lies)
    - soundness of Copland semantics

*)

Notation component := nat (only parsing).
Notation resource := nat (only parsing).

Inductive privilege : Set :=
  | read 
  | write 
  | exec.

(* Separate static and dynamic access? *)
(* Axiom access : component -> resource -> privilege -> Prop. *)

Definition specification : Set := component * resource * privilege.
