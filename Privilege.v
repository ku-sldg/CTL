Require Import Notation.
Require Import BinaryRelations.
Require Import Coq.Strings.String.

Require Export Coq.Strings.String.

Open Scope string_scope.


Inductive privilege : Set :=
  | p_read 
  | p_write.
  (* | exec. *)

Definition comp := string.

Definition access := comp -> privilege -> bool.

Definition allAcc : access := λ _ _, true.

Definition allReadOnly : access := λ _ p,
  match p with 
  | p_read => true 
  | _    => false 
  end.

Definition private (c: comp): access := λ c' _, c =? c'.
  
Close Scope string_scope.