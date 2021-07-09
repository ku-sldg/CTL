Require Import Coq.Relations.Relation_Definitions.
Require Import SepLogic.

(* Record state A B := mkState {global : A; local : B}.
Definition transition A B := relation (state A B). *)

Definition transition A B := relation (A * B).

(* This mirrors Chlipala's definition of concurrent transitions in FRAP *)
(* Can nested transitions have "globals" for various levels? *)
Inductive either_transition {G A B} (R: transition G A) (Q: transition G B) : transition G (A * B) :=
  | step_l : forall g g' a a' b,
      R (g,a) (g',a') -> either_transition R Q (g,(a,b)) (g',(a',b))
  | step_r : forall g g' a b b',
      Q (g,b) (g',b') -> either_transition R Q (g,(a,b)) (g',(a,b')).
    
Notation "R ⊔ S" := (either_transition R S) (at level 70).

(* Todo, support hoare logic syntax of relations? *)
Inductive sentails_clos {comp loc A} (R: transition (sprop comp loc) A) : transition (sprop comp loc) A :=
  | sentails_noframe : forall x x' y y' a a',
      x' ⊢ x  ->
      y  ⊢ y' ->
      R (x,a) (y,a') ->
      sentails_clos R (x',a) (y',a')
  (* | sentails_frame : forall x x' y y' a a' z,
      x' ⊢ x  ->
      y  ⊢ y' ->
      R (x,a) (y,a') ->
      separate x z ->
      separate y z ->
      sentails_clos R (x' ** z, a) (y' ** z, a') *)
  | sentails_frame : forall x x' y y' a a' z,
      x' ** z ⊢ x ** z ->
      y ** z ⊢ y' ** z ->
      R (x,a) (y,a') ->
      sentails_clos R (x' ** z, a) (y' ** z, a')
  .
