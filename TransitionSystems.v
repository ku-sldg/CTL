Require Import BinaryRelations.

(* A transition relation over a global and local state *)
Definition state_trans A B := relation (A * B).

(* This mirrors Chlipala's definition of concurrent transitions in FRAP *)
Inductive either_trans {G A B} (R: state_trans G A) (Q: state_trans G B)
  : state_trans G (A * B) :=
  | step_l : forall g g' a a' b,
      R (g,a) (g',a') -> either_trans R Q (g,(a,b)) (g',(a',b))
  | step_r : forall g g' a b b',
      Q (g,b) (g',b') -> either_trans R Q (g,(a,b)) (g',(a,b')).
    
Notation "R ⊔ S" := (either_trans R S) (at level 70).
