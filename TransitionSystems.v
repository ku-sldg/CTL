Require Import Coq.Relations.Relation_Definitions.
Require Import SepLogic.

(* Definition transition A := relation (A * sprop nat). *)
(* A is global state, B is local *)
Definition transition A B := relation (A * B).

(* This is effectively a union *)
(* This mirrors Chlipala's definition of concurrent transitions in FRAP *)
(* Can nested transitions have "globals" for various levels? *)
(* Inductive either_transition {A B} (R: transition A) (Q: transition B) : transition (A * B) :=
  | step_l : forall a a' b s s',
      R (a,s) (a',s') -> either_transition R Q ((a,b),s) ((a',b),s')
  | step_r : forall a b b' s s',
      Q (b,s) (b',s') -> either_transition R Q ((a,b),s) ((a,b'),s'). *)
Inductive either_transition {G A B} (R: transition G A) (Q: transition G B) : transition G (A * B) :=
  | step_l : forall g g' a a' b,
      R (g,a) (g',a') -> either_transition R Q (g,(a,b)) (g',(a',b))
  | step_r : forall g g' a b b',
      Q (g,b) (g',b') -> either_transition R Q (g,(a,b)) (g',(a,b')).
    
(* Definition sprop_union {loc} : sprop loc -> sprop loc -> sprop loc. Admitted. *)
(* Is this a useful abstraction, distinct from either? *)
(* Inductive concurrent_transitions {G A B} (gunion : G -> G -> G) (R: transition G A) (Q: transition G B) : transition G (A * B) :=
  | step_lr   : forall s s', either_transition R Q s s' -> concurrent_transitions gunion R Q s s'
  | step_both : forall g g' g'' a a' b b',
      R (g,a) (g,a') -> 
      Q (g,b) (g,b') -> 
      concurrent_transitions gunion R Q (g,(a,b)) (gunion g' g'', (a',b')). *)
      
Notation "R ⊔ S" := (either_transition R S) (at level 70).
(* Notation "R ∥ S" := (concurrent_transitions R S) (at level 70). *)

(* TODO: non-starving variation. *)
(* Uses the fuel idiom? *)
(* n is the number of steps it can take in a row in one transition *)
(* Inductive either_transition_nostarve {A B} (R: transition A) (Q: transition B) (n m r: nat) : transition (A * B) :=
  | steps_l : forall a a' b s s',
      R (a,s) (a',s') -> either_transition_nostarve R Q n n r ((a,b),s) ((a',b),s')
  | steps_r : forall a b b' s s',
      Q (b,s) (b',s') -> either_transition_nostarve R Q ((a,b),s) ((a,b'),s').
 
Notation "R ⊕ S" := (either_transition_nostarve R S) (at level 70). *)

(* Todo, support hoare logic syntax of relations? *)
Inductive stransition {comp loc A} (R: transition (sprop comp loc) A) : transition (sprop comp loc) A :=
  | frame_rule : forall Q Q' S a a',
      R (Q,a) (Q',a') ->
      (* Nothing "modified" by R free in S? -> *)
      stransition R (Q ** S, a) (Q' ** S, a')
  | sentails_pre : forall Q Q' S a a',
      Q ⊢ S ->
      stransition R (Q,a) (Q',a') ->
      stransition R (S,a) (Q',a')
  | sentails_post : forall Q Q' S a a',
      Q' ⊢ S ->
      stransition R (Q,a) (Q',a') ->
      stransition R (Q,a) (S,a').
