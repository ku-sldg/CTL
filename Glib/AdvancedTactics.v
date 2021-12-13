Require Import Notation.
Require Import TacticCombinators.
Require Import GeneralTactics.
Require Import Axioms.

Ltac decompose_products := 
  repeat match goal with 
  | H : exists x, _ |- _ => let x := fresh x in destruct H as [x H]
  | H : {x | _} |- _ => let x := fresh x in destruct H as [x H]
  | H : Σ x, _ |- _ => let x := fresh x in destruct H as [x H]
  | H : _ × _ |- _ => destruct H as [? ?]
  | H : _ /\ _ |- _ => destruct H as [? ?]
  end;
  subst;
  repeat find inject.

Ltac decompose_all := 
  repeat match goal with 
  | H : exists x, _ |- _ => let x := fresh x in destruct H as [x H]
  | H : {x | _} |- _ => let x := fresh x in destruct H as [x H]
  | H : Σ x, _ |- _ => let x := fresh x in destruct H as [x H]
  | H : _ /\ _ |- _ => destruct H as [? ?]
  | H : _ × _ |- _ => destruct H as [? ?]
  | H : _ \/ _ |- _ => destruct H as [H|H]
  end;
  subst;
  repeat find inject.


(* experimental tedious! *)

Ltac _etedious_excl n := 
  match n with 
  | 0 => fail 1 "Ran out of gas"
  | S ?n' => intros; (
      (eauto; easy) +
      (constructor; _etedious_excl n') +
      (econstructor; _etedious_excl n') +
      (find (fun H => inject H || induction H || destruct H); _etedious_excl n') +
      (fail 1 "Cannot solve goal")
    )
  end.

Ltac _tedious_excl n := 
  match n with 
  | 0 => fail 1 "Ran out of gas"
  | S ?n' => intros; (
      (auto; easy) +
      (constructor; _tedious_excl n') +
      (econstructor; _etedious_excl n') +
      (find (fun H => inject H || induction H || destruct H); _tedious_excl n') +
      (fail 1 "Cannot solve goal")
    )
  end.

(* Slows exponentially with gas. Wouldn't suggest higher than 10. *)
Tactic Notation "tedious!" constr(n) :=
  if has_evar goal then 
    _etedious_excl n
  else 
    _tedious_excl n.

Tactic Notation "tedious!" :=
  tedious! 5.



Ltac _ebrute := 
  intros; (
    (eauto; easy) +
    (constructor; _ebrute) +
    (econstructor; _ebrute) +
    (find (fun H => inject H || induction H || destruct H); _ebrute) +
    (fail 1 "Cannot solve goal")
  ).

Ltac _brute := 
  intros; (
    (auto; easy) +
    (constructor; _brute) +
    (econstructor; _brute) +
    (find (fun H => inject H || induction H || destruct H); _brute) +
    (fail 1 "Cannot solve goal")
  ).

Tactic Notation "brute" int_or_var(n) :=
  tryif has_evar goal then 
    (timeout n _ebrute)
  else 
    (timeout n _brute).

