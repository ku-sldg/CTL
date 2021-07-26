Require Import Ctl.Paths.
Require Import Ctl.Definition.
Require Import Ctl.Basic.
Open Scope tprop_scope.

Require Import Tactics.General.
Require Import Tactics.Misc.

(*
Tactic Notation "unfold_timpl" :=
  progress change_no_check (?R @?s ⊨ ?p ⟶ ?q) with (R @s ⊨ p -> R @s ⊨ q).
Tactic Notation "unfold_timpl" "in" hyp(H) :=
  progress change_no_check (?R @?s ⊨ ?p ⟶ ?q) with (R @s ⊨ p -> R @s ⊨ q) in H.

Tactic Notation "unfold_tnot" := 
  progress change_no_check (?R @?s ⊨ ¬?P) with (R @s ⊭ P).
Tactic Notation "unfold_tnot" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ ¬?P) with (R @s ⊭ P) in H.

Tactic Notation "unfold_tconj" := 
  progress change_no_check (?R @?s ⊨ ?P ∧ ?Q) with (R @s ⊨ P /\ R @s ⊨ Q).
Tactic Notation "unfold_tconj" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ ?P ∧ ?Q) with (R @s ⊨ P /\ R @s ⊨ Q) in H.

Tactic Notation "unfold_tbiimpl" := 
  progress change_no_check (?R @?s ⊨ ?P ⟷ ?Q) with (R @s ⊨ P <-> R @s ⊨ Q).
Tactic Notation "unfold_tbiimpl" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ ?P ⟷ ?Q) with (R @s ⊨ P <-> R @s ⊨ Q) in H.

Tactic Notation "unfold_AX" := 
  progress change_no_check (?R @?s ⊨ AX ?P) with (forall s', R s s' -> R @s' ⊨ P).
Tactic Notation "unfold_AX" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ AX ?P) with (forall s', R s s' -> R @s' ⊨ P) in H.

Tactic Notation "unfold_AG" := 
  progress change_no_check (?R @?s ⊨ AG ?P) with 
    (forall n (p: path R n s) s', in_path s' p -> R @s' ⊨ P).
Tactic Notation "unfold_AG" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ AG ?P) with 
    (forall n (p: path R n s) s', in_path s' p -> R @s' ⊨ P) in H.
*)

Tactic Notation "unfold_timpl" :=
  progress change_no_check (?R @?s ⊨ ?p ⟶ ?q) with (R @s ⊨ p -> R @s ⊨ q) +
  rewrite rew_timpl +
  setoid_rewrite rew_timpl.
Tactic Notation "unfold_timpl" "in" hyp(H) :=
  progress change_no_check (?R @?s ⊨ ?p ⟶ ?q) with (R @s ⊨ p -> R @s ⊨ q) in H +
  rewrite rew_timpl in H +
  setoid_rewrite rew_timpl in H.

Tactic Notation "unfold_tnot" :=
  progress change_no_check (?R @?s ⊨ ¬?P) with (R @s ⊭ P) +
  rewrite rew_tnot +
  setoid_rewrite rew_tnot.
Tactic Notation "unfold_tnot" "in" hyp(H) :=
  progress change_no_check (?R @?s ⊨ ¬?P) with (R @s ⊭ P) in H +
  rewrite rew_tnot in H +
  setoid_rewrite rew_tnot in H.

Tactic Notation "unfold_tconj" := 
  progress change_no_check (?R @?s ⊨ ?P ∧ ?Q) with (R @s ⊨ P /\ R @s ⊨ Q) +
  rewrite rew_tconj +
  setoid_rewrite rew_tconj.
Tactic Notation "unfold_tconj" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ ?P ∧ ?Q) with (R @s ⊨ P /\ R @s ⊨ Q) in H +
  rewrite rew_tconj in H +
  setoid_rewrite rew_tconj in H.

Tactic Notation "unfold_tdisj" := 
  progress change_no_check (?R @?s ⊨ ?P ∨ ?Q) with (R @s ⊨ P \/ R @s ⊨ Q) +
  rewrite rew_tdisj +
  setoid_rewrite rew_tdisj.
Tactic Notation "unfold_tdisj" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ ?P ∨ ?Q) with (R @s ⊨ P ∨ R @s ⊨ Q) in H +
  rewrite rew_tdisj in H +
  setoid_rewrite rew_tdisj in H.

Tactic Notation "unfold_tbiimpl" := 
  progress change_no_check (?R @?s ⊨ ?P ⟷ ?Q) with (R @s ⊨ P <-> R @s ⊨ Q) +
  rewrite rew_tbiimpl +
  setoid_rewrite rew_tbiimpl.
Tactic Notation "unfold_tbiimpl" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ ?P ⟷ ?Q) with (R @s ⊨ P <-> R @s ⊨ Q) in H +
  rewrite rew_tbiimpl in H +
  setoid_rewrite rew_tbiimpl in H.

Tactic Notation "unfold_AX" := 
  progress change_no_check (?R @?s ⊨ AX ?P) with (forall s', R s s' -> R @s' ⊨ P) +
  rewrite rew_AX +
  setoid_rewrite rew_AX.
Tactic Notation "unfold_AX" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ AX ?P) with (forall s', R s s' -> R @s' ⊨ P) in H +
  rewrite rew_AX in H +
  setoid_rewrite rew_AX in H.

Tactic Notation "unfold_EX" := 
  progress change_no_check (?R @?s ⊨ EX ?P) with (exists s', R s s' -> R @s' ⊨ P) +
  rewrite rew_EX +
  setoid_rewrite rew_EX.
Tactic Notation "unfold_EX" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ EX ?P) with (exists s', R s s' -> R @s' ⊨ P) in H +
  rewrite rew_EX in H +
  setoid_rewrite rew_EX in H.

Tactic Notation "unfold_AG" := 
  progress change_no_check (?R @?s ⊨ AG ?P) with 
    (forall n (p: path R n s) s', in_path s' p -> R @s' ⊨ P) +
  rewrite rew_AG +
  setoid_rewrite rew_AG.
Tactic Notation "unfold_AG" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ AG ?P) with 
    (forall n (p: path R n s) s', in_path s' p -> R @s' ⊨ P) in H +
  rewrite rew_AG in H +
  setoid_rewrite rew_AG in H.

Tactic Notation "unfold_EG" := 
  progress change_no_check (?R @?s ⊨ EG ?P) with 
    (forall n, exists p: path R n s, forall s', in_path s' p -> R @s' ⊨ P) +
  rewrite rew_EG +
  setoid_rewrite rew_EG.
Tactic Notation "unfold_EG" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ EG ?P) with 
    (forall n, exists p: path R n s, forall s', in_path s' p -> R @s' ⊨ P) in H +
  rewrite rew_EG in H +
  setoid_rewrite rew_EG in H.

Tactic Notation "unfold_AF" := 
  progress change_no_check (?R @?s ⊨ AF ?P) with 
    (exists n, forall p: path R n s, exists s', in_path s' p /\ R @s' ⊨ P) +
  rewrite rew_AF +
  setoid_rewrite rew_AF.
Tactic Notation "unfold_AF" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ AF ?P) with 
    (exists n, forall p: path R n s, exists s', in_path s' p /\ R @s' ⊨ P) in H +
  rewrite rew_AF in H +
  setoid_rewrite rew_AF in H.

Tactic Notation "unfold_EF" := 
  progress change_no_check (?R @?s ⊨ EF ?P) with 
    (exists n (p: path R n s) s', in_path s' p /\ R @s' ⊨ P) +
  rewrite rew_EF +
  setoid_rewrite rew_EF.
Tactic Notation "unfold_EF" "in" hyp(H) := 
  progress change_no_check (?R @?s ⊨ EF ?P) with 
    (exists n (p: path R n s) s', in_path s' p /\ R @s' ⊨ P) in H +
  rewrite rew_EF in H +
  setoid_rewrite rew_EF in H.

(* tintro - intro a timpl *)

Tactic Notation "tintro" := 
  match goal with
  | |- _ @_ ⊨ ¬ _ => unfold_tnot; intro
  | |- _ @_ ⊨ _ ⟶ _ => unfold_timpl; intro
  end.

Tactic Notation "tintro" ident(x) := 
  match goal with
  | |- _ @_ ⊨ ¬ _ => unfold_tnot; intro x
  | |- _ @_ ⊨ _ ⟶ _ => unfold_timpl; intro x
  end.

Tactic Notation "tintros" :=
  repeat tintro.
Tactic Notation "tintros" ident(x1) :=
  tintro x1.
Tactic Notation "tintros" ident(x1) ident(x2) :=
  tintro x1; tintros x2.
Tactic Notation "tintros" ident(x1) ident(x2) ident(x3) :=
  tintro x1; tintros x2 x3.
Tactic Notation "tintros" ident(x1) ident(x2) ident(x3) ident(x4) :=
  tintro x1; tintros x2 x3 x4.
Tactic Notation "tintros" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) :=
  tintro x1; tintros x2 x3 x4 x5.
Tactic Notation "tintros" ident(x1) ident(x2) ident(x3) ident(x4) ident(x6) :=
  tintro x1; tintros x2 x3 x4 x5 x6.


(* tsimpl - simple a tprop *)

Tactic Notation "tsimpl_step" :=
  unfold_timpl +
  unfold_tbiimpl +
  unfold_tnot +
  unfold_AX +
  unfold_EX +
  unfold_AG +
  unfold_EG +
  unfold_AF +
  unfold_EF.

Tactic Notation "tsimpl_step" "in" hyp(H) :=
  unfold_timpl in H +
  unfold_tbiimpl in H +
  unfold_tnot in H +
  unfold_AX in H +
  unfold_EX in H +
  unfold_AG in H +
  unfold_EG in H +
  unfold_AF in H +
  unfold_EF in H.

Tactic Notation "tsimpl" := repeat tsimpl_step.
Tactic Notation "tsimpl" "in" hyp(H) := repeat tsimpl_step in H.
Tactic Notation "tsimpl" "in" "*" :=
  repeat match goal with 
  | H: _ @_ ⊨ _ |- _ => tsimpl in H
  end.

(* tapply: carefully unfolds TProp hypothesis just enough to use apply *)

Ltac _tapply_unfold_step H :=
  match type of H with 
  | _ @_ ⊨ _ ⟶ _ => 
      unfold_timpl in H
  | _ @_ ⊨ ¬ _ =>
      unfold_tnot in H
  | _ @_ ⊨ _ ⟷ _ =>
      unfold_tbiimpl in H
  | _ @_ ⊨ AX _ =>
      unfold_AX in H
  | _ @_ ⊨ AG _ => 
      unfold_AG in H
  end + 
  unfold_timpl in H +
  unfold_tnot in H +
  unfold_tbiimpl in H +
  unfold_AX in H +
  unfold_AG in H.

Ltac _tapply_aux H :=
  apply H + (_tapply_unfold_step H; _tapply_aux H).

Ltac _tapply_aux_in H H2 :=
  apply H in H2 + (_tapply_unfold_step H; _tapply_aux_in H H2).

Ltac _etapply_aux H :=
  eapply H + (_tapply_unfold_step H; _etapply_aux H).

Ltac _etapply_aux_in H H2 :=
  eapply H in H2 + (_tapply_unfold_step H; _etapply_aux_in H H2).


Tactic Notation "tapply" uconstr(c) :=
  let Htemp := fresh in 
  eset (Htemp := c);
  _tapply_aux Htemp;
  clear Htemp.

Tactic Notation "tapply" uconstr(c) "in" hyp(H) :=
  let Htemp := fresh in 
  eset (Htemp := c);
  _tapply_aux_in Htemp H;
  clear Htemp.

Tactic Notation "etapply" uconstr(c) :=
  let Htemp := fresh in 
  eset (Htemp := c);
  _etapply_aux Htemp;
  clear Htemp.

Tactic Notation "etapply" uconstr(c) "in" hyp(H) :=
  let Htemp := fresh in 
  eset (Htemp := c);
  _etapply_aux_in Htemp H;
  clear Htemp.

Tactic Notation "tapplyc" hyp(H) :=
  tapply H; clear H.
Tactic Notation "tapplyc" hyp(H) "in" hyp(H2) :=
  tapply H in H2; clear H.
Tactic Notation "etapplyc" hyp(H) :=
  etapply H; clear H.
Tactic Notation "etapplyc" hyp(H) "in" hyp(H2) :=
  etapply H in H2; clear H.
