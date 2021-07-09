Require Import Ctl.Paths.
Require Import Ctl.Definition.

Require Import GeneralTactics.

(* tapply: carefully unfolds TProp hypothesis just enough to use apply *)

Tactic Notation "unfold_TImpl" :=
  change_no_check (?R;?s ⊨ ?p --> ?q) with (R;s ⊨ p -> R;s ⊨ q).
Tactic Notation "unfold_TImpl" "in" hyp(H) :=
  change_no_check (?R;?s ⊨ ?p --> ?q) with (R;s ⊨ p -> R;s ⊨ q) in H.

Tactic Notation "unfold_TNot" := 
  change_no_check (?R;?s ⊨ ¬?P) with (R;s ⊭ P).
Tactic Notation "unfold_TNot" "in" hyp(H) := 
  change_no_check (?R;?s ⊨ ¬?P) with (R;s ⊭ P) in H.

Ltac tapply_normalize H :=
  repeat unfold_TImpl in H;
  unfold_TNot in H.

Tactic Notation "tapply" uconstr(c) :=
  let Htemp := fresh in 
  eset (Htemp := c);
  tapply_normalize Htemp;
  apply Htemp;
  clear Htemp.

Tactic Notation "tapply" uconstr(c) "in" hyp(H) :=
  let Htemp := fresh in 
  eset (Htemp := c);
  tapply_normalize Htemp;
  apply Htemp in H;
  clear Htemp.

Tactic Notation "etapply" uconstr(c) :=
  let Htemp := fresh in 
  eset (Htemp := c);
  tapply_normalize Htemp;
  eapply Htemp;
  clear Htemp.

Tactic Notation "etapply" uconstr(c) "in" hyp(H) :=
  let Htemp := fresh in 
  eset (Htemp := c);
  tapply_normalize Htemp;
  eapply Htemp in H;
  clear Htemp.

Tactic Notation "tapplyc" hyp(H) :=
  tapply H; clear H.
Tactic Notation "tapplyc" hyp(H) "in" hyp(H2) :=
  tapply H in H2; clear H.
Tactic Notation "etapplyc" hyp(H) :=
  etapply H; clear H.
Tactic Notation "etapplyc" hyp(H) "in" hyp(H2) :=
  etapply H in H2; clear H.

(* Folds to roll-back over-reduction *)

Tactic Notation "fold_TNot" :=
  match goal with 
  | |- context[?R;?s ⊭ ?P] =>
      unfold tEntails; fold (R;s ⊨ ¬P)
  end.
Tactic Notation "fold_TNot" "in" hyp(H) :=
  match type of H with 
  | context[?R;?s ⊭ ?P] =>
      unfold tEntails in H; fold (R;s ⊨ ¬P) in H
  end.

Tactic Notation "fold_TConj" :=
  match goal with 
  | |- context[?R;?s ⊨ ?P /\ ?R;?s ⊨ ?Q] =>
      unfold tEntails; fold (R;s ⊨ P ∧ Q)
  end.
Tactic Notation "fold_TConj" "in" hyp(H) :=
  match type of H with 
  | context[?R;?s ⊨ ?P /\ ?R;?s ⊨ ?Q] =>
      unfold tEntails in H; fold (R;s ⊨ P ∧ Q) in H
  end.

Tactic Notation "fold_TDisj" :=
  match goal with 
  | |- context[?R;?s ⊨ ?P \/ ?R;?s ⊨ ?Q] =>
      unfold tEntails; fold (R;s ⊨ P ∨ Q)
  end.
Tactic Notation "fold_TDisj" "in" hyp(H) :=
  match type of H with 
  | context[?R;?s ⊨ ?P \/ ?R;?s ⊨ ?Q] =>
      unfold tEntails in H; fold (R;s ⊨ P ∨ Q) in H
  end.

Tactic Notation "fold_TImpl" :=
  match goal with 
  | |- context[?R;?s ⊨ ?P -> ?R;?s ⊨ ?Q] =>
      unfold tEntails; fold (R;s ⊨ P --> Q)
  end.
Tactic Notation "fold_TImpl" "in" hyp(H) :=
  match type of H with 
  | context[?R;?s ⊨ ?P -> ?R;?s ⊨ ?Q] =>
      unfold tEntails in H; fold (R;s ⊨ P --> Q) in H
  end.

Tactic Notation "fold_AX" :=
  match goal with 
  | |- context[forall s', ?R ?s s' -> ?R;s' ⊨ ?P] =>
      unfold tEntails; fold (R;s ⊨ AX P)
  end.
Tactic Notation "fold_AX" "in" hyp(H) :=
  match type of H with 
  | context[forall s', ?R ?s s' -> ?R;s' ⊨ ?P] =>
      unfold tEntails in H; fold (R;s ⊨ AX P) in H
  end.

Tactic Notation "fold_EX" :=
  match goal with 
  | |- context[exists s', ?R ?s s' -> ?R;s' ⊨ ?P] =>
      unfold tEntails; fold (R;s ⊨ EX P)
  end.
Tactic Notation "fold_EX" "in" hyp(H) :=
  match type of H with 
  | context[exists s', ?R ?s s' -> ?R;s' ⊨ ?P] =>
      unfold tEntails in H; fold (R;s ⊨ EX P) in H
  end.

Tactic Notation "fold_AG" :=
  match goal with 
  | |- context[forall n (p: path ?R ?s n) s', in_path s' p -> ?R;s' ⊨ ?P] =>
      unfold tEntails; fold (R;s ⊨ AG P)
  end.
Tactic Notation "fold_AG" "in" hyp(H) :=
  match type of H with 
  | context[forall n (p: path ?R ?s n) s', in_path s' p -> ?R;s' ⊨ ?P] =>
      unfold tEntails in H; fold (R;s ⊨ AG P) in H
  end.

Tactic Notation "fold_EG" :=
  match goal with 
  | |- context[forall n, exists p: path ?R ?s n, forall s', in_path s' p -> ?R;s' ⊨ ?P] =>
      unfold tEntails; fold (R;s ⊨ EG P)
  end.
Tactic Notation "fold_EG" "in" hyp(H) :=
  match type of H with 
  | context[forall n, exists p: path ?R ?s n, forall s', in_path s' p -> ?R;s' ⊨ ?P] =>
      unfold tEntails in H; fold (R;s ⊨ EG P) in H
  end.

Tactic Notation "fold_AF" :=
  match goal with 
  | |- context[exists n, forall p: path ?R ?s n, exists s', in_path s' p /\ ?R;s' ⊨ ?P] =>
      unfold tEntails; fold (R;s ⊨ AF P)
  end.
Tactic Notation "fold_AF" "in" hyp(H) :=
  match type of H with 
  | context[exists n, forall p: path ?R ?s n, exists s', in_path s' p /\ ?R;s' ⊨ ?P] =>
      unfold tEntails in H; fold (R;s ⊨ AF P) in H
  end.
  
Tactic Notation "fold_EF" :=
  match goal with 
  | |- context[exists n (p: path ?R ?s n) s', in_path s' p /\ ?R;s' ⊨ ?P] =>
      unfold tEntails; fold (R;s ⊨ EF P)
  end.
Tactic Notation "fold_EF" "in" hyp(H) :=
  match type of H with 
  | context[exists n (p: path ?R ?s n) s', in_path s' p /\ ?R;s' ⊨ ?P] =>
      unfold tEntails in H; fold (R;s ⊨ EF P) in H
  end.

Tactic Notation "fold_tEntails" :=
  match goal with 
  | |- context[(fix f _ _ _ tp {struct tp} := _) ?state] =>
      fold (@tEntails state)
  end.

Tactic Notation "fold_tEntails" "in" hyp(H) :=
  match goal with 
  | |- context[(fix f _ _ _ tp {struct tp} := _) ?state] =>
      fold (@tEntails state) in H
  end.

Tactic Notation "fold_TProp" := intros_do_revert (
  fold_TNot +
  fold_TConj +
  fold_TDisj +
  fold_TImpl +
  fold_AX +
  fold_EX +
  fold_AG +
  fold_EG +
  fold_AF +
  fold_EF +
  fold_tEntails
).

(* TODO: consider application of intros_do_revert to a hypothesis *)
Tactic Notation "fold_TProp" "in" hyp(H) :=
  fold_TNot in H +
  fold_TConj in H +
  fold_TDisj in H +
  fold_TImpl in H +
  fold_AX in H +
  fold_EX in H +
  fold_AG in H +
  fold_EG in H +
  fold_AF in H +
  fold_EF in H +
  fold_tEntails in H.

(* tspecialize: like specialize, but rolls-back over-reduction of TProps *)
(* TODO: rewrite to just unfold 1-step if no forall-binder *)

(* If simpl isn't called before specialize, and specializable binder isn't visible,
   then specialize will over-evaluate before specializing *)
Tactic Notation "tspecialize" hyp(H) uconstr(a) :=
  (* simpl in H; specialize (H a). *)
  simpl in H; specialize (H a); repeat fold_TProp in H.
Tactic Notation "tspecialize" hyp(H) uconstr(a) uconstr(b) :=
  tspecialize H a;
  tspecialize H b.
Tactic Notation "tspecialize" hyp(H) uconstr(a) uconstr(b) uconstr(c) :=
  tspecialize H a b;
  tspecialize H c.
Tactic Notation "tspecialize" hyp(H) uconstr(a) uconstr(b) uconstr(c) uconstr(d) :=
  tspecialize H a b c;
  tspecialize H d.
