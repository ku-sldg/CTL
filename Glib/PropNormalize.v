Require Import Notation.
Require Import GeneralTactics.
Require Import Axioms.

Create HintDb prop_simpl.

Theorem and_idempotent : forall P: Prop,
  (P /\ P) = P.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite and_idempotent : prop_simpl.

Theorem or_idempotent : forall P: Prop,
  (P \/ P) = P.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite or_idempotent : prop_simpl.

Theorem and_inv : forall P: Prop,
  (P /\ ~P) = False.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite and_inv : prop_simpl.

Theorem or_inv : forall P: Prop,
  (P \/ ~P) = True.
Proof using.
  intros *.
  extensionality.
  after split.
  intro.
  apply classic.
Qed.
Hint Rewrite or_inv : prop_simpl.

Theorem and_id_left : forall P: Prop,
  (True /\ P) = P.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite and_id_left : prop_simpl.

Theorem and_id_right : forall P: Prop,
  (P /\ True) = P.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite and_id_right : prop_simpl.

Theorem or_id_left : forall P: Prop,
  (False \/ P) = P.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite or_id_left : prop_simpl.

Theorem or_id_right : forall P: Prop,
  (P \/ False) = P.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite or_id_right : prop_simpl.

Theorem or_true_left : forall P: Prop,
  (True \/ P) = True.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite or_true_left : prop_simpl.

Theorem or_true_right : forall P: Prop,
  (P \/ True) = True.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite or_true_right : prop_simpl.

Theorem and_false_left : forall P: Prop,
  (False /\ P) = False.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite and_false_left : prop_simpl.

Theorem and_false_right : forall P: Prop,
  (P /\ False) = False.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite and_false_right : prop_simpl.

Theorem impl_refl : forall P: Prop,
  (P -> P) = True.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite impl_refl : prop_simpl.

Theorem impl_true_left : forall P: Prop,
  (True -> P) = P.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite impl_true_left : prop_simpl.

Theorem impl_true_right : forall P: Prop,
  (P -> True) = True.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite impl_true_right : prop_simpl.
 
Theorem impl_false_left : forall P: Prop,
  (False -> P) = True.
Proof using.
  intros *.
  follows extensionality.
Qed.
Hint Rewrite impl_false_left : prop_simpl.


(* Positivity rewrites *)
Hint Rewrite rew_not_not   : prop_simpl.
Hint Rewrite rew_not_and   : prop_simpl.
Hint Rewrite rew_not_or    : prop_simpl.
Hint Rewrite rew_not_all   : prop_simpl.
Hint Rewrite rew_not_ex    : prop_simpl.
Hint Rewrite rew_not_imply : prop_simpl.


(* Agressive rewriting with UIP and propositional extensionality *)

Tactic Notation "simpl!" :=
  cbn;
  repeat (progress crush_eqs; cbn);
  autorewrite with prop_simpl.

Tactic Notation "simpl!" "in" hyp(H) :=
  cbn in H;
  repeat (progress crush_eqs; cbn in H);
  autorewrite with prop_simpl in H.
  
Tactic Notation "simpl!" "in" "*" :=
  cbn in *;
  repeat (progress crush_eqs; cbn in *);
  autorewrite with prop_simpl in *.


(* `with` adds rewriting rule *)

Tactic Notation "simpl!" "with" uconstr(rew) := 
  simpl!;
  repeat (progress rewrite rew; progress simpl!).

Tactic Notation "simpl!" "in" hyp(H) "with" uconstr(rew) := 
  simpl! in H;
  repeat (progress rewrite rew in H; progress simpl! in H).

Tactic Notation "simpl!" "in" "*" "with" uconstr(rew) := 
  simpl! in *;
  repeat (progress rewrite rew in *; progress simpl! in *).
