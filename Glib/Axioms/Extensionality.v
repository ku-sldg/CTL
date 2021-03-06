Require Import Coq.Logic.ClassicalFacts.

Require Import Notation.
Require Import GeneralTactics.
Require Import Axioms.Classical.

Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.PropExtensionality.

(* Modified from `Coq.Logic.FunctionalExtensionality` to include propositional
   extensionality
 *)
Tactic Notation "extensionality" :=
  match goal with
    [ |- ?X = ?Y ] =>
    (apply (propositional_extensionality X Y) ||
     apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y) ||
     apply forall_extensionalityP ||
     apply forall_extensionalityS ||
     apply forall_extensionality)
  end.

Tactic Notation "extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
    ((apply (propositional_extensionality X Y); split) ||
     apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y) ||
     apply forall_extensionalityP ||
     apply forall_extensionalityS ||
     apply forall_extensionality) ; intro x
  end.

Tactic Notation "extensionality" ident(x0) ident(x1) :=
  extensionality x0; extensionality x1.
Tactic Notation "extensionality" ident(x0) ident(x1) ident(x2) :=
  extensionality x0 x1; extensionality x2.
Tactic Notation "extensionality" ident(x0) ident(x1) ident(x2) ident(x3) :=
  extensionality x0 x1 x2; extensionality x3.


(* Note, LEM and prop extensionality would also follow from assuming 
   degeneracy. Doing so would lessen our number of axioms. However, 
   having both LEM and prop extensionality axiomitzed individually is 
   a better separation of concerns.
 *)
Theorem prop_degeneracy : forall A: Prop, 
  A = True \/ A = False.
Proof using.
  apply prop_ext_em_degen.
  - exact propositional_extensionality.
  - exact classic.
Qed.

Lemma true_neq_false : True <> False.
Proof using.
  intro H.
  now induction H.
Qed.

Lemma provable_is_true : forall A: Prop,
  A = (A = True).
Proof using.
  intros *.
  extensionality H.
  - now (destruct (prop_degeneracy A); subst).
  - symmetry in H.
    now induction H.
Qed.

Lemma provable_contradiction_is_false : forall A: Prop,
  (~A) = (A = False).
Proof using.
  intros *.
  extensionality H.
  - now (destruct (prop_degeneracy A); subst).
  - intros ?.
    now induction H.
Qed.

Lemma false_is_exfalso : False = forall P: Prop, P.
Proof using.
  extensionality; split; intros ?.
  - contradiction.
  - assumption!.
Qed.

(* convenient rewrite rules from LEM + prop extensionality *)

Theorem rew_and_comm : forall P Q: Prop,
  (P /\ Q) = (Q /\ P).
Proof using.
  intros *.
  follows extensionality.
Qed.

Theorem rew_and_assoc : forall P Q R: Prop,
  ((P /\ Q) /\ R) = (P /\ Q /\ R).
Proof using.
  intros *.
  follows extensionality.
Qed.

Theorem rew_or_comm : forall P Q: Prop,
  (P \/ Q) = (Q \/ P).
Proof using.
  intros *.
  follows extensionality.
Qed.

Theorem rew_or_assoc : forall P Q R: Prop,
  ((P \/ Q) \/ R) = (P \/ Q \/ R).
Proof using.
  intros *.
  follows extensionality.
Qed.

Theorem rew_not_not: forall P: Prop,
  (~~P) = P.
Proof using.
  intros *.
  extensionality.
  split.
  - apply NNPP.
  - auto.
Qed.

Theorem rew_not_and : forall P Q: Prop,
  (~ (P /\ Q)) = ~P \/ ~Q.
Proof using.
  intros *.
  extensionality H.
  - now apply not_and_or.
  - now apply or_not_and.
Qed.

Theorem rew_not_or : forall P Q: Prop,
  (~ (P \/ Q)) = ~P /\ ~Q.
Proof using.
  intros *.
  extensionality H.
  - now apply not_or_and.
  - now apply and_not_or.
Qed.

Theorem rew_imply_or : forall P Q: Prop,
  (P -> Q) = (~P \/ Q).
Proof using.
  intros *.
  extensionality H.
  - now apply imply_to_or.
  - now apply or_to_imply.
Qed.

Corollary rew_imply_or' : forall P Q: Prop,
  (P -> Q) = (Q \/ ~P).
Proof using.
  intros *.
  rewrite rew_or_comm.
  apply rew_imply_or.
Qed.

Theorem rew_not_imply : forall P Q: Prop,
  (~ (P -> Q)) = (P /\ ~Q).
Proof using.
  intros *.
  rewrite <- (rew_not_not P) at 2.
  rewrite <- rew_not_or.
  f_equal.
  apply rew_imply_or.
Qed.

Theorem rew_not_all : forall U (P:U -> Prop),
  (~ forall n, P n) = exists n, ~ P n.
Proof using.
  intros *.
  extensionality H.
  - now apply not_all_ex_not.
  - now apply ex_not_not_all.
Qed.

Theorem rew_not_ex : forall U (P:U -> Prop),
  (~ exists n, P n) = forall n, ~ P n.
Proof using.
  intros *.
  extensionality H.
  - now apply not_ex_all_not.
  - now apply all_not_not_ex.
Qed.

Create HintDb positivity.
Hint Rewrite rew_not_not   : positivity.
Hint Rewrite rew_not_and   : positivity.
Hint Rewrite rew_not_or    : positivity.
Hint Rewrite rew_not_all   : positivity.
Hint Rewrite rew_not_ex    : positivity.
Hint Rewrite rew_not_imply : positivity.

Tactic Notation "positivity" :=
  autorewrite with positivity.

Tactic Notation "positivity" "in" hyp(H) :=
  autorewrite with positivity in H.

Tactic Notation "positivity" "in" "*" :=
  positivity;
  repeat find (fun H => positivity in H).


Lemma sig_eq : forall A (P Q: A -> Prop),
  P = Q -> 
  {x | P x} = {x | Q x}.
Proof using.
  now intros * ->.
Qed.

Corollary sig_eq_ext : forall A (P Q: A -> Prop),
  (forall x, P x <-> Q x) -> 
  {x | P x} = {x | Q x}.
Proof using.
  intros * ?.
  apply sig_eq.
  extensionality.
  intros ?.
  now extensionality.
Qed.

Lemma exist_eq_ext : forall A (P: A -> Prop) x y p q,
  (x = y) = (exist P x p = exist P y q).
Proof using.
  intros *.
  extensionality; split.
  - apply exist_eq.
  - now intros [=]. 
Qed.

Lemma exist_eq_ext' : forall A (P: A -> Prop) (x y: {a | P a}),
  (proj1_sig x = proj1_sig y) = (x = y).
Proof using.
  intros *.
  destruct x, y.
  apply exist_eq_ext.
Qed.


Theorem dep_fun_neq_witness : forall (A: Type) (B: A -> Type) (f g: ?? a, B a),
  f <> g -> exists x, f x <> g x.
Proof using.
  intros * Hneq.
  rewrite <- rew_not_all.
  intro contra.
  apply Hneq.
  now extensionality.
Qed.

Corollary fun_neq_witness : forall A B (f g: A -> B),
  f <> g -> exists x, f x <> g x.
Proof using.
  intros *.
  now apply dep_fun_neq_witness.
Qed.


Theorem predicate_neq_bot_witness : forall A (P: A -> Prop),
  P <> (?? _, False) ->
  exists a, P a.
Proof using.
  intros * Hneq.
  apply fun_neq_witness in Hneq as [a Hneq].
  exists a.
  contradict goal.
  applyc Hneq.
  now rewrite <- provable_contradiction_is_false.
Qed.

Theorem types_neq : forall P Q: Type,
  ((P -> Q) -> False) -> P <> Q.
Proof using.
  intros * ? ->.
  auto.
Qed.

Theorem sets_neq : forall P Q: Set,
  ((P -> Q) -> False) -> P <> Q.
Proof using.
  intros * ? ->.
  auto.
Qed.

Theorem props_neq : forall P Q: Prop,
  ~ (P -> Q) -> P <> Q.
Proof using.
  intros * ? ->.
  auto.
Qed.

Goal unit <> Empty_set.
  apply sets_neq.
  intro H.
  destruct (H tt).
Qed.
