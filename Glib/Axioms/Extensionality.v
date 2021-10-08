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

Theorem rew_NNPP: forall P: Prop,
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
  (P -> Q) = ~P \/ Q.
Proof using.
  intros *.
  extensionality H.
  - now apply imply_to_or.
  - now apply or_to_imply.
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

