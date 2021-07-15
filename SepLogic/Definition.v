Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import GeneralTactics.

Notation component := nat (only parsing).

Inductive privilege : Set :=
  | read 
  | write 
  | exec.

Definition access component := component -> privilege -> Prop.

Definition access_eq {component} (a1 a2: access component) :=
  forall c p, a1 c p <-> a2 c p.

Theorem access_eq_is_eq {comp}: equivalence (access comp) access_eq.
Proof using.
  split.
  - easy.
  - unfold access_eq.
    intros a1 a2 a3 Hab Hbc.
    intros c p.
    split; intro H.
    + apply Hbc.
      apply Hab.
      assumption.
    + apply Hab.
      apply Hbc.
      assumption.
  - unfold symmetric, access_eq.
    intros x y H c p.
    split; intro H2. 
    + apply H. assumption.
    + apply H. assumption.
Qed.
Lemma access_eq_refl {comp}: reflexive (access comp) access_eq.
Proof.
  exact (equiv_refl _ _ access_eq_is_eq).
Qed.
Lemma access_eq_sym {comp}: symmetric (access comp) access_eq.
Proof.
  exact (equiv_sym _ _ access_eq_is_eq).
Qed.
Lemma access_eq_trans {comp}: transitive (access comp) access_eq.
Proof.
  exact (equiv_trans _ _ access_eq_is_eq).
Qed.

(* TODO: move these definitions *)
Inductive readonly {component} : access component :=
  | ro : forall c, readonly c read.
Inductive private {component} (c: component): access component :=
  | anyPriv : forall (p: privilege), private c c p.

Inductive sprop_atom (comp loc: Set) :=
  | val_at : forall v, loc -> access comp -> v -> sprop_atom comp loc.
Arguments val_at {comp loc v}%type_scope.
Notation "l # a ↦ v" := (val_at l a v) (at level 50).
 
Definition sprop (comp loc: Set) := list (sprop_atom comp loc).

Definition empty {comp loc}: sprop comp loc := nil.
Notation "⟨⟩" := (empty) (at level 0).

Definition sep_con {comp loc} (x y: sprop comp loc) := x ++ y.
Notation "x ** y" := (sep_con x y) (at level 55, right associativity).