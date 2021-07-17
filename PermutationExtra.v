Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import GeneralTactics.

(* This alternative notion of a permutation more directly exposes
   the underlying structure
 *)
Inductive perm_trace {A} : list A -> list A -> Prop :=
  | pt_nil : 
      perm_trace [] []
  | pt_step : forall h t t1 t2,
      perm_trace t (t1 ++ t2) ->
      perm_trace (h::t) (t1 ++ h :: t2)
  (* | pt_trans : forall x y z,
      perm_trace x y ->
      perm_trace y z ->
      perm_trace x z *)
.

Lemma pt_step_sym {A}: forall h (t t1 t2: list A),
  perm_trace (t1 ++ t2) t ->
  perm_trace (t1 ++ h :: t2) (h::t).
Proof using.
  intros h t t1 t2 H; revert h t2 t H.
  induction t1; intros.
  - simpl in *.
    fold ([] ++ h :: t).
    constructor.
    assumption.
  - simpl in *.
    invc H.
    eapplyc IHt1 in H3.
    replace (h :: t3 ++ a :: t4) with ((h :: t3) ++ a :: t4) 
      by reflexivity.
    constructor.
    simpl.
    eassumption.
Qed. 

Theorem perm_trace_refl {A}: reflexive (list A) perm_trace.
Proof using.
  intros x.
  induction x.
  - constructor.
  - replace (a :: x) with ([] ++ a :: x) at 2 by reflexivity.
    constructor.
    assumption.
Qed.

Theorem perm_trace_sym {A}: symmetric (list A) perm_trace.
  intros x.
  induction x; intros y H.
  - invc H.
    constructor.
  - invc H.
    applyc IHx in H3.
    apply pt_step_sym.
    assumption.
Qed.

Theorem perm_trace_insert {A}: forall x (a b c d: list A),
  perm_trace (a ++ b) (c ++ d) ->
  perm_trace (a ++ x :: b) (c ++ x :: d).
Proof using.
  intros x a; revert x.
  induction a; intros x b c d H.
  - simpl in *.
    constructor.
    assumption.
  - simpl in *.
    invc H.
    apply (IHa a) in H1.
    rewrite H3 in H1.
Admitted.

Theorem perm_trace_trans {A}: transitive (list A) perm_trace.
  intros x y z Hxy Hyz; revert x Hxy.
  induction Hyz; intros x Hxy.
  - assumption.
  - apply perm_trace_sym in Hxy.
    invc Hxy.
    apply perm_trace_sym in H2.
    apply IHHyz in H2.
    apply perm_trace_insert.
    assumption.
Qed.

Theorem perm_to_trace {A}: forall x y: list A,
  Permutation x y ->
  perm_trace x y.
Proof using.
  intros x y H.
  induction H.
  - constructor.
  - fold ([] ++ x :: l').
    constructor.
    assumption.
  - fold ([x] ++ y :: l).
    constructor.
    simpl.
    apply perm_trace_refl.
  - eapply perm_trace_trans; eassumption.
Qed.

Theorem trace_to_perm {A}: forall x y: list A,
  perm_trace x y ->
  Permutation x y.
Proof using.
  intros x y H.
  induction H.
  - constructor.
  - apply Permutation_cons_app.
    assumption.
Qed.

Lemma Permutation_cons_structure {A}: forall x (y z: list A),
  Permutation (x :: y) z ->
  exists z1 z2,
    z = z1 ++ x :: z2 /\
    Permutation y (z1 ++ z2).
Proof using.
  intros x y z H.
  apply perm_to_trace in H.
  invc H.
  exists t1 t2.
  split. 
  - reflexivity.
  - apply trace_to_perm.
    assumption.
Qed.
