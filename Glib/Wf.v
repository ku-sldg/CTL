Require Import Notation.
Require Import Axioms.
Require Import GeneralTactics.
Require Import Gen.

Require Import Coq.Relations.Relation_Definitions.
Require Import Lia.


(* Class to register well_founded relations *)
Class wf {A} (R: relation A) := {get_wf : well_founded R}.

Class has_wf A := {has_wf_R: relation A; has_wf_wf: well_founded has_wf_R}.

Instance wf_has_wf {A} {R: relation A} {wf_inst: wf R} : has_wf A.
  econstructor.
  exact get_wf.
Defined.

(* Tactic Notation "wf_induction" constr(x) uconstr(R) :=
  first [ has_instance wf R
        | fail 1 R "does not have an instance of wf"];
  induction x using (well_founded_induction_type
    (@get_wf _ R (get_instance wf R))).

Tactic Notation "wf_induction" constr(x) uconstr(R)
  "as" simple_intropattern(pat) :=
  first [ has_instance wf R
        | fail 1 R "does not have an instance of wf"];
  induction x as pat using (well_founded_induction_type
    (@get_wf _ R (get_instance wf R))). *)

Tactic Notation "wf_induction" constr(x) uconstr(R) "as" ident(H) :=
  first [ has_instance wf R
        | fail 1 R "does not have an instance of wf"];
  induction x as [x H] using (well_founded_induction_type
    (@get_wf _ R (get_instance wf R))).

Tactic Notation "wf_induction" constr(x) uconstr(R) :=
  let H := fresh "wfIH" in
  wf_induction x R as H.

(* If no relation is given, we try to assume one. This should probably not 
   be relied on, since adding further wf instances could change behavior.
 *)
Tactic Notation "wf_induction" constr(x) :=
  let t := type of x in
  first [ has_instance has_wf t
        | fail 1 "Could not find wf instance associated with" t];
  induction x using (well_founded_induction_type
    (@has_wf_wf _ (get_instance has_wf t)));
  simpl has_wf_R in *.


Instance wf_lt : wf lt.
Proof using.
  constructor.
  intro i.
  gen j := i to (λ j, j <= i) by tedious;
    cbn; revert j.
  induction i.
  - intros * jlt.
    follows inv jlt.
  - intros j jlt.
    constructor.
    intros k klt.
    apply IHi.
    lia.
Qed.


Definition ceiling (n: nat) : relation nat :=
  λ x y, y < x /\ x <= n.

Theorem nat_rect_down (c: nat) : forall P: nat -> Type,
  P c ->
  (forall n, P n -> P (n - 1)) ->
  forall n, n <= c -> P n.
Proof using.
  intros P BH IH n nlt.
  assert (n = c - (c - n)) as -> by lia.
  clear nlt.
  induction (c - n) as [|m].
  - follows replace (c - 0) with c by lia.
  - follows replace (c - S m) with ((c - m) - 1) by lia.
Defined.

Theorem nat_ind_down (c: nat) : forall P: nat -> Prop,
  P c ->
  (forall n, P n -> P (n - 1)) ->
  forall n, n <= c -> P n.
Proof using.
  exact (nat_rect_down c).
Qed.

Instance wf_ceiling {n}: wf (ceiling n).
Proof using.
  constructor.
  intro m.
  gen i := m to (λ j, m <= j) by tedious;
    cbn; revert i.

  destruct classic (m > n) as case.
  { intros * mlt.
    transform case (i > n) by lia.
    constructor.
    intros * [? ?].
    exfalso; lia.
  }
  transform case (m <= n) by lia.

  pattern m.
  apply (nat_ind_down n).
  - intros * nlt.
    constructor.
    intros j [H H'].
    exfalso; lia.
  - intros x H y xlt.
    constructor.
    intros * [? ?].
    apply H.
    lia.
  - assumption.
Qed.


(* List orders *)
Require Import Coq.Lists.List.
Import ListNotations.

(* (proper) prefix ordering *)
Definition lprefix {A} (x l: list A) : Prop :=
  exists y, y <> [] /\ x ++ y = l.

Lemma lprefix_nil {A} : forall l: list A,
  ~ lprefix l [].
Proof using.
  intros * (k & H & H').
  follows apply app_eq_nil in H' as [_ ?].
Qed. 

Instance wf_lprefix {A} : wf (@lprefix A).
Proof using.
  constructor.
  intro l.
  gen k := l to (λ k, lprefix k l \/ k = l) by follows right.
    cbn; revert k.
  induction l.
  - intros k [H|H].
    + contradict H.
      apply lprefix_nil.
    + subst.
      constructor.
      intros * H.
      contradict H.
      apply lprefix_nil.
  - intros k H.
    destruct or H.
Admitted.

(* (proper) suffix ordering *)
Inductive lsuffix {A} : list A -> list A -> Prop :=
  | lsuffix_cons : forall a l,
      lsuffix l (a :: l)
  | lsuffix_step : forall a l1 l2,
      lsuffix l1 l2 ->
      lsuffix l1 (a :: l2).

Instance wf_lsuffix {A} : wf (@lsuffix A).
Proof using.
  constructor.
  intro l.
  gen k := l to (λ k, lsuffix k l \/ k = l) by follows right;
    cbn; revert k.
  induction l.
  - intros k [H| ->].
    + inv H.
    + constructor.
      intros * H.
      inv H.
  - intros k [H| ->].
    + apply IHl.
      follows inv H.
    + constructor.
      intros k H.
      apply IHl.
      follows inv H.
Qed.

(* "subset" ordering *)
(* Check incl. *)

(* length ordering *)
(* Check lel. *)