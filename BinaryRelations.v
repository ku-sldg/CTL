Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Lists.List.

Require Import Setoid.
Require Import Psatz.
Require Import Tactics.General.

Definition is_serial {A} (R: relation A) := forall a, exists b, R a b.
Definition serial A := {R: relation A | is_serial R}.

(* Definition is_serialT {A} (R: relation A) := forall a, {b | R a b}. *)
(* Definition serialT A := {R: relation A & is_serialT R}. *)
Definition serial_witness {A} (R: relation A) := forall a, {b | R a b}.
Definition serialT A := {R: relation A & serial_witness R}.

Definition reachable {A} (R: relation A) (l: list A) (b: A) := 
  exists a, In a l /\ clos_refl_trans_n1 A R a b.

Definition is_serial_from {A} (R: relation A) s := forall s', 
  clos_refl_trans A R s s' ->
  exists s'', R s' s''.

Definition serial_from_witness {A} (R: relation A) s := forall s',
  clos_refl_trans A R s s' ->
  {s''| R s' s''}.

Inductive steps : nat -> forall {A}, relation A -> relation A :=
  | steps_one   : forall {A} (R: relation A) x y,
      R x y -> steps 1 R x y
  | steps_multi : forall {A} n (R: relation A) x y z,
      steps n R x y -> R y x -> steps (S n) R x z.

Definition rel_singleton {A} (x y : A): relation A :=
  fun x' y' => x' = x /\ y' = y -> True.


Definition relationT A := A -> A -> Type.

Reserved Notation "R ^*" (at level 5, format "R ^*").
Inductive rtcT {A} (R: relation A) x : A -> Type :=
  | rtcT_refl :
      R^* x x
  | rtcT_step : forall y z,
      R y z ->
      R^* x y ->
      R^* x z
  where "R ^*" := (rtcT R).

Definition rtcT_singleton {state} {R: relation state} {x y} (r: R x y)
  : R^* x y :=
  rtcT_step R x x y r (rtcT_refl R x).

(* Definition rtc_ind_struct
  (A: Type) (R: relation A) x (P: forall x y, R^* x y -> Prop)
  (p_refl: P x x (rtn1_refl A R x))
  (p_step: forall y z (Ryz: R y z) (Rxy: R^* x y),
    P x y Rxy -> P x z (rtn1_trans A R x y z Ryz Rxy)) :=
  fix F z (Rxy: R^* x z) : P x z Rxy :=
    match Rxy with
    | rtn1_refl _ _ _ => p_refl
    | rtn1_trans _ _ _ y z0 Ryz Rxy => p_step y z0 Ryz Rxy (F y Rxy)
    end.
 *)
(* Definition rtc_ind_struct
  (A: Type) (R: relation A) (P: forall x y, R^* x y -> Prop)
  (p_refl: forall x, P x x (rtn1_refl A R x))
  (p_step: forall x y z (Ryz: R y z) (Rxy: R^* x y),
    P x y Rxy -> P x z (rtn1_trans A R x y z Ryz Rxy)) :=
  fix F x z (Rxy: R^* x z) : P x z Rxy :=
    match Rxy with
    | rtn1_refl _ _ _ => p_refl x
    | rtn1_trans _ _ _ y z0 Ryz Rxy => p_step x y z0 Ryz Rxy (F x y Rxy)
    end. *)

Definition reflexiveT {A} (R: relationT A) := forall x, R x x.

Definition symmetrycT {A} (R: relationT A) := forall x y,
  R x y ->
  R y x.

Definition transitiveT {A} (R: relationT A) := forall x y z,
  R x y ->
  R y z -> 
  R x z.

Lemma rtcT_trans {A}: forall R: relation A,
  transitiveT R^*.
Proof.
  intros R x y z Hxy Hyz.
  induction Hyz.
  - assumption.
  - econstructor; eassumption.
Defined.

Lemma rtcT_step_rev {A}: forall (R: relation A) a b c,
  R a b ->
  R^* b c ->
  R^* a c.
Proof.
  intros R a b c Hab Hbc.
  eapply rtcT_trans; [|eassumption].
  econstructor.
  - eassumption.
  - constructor.
Defined.

Inductive in_rtcT {A} {R: relation A} {a}
  : forall {a'}, A -> R^* a a' -> Prop :=
  | in_rtcT_head_refl :
      in_rtcT a (rtcT_refl R a)
  | in_rtcT_head_step : forall x x' r p,
      in_rtcT x' (rtcT_step R a x x' r p)
  | in_rtcT_tail : forall x x' y r p,
      in_rtcT y p ->
      in_rtcT y (rtcT_step R a x x' r p).

(* indexed rtc *)

Reserved Notation "R ^#" (at level 5, format "R ^#").
Inductive rtcT_idx {A} (R: relation A) : nat -> A -> A -> Type :=
  | rtcT_idx_refl : forall x,
      R^#0 x x
  | rtcT_idx_step : forall n x y z,
      R y z ->
      R^#n x y ->
      R^#(S n) x z
  where "R ^#" := (rtcT_idx R).

Definition rtcT_idx_singleton {state} {R: relation state} {x y} (r: R x y)
  : R^# 1 x y :=
  rtcT_idx_step R 0 x x y r (rtcT_idx_refl R x).

Theorem rtcT_idx_step_rev {state}: forall (R: relation state) n s s' x,
  R s s' ->
  R^# n s' x ->
  R^# (S n) s x.
Proof using.
  intros R n s s' x Hstep Hpath.
  induction Hpath.
  - apply rtcT_idx_singleton.
    assumption.
  - econstructor.
    + eassumption.
    + applyc IHHpath.
      assumption.
Qed.

(* Definition rtc_idx_ind_struct
  (A: Type) (R: relation A) (P: forall n x y, R^# n x y -> Prop)
  (p_refl: forall x, P 0 x x (rtc_idx_refl R x))
  (p_step: forall n x y z (Ryz: R y z) (Rxy: R^# n x y),
    P n x y Rxy -> P (S n) x z (rtc_idx_step R n x y z Ryz Rxy)) :=
  fix F n x z (Rxy: R^# n x z) : P n x z Rxy :=
    match Rxy as Rxy0 in (_^# n0 x0 y0) return (P n0 x0 y0 Rxy0) with
    | rtc_idx_refl _ x0 => p_refl x0
    | rtc_idx_step _ n0 x0 y z0 Ryz Rxy => p_step n0 x0 y z0 Ryz Rxy (F n0 x0 y Rxy)
    end. *)

(* Definition rtc_idx_ind_struct_fixed_origin
  (A: Type) (R: relation A) x (P: forall n x y, R^# n x y -> Prop)
  (p_refl: P 0 x x (rtc_idx_refl R x))
  (p_step: forall n y z (Ryz: R y z) (Rxy: R^# n x y),
    P n x y Rxy -> P (S n) x z (rtc_idx_step R n x y z Ryz Rxy)) :=
  fix F n z (Rxy: R^# n x z) : P n x z Rxy :=
    (* match Rxy as Rxy0 in (_^# n0 x0 y0) return (P n0 x0 y0 Rxy0) with *)
    match Rxy with
    | rtc_idx_refl _ x0 => p_refl
    | rtc_idx_step _ n0 x0 y z0 Ryz Rxy => p_step n0 x0 y z0 Ryz Rxy (F n0 y Rxy)
    end. *)

(* (almost) transitivity *)
Theorem rtcT_idx_combine {A}: forall n m (R: relation A) x y z,
  R^# n x y ->
  R^# m y z ->
  R^# (n+m) x z.
Proof using.
  intros n m R x y z Hxy Hyz; revert x Hxy.
  (* induction Hyz using rtc_idx_ind_struct; intros. *)
  induction Hyz; intros.
  - rewrite PeanoNat.Nat.add_0_r.
    assumption.
  - rewrite PeanoNat.Nat.add_succ_r.
    econstructor.
    + eassumption.
    + applyc IHHyz.
      assumption.
Defined.

Theorem rtcT_idx_to_rtcT {A n} {R: relation A} {x y}:
  R^# n x y ->
  R^* x y.
Proof using.
  introv H.
  induction H.
  - constructor.
  - econstructor; eassumption.
Defined.

Theorem rtcT_to_rtcT_idx {A} {R: relation A} {x y}:
  R^* x y ->
  {n & R^# n x y}.
Proof using.
  introv H.
  induction H.
  - eexists. constructor.
  - destruct exists IHrtcT n.
    exists (S n).
    econstructor; eassumption.
Defined.

Inductive in_rtcT_idx_at {A} {R: relation A} {a}
  : forall {n a'}, A -> nat -> R^# n a a' -> Prop :=
  | in_rtcT_idx_at_head_refl :
      in_rtcT_idx_at a 0 (rtcT_idx_refl R a)
  | in_rtcT_idx_at_head_step : forall n x x' r p,
      in_rtcT_idx_at x' n (rtcT_idx_step R n a x x' r p)
  | in_rtcT_idx_at_tail : forall n m x x' y r p,
      in_rtcT_idx_at y m p ->
      in_rtcT_idx_at y m (rtcT_idx_step R n a x x' r p).

Inductive in_rtcT_idx {A} {R: relation A} {a}
  : forall {n a'}, A -> R^# n a a' -> Prop :=
  | in_rtcT_idx_head_refl :
      in_rtcT_idx a (rtcT_idx_refl R a)
  | in_rtcT_idx_head_step : forall n x x' r p,
      in_rtcT_idx x' (rtcT_idx_step R n a x x' r p)
  | in_rtcT_idx_tail : forall n x x' y r p,
      in_rtcT_idx y p ->
      in_rtcT_idx y (rtcT_idx_step R n a x x' r p).

Theorem in_rtcT_idx_at__in_rtcT_idx {A}:
  forall (R: relation A) x a b n m (r: R^# n a b),
    in_rtcT_idx_at x m r ->
    in_rtcT_idx x r.
Proof using.
  introv H.
  induction H; constructor.
  assumption.
Qed.

Theorem in_rtcT_idx__in_rtcT_idx_at {A}:
  forall (R: relation A) x a b n (r: R^# n a b),
    in_rtcT_idx x r ->
    exists m, m <= n /\ in_rtcT_idx_at x m r.
Proof using.
  introv H.
  induction H.
  - eexists.
    split; [|constructor].
    reflexivity.
  - eexists.
    split; [|constructor].
    lia.
  - destruct exists IHin_rtcT_idx m.
    exists m.
    destruct IHin_rtcT_idx.
    split.
    + lia.
    + constructor.
      assumption.
Qed. 

Require Import Coq.Program.Equality.
Theorem in_rtcT__in_rtcT_idx {A}:
  forall (R: relation A) x a b (r: R^* a b),
    in_rtcT x r ->
    exists n (r': R^# n a b), in_rtcT_idx x r'.
Proof using.
  introv.
  dependent induction r; intros.
  - repeat eexists. repeat constructor.
Admitted.

Theorem in_rtcT_idx__in_rtcT {A}:
  forall (R: relation A) x n a b (r: R^# n a b),
    in_rtcT_idx x r ->
    in_rtcT x (rtcT_idx_to_rtcT r).
Proof using.
  introv H.
  induction H. 
  - constructor.
  - constructor.
  - simpl.
    constructor.
    assumption.
Qed.

Definition in_rtcT_idx_before {state} {R: relation state} {n s s'}
  x i (r: R^# n s s') := 
  exists j, j < i /\ in_rtcT_idx_at x i r.

