Require Import Tactics.General.
Require Import BinaryRelations.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

(* Old path defn *)
(* Inductive path {state} (R: relation state) : state -> nat -> Prop := 
  | path_trivial : forall s, path R s 0
  | path_step : forall s s' n,
      R s s' ->
      path R s' n ->
      path R s (S n).
Arguments path_trivial {state R}%type_scope.
Arguments path_step    {state R}%type_scope. *)

(* A length-indexed transition sequence
   Essentially a reflexive-transitive closure, where the sequence of steps is 
   transparent (plus the type-level length info).
*)
Inductive path_to {state} (R: relation state): nat -> state -> state -> Prop :=
  | path_to_refl : forall s,
      path_to R 0 s s
  | path_to_step : forall s x x' n,
      R x x' ->
      path_to R n s x ->
      path_to R (S n) s x'.
Arguments path_to_refl {state R}%type_scope.
Arguments path_to_step {state R}%type_scope.

(* (almost) transitivity *)
Definition path_to_combine {state n m} {R: relation state} {x y z}:
  path_to R n x y ->
  path_to R m y z ->
  path_to R (n+m) x z.
intros path_xy path_yz; revert n x path_xy.
induction path_yz; intros.
+ rewrite PeanoNat.Nat.add_0_r. 
  assumption.
+ rewrite PeanoNat.Nat.add_succ_r.
  eapply path_to_step.
  * eassumption.
  * applyc IHpath_yz.
    assumption.
Defined.

Definition path {state} (R: relation state) (n: nat) (s: state) :=
  exists s', path_to R n s s'.

Theorem path_refl {state}: forall (R: relation state) s,
  path R 0 s.
Proof using.
  intros.
  econstructor.
  constructor.
Qed.

Theorem path_step {state}: forall (R: relation state) n s x x',
  R x x' ->
  path_to R n s x ->
  path R (S n) s.
Proof using.
  intros.
  econstructor.
  econstructor; eassumption.
Qed.

Definition path_from_path_to {state} {R: relation state} {n s s'}
  (p: path_to R n s s') : path R n s :=
  ex_intro _ s' p.

Inductive in_path_to_at {state} {R: relation state} {s}
  : forall {s'}, state -> nat -> forall {n}, path_to R n s s' -> Prop :=
  | in_path_to_at_head_refl :
      in_path_to_at s 0 (path_to_refl s)
  | in_path_to_at_head_step : forall x x' n r p,
      in_path_to_at x' n (path_to_step s x x' n r p)
  | in_path_to_at_tail : forall x x' y n m r p,
      in_path_to_at y m p ->
      in_path_to_at y m (path_to_step s x x' n r p).

Inductive in_path_at {state} {R: relation state} {n s} 
  : state -> nat -> path R n s -> Prop :=
  | in_path_at_rule : forall x m s' (p: path_to R n s s'),
      in_path_to_at x m p ->
      in_path_at x m (path_from_path_to p).

Inductive in_path_to {state} {R: relation state} {s}
  : forall {s'}, state -> forall {n}, path_to R n s s' -> Prop :=
  | in_path_to_head_refl :
      in_path_to s (path_to_refl s)
  | in_path_to_head_step : forall x x' n r p,
      in_path_to x' (path_to_step s x x' n r p)
  | in_path_to_tail : forall x x' y n r p,
      in_path_to y p ->
      in_path_to y (path_to_step s x x' n r p).

Inductive in_path {state} {R: relation state} {n s} 
  : state -> path R n s -> Prop :=
  | in_path_rule : forall x s' (p: path_to R n s s'),
      in_path_to x p ->
      in_path x (path_from_path_to p).

Theorem in_path_from_in_path_to {state}:
  forall (R: relation state) n s s' (p: path_to R n s s') x,
    in_path_to x p ->
    in_path x (path_from_path_to p).
Proof using.
  intros.
  destruct H; repeat constructor.
  assumption.
Qed. 

Theorem in_path_at_from_in_path_to_at {state}:
  forall (R: relation state) n s s' i (p: path_to R n s s') x,
    in_path_to_at x i p ->
    in_path_at x i (path_from_path_to p).
Proof using.
  intros.
  destruct H; repeat constructor.
  assumption.
Qed. 

Theorem in_path_to_impl_in_path_to_at {state} {R: relation state} {n s s'}:
  forall x (p: path_to R n s s'), 
    in_path_to x p ->
    exists i, in_path_to_at x i p.
Proof.
  intros x p H.
  induction H. 
  - eexists; constructor.
  - eexists; constructor.
  - destruct exists IHin_path_to i.
    eexists.
    constructor.
    eassumption.
Qed.

Theorem in_path_to_at_impl_in_path_to {state} {R: relation state} {n s s'}:
  forall x i (p: path_to R n s s'),
    in_path_to_at x i p ->
    in_path_to x p.
Proof.
  intros x i p H.
  induction H; constructor.
  assumption.
Qed.

Theorem in_path_impl_in_path_at {state} {R: relation state} {n s}:
  forall x (p: path R n s), 
    in_path x p ->
    exists i, in_path_at x i p.
Proof.
  intros x p H.
  invc H.
  apply in_path_to_impl_in_path_to_at in H0.
  destruct exists H0 i.
  exists i.
  constructor.
  assumption.
Qed.

Theorem in_path_at_impl_in_path {state} {R: relation state} {n s}:
  forall x i (p: path R n s),
    in_path_at x i p ->
    in_path x p.
Proof.
  intros x i p H.
  invc H.
  constructor.
  eapply in_path_to_at_impl_in_path_to.
  eassumption.
Qed.

Definition in_path_to_before {state} {R: relation state} {n s s'}
  x i (p: path_to R n s s') := 
  exists j, j < i /\ in_path_to_at x i p.

Definition in_path_before {state} {R: relation state} {n s} x i (p: path R n s) := 
  exists j, j < i /\ in_path_at x i p.


(* A single-step path *)
Definition path_to_singleton {state} {R: relation state} {x y} (r: R x y)
  : path_to R 1 x y :=
  path_to_step x x y 0 r (path_to_refl x).

Definition path_singleton {state} {R: relation state} {x y} (r: R x y)
  : path R 1 x :=
  path_from_path_to (path_to_singleton r).


Theorem path_to_step_rev {state}: forall (R: relation state) n s s' x,
  R s s' ->
  path_to R n s' x ->
  path_to R (S n) s x.
Proof using.
  intros R n s s' x Hstep Hpath.
  induction Hpath.
  - apply path_to_singleton.
    assumption.
  - econstructor.
    + eassumption.
    + applyc IHHpath.
      assumption.
Qed.

Theorem path_step_rev {state}: forall (R: relation state) n s s',
  R s s' ->
  path R n s' ->
  path R (S n) s.
Proof using.
  intros R n s s' Hstep Hpath.
  destruct exists Hpath x.
  eapply path_from_path_to.
  eapply path_to_step_rev; eassumption.
Qed.

(*
Require Import Psatz.
Definition path_pop n {state} {R: relation state} {m s} (p: path R s m) 
  : {s' & path R s' (m-n)}.
  induction n.
  - exists s.
    replace (m - 0) with m by lia.
    assumption.
  - destruct exists IHn s'.
    inv IHn.
    + exists s'.
      rewrite <- H1 in IHn.
      replace (m - S n) with 0 by lia.
      assumption.
    + exists s'0.
      replace (m - S n) with n0 by lia.
      assumption.
Qed.

Definition path_tail {state} {R: relation state} {s n}
  (p: path R s (S n)) : {s' & path R s' n}.
inv p.
eexists.
eassumption.
Defined.

Lemma path_tail_correct {state} {R: relation state}:
  forall s s' n r (p: path R s' n),
  (* path_tail (path_step s s' n r p) = existT _ s' p. *)
  projT2 (path_tail (path_step s s' n r p)) = p.
Proof. reflexivity. Qed.

Definition path_get_step {state} {R: relation state} {m s}
  n (HinBounds: n < m) (p: path R s m) : {x & {y | R x y}}.
move n at top.
generalize_max.
induction n; intros.
- inv p.
  + lia.
  + repeat eexists. eassumption.
- destruct m as [|m']; [lia|].
  inv p.
  clear H1.
  assert (HLt: n < m') by lia.
  specialize (IHn state R m' s' HLt X).
  destruct exists IHn x y.
  repeat eexists.
  eapply IHn.
Defined.

Definition arbitrary_path {state} {R: relation state} 
  (sw: serial_witness R) s n: path R s n.
induction n.
- constructor.
- induction IHn.
  + specialize (sw s).
    destruct exists sw s'.
    econstructor.
    * eassumption.
    * constructor.
  + econstructor; eassumption.
Defined.

Definition gen_path {state} {R: relation state} {s}
  (sfw: serial_from_witness R s) n: path R s n.
induction n.
- constructor.
- induction IHn.
  + specialize (sfw s (rtn1_refl _ R s)).
    destruct exists sfw s'.
    econstructor.
    * eassumption.
    * constructor.
  + econstructor.
    * eassumption.
    * apply IHIHn.
      intros s'' Hsteps.
      apply sfw.
      eapply rtc_alt_trans; eassumption.
Defined.
*)

(*
Theorem in_path_at_combine {state} {R: relation state}: 
  forall n m i j x x' y y' s (p: path n R x x') (p': path m R y y'),
    in_path_at y i p -> 
    in_path_at s j p' -> 
    (* Could also be path size (i+j) if we wanted to cut it as short as possible *)
    (* exists p'': path (i+m) R x y', in_path_at s (i+j) p''. *)
    exists l (p'': path l R x y'), in_path_at s (i+j) p''.
Proof.
  intros n m i j x x' y y' s p p' Hy Hs.
  revert m j y' s p' Hs.
  induction Hy; intros; try solve [eauto].
  eapply path_step in p; [|eassumption]; clear r.
  exists (S n + m) (path_combine p p').
  induction Hs.
  - simpl.
  
  (* Check (path_combine (path_step _ _ _ _ r p) p'). *)

  (* intros s x i x' j n n' p p' Hx Hx'.
  induction Hx; [eauto|eauto|].
  specialize (IHHx p' Hx').
  destruct exists IHHx n'' p''.
  exists (S n'').
  exists (path_step s s' n'' r p'').
  constructor.
  assumption.
Qed. *)
Admitted.
*)

(* 
Theorem in_path_at_combine {state} {R: relation state}: 
  forall s x i x' j n n' (p: path R s n) (p': path R x n'),
    in_path_at x i p -> in_path_at x' j p' -> 
    exists n'' (p'': path R s n''), in_path_at x' (i+j) p''.
Proof.
  intros s x i x' j n n' p p' Hx Hx'.
  induction Hx; [eauto|eauto|].
  specialize (IHHx p' Hx').
  destruct exists IHHx n'' p''.
  exists (S n'').
  exists (path_step s s' n'' r p'').
  constructor.
  assumption.
Qed. *)

(* Theorem in_path_combine {state} {R: relation state}: 
  forall s x x' n n' (p: path R s n) (p': path R x n'),
    in_path x p -> in_path x' p' -> 
    exists n'' (p'': path R s n''), in_path x' p''.
Proof.
  intros.
  apply in_path_eq_in_path_at in H, H0.
  destruct exists H i.
  destruct exists H0 j.
  eapply in_path_at_combine in H0; [|eassumption].
  destruct exists H0 n'' p''.
  exists n'' p''.
  eapply in_path_at_to_in_path.
  eassumption.
Qed.  *)

Theorem path_to_impl_rtc {state}: forall (R: relation state) n s s',
  path_to R n s s' -> R^* s s'.
Proof.
  intros R n s s' H.
  induction H.
  - reflexivity.
  - econstructor; eassumption.
Qed.
  
Theorem in_path_impl_rtc {state}:
  forall (R: relation state) n s s' (p: path R n s),
    in_path s' p -> R^* s s'.
Proof.
  intros R n s s' p Hin.
  invc Hin.
  induction H.
  - constructor.
  - econstructor.
    + eassumption.
    + eapply path_to_impl_rtc.
      eassumption.
  - assumption.
Qed.

Lemma rtc_impl_path_to {state}: forall (R: relation state) s s',
  R^* s s' -> exists n, path_to R n s s'.
Proof using.
  intros R s s' H.
  induction H.
  - eexists. apply path_to_refl.
  - destruct exists IHclos_refl_trans_n1 n.
    exists (S n).
    econstructor; eassumption.
Qed.

(*
(* Print clos_refl_trans_n1. *)
Inductive rtc_len {A} {R: relation A} : nat -> R^* x y -> Prop :=
  | rtc_len_0 : 
      rtc_len 0 
*)
Inductive in_rtc {state} {R: relation state} {s}
  : forall {s'}, state -> R^* s s' -> Prop :=
  | in_rtc_head_refl :
      in_rtc s (rtn1_refl state R s)
  | in_rtc_head_step : forall x x' r p,
      in_rtc x' (rtn1_trans state R s x x' r p)
  | in_rtc_tail : forall x x' y r p,
      in_rtc y p ->
      in_rtc y (rtn1_trans state R s x x' r p)
  .

Theorem foo {state}: forall (R: relation state) n s s' (p: path_to R n s s') x,
  in_path_to x p ->
  in_rtc x (path_to_impl_rtc _ _ _ _ p).

Theorem in_path_to_first {state}:
  forall (R: relation state) n s s' (p: path_to R n s s'),
    in_path_to s p.
Proof using.
  intros.
  elim p.
  induction p.
Admitted.

Theorem in_path_to_last {state}:
  forall n (R: relation state) s s' (p: path_to n R s s'),
    in_path_to s' p.
Proof using.
  intros.
  destruct p; constructor.
Qed.

Theorem in_path_last {state}:
  forall n (R: relation state) s s' (p: path_to n R s s'),
    in_path s' (path_from_path_to p).
Proof using.
  intros.
  eapply in_path_from_in_path_to.
  apply in_path_to_last.
Qed.

Lemma rtc_impl_in_some_path {state}: forall (R: relation state) s s',
  R^* s s' -> exists n (p: path n R s), in_path s' p.
Proof.
  intros R s s' H.
  apply rtc_impl_path_to in H.
  destruct exists H n.
  exists n.
  exists (path_from_path_to H).
Qed.