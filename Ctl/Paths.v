Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import BinaryRelations.

Require Import Coq.Program.Equality.
Require Import Tactics.General.

Definition path {state} (R: relation state) (n: nat) (s: state) :=
  {s' & R^# n s s'}.

Theorem path_refl {state}: forall (R: relation state) s,
  path R 0 s.
Proof using.
  intros.
  eexists.
  constructor.
Qed.

Theorem path_step {state}: forall (R: relation state) n s x x',
  R x x' ->
  R^# n s x ->
  path R (S n) s.
Proof using.
  intros.
  eexists.
  econstructor; eassumption.
Qed.

Definition rtcT_idx_to_path {state} {R: relation state} {n s s'}
  (r: R^# n s s') : path R n s :=
  existT _ s' r.

Inductive in_path_at {state} {R: relation state} {n s} 
  : state -> nat -> path R n s -> Prop :=
  | in_path_at_rule : forall x m s' (r: R^# n s s'),
      in_rtcT_idx_at x m r ->
      in_path_at x m (rtcT_idx_to_path r).

Inductive in_path {state} {R: relation state} {n s} 
  : state -> path R n s -> Prop :=
  | in_path_rule : forall x s' (r: R^# n s s'),
      in_rtcT_idx x r ->
      in_path x (rtcT_idx_to_path r).

Theorem in_path__in_path_at {state} {R: relation state} {n s}:
  forall x (p: path R n s), 
    in_path x p ->
    exists m, m <= n /\ in_path_at x m p.
Proof.
  intros x p H.
  invc H.
  apply in_rtcT_idx__in_rtcT_idx_at in H0.
  destruct exists H0 m.
  exists m.
  destruct H0.
  split.
  - assumption.
  - constructor.
    assumption.
Qed.

Theorem in_path_at__in_path {state} {R: relation state} {n s}:
  forall x i (p: path R n s),
    in_path_at x i p ->
    in_path x p.
Proof.
  intros x i p H.
  invc H.
  constructor.
  eapply in_rtcT_idx_at__in_rtcT_idx.
  eassumption.
Qed.

Definition in_path_before {state} {R: relation state} {n s} x i (p: path R n s) := 
  exists j, j < i /\ in_path_at x i p.

(* A single-step path *)
Definition path_singleton {state} {R: relation state} {x y} (r: R x y)
  : path R 1 x :=
  rtcT_idx_to_path (rtcT_idx_singleton r).

Theorem path_step_rev {state}: forall (R: relation state) n s s',
  R s s' ->
  path R n s' ->
  path R (S n) s.
Proof using.
  intros R n s s' Hstep Hpath.
  destruct exists Hpath x.
  eapply rtcT_idx_to_path.
  eapply rtcT_idx_step_rev; eassumption.
Defined.

(* This would require in_path be switched from `Prop` to `Type` *)
Theorem in_path_impl_rtc {state}:
  forall (R: relation state) n s s' (p: path R n s),
    in_path s' p -> R^* s s'.
Proof.
(* intros R n s s' p Hin.
  invc Hin.
  induction H.
  - constructor.
  - econstructor.
    + eassumption.
    + eapply path_to_impl_rtc.
      eassumption.
  - assumption.
Qed.
*)
Abort.

Theorem in_rtcT_idx_first {state}:
  forall (R: relation state) n s s' (r: R^# n s s'),
    in_rtcT_idx s r.
Proof using.
  intros.
  induction r; constructor.
  assumption. 
Qed.

Theorem in_rtcT_idx_last {state}:
  forall n (R: relation state) s s' (r: R^# n s s'),
    in_rtcT_idx s' r.
Proof using.
  intros.
  destruct r; constructor.
Qed.

Theorem in_rtcT_idx__in_path {state}:
  forall n (R: relation state) x s s' (r: R^# n s s'),
    in_rtcT_idx x r ->
    in_path x (rtcT_idx_to_path r).
Proof using.
  introv H.
  destruct H; repeat constructor.
  assumption.
Qed.

Theorem in_path_last {state}:
  forall n (R: relation state) s s' (r: R^# n s s'),
    in_path s' (rtcT_idx_to_path r).
Proof using.
  intros.
  eapply in_rtcT_idx__in_path.
  apply in_rtcT_idx_last.
Qed.

Theorem in_path_first {state}:
  forall n (R: relation state) s s' (r: R^# n s s'),
    in_path s (rtcT_idx_to_path r).
Proof using.
  intros.
  eapply in_rtcT_idx__in_path.
  apply in_rtcT_idx_first.
Qed.

Lemma rtc__in_some_path {state}: forall (R: relation state) s s',
  R^* s s' -> exists n (p: path R n s), in_path s' p.
Proof using.
  (* Why does `introv` intro x? *)
  intros R s s' r.
  apply rtcT_to_rtcT_idx in r.
  destruct exists r n.
  exists n (rtcT_idx_to_path r).
  apply in_path_last.
Qed.

Theorem in_path_combine {A}:
  forall (R: relation A) n a (pa: path R n a) m b (pb: path R m b) c,
    in_path b pa ->
    in_path c pb ->
    exists l (p: path R l a), in_path c p.
Proof using.
  introv H.
  revert n a pa x.
  invc H.
  induction H0; intros.
  - eexists.
    exists pa.
    assumption.
  - eapply rtcT_idx_step in p; [|eassumption]; clear r.
    invc x0.
    induction H.
    + exists (S n) (rtcT_idx_to_path p).
      apply in_path_last.
    + eapply rtcT_idx_step in p0; [|eassumption]; clear r.
      eapply rtcT_idx_combine in p; [|eassumption]; clear p0.
      exists (S n0 + S n) (rtcT_idx_to_path p).
      apply in_path_last.
    + applyc IHin_rtcT_idx.
      assumption.
  - eapply IHin_rtcT_idx.
    eassumption.
Qed.

Theorem in_path__rtc {state}: forall (R:relation state) n s (p: path R n s) s',
  in_path s' p ->
  inhabited (R^* s s').
Proof using.
  intros R n s p s' H.
  invc H.
  eapply in_rtcT_idx__prefix'.
  eassumption.
Qed.
