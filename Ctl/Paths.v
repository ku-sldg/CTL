Require Import BinaryRelations.
Require Import Tactics.Tactics.
(* Require Import Classical. *)

Section Paths.

Variable state : Type.
Variable R : relation state.

CoInductive path (s: state) : Type := 
  | step : forall s', R s s' -> path s' -> path s.

Inductive in_path {s}: state -> path s -> Prop :=
  | in_head : forall s' r p,
      in_path s (step s s' r p)
  | in_tail : forall s' x r p,
      in_path x p ->
      in_path x (step s s' r p).

Inductive in_path_at {s}: state -> nat -> path s -> Prop :=
  | in_head_at : forall s' r p,
      in_path_at s 0 (step s s' r p)
  | in_tail_at : forall s' x n r p,
      in_path_at x n p ->
      in_path_at x (S n) (step s s' r p). 

Definition in_path_before {s} x n (p: path s) : Prop :=
  exists m, m < n /\ in_path_at x m p.

Theorem in_path__in_path_at {s}: forall x (p: path s),
  in_path x p ->
  exists n, in_path_at x n p.
Proof using.
  intros * Hin.
  induction Hin.
  - eexists. econstructor.
  - destruct exists IHHin n.
    eexists.
    enow econstructor.
Qed.

Theorem in_path_at__in_path {s}: forall x n (p: path s),
  in_path_at x n p ->
  in_path x p.
Proof using.
  intros * Hin_at.
  induction Hin_at; now constructor.
Qed.

Definition serial_witness__path (witness: serial_witness R) s : path s.
  revert s.
  cofix p.
  intro s.
  specialize (witness s).
  destruct witness.
  econstructor.
  - eassumption.
  - apply p.
Defined.

Definition path_prepend {x y} (seq: R#* x y) (p: path y) : path x.
  apply seq__seq_rev in seq.
  induction seq.
  - assumption.
  - specializec IHseq p.
    econstructor; eassumption.
Defined.

Theorem in_path__star : forall s (p: path s) s',
  in_path s' p ->
  R^* s s'.
Proof using.
  intros * Hin.
  apply rt1n_star.
  induction Hin.
  - constructor.
  - enow econstructor.
Qed.
(* If I want to define a similar function to derive a sequence, I'll need to define a
   `Type`-sorted equivalent to `in_path` (`prefix_upto`).
 *)

Theorem star__in_path : forall s s',
  serial_witness R ->
  R^* s s' ->
  exists p: path s, 
    in_path s' p.
Proof using.
  intros * Hserial Hstar.
  apply star_rt1n in Hstar.
  induction Hstar.
  - apply serial_witness__path with (s := x) in Hserial.
    exists Hserial.
    destruct Hserial.
    constructor.
  - destruct exists IHHstar p.
    exists (step x y H p).
    now apply in_tail.
Qed.

End Paths.

Arguments path {state}.
Arguments in_path {state R s}.
Arguments in_path_at {state R s}.
Arguments in_path_before {state R s}.