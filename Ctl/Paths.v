Require Import BinaryRelations.

Require Import Coq.Program.Equality.
Require Import Tactics.General.
Require Import Tactics.Construct.

Definition path {state} (R: relation state) (n: nat) (s: state) :=
  {s' & R# n s s'}.

Theorem path_refl {state}: forall (R: relation state) s,
  path R 0 s.
Proof using.
  intros.
  eexists.
  constructor.
Qed.

Theorem path_step {state}: forall (R: relation state) n s x x',
  R x x' ->
  R#n s x ->
  path R (S n) s.
Proof using.
  intros.
  eexists.
  econstructor; eassumption.
Qed.

Definition nseq_to_path {state} {R: relation state} {n s s'}
  (r: R#n s s') : path R n s :=
  existT _ s' r.

Inductive in_path_at {state} {R: relation state} {n s} 
  : state -> nat -> path R n s -> Prop :=
  | in_path_at_rule : forall x m s' (r: R#n s s'),
      in_nseq_at x m r ->
      in_path_at x m (nseq_to_path r).

Inductive in_path {state} {R: relation state} {n s} 
  : state -> path R n s -> Prop :=
  | in_path_rule : forall x s' (r: R#n s s'),
      in_nseq x r ->
      in_path x (nseq_to_path r).

Theorem in_path__in_path_at {state} {R: relation state} {n s}:
  forall x (p: path R n s), 
    in_path x p ->
    exists m, m <= n /\ in_path_at x m p.
Proof.
  intros x p H.
  invc H.
  apply in_nseq__in_nseq_at in H0.
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
  eapply in_nseq_at__in_nseq.
  eassumption.
Qed.

Definition in_path_before {state} {R: relation state} {n s} x i (p: path R n s) := 
  exists j, j < i /\ in_path_at x j p.

Lemma in_nseq_before__in_path_before {A}:
  forall (R: relation A) n a b (r: R#n a b) x i,
    in_nseq_before x i r ->
    in_path_before x i (nseq_to_path r).
Proof using.
  intros.
  destruct H as [x0 [Hlt H]].
  exists x0.
  split; [exact Hlt|]; clear Hlt.
  constructor.
  assumption.
Qed.

(* A single-step path *)
Definition path_singleton {state} {R: relation state} {x y} (r: R x y)
  : path R 1 x :=
  nseq_to_path (nseq_singleton r).

Theorem path_step_rev {state}: forall (R: relation state) n s s',
  R s s' ->
  path R n s' ->
  path R (S n) s.
Proof using.
  intros R n s s' Hstep Hpath.
  destruct exists Hpath x.
  eapply nseq_to_path.
  eapply nseq_step_rev; eassumption.
Defined.

Lemma path_step_rev_preserves_in {state}: 
  forall (R: relation state) s s' (r: R s s') n (p: path R n s') x,
    in_path x p ->
    in_path x (path_step_rev R n s s' r p).
Proof using.
  intros * H.
  invc H.
  induction H0; simpl; repeat constructor.
  simpl in IHin_nseq.
  dependent induction IHin_nseq.
  assumption.
Qed.

Theorem in_nseq__in_path {state}:
  forall n (R: relation state) x s s' (r: R#n s s'),
    in_nseq x r ->
    in_path x (nseq_to_path r).
Proof using.
  intros * H.
  destruct H; repeat constructor.
  assumption.
Qed.

Theorem in_path_at_first {state}: forall (R: relation state) n s (p: path R n s),
  in_path_at s 0 p.
Proof using.
  intros.
  destruct p.
  constructor.
  apply in_nseq_at_first.
Qed.

Theorem in_path_at_first_inv {state}:
  forall (R: relation state) n s (p: path R n s) x,
    in_path_at x 0 p ->
    x = s.
Proof using.
  intros.
  invc H.
  dependent induction H0.
  - reflexivity.
  - apply IHin_nseq_at.
    reflexivity.
Qed. 

Theorem in_path_first {state}:
  forall n (R: relation state) s s' (r: R#n s s'),
    in_path s (nseq_to_path r).
Proof using.
  intros.
  eapply in_nseq__in_path.
  apply in_nseq_first.
Qed.

Theorem in_path_last {state}:
  forall n (R: relation state) s s' (r: R#n s s'),
    in_path s' (nseq_to_path r).
Proof using.
  intros.
  eapply in_nseq__in_path.
  apply in_nseq_last.
Qed.

Lemma seq__in_some_path {state}: forall (R: relation state) s s',
  R#* s s' -> exists n (p: path R n s), in_path s' p.
Proof using.
  intros * r.
  apply seq_to_nseq in r.
  destruct exists r n.
  exists n (nseq_to_path r).
  apply in_path_last.
Qed.

Theorem in_path_combine {A}:
  forall (R: relation A) n a (pa: path R n a) m b (pb: path R m b) c,
    in_path b pa ->
    in_path c pb ->
    exists l (p: path R l a), in_path c p.
Proof using.
  intros * Hin_pa Hin_pb.
  revert n a pa Hin_pa.
  destruct Hin_pb as [c b' r Hin].
  induction Hin; intros.
  - eexists.
    exists pa.
    assumption.
  - eapply nseq_step in p; [|eassumption]; clear r.
    invc Hin_pa.
    induction H.
    + exists (S n) (nseq_to_path p).
      apply in_path_last.
    + eapply nseq_step in p0; [|eassumption]; clear r.
      eapply nseq_trans in p; [|eassumption]; clear p0.
      exists (S n0 + S n) (nseq_to_path p).
      apply in_path_last.
    + applyc IHin_nseq.
      assumption.
  - eapply IHHin.
    eassumption.
Qed.

Theorem in_path__get_prefix_seq {state}: forall (R:relation state) n s (p: path R n s) s',
  in_path s' p ~>
  R#* s s'.
Proof using.
  intros R n s p s' H.
  invc H.
  econstruct in_nseq__get_prefix'.
  eassumption.
Qed.

Inductive path_prefix {A} {R: relation A} {a}
  : forall {n m}, path R n a -> path R m a -> Prop :=
  | path_prefix_rule :
      forall n b (Rab: R#n a b) m c (Rac: R#m a c),
        nseq_prefix Rab Rac ->
        path_prefix (nseq_to_path Rab) (nseq_to_path Rac).

Theorem path_prefix_trans {A}: forall {R: relation A} {a n1 n2 n3},
  forall (p1: path R n1 a) (p2: path R n2 a) (p3: path R n3 a),
    path_prefix p1 p2 ->
    path_prefix p2 p3 ->
    path_prefix p1 p3.
Proof using. 
  intros R a n1 n2 n3 p1 p2 p3 H12 H23.
  dependent destruction H12.
  dependent destruction H23.
  constructor.
  eapply nseq_prefix_trans; eassumption.
Qed.

Theorem in_path_at_prefix {A}:
  forall (R: relation A) a n1 (p1: path R n1 a) n2 (p2: path R n2 a) x i,
    path_prefix p1 p2 ->
    in_path_at x i p1 ->
    in_path_at x i p2.
Proof using.
  intros R a n1 p1 n2 p2 x i Hpre Hin.
  dependent destruction Hpre.
  dependent invc Hin.
  constructor.
  eapply in_nseq_at_prefix; eassumption.
Qed.

Lemma path_prefix_before {A}:
  forall (R: relation A) a n1 (p1: path R n1 a) n2 (p2: path R n2 a) x,
    path_prefix p1 p2 ->
    in_path x p1 ->
    in_path_before x (S n1) p2.
Proof using.
  intros R a n1 p1 n2 p2 x Hpre Hin.
  dependent destruction Hpre.
  dependent invc Hin.
  apply in_nseq_before__in_path_before.
  eapply nseq_prefix_before; eassumption.
Qed.

Theorem in_path_at__get_prefix {A}:
  forall (R: relation A) x i n a (p: path R n a),
    in_path_at x i p ->
    exists p': path R i a, path_prefix p' p.
Proof using.
  intros.
  invc H.
  apply in_nseq_at__get_prefix in H0.
  destruct exists H0 r'.
  exists (nseq_to_path r').
  constructor.
  assumption.
Qed. 

Theorem in_path__get_prefix {A}: 
  forall (R: relation A) x n a (p: path R n a),
    in_path x p ->
    exists m (p': path R m a), path_prefix p' p.
Proof using.
  intros.
  invc H.
  apply in_nseq__get_prefix in H0.
  destruct exists H0 m r'.
  exists m (nseq_to_path r').
  constructor.
  assumption.
Qed.
