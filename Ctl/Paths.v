Require Import Coq.Classes.RelationClasses.

Require Import Ctl.BinaryRelations.

Require Import Glib.Glib.
Require Import Lia.


Section Paths.

Class transition {A} (R: relation A) := 
  {trans_serial: serial_witness R}.

Context {state : Type} (R: relation state) {t: transition R}.

Definition path (s: state) : Type :=
  {p: nat -> state |
    p 0 = s /\
    forall i, R (p i) (p (S i))
  }.
    
Definition state_at {s} (p: path s) : nat -> state := proj1_sig p.
Coercion state_at : path >-> Funclass.

Definition in_path {s} (x: state) (p: path s) : Prop :=
  exists i, p i = x.

Definition in_path_before {s} x i (p: path s) : Prop :=
  exists j, j < i /\ p j = x.


(* Basic properties *)

Lemma state_at_0 : forall s (p: path s),
  p 0 = s.
Proof using.
  intros *.
  now destruct p.
Qed.

Lemma in_path_0 : forall s (p: path s),
  in_path s p.
Proof using.
  intros *.
  exists 0.
  apply state_at_0.
Qed.

Theorem path_succ_related : forall i x (p: path x) y z,
  p i = y ->
  p (S i) = z ->
  R y z.
Proof using.
  intros * <- <-.
  now destruct p.
Qed.

Lemma in_path_before_grow_strict : forall s (p: path s) x i j,
  i < j ->
  in_path_before x i p ->
  in_path_before x j p.
Proof using.
  intros * ilt (k & klt & <-).
  exists k.
  after split.
  lia.
Qed.

Corollary in_path_before_grow : forall s (p: path s) x i j,
  i <= j ->
  in_path_before x i p ->
  in_path_before x j p.
Proof using.
  intros * ile.
  after invc ile.
  apply in_path_before_grow_strict.
  lia.
Qed.


(* Introduction and elimination *)

Definition path_drop {s} (p: path s) (n: nat) : path (p n).
  exists (λ i, p (i + n)).
  after split.
  intro i.
  simpl!.
  follows destruct p.
Defined.

Definition path_tail {s} (p: path s) : path (p 1) :=
  path_drop p 1.

(* Definition serial_witness__path (witness: serial_witness R) s : path s. *)
Definition serial_witness__path s : path s.
  exists (nat_rect _ s (λ _ x, proj1_sig (trans_serial x))).
  split.
  - reflexivity.
  - intros ?.
    cbn.
    follows destruct (trans_serial _).
Defined.   

Definition path_cons {y} x (r: R x y) (p: path y) : path x.
  exists (λ n, 
    match n with 
    | 0 => x
    | S n' => p n'
    end
  ).
  split.
  - reflexivity.
  - intros [].
    + now rewrite state_at_0.
    + now destruct p.
Defined.

Theorem destruct_path : forall x (p: path x),
  exists! (r: R x (p 1)),
    p = path_cons x r (path_tail p).
Proof using.
  intros *.
  assert (r : R x (p 1)) by tedious; exists r.
  split.
  - destruct p as (π & Hπ0 & HπS); simpl!.
    apply exist_eq.
    extensionality i.
    after destruct i.
    simpl!.
    f_equal.
    lia.
  - intros.
    apply proof_irrelevance.
Qed.

Theorem ex_destruct_path : forall x (p: path x),
  exists (r: R x (p 1)),
    p = path_cons x r (path_tail p).
Proof using.
  intros *.
  follows destruct (destruct_path x p).
Qed.

Theorem all_destruct_path : forall x (p: path x),
  forall (r: R x (p 1)),
    p = path_cons x r (path_tail p).
Proof using.
  intros *.
  destruct (ex_destruct_path x p) as [r' ?].
  replace r with r' by apply proof_irrelevance.
  assumption.
Qed.


(* Prepending *)

Definition rev_prepend_sig {x y} (seqr: seq_rev R x y) (p: path y) : 
  {prep: path x
  | (forall s i, in_seq_rev_at R s i seqr -> prep i = s) /\
    forall i, seq_rev_length R seqr <= i -> prep i = p (i - seq_rev_length R seqr)}.
Proof using.
  induction seqr.
  - exists p.
    after split.
    intros * H.
    inv! H.
    apply state_at_0.
  - specialize (IHseqr p).
    destruct IHseqr as (prep' & ? & ?).
    exists (path_cons x r prep').
    split.
    + intros * Hin.
      after invc! Hin.
      follows simpl!.
    + intros * Hlt.
      simpl! in *.
      after destruct i.
      follows apply le_S_n in Hlt.
Defined.

Definition prepend {x y} (seq: R#* x y) (p: path y) : path x :=
  proj1_sig (rev_prepend_sig (ϕ_seq__seq_rev seq) p).
 
Theorem in_prepend_at_seq {x y} (seq: R#* x y) (p: path y): forall s i,
  in_seq_at s i seq -> 
  prepend seq p i = s.
Proof using.
  intros * Hin.
  apply (proj1 (proj2_sig (rev_prepend_sig (ϕ_seq__seq_rev seq) p))).
  follows apply in_seq_at__in_seq_rev_at__iso'.
Qed.

Theorem in_prepend_at_path {x y} (seq: R#* x y) (p: path y): forall i,
  seq_length seq <= i ->
  prepend seq p i = p (i - seq_length seq).
Proof using.
  intros * Hle.
  rewrite seq_length_iso_seq_rev_length in *.
  follows apply (proj2 (proj2_sig (rev_prepend_sig (ϕ_seq__seq_rev seq) p))).
Qed.

Theorem in_prepend_seq : forall x y z (seq: R#* x z) (p: path z),
  in_seq y seq ->
  in_path y (prepend seq p).
Proof using.
  intros * Hin.
  apply in_seq__in_seq_at in Hin as [? Hin].
  follows eapply in_prepend_at_seq in Hin.
Qed.

Theorem in_prepend_path : forall x y z (seq: R#* x y) (p: path y),
  in_path z p ->
  in_path z (prepend seq p).
Proof using.
  intros * [i <-].
  exists (i + seq_length seq).
  replace i with ((i + seq_length seq) - seq_length seq) at 2 by lia.
  apply in_prepend_at_path.
  lia.
Qed.


(* Finite prefixes *)

Definition rev_prefix_sig {s} (p: path s) n :
  {prefix: seq_rev R s (p n) |
    seq_rev_length R prefix = n /\
    forall x i, in_seq_rev_at R x i prefix -> p i = x
  }.
Proof using.
  destruct p as (π & <- & HπS); cbn.
  generalize dependent π;
    induction n;
    intros.
  - define exists by constructor.
    after split.
    intros * H.
    follows inv H.
  - specialize (IHn (λ i, π (S i))).
    forward IHn by tedious.
    destruct IHn as (pre_tail & Hlength & Hpre_tail).
    define exists by tedious.
    split.
    + simpl.
      follows rewrite Hlength.
    + intros x i H.
      follows inv! H.
Defined.

Definition rev_prefix {s} (p: path s) n : seq_rev R s (p n) :=
  proj1_sig (rev_prefix_sig p n).

Definition prefix {s} (p: path s) n : R#* s (p n) :=
  seq_rev__seq R (rev_prefix p n).

Lemma prefix_length {s}: forall (p: path s) n,
  seq_length (prefix p n) = n.
Proof using.
  intros *.
  rewrite seq_length_iso_seq_rev_length.
  unfold prefix.
  change (seq_rev__seq _ ?x) with (ϕ_seq__seq_rev⁻¹ x).
  rewrite iso_cancel_inv.
  apply (proj1 (proj2_sig (rev_prefix_sig p n))).
Qed.

Theorem in_prefix_at {s}: forall (p: path s) x i n,
  in_seq_at x i (prefix p n) ->
  p i = x.
Proof using.
  intros * H.
  apply (proj2_sig (rev_prefix_sig p n)).
  fold (rev_prefix p n).
  follows apply in_seq_at__in_seq_rev_at.
Qed.

Theorem in_prefix_at' {s}: forall (p: path s) i n,
  i <= n ->
  in_seq_at (p i) i (prefix p n).
Proof using.
  intros * H.
  rewrite <- (prefix_length p n) in H.
  apply ex_in_seq_at_le_length in H as [? H].
  follows rewrite (in_prefix_at _ _ _ _ H).
Qed.

Theorem inv_in_prefix : forall s (p: path s) n x,
  in_seq x (prefix p n) ->
  in_path_before x (S n) p.
Proof using.
  intros * Hin.
  apply in_seq__in_seq_at in Hin as [i Hin].
  pose proof (in_seq_at_length _ _ _ _ Hin).
  apply in_prefix_at in Hin as <-.
  follows rewrite prefix_length in H.
Qed.

Theorem prefix_nil : forall s (p: path s),
  prefix p 0 ~=~ seq_refl R s.
Proof using.
  intros *.
  follows repeat destructr p.
Qed.


(* More general properties *)

Theorem in_path_star : forall s (p: path s) x,
  in_path x p ->
  R^* s x.
Proof using.
  intros * [i <-].
  induction i.
  - now rewrite state_at_0.
  - destruct p as (π & Hπ0 & HπS); simpl! in *.
    now econstructor.
Qed.

Theorem star_in_path : forall s x,
  R^* s x ->
  exists p: path s, in_path x p.
Proof using t.
  intros * Hstar.
  apply star__seq in Hstar as [seq].
  exists (prepend seq (serial_witness__path x)).
  follows apply in_prepend_seq.
Qed.

Theorem ex_in_path_composition : forall x (px: path x) y (py: path y) z,
  in_path y px ->
  in_path z py ->
  exists px': path x, in_path z px'.
Proof using.
  intros * in_px in_py.
  pose proof (in_path_star _ _ _ in_px) as px_prefix.
  inhabit star__seq in px_prefix.
  exists (prepend px_prefix py).
  follows apply in_prepend_path.
Qed.

End Paths.

Arguments in_path        {state R s}.
Arguments in_path_before {state R s}.
Arguments star_in_path   {state R t}.