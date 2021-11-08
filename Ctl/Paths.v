Require Import Coq.Classes.RelationClasses.

Require Import Ctl.BinaryRelations.

Require Import Glib.Glib.
Require Import Lia.


Section Paths.

Context {state : Type} (R: relation state).

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


(* Properties *)

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

Definition path_drop {s} (p: path s) (n: nat) : path (p n).
  exists (λ i, p (i + n)).
  after split.
  intro i.
  simpl!.
  follows destruct p.
Defined.

Definition serial_witness__path (witness: serial_witness R) s : path s.
  exists (nat_rect _ s (λ _ x, proj1_sig (witness x))).
  split.
  - reflexivity.
  - intros ?.
    cbn.
    now destruct (witness _).
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
    p = path_cons x r (path_drop p 1).
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
    p = path_cons x r (path_drop p 1).
Proof using.
  intros *.
  follows destruct (destruct_path x p).
Qed.

Theorem all_destruct_path : forall x (p: path x),
  forall (r: R x (p 1)),
    p = path_cons x r (path_drop p 1).
Proof using.
  intros *.
  destruct (ex_destruct_path x p) as [r' ?].
  replace r with r' by apply proof_irrelevance.
  assumption.
Qed.

Definition prepend {x y} (seq: R#* x y) (p: path y) : path x.
  apply seq__seq_rev in seq.
  induction seq.
  - assumption.
  - specializec IHseq p.
    follows eapply path_cons.
Defined.

Definition prefix {s} (p: path s) n : R#* s (p n).
  induction n.
  - rewrite state_at_0.
    constructor.
  - destruct p as (π & Hπ0 & HπS); cbn in *.
    econstructor.
    + apply HπS.
    + assumption.
Defined.

Theorem prefix_nil : forall s (p: path s),
  prefix p 0 ~= seq_refl R s.
Proof using.
  intros *.
  follows simpl!.
Qed.

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

Theorem prefix_cons : forall n x y (p: path y) (r: R x y),
  prefix (path_cons x r p) (S n) = seq_prepend R x y (p n) r (prefix p n).
Proof using.
  intro n.
  induction n.
  - intros.
    apply JMeq_eq.
    follows simpl! with state_at_0.
  - intros.
Admitted.

Theorem in_seq_at_prefix : forall x y z (p: path y) n i (r: R x y),
  in_seq_at z (S i) (prefix (path_cons x r p) (S n)) ->
  in_seq_at z i (prefix p n).
Proof using.
Admitted.

Theorem in_prefix_at : forall s (p: path s) n x i,
  in_seq_at x i (prefix p n) ->
  p i = x.
Proof using. 
  intros * H.
  after induction H.
Admitted.

Theorem inv_in_prefix : forall s (p: path s) n x,
  in_seq x (prefix p n) ->
  in_path_before x (S n) p.
Admitted.

(* Theorem inv_in_prefix : forall s (p: path s) n x,
  in_nseq x (prefix p n) ->
  in_path x p.
Admitted.  *)

Theorem in_prepend_seq : forall x y z (seq: R#* x z) (p: path z),
  in_seq y seq ->
  in_path y (prepend seq p).
Proof using.
  intros * Hin.
Admitted.

Theorem in_prepend_path : forall x y z (seq: R#* x y) (p: path y),
  in_path z p ->
  in_path z (prepend seq p).
Proof using.
Admitted.

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
