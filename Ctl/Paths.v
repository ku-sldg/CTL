Require Import Coq.Logic.FinFun.
Require Import Coq.Classes.RelationClasses.

Require Import Ctl.BinaryRelations.

Require Import Glib.Glib.
Require Import Lia.


Section Paths.

Context {state : Type}.
Variable R : relation state.


CoInductive path (s: state) : Type := 
  | step : forall s', R s s' -> path s' -> path s.


(* This definition forces a path to unfold *)
Definition unfold_path {s} (p: path s) : path s :=
  match p with 
  | step _ s' r p' => step s s' r p'
  end.

Theorem unfold_path_eq {s} : forall p: path s,
  p = unfold_path p.
Proof using.
  intros *.
  now destruct p.
Qed.

Theorem unfold_path_injective {s}: Injective (@unfold_path s).
Proof using.
  intros ? ?.
  now repeat rewrite <- unfold_path_eq.
Qed.

Theorem unfold_path_surjective {s}: Surjective (@unfold_path s).
Proof using.
  intros p; exists p.
  now destruct p.
Qed.

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


Theorem in_path_at_unique : forall n x (p: path x) y z,
  in_path_at y n p ->
  in_path_at z n p ->
  y = z.
Proof using.
  intros n.
  induction n; intros * Hin Hin'.
  - inv Hin.
    now inv Hin'.
  - dependent invc Hin.
    dependent invc Hin'.
    enow eapply IHn.
Qed. 

Theorem in_path_at_succ_related : forall n x (p: path x) y z,
  in_path_at y n p ->
  in_path_at z (S n) p ->
  R y z.
Proof using.
  intros * Hin Hin'.
  induction Hin.
  - invc Hin'.
    find (fun H => now inv H).
  - apply IHHin.
    now dependent invc Hin'.
Qed.

Fixpoint state_at {s} (p: path s) n : state :=
  match p with
  | step _ s' _ p' => 
      match n with 
      | 0 => s
      | S n' => @state_at s' p' n'
      end
  end.

Theorem state_at_spec : forall s (p: path s) n,
  in_path_at (state_at p n) n p.
Proof using.
  intros s p n; revert s p.
  induction n; intros *.
  - destruct p. 
    constructor.
  - destruct p.
    cbn.
    constructor.
    apply IHn.
Qed.

(* Fixpoint path_at {s} (p: path s) n : {x | in_path_at x n p}.
  refine (match p with
  | step _ s' _ p' => 
      match n with 
      | 0 => exist _ s _
      | S n' => 
          match @path_at s' p' n' with 
          | exist _ x prf => exist _ x _
          end
      end
  end).
  - constructor.
  - now constructor.
Defined. *)

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

(* Theorem in_path_at__seq : forall s (p: path s) s' i,
  in_path_at s' i p ->
  exists seq: R#* s s',
    forall x, in_path_before x i p -> in_seq x seq.
Proof using.
  intros * Hin.
  apply isomorphism_refl_exists_inv with (ϕ := ϕ_seq__seq_rev).
  induction Hin.
  - exists (seq_rev_refl R s).
    simpl.
    intros * contra.
    now inv contra.
  - destruct exists IHHin seqr.
    exists (seq_rev_step R s s' x r seqr).
    intros * Hbefore.
    specialize (IHHin x0).
    rewrite <- in_seq_iso_in_seq_rev_flip in *.
    destruct Hbefore as (m & Hlt & Hin').
    dependent invc Hin'.
    + constructor.
    + constructor.
      find applyc.
      exists n0.
      split.
      * lia.
      * assumption.
Qed. *)

Theorem in_path_at__seq : forall s (p: path s) s' i,
  in_path_at s' i p ->
  exists seq: R#* s s',
    forall x, in_path_before x (S i) p -> in_seq x seq.
Proof using.
  intros * Hin.
  apply isomorphism_refl_exists_inv with (ϕ := ϕ_seq__seq_rev).
  induction Hin.
  - exists (seq_rev_refl R s).
    simpl.
    intros * H.
    destruct H as (i & Hlt & H).
    replace i with 0 in * by lia; clear Hlt.
    invc H.
    constructor.
  - destruct exists IHHin seqr.
    exists (seq_rev_step R s s' x r seqr).
    intros * Hbefore.
    specialize (IHHin x0).
    rewrite <- in_seq_iso_in_seq_rev_flip in *.
    destruct Hbefore as (m & Hlt & Hin').
    dependent invc Hin'.
    + constructor.
    + constructor.
      find applyc.
      exists n0.
      split.
      * lia.
      * assumption.
Qed.

Theorem in_path_at__seq' : forall s (p: path s) s' i,
  in_path_at s' i p ->
  exists seq: R#* s s',
    forall x j, 
      j <= i ->
      in_path_at x j p -> in_seq_at x j seq.
Proof using.
  intros * Hin.
  apply isomorphism_refl_exists_inv with (ϕ := ϕ_seq__seq_rev).
  induction Hin.
  - exists (seq_rev_refl R s).
    simpl.
    intros * Hlt Hin.
    invc Hlt.
    invc Hin.
    apply in_seq_at_0.
  - destruct exists IHHin seqr.
    exists (seq_rev_step R s s' x r seqr).
    intros * Hlt Hin'.
    specialize (IHHin x0 j).

    (* Need to proof iso equivalence of in_seq_at and in_seq_at_rev *)

    (* rewrite <- in_seq_iso_in_seq_rev_flip.
    destruct Hbefore as (m & Hlt & Hin').
    dependent invc Hin'.
    + constructor.
    + constructor.
      find applyc.
      exists n0.
      split.
      * lia.
      * assumption. *)
Admitted.

(* Could instead use prefix? *)
Theorem in_path_at__seq'' : forall s (p: path s) s' i,
  in_path_at s' i p ->
  exists seq: R#* s s',
    forall x j, 
      j <= i ->
      in_path_at x j p = in_seq_at x j seq.
Proof using.
  intros * Hin.
  apply isomorphism_refl_exists_inv with (ϕ := ϕ_seq__seq_rev).
  induction Hin.
  - exists (seq_rev_refl R s).
    simpl.
    intros * Hlt.
    invc Hlt.
    extensionality Hin; invc Hin.
    + apply in_seq_at_0.
    + rewrite H2. constructor.
  - destruct exists IHHin seqr.
    exists (seq_rev_step R s s' x r seqr).
    intros * Hlt.
    
    rewrite <- in_seq_at_iso_in_seq_rev_at_flip.
    destruct j.
    + specialize (IHHin x0 0).
      forward IHHin by lia.
      extensionality H; inv H; constructor.
    + specialize (IHHin x0 j).
(* 
    specialize (IHHin x0 j).
    rewrite <- in_seq_at_iso_in_seq_rev_at_flip in *.
    destruct j.

  - destruct exists IHHin seqr.
    exists (seq_rev_step R s s' x r seqr).
    intros * Hlt Hin'.
    specialize (IHHin x0 j).
 *)
Admitted. 

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

Inductive prefix_rev {s}: forall {s'}, seq_rev R s s' -> path s -> Prop :=
  | prefix_rev_trivial : forall (p: path s),
      prefix_rev (seq_rev_refl R s) p
  | prefix_rev_step : forall x y (seqr: seq_rev R x y) (p: path x) (r: R s x),
      prefix_rev seqr p ->
      prefix_rev (seq_rev_step R s x y r seqr) (step s x r p).
    
Definition prefix {s s'} (r: R#* s s') : path s -> Prop :=
  prefix_rev (ϕ_seq__seq_rev r).

Theorem seq_prefix : forall s s',
  serial_witness R ->
  forall seq: R#* s s',
    Σ p: path s, prefix seq p.
Proof using.
  intros * Hserial *.
  iso ϕ_seq__seq_rev seq.
  induction seq.
  - exists (serial_witness__path Hserial x).
    constructor.
  - destruct exists IHseq p.
    exists (step x y r p).
    unfold prefix in *.
    rewrite iso_cancel_inv.
    rewrite iso_cancel_inv in IHseq.
    now constructor.
Defined.

Theorem in_prefix: forall x (p: path x) z (seq: R#* x z) y,
  prefix seq p ->
  in_seq y seq ->
  in_path y p.
Proof using.
  intros *.
  iso ϕ_seq__seq_rev seq.
  intros Hprefix Hin.
  unfold prefix in Hprefix.
  rewrite iso_cancel_inv in Hprefix.
  rewrite <- in_seq_iso_in_seq_rev_flip in Hin.
  induction Hprefix.
  - invc Hin.
    destruct p.
    constructor.
  - dependent invc Hin.
    + constructor.
    + constructor.
      now find apply.
Qed.

(* Theorem path_to_index_fun_spec : forall x (p: path x)
  (path_to_index_fun p 0) *)

(* Definition path_to_index_fun : forall x (p: path x),
  { f : nat -> state | 
      f 0 = x /\
      forall n, R (f n) (f (S n))
  }.
Proof using.
  intros * p.
  define exists.
  - intro n.
    destruct (path_at p n) as [s ?].
    exact s.
  - split.
    + destruct (path_at p 0) as [? Hin].
      now inv Hin.
    + intro n.
      destruct (path_at p n) as [? Hin],
               (path_at p (S n)) as [? Hin'].
      simpl.
      enow eapply in_path_at_succ_related.
Defined. *)

Definition index_fun_to_path_n (f: nat -> state) (H: forall n, R (f n) (f (S n)))
  : Π n, path (f n) :=
  (cofix p (n: nat) : path (f n) := step (f n) (f (S n)) (H n) (p (S n))).

Theorem index_fun_to_path_n_unfold :
  forall (f: nat -> state) (H: forall n, R (f n) (f (S n))) n,
    index_fun_to_path_n f H (n) =
    step (f n) (f (S n)) (H n) (index_fun_to_path_n f H (S n)).
Proof using.
  intros *.
  now apply unfold_path_injective.
Qed.

Definition index_fun_to_path (f: nat -> state) (H: forall n, R (f n) (f (S n)))
  : path (f 0) :=
  index_fun_to_path_n f H 0.
 
Definition index_fun_to_path_spec :
  forall (f: nat -> state) (H: forall n, R (f n) (f (S n))) n,
    in_path_at (f n) n (index_fun_to_path f H).
Proof using.
  intros *.
  cut (forall m, in_path_at (f (n + m)) n (index_fun_to_path_n f H m)).
  - intros Hcut. 
    replace n with (n + 0) at 1 by lia.
    apply Hcut.
  - induction n; intros m.
    + simpl.
      rewrite index_fun_to_path_n_unfold.
      constructor.
    + rewrite index_fun_to_path_n_unfold.
      constructor.
      replace (S n + m) with (n + S m) by lia.
      apply IHn.
Qed.

Theorem state_at_index_fun :
  forall (f: nat -> state) (H: forall n, R (f n) (f (S n))),
    state_at (index_fun_to_path f H) = f.
Proof using.
  intros *.
  extensionality n.
  cut (forall m, state_at (index_fun_to_path_n f H m) n = f (n + m)).
  - intros Hcut.
    replace n with (n + 0) at 2 by lia.
    apply Hcut.
  - induction n; intros m.
    + reflexivity.
    + cbn.
      replace (S (n + m)) with (n + S m) by lia.
      apply IHn.
Qed.

CoInductive path_eq : forall {s}, path s -> path s -> Prop :=
  | path_eq_intro : forall x y r p p',
      path_eq p p' ->
      path_eq (step x y r p) (step x y r p').

Theorem path_eq_refl : forall s,
  reflexive (path s) path_eq.
Proof using.
  cofix coIH.
  intros * [].
  constructor.
  apply coIH.
Qed.

Theorem path_eq_sym : forall s,
  symmetric (path s) path_eq.
Proof using.
  cofix coIH.
  intros * [] q Heq.
  dependent invc Heq.
  replace r1 with r by (apply proof_irrelevance).
  constructor.
  now apply coIH.
Qed.

Theorem path_eq_trans : forall s,
  transitive (path s) path_eq.
Proof using.
  cofix coIH.
  intros * x y z Heq Heq'.
  dependent invc Heq.
  dependent invc Heq'.
  replace r1 with r by (apply proof_irrelevance).
  constructor.
  enow eapply coIH.
Qed.

Instance path_eq_Equivalence {s} : Equivalence (@path_eq s).
  max split.
  - apply path_eq_refl.
  - apply path_eq_sym.
  - apply path_eq_trans.
Defined.

Axiom path_eq_extensionality : forall s (p q: path s),
  path_eq p q ->
  p = q.

Theorem path_eq_is_eq : forall s (p q: path s),
  path_eq p q <-> p = q.
Proof using.
  intros *.
  split.
  - apply path_eq_extensionality.
  - now intros <-.
Qed.

Theorem path_eq_unfold : forall s (p q: path s),
  path_eq (unfold_path p) (unfold_path q) ->
  path_eq p q.
Proof using.
  intros * H.
  rewrite (unfold_path_eq p).
  now rewrite (unfold_path_eq q).
Qed.

(* For some reason, coinductive proofs based on this proposition are not 
   well-guarded unless we rewrite directly.
 *)
Ltac apply_path_eq_unfold :=
  match goal with 
  | |- path_eq ?x ?y =>
      rewrite (unfold_path_eq x);
      rewrite (unfold_path_eq y)
  end.

Ltac proof_irrelevance := apply proof_irrelevance.

(* Ltac get_hyp_body H := 
  match goal with
    | H' := ?body |- _ => 
      match H' with 
      | H => body
      end
  end.
 *)

Theorem index_fun_to_path_Sn_state_at_unfold : 
  forall s s' (r: R s s') (p: path s') H H' n,
    (index_fun_to_path_n (state_at (step s s' r p)) H (S n)) =
    (index_fun_to_path_n (state_at p) H' n). 
Proof using.
  (* intros *; revert n. *)
  intros *.
  apply path_eq_is_eq.
  revert n.
  cofix coIH; intros n.
  apply_path_eq_unfold.
  cbn.
  replace (H (S n)) with (H' n) by proof_irrelevance.
  constructor.
  apply (coIH (S n)).
Qed.

Lemma state_at_unfold : forall s s' s'' r r' p n,
  state_at (step s s' r (step s' s'' r' p)) (S n) =
  state_at (step s' s'' r' p) n.
Proof using.
  trivial.
Qed.

Theorem index_fun_state_at : 
  forall s (p: path s) (H: forall n, R (state_at p n) (state_at p (S n))),
    index_fun_to_path (state_at p) H ~= p.
Proof using.
  intros *.
  destruct p.
  apply heq_is_eq.
  apply path_eq_is_eq.
  revert s s' r p H.
  cofix coIH.
  intros.
  apply_path_eq_unfold.
  cbn.
  destruct p.
  replace (H 0) with r by proof_irrelevance.
  constructor.
  unshelve erewrite index_fun_to_path_Sn_state_at_unfold.
  { intro n.
    repeat rewrite <- (state_at_unfold s s' s'0 r r0 p).
    apply H.
  }
  apply coIH.
Qed.

Definition path_iso_index_fun {s} :
  path s ≃> {f: nat -> state | f 0 = s /\ forall n, R (f n) (f (S n))}.
Proof using.
  define exists.
  { intro p.
    exists (state_at p).
    split.
    - now destruct p.
    - intro n.
      eapply in_path_at_succ_related;
      apply state_at_spec.
  }
  define exists.
  { intros (f & <- & H).
    exact (index_fun_to_path f H).
  }
  split.
  - intros (f & <- & H).
    cbn.
    apply exist_eq.
    apply state_at_index_fun.
  - intros [].
    cbn.
    apply heq_is_eq.
    apply (index_fun_state_at s (step s s' r p)).
Defined.


End Paths.

Arguments in_path        {state R s}.
Arguments in_path_at     {state R s}.
Arguments in_path_before {state R s}.
