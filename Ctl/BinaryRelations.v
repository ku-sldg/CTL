Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Lists.List.

Require Import Setoid.
Require Import Lia.
Require Import Glib.Glib.

Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Relations.Relation_Operators.


(* star - a reflexive transitive closure *)
Definition star {A} (R: relation A) : relation A := clos_refl_trans_n1 A R.
Notation "R ^*" := (star R) (at level 5, format "R ^*").

(* seq - a transparent sequence of relation steps.
   It is equivalent to the reflexive transitive closure, but is a `Type` rather than a `Prop`.
 *)
Reserved Notation "R #*" (at level 5, format "R #*").
Inductive seq {A} (R: relation A) : A -> A -> Type :=
  | seq_refl : forall x,
      R#* x x
  | seq_step : forall x y z,
      R y z ->
      R#* x y ->
      R#* x z
  where "R #*" := (seq R).

(* nseq - a length-indexed transition sequence *)
Reserved Notation "R #" (at level 5, format "R #").
Inductive nseq {A} (R: relation A) : nat -> A -> A -> Type :=
  | nseq_refl : forall x,
      R#0 x x
  | nseq_step : forall n x y z,
      R y z ->
      R#n x y ->
      R#(S n) x z
  where "R #" := (nseq R).
Notation "R # n" := (nseq R n) (at level 5, format "R # n").


(* Inductive in_seq {A} {R: relation A} {a}
  : forall {a'}, A -> R#* a a' -> Prop :=
  | in_seq_head_refl :
      in_seq a (seq_refl R a)
  (* | in_seq_head_step : forall x x' r p,
      in_seq x' (seq_step R a x x' r p) *)
  | in_seq_head_step : forall x x' r p,
      in_seq a (seq_step R a x x' r p)
  | in_seq_tail : forall x x' y r p,
      in_seq y p ->
      in_seq y (seq_step R a x x' r p). *)

Fixpoint seq_length {A} {R: relation A} {a a'} (seq: R#* a a') :=
  match seq with 
  | seq_refl _ x => 0
  | seq_step _ x y z r seq' => S (seq_length seq')
  end.

Inductive in_seq {A} {R: relation A} {a}
  : forall {a'}, A -> R#* a a' -> Prop :=
  | in_seq_head : forall a' (seq: R#* a a'),
      in_seq a' seq
  | in_seq_tail : forall x x' y r seq,
      in_seq y seq ->
      in_seq y (seq_step R a x x' r seq).

Inductive in_seq_at {A} {R: relation A} {a}
  : forall {a'}, A -> nat -> R#* a a' -> Prop :=
  | in_seq_at_head : forall a' (seq: R#* a a'),
      in_seq_at a' (seq_length seq) seq
  | in_seq_at_tail : forall n x x' y r seq,
      in_seq_at y n seq ->
      in_seq_at y n (seq_step R a x x' r seq).


(* This is an old, more complicated definition
   TODO: rewrite in the style of in_seq
 *)
Inductive in_nseq {A} {R: relation A} {a}
  : forall {n a'}, A -> R#n a a' -> Prop :=
  | in_nseq_head_refl :
      in_nseq a (nseq_refl R a)
  | in_nseq_head_step : forall n x x' r p,
      in_nseq x' (nseq_step R n a x x' r p)
  | in_nseq_tail : forall n x x' y r p,
      in_nseq y p ->
      in_nseq y (nseq_step R n a x x' r p).

Inductive in_nseq_at {A} {R: relation A} {a}
  : forall {n a'}, A -> nat -> R#n a a' -> Prop :=
  | in_nseq_at_head_refl :
      in_nseq_at a 0 (nseq_refl R a)
  | in_nseq_at_head_step : forall n x x' r p,
      in_nseq_at x' (S n) (nseq_step R n a x x' r p)
  | in_nseq_at_tail : forall n m x x' y r p,
      in_nseq_at y m p ->
      in_nseq_at y m (nseq_step R n a x x' r p).


(* Misc. definitions *)

Definition is_serial {A} (R: relation A) := forall a, exists b, R a b.
Definition serial A := {R: relation A | is_serial R}.

Definition serial_witness {A} (R: relation A) := forall a, {b | R a b}.
Definition serialT A := {R: relation A & serial_witness R}.

Definition rel_singleton {A} (x y : A): relation A :=
  fun x' y' => x' = x /\ y' = y -> True.


Section BinaryRelationsProperties.

Context {A: Type}.
Variable R : relation A.

(* star properties *)

Theorem star_refl :
  reflexive A R^*.
Proof using.
  constructor.
Qed.

Theorem star_trans : 
  transitive A R^*.
Proof using.
  unfold transitive.
  intros * Hxy Hyz.
  induction Hyz.
  - assumption.
  - follows econstructor.
Qed.

Lemma star_lift : forall x y, 
  R x y ->
  R^* x y.
Proof using.
  intros * H.
  econstructor.
  - eassumption.
  - constructor.
Qed.

Theorem rt1n_star : forall x y,
  clos_refl_trans_1n A R x y -> star R x y.
Proof.
  intros * ?.
  apply clos_rt_rtn1.
  now apply clos_rt1n_rt.
Qed.

Theorem star_rt1n : forall x y,
  star R x y -> clos_refl_trans_1n A R x y.
Proof.
  intros * ?.
  apply clos_rt_rt1n.
  now apply clos_rtn1_rt.
Qed.

Theorem star_rt1n_trans : forall x y z,
  R x y ->
  R^* y z ->
  R^* x z.
Proof using.
  intros.
  apply rt1n_star.
  econstructor.
  - eassumption.
  - now apply star_rt1n.
Qed.


(* seq properties *)

Theorem seq__star : forall x y,
  R#* x y ->
  R^* x y.
Proof using.
  intros * H.
  induction H.
  - constructor.
  - follows econstructor.
Qed.

Theorem star__seq : forall x y,
  R^* x y ->
  ‖R#* x y‖.
Proof using.
  intros * H.
  induction H.
  - repeat constructor.
  - find uninhabit.
    constructor.
    follows econstructor.
Qed.

Definition seq_singleton {x y} (r: R x y)
  : R#* x y :=
  seq_step R x x y r (seq_refl R x).

(* Require Import Coq.Init.Nat.
Check PeanoNat.Nat.ltb_lt. *)
(* Definition refl_lt_ltb {n m} (n < m) : {} *)

Definition seq_tail {x z} (r: R#* x z) (p: seq_length r > 0) : Σ y, R#* y z.
  induction r.
  - follows exfalso.
  - destruct r0.
    + exists x.
      follows apply seq_singleton.
    + forward IHr by (cbn; lia).
      destruct exists IHr s.
      exists s.
      tedious.
Defined.

(* Fixpoint get_seq_at {x y} (r: R#* x y) (n: nat) (p: n < seq_length r): A :=
  match n with 
  | 0 => x
  | S n' => get_seq_at
  end. *)

Theorem in_seq_first : forall x y (r: R#* x y),
  in_seq x r.
Proof using.
  intros *.
  induction r.
  - constructor.
  - now constructor.
Qed.

Theorem in_seq_at_0 : forall x y (r: R#* x y),
  in_seq_at x 0 r.
Proof using.
  intros *.
  induction r.
  - fold (seq_length (seq_refl R x)).
    constructor.
  - now constructor.
Qed.

Theorem inv_in_seq_at_0 : forall x y (r: R#* x y) s,
  in_seq_at s 0 r ->
  s = x.
Proof using.
  intros * H.
  after induct! H as [z r|].
  follows destruct r.
Qed.

Theorem in_seq_at_unique : forall x y (r: R#* x y) s s' i,
  in_seq_at s i r ->
  in_seq_at s' i r ->
  s = s'.
Proof using.
  intros * H H'.
  induction i.
  - follows apply inv_in_seq_at_0 in H, H'.
  -
Admitted.

Lemma in_seq_at__in_seq {x y z}: forall (r: R#* x z) i,
  in_seq_at y i r ->
  in_seq y r.
Proof using.
  tedious.
Qed.

Lemma in_seq__in_seq_at {x y z}: forall (r: R#* x z),
  in_seq y r ->
  exists i, in_seq_at y i r.
Proof using.
  intros * H.
  follows induction H.
Qed.

Lemma ex_in_seq_at_lt_length {x z}: forall (r: R#* x z) i,
  i < seq_length r ->
  exists y, in_seq_at y i r.
Proof using.
  intros * ilt.
  induction r.
  - inv ilt.
  - simpl! in ilt.
    follows inv ilt.
Qed.

Lemma in_seq_at_length {x z}: forall (r: R#* x z) y i,
  in_seq_at y i r ->
  i < seq_length r.
Proof using.
  intros *.
Admitted.

Lemma in_seq_at_succ_related {w z}: forall (r: R#* w z) x y i,
  in_seq_at x i r ->
  in_seq_at y (S i) r ->
  R x y.
Proof using.
  intros * Hin Hin'.
Admitted.

(* Print seq.
(* proper seq prefixes *)
Inductive seq_pprefix {x y z} : R#* x y -> R#* x z -> Prop :=
  | seq_pprefix_intro : forall r,
      seq_pprefix r (seq_step x y z)
 *)
Definition seq_prefix {x y z} (pre: R#* x y) (seq: R#* x z) :=
  forall s i, in_seq_at s i pre -> in_seq_at s i seq.

(* Definition seq_prefix_sig {x} : relation (Σ y, R#* x y) := λ pre seq,
  seq_length (projT2 pre) < seq_length (projT2 seq) /\
  forall s i, in_seq_at s i (projT2 pre) -> in_seq_at s i (projT2 seq).

Theorem wf_seq_prefix_sig {x}: well_founded (@seq_prefix_sig x).
Proof using.
  intros r.
  gen s := r to (λ j, j <= r \/) by tedious;
    cbn; revert j. *)

(* Print in_seq_at.
Check in_seq_at_ind.


Theorem in_seq_at_strong_nondep_ind : forall a,
  forall P: A -> nat -> Prop,
  (forall x (seq: R#* a x), P x (seq_length seq)) ->
  (forall x (seq: R#* a x) n i,
    n < i ->
    P x n -> 
    P (seq_step) 
  ) *)
 

(* Inductive AccFamily (R: forall {a b}, X a -> X b -> Prop) {a} (x: X a) :=
  | AccFamily_intro : (forall ) *)

Lemma ex_seq_prefix {x y z} : forall (r: R#* x z),
  in_seq y r ->
  exists prefix: R#* x y, 
    forall s i, in_seq_at s i prefix -> in_seq_at s i r.
Proof using.
  (* Wow, `tedious` is impressive! *)
  (* time tedious. *)
  tedious.

  (* intros * Hin.
  induction Hin.
  - exists seq0.
    easy.
  - destruct exists IHHin prefix.
    exists prefix.
    intros.
    constructor.
    auto. *)

 (* intros * Hin.
  induction Hin.
  - follows define exists by assumption.
  - follows destruct exists IHHin prefix. *)
Qed.

Lemma ex_seq_at_prefix {x y z} : forall (r: R#* x z) n,
  in_seq_at y n r ->
  exists prefix: R#* x y, 
    seq_length prefix = n /\
    forall s i, in_seq_at s i prefix -> in_seq_at s i r.
Proof using.
  intros * Hin.
  induction Hin.
  - follows define exists by assumption.
  - follows destruct exists IHHin prefix.
Qed.

(* Note equivalence to transitivity under Curry-Howard reflection to star *)
Definition seq_concat {x y z} (Rxy: R#* x y) (Ryz: R#* y z)
  : R#* x z.
Proof using.
  induction Ryz.
  - assumption.
  - econstructor.
    + eassumption.
    + find applyc.
      assumption.
Defined.

Theorem seq_concat_refl : forall x y (r: R#* x y),
  seq_concat (seq_refl R x) r = r.
Proof using.
  intros *.
  induction r.
  - reflexivity.
  - simpl.
    now find rewrite.
Qed.  

Theorem seq_concat_assoc : forall w x y z,
  forall (a: R#* w x) (b: R#* x y) (c: R#* y z),
    seq_concat (seq_concat a b) c =
    seq_concat a (seq_concat b c).
Proof using.
  intros *.
  max induct c.
  - reflexivity.
  - simpl.
    follows find rewrite.
Qed.

Theorem in_seq__concat {x y z}: forall (a: R#* x y) (b: R#* y z) n,
  in_seq n (seq_concat a b) <-> in_seq n a \/ in_seq n b.
Proof using.
  intros *.
  split; intro H. 
  - induction b.
    + simpl in H.
      now left.
    + simpl in *.
      (* inv H. *)
      (* inversion_sigma. *)
      (* rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq in H1. *)
      dependent invc H.
      * right. constructor.
      * specialize (IHb a H2); clear H2.
        destruct IHb.
       -- now left.
       -- right. constructor. assumption.
  - destruct H.
    + induction b.
      * assumption.
      * simpl.
        constructor.
        now find apply.
    + induction b.
      * simpl.
        inversion H; subst.
        constructor.
      * simpl.
        dependent invc H.
       -- constructor.
       -- constructor.
          now find apply.
Qed.

Theorem in_seq_at__concat_l {x y z}: forall (a: R#* x y) (b: R#* y z) n i,
  in_seq_at n i a -> in_seq_at n i (seq_concat a b).
Proof using.
  intros * H.
  induction b.
  (* max induction b. *)
  - assumption.
  - simpl.
    constructor.
    now find applyc.
Qed.

Theorem in_seq_at__concat_r {x y z}: forall (a: R#* x y) (b: R#* y z) n i,
  in_seq_at n i b -> in_seq_at n (seq_length a + i) (seq_concat a b).
Proof using.
  intros * H.
  induction b.
  - dependent invc H.
    simpl.
    rewrite PeanoNat.Nat.add_0_r.
    constructor.
  - simpl.
    dependent invc H.
    + clear IHb. 
      simpl.
      match goal with 
      | |- in_seq_at _ ?i ?seq => 
          replace i with (seq_length seq)
      end; [constructor|].
      simpl.
      rewrite PeanoNat.Nat.add_succ_r.
      f_equal.
      clear.
      induction b; simpl; try find rewrite; lia.
    + constructor.
      now find apply.
Qed.

Lemma seq_length_concat {x y z}: forall (a: R#* x y) (b: R#* y z),
  seq_length (seq_concat a b) = seq_length a + seq_length b.
Proof using.
  intros *.
  induction b; simpl; try find rewrite; lia.
Qed.

Definition seq_prepend (x y z: A):
  R x y ->
  R#* y z ->
  R#* x z.
Proof using.
  intros ? Ryz.
  induction Ryz.
  - now apply seq_singleton.
  - econstructor.
    + eassumption.
    + now find apply.
Defined.

(* Isomorphic to seq. Sometimes, this reversed structure is more convenient
   (Note the "growth" step prepends rather than appending to the end)
*)
Inductive seq_rev : A -> A -> Type :=
  | seq_rev_refl : forall x,
      seq_rev x x
  | seq_rev_step : forall x y z,
      R x y ->
      seq_rev y z ->
      seq_rev x z.

Fixpoint seq_rev_length {a a'} (seqr: seq_rev a a') :=
  match seqr with 
  | seq_rev_refl x => 0
  | seq_rev_step x y z r seq' => S (seq_rev_length seq')
  end.

Definition seq_rev_concat {x y z} (Rxy: seq_rev x y) (Ryz: seq_rev y z)
  : seq_rev x z.
Proof using.
  induction Rxy.
  - assumption.
  - econstructor.
    + eassumption.
    + find applyc.
      assumption.
Defined.

Definition seq__seq_rev {x y} (seq: R#* x y): seq_rev x y.
  induction seq.
  - constructor.
  - eapply seq_rev_concat; [eassumption|].
    econstructor.
    + eassumption.
    + constructor.
Defined.

Definition seq_rev__seq {x y} (seqr: seq_rev x y): R#* x y.
  induction seqr.
  - constructor.
  - eapply seq_concat; [|eassumption].
    econstructor.
    + eassumption.
    + constructor.
Defined.

Theorem seq_rev_concat_refl : forall x y (r: seq_rev x y),
  seq_rev_concat r (seq_rev_refl y) = r.
Proof using.
  intros *.
  induction r.
  - reflexivity.
  - simpl.
    now find rewrite.
Qed.  

Theorem seq_rev_concat_assoc : forall w x y z,
  forall (a: seq_rev w x) (b: seq_rev x y) (c: seq_rev y z),
    seq_rev_concat (seq_rev_concat a b) c =
    seq_rev_concat a (seq_rev_concat b c).
Proof using.
  intros *.
  (* revert y z b c; induct a. *)
  max induct a.
  - reflexivity.
  - simpl.
    follows find rewrite.
Qed.
  
Theorem seq__seq_rev__concat {x y z}: forall (a: R#* x y) (b: R#* y z),
  seq__seq_rev (seq_concat a b) = seq_rev_concat (seq__seq_rev a) (seq__seq_rev b).
Proof using.
  intros *.
  revert x a; induct b; intros.
  - simpl.
    now rewrite seq_rev_concat_refl.
  - simpl seq_concat; simpl seq__seq_rev at 1.
    find rewrite ->.
    rewrite seq_rev_concat_assoc.
    reflexivity.
Qed.

Theorem seq_rev__seq__concat {x y z}: forall (a: seq_rev x y) (b: seq_rev y z),
  seq_rev__seq (seq_rev_concat a b) = seq_concat (seq_rev__seq a) (seq_rev__seq b).
Proof using.
  intros *.
  revert z b; induct a; intros.
  - simpl.
    now rewrite seq_concat_refl.
  - simpl seq_rev_concat; simpl seq_rev__seq at 1.
    find rewrite ->.
    rewrite <- seq_concat_assoc.
    reflexivity.
Qed.

Definition ϕ_seq__seq_rev : forall x y,
  R#* x y ≃> seq_rev x y.
Proof using.
  intros *.
  exists (@seq__seq_rev x y) (@seq_rev__seq x y).
  split.
  - intros *.
    induct b.
    + reflexivity.
    + simpl.
      rewrite seq__seq_rev__concat.
      simpl.
      now find rewrite.
  - intros *.
    induct a.
    + reflexivity.
    + simpl.
      rewrite seq_rev__seq__concat.
      simpl.
      now find rewrite.
Defined.

Theorem isomorphic_seq__seq_rev : forall x y,
  R#* x y ≃ seq_rev x y.
Proof using.
  intros.
  apply isomorphism__isomorphic.
  apply ϕ_seq__seq_rev.
Qed.

(* equivalent to in_seq under the obvious isomorphism *)
Inductive in_seq_rev {a} 
  : forall {a'}, A -> seq_rev a a' -> Prop :=
  | in_seq_rev_head : forall a' (seqr: seq_rev a a'),
      in_seq_rev a seqr
  | in_seq_rev_tail : forall x x' y r seqr,
      in_seq_rev y seqr ->
      in_seq_rev y (seq_rev_step a x x' r seqr).

Inductive in_seq_rev_at {a} 
  : forall {a'}, A -> nat -> seq_rev a a' -> Prop :=
  | in_seq_rev_at_head : forall a' (seqr: seq_rev a a'),
      in_seq_rev_at a 0 seqr
  | in_seq_rev_at_tail : forall n x x' y r seqr,
      in_seq_rev_at y n seqr ->
      in_seq_rev_at y (S n) (seq_rev_step a x x' r seqr).


Theorem in_seq_rev_at__concat_l {x y z}: forall (a: seq_rev x y) (b: seq_rev y z) n i,
  in_seq_rev_at n i a -> in_seq_rev_at n i (seq_rev_concat a b).
Proof using.
  intros * H.
  max induction a.
  - follows inv H.
  - simpl.
    follows dependent invc H.
Qed.

Theorem in_seq_rev_at__in_seq_at {x y z i} {seqr: seq_rev x z}:
  in_seq_rev_at y i seqr ->
  in_seq_at y i (seq_rev__seq seqr).
Proof using.
  intros Hin.
  max induction Hin.
  - induction seqr.
    + simpl.
      apply in_seq_at_0.
    + simpl.
      apply in_seq_at__concat_l.
      constructor.
      apply in_seq_at_0.
  - simpl.
    change (S n) with (seq_length (seq_step R a a x r (seq_refl R a)) + n).
    follows apply in_seq_at__concat_r.
Qed.

Theorem in_seq_at__in_seq_rev_at__iso {x y z i} {seqr: seq_rev x z}:
  in_seq_at y i ((ϕ_seq__seq_rev x z)⁻¹ seqr) ->
  in_seq_rev_at y i seqr.
Proof using.
  intros Hin.
  max induct Hin.
  - after induction seqr.
    simpl.
    follows rewrite seq_length_concat.
  - change (seq_rev__seq ?x) with ((ϕ_seq__seq_rev _ _)⁻¹ x) in H0.
    apply eq_cancel_right in H0.
    especialize IHHin; forward IHHin by apply inv_cancel_iso.
    simpl in H0;
    change (seq__seq_rev ?x) with (ϕ_seq__seq_rev _ _ x) in H0.
    subst.
    follows apply in_seq_rev_at__concat_l.
Qed. 

Theorem in_seq_at__in_seq_rev_at {x y z i} {seqr: seq_rev x z}:
  in_seq_at y i (seq_rev__seq seqr) ->
  in_seq_rev_at y i seqr.
Proof using.
  apply in_seq_at__in_seq_rev_at__iso.
Qed.

Theorem in_seq_at__in_seq_rev_at__iso' {x y z i} {seq: R#* x z}:
  in_seq_at y i seq ->
  in_seq_rev_at y i (ϕ_seq__seq_rev x z seq).
Proof using.
  iso ϕ_seq__seq_rev seq seqr.
  rewrite iso_cancel_inv.
  apply in_seq_at__in_seq_rev_at__iso.
Qed.

(* Definition get_seq_rev_at ()

Definition get_seq_at *)
      
Theorem in_seq_iso_in_seq_rev_flip : forall x y z,
  forall b: seq_rev x y, in_seq_rev z b = in_seq z ((ϕ_seq__seq_rev x y)⁻¹ b).
Proof using.
  intros *.
  induct b; extensionality.
  - simpl.
    split; intro; find inversion; subst; constructor.
  - split; intro H; simpl in *.
    + apply in_seq__concat.
      rewrite <- IHb.
      dependent inv H.
      * left.
        repeat constructor.
      * auto.
    + apply in_seq__concat in H.
      rewrite <- IHb in H.
      destruct H.
      * dependent inv H.
       -- destruct b; repeat constructor.
       -- inversion H3; subst.
          repeat constructor.
      * now constructor.
Qed.

Theorem in_seq_iso_in_seq_rev : forall x y z,
  iso_equiv (ϕ_seq__seq_rev x y) (@in_seq A R x y z) (@in_seq_rev x y z).
Proof using.
  intros *.
  rewrite iso_equiv_flip.
  apply in_seq_iso_in_seq_rev_flip.
Qed.

Theorem seq_length_iso_seq_rev_length : forall x y,
  iso_equiv (ϕ_seq__seq_rev x y) seq_length seq_rev_length.
Proof using.
  intros *.
  rewrite iso_equiv_flip.
  intros seqr.
  after max induction seqr.
  simpl.
  rewrite seq_length_concat.
  simpl.
  follows f_equal.
Qed.

Lemma in_seq_rev_at_last : forall x y (seqr: seq_rev x y),
  in_seq_rev_at y (seq_length (seq_rev__seq seqr)) seqr.
Proof using.
Admitted.

Theorem in_seq_at_iso_in_seq_rev_at_flip : forall x y z n,
  forall b: seq_rev x y, in_seq_rev_at z n b = in_seq_at z n ((ϕ_seq__seq_rev x y)⁻¹ b).
Proof using.
  intros *.
  max induct b; extensionality.
  - simpl.
    split; intro H.
    + invc H.
      apply in_seq_at_0.
    + dependent invc H.
      constructor.
  - split; intro H; simpl in *.
    + dependent inv H.
      * apply in_seq_at_0.
      * replace (S n0) with 
          (seq_length (seq_step R x x y r (seq_refl R x)) + n0)
          by reflexivity.
        apply in_seq_at__concat_r.
        now find rewrite.
    + dependent inv H.
      * replace (seq_length (seq_concat (seq_step R x x y r (seq_refl R x)) (seq_rev__seq b))) with 
          (S (seq_length (seq_rev__seq b))).
          constructor.
        apply in_seq_rev_at_last.
        rewrite seq_length_concat.
        reflexivity.
      * apply (f_equal seq__seq_rev) in H0.
        rewrite seq__seq_rev__concat in H0.
        pose proof (rew := fun x y => iso_cancel_inv (ϕ_seq__seq_rev x y));
          simpl in rew.
        rewrite rew in H0; clear rew.

        simpl seq_rev_concat in H0.
        rewrite <- H0.

        simpl.
        apply in_seq_rev_at__concat_l.
Admitted.

Theorem in_seq_at_iso_in_seq_rev_at : forall x y z i,
  iso_equiv (ϕ_seq__seq_rev x y) (@in_seq_at A R x y z i) (@in_seq_rev_at x y z i).
Proof using.
  intros *.
  rewrite iso_equiv_flip.
  apply in_seq_at_iso_in_seq_rev_at_flip.
Qed.


(* nseq properties *)

Definition nseq__seq {n} {x y}:
  R#n x y ->
  R#* x y.
Proof using.
  intros * H.
  induction H.
  - constructor.
  - econstructor; eassumption.
Defined.

Definition seq__nseq {x y}:
  R#* x y ->
  {n & R#n x y}.
Proof using.
  intros * H.
  induction H.
  - eexists. constructor.
  - destruct exists IHseq n.
    exists (S n).
    econstructor; eassumption.
Defined.

Theorem in_nseq_at__in_nseq : forall x a b n m (r: R#n a b),
  in_nseq_at x m r ->
  in_nseq x r.
Proof using.
  intros * H.
  induction H; constructor.
  assumption.
Qed.

Theorem in_nseq__in_nseq_at : forall x a b n (r: R#n a b),
  in_nseq x r ->
  exists m, m <= n /\ in_nseq_at x m r.
Proof using.
  intros * H.
  induction H.
  - eexists.
    split; [|constructor].
    reflexivity.
  - eexists.
    split; [|constructor].
    lia.
  - destruct exists IHin_nseq m.
    exists m.
    destruct IHin_nseq.
    split.
    + lia.
    + constructor.
      assumption.
Qed. 

Definition nseq_singleton {x y} (r: R x y) : R#1 x y.
  tedious.
Defined.

Definition nseq_prepend (x y z: A) n:
  R x y ->
  R#n y z ->
  R#(S n) x z.
Proof using.
  intros ? Ryz.
  follows induction Ryz.
Defined.


(*
Theorem in_seq__in_nseq : forall x a b (r: R#* a b),
  in_seq x r ->
  in_nseq x (projT2 (seq__nseq r)).
Proof using.
  intros x a b r H.
  induction H.
  - constructor.
  - simpl. break_let. simpl.
    constructor.
  - simpl. break_let. simpl in *.
    constructor.
    assumption.
Qed.

Theorem in_nseq__in_seq : forall x n a b (r: R#n a b),
  in_nseq x r ->
  in_seq x (nseq__seq r).
Proof using.
  intros * H.
  induction H. 
  - constructor.
  - constructor.
  - simpl.
    constructor.
    assumption.
Qed.

Theorem in_nseq_at_first : forall n s s' (r: R# n s s'),
  in_nseq_at s 0 r.
Proof using.
  intros.
  induction r; constructor.
  assumption. 
Qed.

Theorem in_nseq_first : forall n s s' (r: R#n s s'),
  in_nseq s r.
Proof using.
  intros.
  induction r; constructor.
  assumption. 
Qed.

Theorem in_nseq_last : forall n s s' (r: R#n s s'),
  in_nseq s' r.
Proof using.
  intros.
  destruct r; constructor.
Qed.

Definition in_nseq_before {n s s'}
  x i (r: R#n s s') := 
  exists j, j < i /\ in_nseq_at x j r.

Inductive nseq_prefix {a}
  : forall {n m b c}, R#n a b -> R#m a c -> Prop :=
  | nseq_prefix_refl :
      forall n b (Rab: R#n a b),
        nseq_prefix Rab Rab
  | nseq_prefix_step :
      forall n b (Rab: R#n a b) m c (Rac: R#m a c) d (Rcd: R c d),
        nseq_prefix Rab Rac ->
        nseq_prefix Rab (nseq_step R m a c d Rcd Rac).

Theorem nseq_prefix_trans : forall {nx ny nz a x y z},
  forall (rx: R#nx a x) (ry: R#ny a y) (rz: R#nz a z),
    nseq_prefix rx ry ->
    nseq_prefix ry rz ->
    nseq_prefix rx rz.
Proof using. 
  intros * Hxy Hyz.
  revert nx x rx Hxy.
  induction Hyz; intros.
  - assumption.
  - constructor.
    apply IHHyz.
    assumption.
Qed.

Theorem in_nseq_at_prefix :
  forall a nb b (Rab: R#nb a b) nc c (Rac: R#nc a c) x i,
    nseq_prefix Rab Rac ->
    in_nseq_at x i Rab ->
    in_nseq_at x i Rac.
Proof using.
  intros * Hprefix Hin.
  induction Hprefix.
  - assumption.
  - constructor.
    applyc IHHprefix.
    assumption.
Qed.

Lemma nseq_prefix_before :
  forall a nb b (Rab: R#nb a b) nc c (Rac: R#nc a c) x,
    nseq_prefix Rab Rac ->
    in_nseq x Rab ->
    in_nseq_before x (S nb) Rac.
Proof using.
  intros * Hprefix Hin.
  apply in_nseq__in_nseq_at in Hin.
  destruct Hin as [m [Hlt Hin]].
  exists m.
  split.
  - lia. 
  - eapply in_nseq_at_prefix; eassumption.
Qed.

Theorem in_nseq_at__get_prefix:
  forall x i n a b (r: R#n a b),
    in_nseq_at x i r ->
    exists r': R#i a x, nseq_prefix r' r.
Proof using.
  intros.
  induction H.
  - repeat eexists. constructor.
  - repeat eexists. constructor.
  - destruct exists IHin_nseq_at r'.
    exists r'.
    constructor.
    assumption.
Qed.

Theorem in_nseq__get_prefix : 
  forall x n a b (r: R#n a b),
    in_nseq x r ->
    exists m (r': R#m a x), nseq_prefix r' r.
Proof using.
  intros.
  apply in_nseq__in_nseq_at in H as [i [_ H]].
  exists i.
  eapply in_nseq_at__get_prefix.
  eassumption.
Qed.

Theorem in_nseq__get_prefix' : 
  forall x y z n (Rxz: R#n x z),
    in_nseq y Rxz ~>
    R#* x y.
Proof using.
  intros * H.
  induct H.
  - construct. constructor. 
  - construct.
    econstructor.
    + eassumption.
    + eapply nseq__seq.
      eassumption.
  - assumption.
Qed.
*)

End BinaryRelationsProperties.


(* These must be declared outside the section to be visisble *)

Add Parametric Relation {A: Type} (R: relation A): A (star R)
  reflexivity  proved by (star_refl R)
  transitivity proved by (star_trans R)
  as star_rel.

Arguments ϕ_seq__seq_rev {A R x y}.