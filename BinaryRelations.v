Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Lists.List.

Require Import Setoid.
Require Import Lia.
(* Require Import Coq.Program.Equality. *)
Require Import Isomorphisms.
Require Import Tactics.Tactics.

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


Inductive in_seq {A} {R: relation A} {a}
  : forall {a'}, A -> R#* a a' -> Prop :=
  | in_seq_head_refl :
      in_seq a (seq_refl R a)
  | in_seq_head_step : forall x x' r p,
      in_seq x' (seq_step R a x x' r p)
  | in_seq_tail : forall x x' y r p,
      in_seq y p ->
      in_seq y (seq_step R a x x' r p).

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


(* star properties *)

Theorem star_refl : forall A (R: relation A),
  reflexive A R^*.
Proof using.
  constructor.
Qed.

Theorem star_trans : forall A (R: relation A),
  transitive A R^*.
Proof using.
  unfold transitive.
  intros * Hxy Hyz.
  induction Hyz.
  - assumption.
  - enow econstructor.
Qed.

Add Parametric Relation (A: Type) (R: relation A) : A (@star A R)
  reflexivity  proved by (star_refl A R)
  transitivity proved by (star_trans A R)
  as star_rel.

Theorem rt1n_star : forall A (R: relation A) x y,
  clos_refl_trans_1n A R x y -> star R x y.
Proof.
  intros * ?.
  apply clos_rt_rtn1.
  now apply clos_rt1n_rt.
Qed.

Theorem star_rt1n : forall A (R: relation A) x y,
  star R x y -> clos_refl_trans_1n A R x y.
Proof.
  intros * ?.
  apply clos_rt_rt1n.
  now apply clos_rtn1_rt.
Qed.

Theorem star_rt1n_trans : forall A (R: relation A) x y z,
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

Theorem seq__star {A}: forall (R: relation A) x y,
  R#* x y ->
  R^* x y.
Proof using.
  intros * H.
  induction H.
  - constructor.
  - enow econstructor.
Qed.

Theorem star__seq {A}: forall (R: relation A) x y,
  R^* x y ~>
  R#* x y.
Proof using.
  intros * H.
  induction H.
  - repeat constructor.
  - find uninhabit.
    constructor.
    enow econstructor.
Qed.

Definition seq_singleton {A} {R: relation A} {x y} (r: R x y)
  : R#* x y :=
  seq_step R x x y r (seq_refl R x).

(* Note equivalence to transitivity under Curry-Howard reflection to star *)
Definition seq_concat {A} {R: relation A} {x y z} (Rxy: R#* x y) (Ryz: R#* y z)
  : R#* x z.
Proof using.
  induction Ryz.
  - assumption.
  - econstructor.
    + eassumption.
    + find applyc.
      assumption.
Defined.

Theorem seq_concat_refl {A}: forall (R: relation A) x y (r: R#* x y),
  seq_concat (seq_refl R x) r = r.
Proof using.
  intros *.
  induction r.
  - reflexivity.
  - simpl.
    now find rewrite.
Qed.  

Theorem seq_concat_assoc {A}: forall (R: relation A) w x y z,
  forall (a: R#* w x) (b: R#* x y) (c: R#* y z),
    seq_concat (seq_concat a b) c =
    seq_concat a (seq_concat b c).
Proof using.
  intros *.
  revert w x a b; induct c.
  - reflexivity.
  - simpl.
    now find rewrite.
Qed.


(* Isomorphic to seq. Sometimes, this reversed structure is more convenient *)
Inductive seq_rev {A} (R: relation A) : A -> A -> Type :=
  | seq_rev_refl : forall x,
      seq_rev R x x
  | seq_rev_step : forall x y z,
      R x y ->
      seq_rev R y z ->
      seq_rev R x z.

Definition seq_rev_concat {A} {R: relation A} {x y z} (Rxy: seq_rev R x y) (Ryz: seq_rev R y z)
  : seq_rev R x z.
Proof using.
  induction Rxy.
  - assumption.
  - econstructor.
    + eassumption.
    + find applyc.
      assumption.
Defined.

Definition seq__seq_rev {A} {R: relation A} {x y} (seq: R#* x y): seq_rev R x y.
  induction seq.
  - constructor.
  - eapply seq_rev_concat; [eassumption|].
    econstructor.
    + eassumption.
    + constructor.
Defined.

Definition seq_rev__seq {A} {R: relation A} {x y} (seqr: seq_rev R x y): R#* x y.
  induction seqr.
  - constructor.
  - eapply seq_concat; [|eassumption].
    econstructor.
    + eassumption.
    + constructor.
Defined.

Theorem seq_rev_concat_refl {A}: forall (R: relation A) x y (r: seq_rev R x y),
  seq_rev_concat r (seq_rev_refl R y) = r.
Proof using.
  intros *.
  induction r.
  - reflexivity.
  - simpl.
    now find rewrite.
Qed.  

Theorem seq_rev_concat_assoc {A}: forall (R: relation A) w x y z,
  forall (a: seq_rev R w x) (b: seq_rev R x y) (c: seq_rev R y z),
    seq_rev_concat (seq_rev_concat a b) c =
    seq_rev_concat a (seq_rev_concat b c).
Proof using.
  intros *.
  revert y z b c; induct a.
  - reflexivity.
  - simpl.
    now find rewrite.
Qed.
  
Theorem seq__seq_rev__concat {A x y z}: forall (R: relation A) (a: R#* x y) (b: R#* y z),
  seq__seq_rev (seq_concat a b) = seq_rev_concat (seq__seq_rev a) (seq__seq_rev b).
Proof using.
  intros *.
  revert x a; induct b.
  - simpl.
    now rewrite seq_rev_concat_refl.
  - simpl seq_concat; simpl seq__seq_rev at 1.
    find rewrite ->.
    rewrite seq_rev_concat_assoc.
    reflexivity.
Qed.

Theorem seq_rev__seq__concat {A x y z}: forall (R: relation A) (a: seq_rev R x y) (b: seq_rev R y z),
  seq_rev__seq (seq_rev_concat a b) = seq_concat (seq_rev__seq a) (seq_rev__seq b).
Proof using.
  intros *.
  revert z b; induct a.
  - simpl.
    now rewrite seq_concat_refl.
  - simpl seq_rev_concat; simpl seq_rev__seq at 1.
    find rewrite ->.
    rewrite <- seq_concat_assoc.
    reflexivity.
Qed.

Definition seq_isoT_seq_rev {A}: forall (R: relation A) x y,
  isoT (R#* x y) (seq_rev R x y).
Proof using.
  intros *.
  exists (@seq__seq_rev A R x y) (@seq_rev__seq A R x y).
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

Theorem seq_iso_seq_rev {A}: forall (R: relation A) x y,
  R#* x y ≅ seq_rev R x y.
Proof using.
  intros.
  apply isoT__iso.
  apply seq_isoT_seq_rev.
Qed.


(* nseq properties *)

Definition nseq__seq {A n} {R: relation A} {x y}:
  R#n x y ->
  R#* x y.
Proof using.
  intros * H.
  induction H.
  - constructor.
  - econstructor; eassumption.
Defined.

Definition seq__nseq {A} {R: relation A} {x y}:
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

Theorem in_nseq_at__in_nseq {A}:
  forall (R: relation A) x a b n m (r: R#n a b),
    in_nseq_at x m r ->
    in_nseq x r.
Proof using.
  intros * H.
  induction H; constructor.
  assumption.
Qed.

Theorem in_nseq__in_nseq_at {A}:
  forall (R: relation A) x a b n (r: R#n a b),
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

Theorem in_seq__in_nseq {A}:
  forall (R: relation A) x a b (r: R#* a b),
    in_seq x r ->
    in_nseq x (projT2 (seq__nseq r)).
Proof using.
  intros R x a b r H.
  induction H.
  - simpl. constructor.
  - simpl. break_let. simpl.
    constructor.
  - simpl. break_let. simpl in *.
    constructor.
    assumption.
Qed.

Theorem in_nseq__in_seq {A}:
  forall (R: relation A) x n a b (r: R#n a b),
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

Theorem in_nseq_at_first {state}:
  forall (R: relation state) n s s' (r: R# n s s'),
    in_nseq_at s 0 r.
Proof using.
  intros.
  induction r; constructor.
  assumption. 
Qed.

Theorem in_nseq_first {state}:
  forall (R: relation state) n s s' (r: R#n s s'),
    in_nseq s r.
Proof using.
  intros.
  induction r; constructor.
  assumption. 
Qed.

Theorem in_nseq_last {state}:
  forall n (R: relation state) s s' (r: R#n s s'),
    in_nseq s' r.
Proof using.
  intros.
  destruct r; constructor.
Qed.

Definition in_nseq_before {state} {R: relation state} {n s s'}
  x i (r: R#n s s') := 
  exists j, j < i /\ in_nseq_at x j r.

Inductive nseq_prefix {A} {R: relation A} {a}
  : forall {n m b c}, R#n a b -> R#m a c -> Prop :=
  | nseq_prefix_refl :
      forall n b (Rab: R#n a b),
        nseq_prefix Rab Rab
  | nseq_prefix_step :
      forall n b (Rab: R#n a b) m c (Rac: R#m a c) d (Rcd: R c d),
        nseq_prefix Rab Rac ->
        nseq_prefix Rab (nseq_step R m a c d Rcd Rac).

Theorem nseq_prefix_trans {A}: forall {R: relation A} {nx ny nz a x y z},
  forall (rx: R#nx a x) (ry: R#ny a y) (rz: R#nz a z),
    nseq_prefix rx ry ->
    nseq_prefix ry rz ->
    nseq_prefix rx rz.
Proof using. 
  intros R nx nyz nz a x y z rx ry rz Hxy Hyz.
  revert nx x rx Hxy.
  induction Hyz; intros.
  - assumption.
  - constructor.
    apply IHHyz.
    assumption.
Qed.

Theorem in_nseq_at_prefix {A}:
  forall (R: relation A) a nb b (Rab: R#nb a b) nc c (Rac: R#nc a c) x i,
    nseq_prefix Rab Rac ->
    in_nseq_at x i Rab ->
    in_nseq_at x i Rac.
Proof using.
  intros R a nb b Rab nc c Rac x i Hprefix Hin.
  induction Hprefix.
  - assumption.
  - constructor.
    applyc IHHprefix.
    assumption.
Qed.

Lemma nseq_prefix_before {A}:
  forall (R: relation A) a nb b (Rab: R#nb a b) nc c (Rac: R#nc a c) x,
    nseq_prefix Rab Rac ->
    in_nseq x Rab ->
    in_nseq_before x (S nb) Rac.
Proof using.
  intros R a nb b Rab nc c Rac x Hprefix Hin.
  apply in_nseq__in_nseq_at in Hin.
  destruct Hin as [m [Hlt Hin]].
  exists m.
  split.
  - lia. 
  - eapply in_nseq_at_prefix; eassumption.
Qed.

Theorem in_nseq_at__get_prefix {A}:
  forall (R: relation A) x i n a b (r: R#n a b),
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

Theorem in_nseq__get_prefix {A}: 
  forall (R: relation A) x n a b (r: R#n a b),
    in_nseq x r ->
    exists m (r': R#m a x), nseq_prefix r' r.
Proof using.
  intros.
  apply in_nseq__in_nseq_at in H as [i [_ H]].
  exists i.
  eapply in_nseq_at__get_prefix.
  eassumption.
Qed.

Theorem in_nseq__get_prefix' {state}: 
  forall (R: relation state) x y z n (Rxz: R#n x z),
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
