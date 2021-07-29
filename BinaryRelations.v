Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Lists.List.

Require Import Setoid.
Require Import Psatz.
Require Import Coq.Program.Equality.
Require Import Tactics.General.
Require Import Tactics.Construct.

Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Relations.Relation_Operators.


(* Misc. definitions *)

Definition is_serial {A} (R: relation A) := forall a, exists b, R a b.
Definition serial A := {R: relation A | is_serial R}.

Definition serial_witness {A} (R: relation A) := forall a, {b | R a b}.
Definition serialT A := {R: relation A & serial_witness R}.

Definition rel_singleton {A} (x y : A): relation A :=
  fun x' y' => x' = x /\ y' = y -> True.

Definition relationT A := A -> A -> Type.


(* star definition *)
(* A reflexive transitive closure *)

Definition star {A} (R: relation A) : relation A := clos_refl_trans_n1 A R.
Notation "R ^*" := (star R) (at level 5, format "R ^*").

Definition is_serial_from {A} (R: relation A) a :=
  forall b,
    R^* a b ->
    exists c, R b c.

Definition serial_from_witness {A} (R: relation A) a :=
  forall b,
    R^* a b ->
    {c| R b c}.


(* seq definition *)
(* A transparent sequence of relation steps.
   It is in fact just a reflexive transitive closure, but as a Type instead of a Prop
 *)

Reserved Notation "R #*" (at level 5, format "R #*").
Inductive seq {A} (R: relation A) : relationT A :=
  | seq_refl : forall x,
      R#* x x
  | seq_step : forall x y z,
      R y z ->
      R#* x y ->
      R#* x z
  where "R #*" := (seq R).

Definition seq_singleton {A} {R: relation A} {x y} (r: R x y)
  : R#* x y :=
  seq_step R x x y r (seq_refl R x).

Definition reflexiveT {A} (R: relationT A) := forall x, R x x.

Definition symmetrycT {A} (R: relationT A) := forall x y,
  R x y ->
  R y x.

Definition transitiveT {A} (R: relationT A) := forall x y z,
  R x y ->
  R y z -> 
  R x z.

Lemma seq_trans {A}: forall R: relation A,
  transitiveT R#*.
Proof.
  intros R x y z Hxy Hyz.
  induction Hyz.
  - assumption.
  - econstructor.
    + eassumption.
    + applyc IHHyz.
      assumption.
Defined.

Lemma seq_step_rev {A}: forall (R: relation A) a b c,
  R a b ->
  R#* b c ->
  R#* a c.
Proof.
  intros R a b c Hab Hbc.
  eapply seq_trans; [|eassumption].
  econstructor.
  - eassumption.
  - constructor.
Defined.

Inductive in_seq {A} {R: relation A} {a}
  : forall {a'}, A -> R#* a a' -> Prop :=
  | in_seq_head_refl :
      in_seq a (seq_refl R a)
  | in_seq_head_step : forall x x' r p,
      in_seq x' (seq_step R a x x' r p)
  | in_seq_tail : forall x x' y r p,
      in_seq y p ->
      in_seq y (seq_step R a x x' r p).


(* nseq definition (indexed seq) *)

Reserved Notation "R #" (at level 5, format "R #").
Inductive nseq {A} (R: relation A) : nat -> relationT A :=
  | nseq_refl : forall x,
      R#0 x x
  | nseq_step : forall n x y z,
      R y z ->
      R#n x y ->
      R#(S n) x z
  where "R #" := (nseq R).
Notation "R # n" := (nseq R n) (at level 5, format "R # n").


Definition nseq_singleton {A} {R: relation A} {x y} (r: R x y)
  : R#1 x y :=
  nseq_step R 0 x x y r (nseq_refl R x).

Theorem nseq_step_rev {A}: forall (R: relation A) n s s' x,
  R s s' ->
  R#n s' x ->
  R#(S n) s x.
Proof using.
  intros R n s s' x Hstep Hpath.
  induction Hpath.
  - apply nseq_singleton.
    assumption.
  - econstructor.
    + eassumption.
    + applyc IHHpath.
      assumption.
Defined.

Lemma nseq_step__nseq_step_rev {X}:
  forall (R: relation X) s x x' n,
    R x x' ->
    R#n s x ->
    {s' &
      R s s' &
      R#n s' x'}.
Proof using.
  intros * Rxx' Rsx.
  revert x' Rxx'.
  induction Rsx; intros.
  - exists x'.
    + assumption. 
    + constructor.
  - applyc IHRsx in r.
    destruct exists r s'.
    exists s'.
    + assumption.
    + econstructor; eassumption.
Qed.

Theorem nseq_trans {A}: forall n m (R: relation A) x y z,
  R#n x y ->
  R#m y z ->
  R#(n+m) x z.
Proof using.
  intros n m R x y z Hxy Hyz; revert x Hxy.
  induction Hyz; intros.
  - rewrite PeanoNat.Nat.add_0_r.
    assumption.
  - rewrite PeanoNat.Nat.add_succ_r.
    econstructor.
    + eassumption.
    + applyc IHHyz.
      assumption.
Defined.

Theorem nseq_to_seq {A n} {R: relation A} {x y}:
  R#n x y ->
  R#* x y.
Proof using.
  intros * H.
  induction H.
  - constructor.
  - econstructor; eassumption.
Defined.

Theorem seq_to_nseq {A} {R: relation A} {x y}:
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

Inductive in_nseq_at {A} {R: relation A} {a}
  : forall {n a'}, A -> nat -> R#n a a' -> Prop :=
  | in_nseq_at_head_refl :
      in_nseq_at a 0 (nseq_refl R a)
  | in_nseq_at_head_step : forall n x x' r p,
      in_nseq_at x' (S n) (nseq_step R n a x x' r p)
  | in_nseq_at_tail : forall n m x x' y r p,
      in_nseq_at y m p ->
      in_nseq_at y m (nseq_step R n a x x' r p).

Inductive in_nseq {A} {R: relation A} {a}
  : forall {n a'}, A -> R#n a a' -> Prop :=
  | in_nseq_head_refl :
      in_nseq a (nseq_refl R a)
  | in_nseq_head_step : forall n x x' r p,
      in_nseq x' (nseq_step R n a x x' r p)
  | in_nseq_tail : forall n x x' y r p,
      in_nseq y p ->
      in_nseq y (nseq_step R n a x x' r p).

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
    in_nseq x (projT2 (seq_to_nseq r)).
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
    in_seq x (nseq_to_seq r).
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
  dependent induction H.
  - construct. constructor. 
  - construct.
    econstructor.
    + eassumption.
    + eapply nseq_to_seq.
      eassumption.
  - assumption.
Qed.