Require Import Tactics.Tactics.


(* gen demo *)

Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Import ListNotations.

Goal forall A x (y z: list A),
  Permutation (x :: y) z ->
  Permutation (y ++ [x]) z.
intros * H.
gen refl xy := (x :: y) to (@Permutation _) in H.
intros perm_xy.
induct H.
Abort.


(* induct demo *)

Lemma not_perm_cons_nil {A}: forall (x: A) (y: list A),
  ~ Permutation (x :: y) [].
Proof using.
  intros * H.
  induct H.
  apply IHPermutation1.
  clear - H0.
  induct H0.
  - reflexivity.
  - etransitivity; eassumption.

(* We could use max induct, although in this case it is actually
   more work
 *)
Restart.
  intros * H.
  max induct H.
  eapply IHPermutation1. reflexivity.
  clear - H0.
  max induct H0.
  - reflexivity.
  - etransitivity; eassumption.
Qed.

Inductive loverlap {A}: list A -> list A -> Prop :=
  | loverlap_hd : forall a l1 l2,
      loverlap (a :: l1) (a :: l2)
  | loverlap_perm : forall l1 l1' l2 l2',
      Permutation l1 l1' ->
      Permutation l2 l2' ->
      loverlap l1 l2 ->
      loverlap l1' l2'.

Lemma not_loverlap_empty {A}: forall l: list A,
  ~ loverlap l [].
Proof using.
  intros l H.
  induct H.
  applyc IHloverlap.
  clear - H0.
  induct H0.
  - reflexivity.
  - transitivity l'; assumption.
Qed.

