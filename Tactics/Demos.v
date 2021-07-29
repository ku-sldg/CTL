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


(* max induct demo *)

Goal forall A (x y z: list A), 
  x ++ y ++ z = (x ++ y) ++ z.
intros *.
induction y.
- admit.
- (* Note non-generalized IH *)
Restart.
intros *.
max induct y.
(* `max induction y` also works *)
- admit.
- (* This IH is generalized *)
Abort.