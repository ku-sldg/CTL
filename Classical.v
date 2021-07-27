Require Import Coq.Logic.Classical.

Require Export Coq.Logic.Classical.

Theorem destruct_impl : forall p q,
  ~p \/ p /\ q <-> (p -> q).
Proof using.
  intros p q.
  split; intro H.
  - destruct H.
    + intro Hp. contradiction.
    + intro H1. apply H.
  - destruct (classic p); auto.
Qed.

Tactic Notation "destruct" "classic" hyp(H) :=
  destruct (classic H).

Tactic Notation "destruct" "classic" ident(H) ":" uconstr(c) :=
  destruct (classic c) as [H|H].
