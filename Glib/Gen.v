Require Import GeneralTactics.

(* `gen`/`to` tactics. Generalizes the term (: A) by a predicate (: A -> Prop)
   Useful when generalizing an inductive principle.
   For instance, `gen z := (x :: y) to (Permutation (x :: y)) in H by reflexivity`
   replaces instances of (x :: y) in H with `z`, and adds the assumption
   `Permutation (x :: y) z` to the goal.
 *)

(* A version of cut where the assumption is the first subgoal *)
Ltac cut_flip p :=
  let H := fresh in
  assert (H: p); 
    [|revert H].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P):=
  set (I := l);
  cut_flip (P I);
    [ unfold I; clear I
    | clearbody I
    ].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P)
  "in" hyp(H) :=
  set (I := l) in H;
  cut_flip (P I); 
    [ unfold I in H |- *; clear I
    | clearbody I
    ].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P)
  "in" "*" :=
  set (I := l) in *;
  cut_flip (P I); 
    [ unfold I in *; clear I
    | clearbody I
    ].

Tactic Notation "gen" "?" ":=" constr(l) "to" uconstr(P):=
  let I := fresh "genv" in 
  gen I := l to P.

Tactic Notation "gen" "?" ":=" constr(l) "to" uconstr(P)
  "in" hyp(H) :=
  let I := fresh "genv" in 
  gen I := l to P in H.

Tactic Notation "gen" "?" ":=" constr(l) "to" uconstr(P)
  "in" "*" :=
  let I := fresh "genv" in 
  gen I := l to P in *.

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P)
  "by" tactic3(tac) :=
  gen I := l to P; [solve [tac]|].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P)
  "in" hyp(H) "by" tactic3(tac) :=
  gen I := l to P in H; [solve [tac]|].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P)
  "in" "*" "by" tactic3(tac) :=
  gen I := l to P in *; [solve [tac]|].

Tactic Notation "gen" "?" ":=" constr(l) "to" uconstr(P)
  "by" tactic3(tac) :=
  gen ? := l to P; [solve [tac]|].

Tactic Notation "gen" "?" ":=" constr(l) "to" uconstr(P)
  "in" hyp(H) "by" tactic3(tac) :=
  gen ? := l to P in H; [solve [tac]|].

Tactic Notation "gen" "?" ":=" constr(l) "to" uconstr(P)
  "in" "*" "by" tactic3(tac) :=
  gen ? := l to P in *; [solve [tac]|].


(* In the `refl` variant, the predicate is a reflexive relation (: A -> A -> Prop) *)
Tactic Notation "gen" "refl" ident(I) ":=" uconstr(u) "to" uconstr(P) :=
  gen I := u to (P u) by reflexivity.

Tactic Notation "gen" "refl" ident(I) ":=" uconstr(u) "to" uconstr(P)
  "in" hyp(H) :=
  gen I := u to (P u) in H by reflexivity.

Tactic Notation "gen" "refl" ident(I) ":=" uconstr(u) "to" uconstr(P)
  "in" "*" :=
  gen I := u to (P u) in * by reflexivity.

Tactic Notation "gen" "refl" "?" ":=" uconstr(u) "to" uconstr(P) :=
  gen ? := u to (P u) by reflexivity.

Tactic Notation "gen" "refl" "?" ":=" uconstr(u) "to" uconstr(P)
  "in" hyp(H) :=
  gen ? := u to (P u) in H by reflexivity.

Tactic Notation "gen" "refl" "?" ":=" uconstr(u) "to" uconstr(P)
  "in" "*" :=
  gen ? := u to (P u) in * by reflexivity.


(* `gen eq` variant is `gen refl` with P = eq *)
Tactic Notation "gen" "eq" ident(I) ":=" uconstr(u) :=
  gen refl I := u to eq.

Tactic Notation "gen" "eq" ident(I) ":=" uconstr(u)
  "in" hyp(H) :=
  gen refl I := u to eq in H.

Tactic Notation "gen" "eq" ident(I) ":=" uconstr(u) 
  "in" "*" :=
  gen refl I := u to eq in *.

Tactic Notation "gen" "eq" "?" ":=" uconstr(u) :=
  gen refl ? := u to eq.

Tactic Notation "gen" "eq" "?" ":=" uconstr(u)
  "in" hyp(H) :=
  gen refl ? := u to eq in H.

Tactic Notation "gen" "eq" "?" ":=" uconstr(u) 
  "in" "*" :=
  gen refl ? := u to eq in *.

(* TODO: gen heq *)