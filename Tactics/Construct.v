Require Import Setoid.
Require Import Tactics.General.

(* Notation "~> b" := (inhabited b) (at level 50, format "~> b"). *)
Notation "~> b" := (inhabited b) (at level 50).

Definition constructs (a b: Type): Prop := a -> (~> b).
Notation "a ~> b" := (constructs a b) (at level 99, right associativity, b at level 200).

(* If `H: ~> a`, and the goal is a Prop, then `uninhabit H` transforms the
   hypothesis into `H: a` by inversion.
 *)
Ltac uninhabit H := 
  let i := fresh in
  inversion H as [i];
  clear H;
  rename i into H.

(* `construct`/`in` applies the inhabits-valued theorem in the hypothesis, and then 
   `uninhabits` the hypothesis.
 *)
Tactic Notation "construct" uconstr(c) "in" hyp(H) :=
  apply c in H;
  uninhabit H.

Tactic Notation "econstruct" uconstr(c) "in" hyp(H) :=
  eapply c in H;
  uninhabit H.

Tactic Notation "constructc" hyp(c) "in" hyp(H) :=
  construct c in H;
  clear c.

Tactic Notation "econstructc" hyp(c) "in" hyp(H) :=
  econstruct c in H;
  clear c.

Theorem lift_arrow: forall a b,
  (a -> b) ->
  (a ~> b).
Proof using.
  intros * H Ha.
  constructor.
  auto.
Qed. 

Theorem lift_constructs_l: forall a b,
  (a ~> b) ->
  (~> a) ~> b.
Proof using.
  intros a b H inhA.
  uninhabit inhA.
  auto.
Qed.

(* Transforms goal from `~> a` to `a` *)
Tactic Notation "construct" :=
  match goal with 
  | |- ~> _ => constructor
  end.

(* ` *)
Tactic Notation "construct" uconstr(c) :=
  solve [construct; apply c] + 
  match type of c with 
  | (~> _) ~> _ => apply c
  | _ ~> _ => apply (lift_constructs_l _ _ c)
  end +
  apply c.

Tactic Notation "econstruct" uconstr(c) :=
  solve [construct; eapply c] + 
  match type of c with 
  | (~> _) ~> _ => eapply c
  | _ ~> _ => eapply (lift_constructs_l _ _ c)
  end +
  eapply c.

Tactic Notation "constructc" hyp(c) :=
  construct c; clear c.

Tactic Notation "econstructc" hyp(c) :=
  econstruct c; clear c.

Theorem inhabited_idempotent: forall a,
  (~> a) <-> (~> ~> a).
Proof using.
  intro a.
  split; intro H.
  - construct H.
  - uninhabit H.
    assumption.
Qed.

Theorem constructs_refl : reflexive Type constructs.
Proof using.
  intros X x.
  construct x.
Qed.

Theorem constructs_trans : transitive Type constructs.
Proof using.
(* Backwards reasoning *)
  unfold transitive.
  intros X Y Z Hxy Hyz x.
  construct Hyz.
  construct Hxy.
  construct x.
 
(* Forward reasoning *)
Restart.
  unfold transitive.
  intros X Y Z Hxy Hyz x.
  constructc Hxy in x.
  auto.
Qed.

Add Parametric Relation : Type constructs 
  reflexivity  proved by constructs_refl
  transitivity proved by constructs_trans
  as constructs_rel.

Theorem construction_weaker: forall a b (P: Prop),
  (a ~> b) ->
  (b -> P) ->
  a -> P.
Proof using.
  intros A B P Hab HbP a.
  constructc Hab in a.
  auto.
Qed.