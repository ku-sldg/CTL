Require Import Setoid.
Require Import Tactics.General.

Definition stronger (a b: Type) := forall P: Prop, a -> (b -> P) -> P.
Notation "a ~> b" := (stronger a b) (at level 99, right associativity, b at level 200).

(* Tactic Notation "weaken" "with" uconstr(str) :=  *)
Tactic Notation "simple" "weaken" uconstr(str) := 
  simple eapply str; try (idtac; [|intro]).

(* Tactic Notation "weaken" hyp(H) "with" uconstr(str) :=  *)
Tactic Notation "simple" "weaken" uconstr(str) "in" hyp(H) := 
  simple eapply str;
    [ apply H
    | clear H; intro H
    ] +
  (* solve [weaken with str; apply H]. *)
  solve [simple eapply str; apply H].

Tactic Notation "simple" "cut_str" hyp(str) uconstr(c) := 
  simple eapply str;
    [ apply c
    | clear str; intro str
    ].

Tactic Notation "simple" "cut_strc" hyp(str) hyp(H) := 
  simple cut_str str H; clear H.

Theorem stronger_refl: reflexive _ stronger.
Proof.
  intro X.
  intros P x Himpl.
  applyc Himpl.
  assumption.
Qed.

Theorem stronger_trans : transitive _ stronger.
Proof.
  intros X Y Z Hxy Hyz.
  intros P x Himpl.
  simple cut_strc Hxy x.
  simple cut_strc Hyz Hxy.
  auto.
Qed.
 
Add Parametric Relation : Type stronger 
  reflexivity  proved by stronger_refl
  transitivity proved by stronger_trans
  as stronger_rel.

(* This definition somehow yields a universe inconsistency *)
(* Definition weak_eq (a b: Type) := a ~> b /\ b ~> a. *)

Reserved Notation "a <~> b" (at level 95, no associativity).
Inductive weak_eq (a b: Type) : Prop :=
  | weak_eq_intro : 
      (a ~> b) ->
      (b ~> a) ->
      a <~> b
  where "a <~> b" := (weak_eq a b).

Definition weak_forward {a b} (x: a <~> b): a ~> b :=
  match x with
  | weak_eq_intro _ _ ab _ => ab
  end.

Definition weak_backwards {a b} (x: a <~> b): b ~> a :=
  match x with
  | weak_eq_intro _ _ _ ba => ba
  end.

(* Note, this only works if weq has no assumptions *)
Tactic Notation "weaken" "->" uconstr(weq) := 
  simple weaken (weak_forward weq).

Tactic Notation "weaken" "<-" uconstr(weq) := 
  simple weaken (weak_backwards weq).

Tactic Notation "weaken" uconstr(str) := 
  simple weaken str +
  match type of str with 
  (* arbitrarily choose to apply in forward direction *)
  | _ <~> _ => weaken -> str
  end.

Tactic Notation "weaken" "->" uconstr(weq) "in" hyp(H) := 
  simple weaken (weak_forward weq) in H.

Tactic Notation "weaken" "<-" uconstr(weq) "in" hyp(H) := 
  simple weaken (weak_backwards weq) in H.

Tactic Notation "weaken" uconstr(str) "in" hyp(H) := 
  simple weaken str in H +
  match type of H with
  | ?a => match type of str with
      | context[a <~> _] => weaken -> str in H
      | context[_ <~> a] => weaken <- str in H
      end
  end.

Tactic Notation "cut_str" hyp(str) uconstr(c) := 
  simple cut_str str c +
  (destruct str as [str _]; simple cut_str str c) +
  (destruct str as [_ str]; simple cut_str str c).

Tactic Notation "cut_strc" hyp(str) hyp(H) := 
  cut_str str H; clear H.

Theorem weak_eq_refl: reflexive _ weak_eq.
Proof using.
  intro X.
  split; reflexivity.
Qed.

Theorem weak_eq_sym : symmetric _ weak_eq.
Proof using.
  intros X Y H.
  destruct H.
  split; assumption.
Qed. 

Theorem weak_eq_trans : transitive _ weak_eq.
Proof using.
  intros X Y Z Hxy Hyz.
  split.
  - intros P x Himpl.
    cut_strc Hxy x.
    cut_strc Hyz Hxy.
    auto.
  - intros P z Himpl.
    cut_strc Hyz z.
    cut_strc Hxy Hyz.
    auto.
Qed.
 
Add Parametric Relation : Type weak_eq 
  reflexivity  proved by weak_eq_refl
  symmetry     proved by weak_eq_sym
  transitivity proved by weak_eq_trans
  as weak_eq_rel.
