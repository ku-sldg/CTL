Require Import Coq.Init.Nat.
Require Import Coq.Arith.Compare_dec.
Require Import Psatz.

Ltac inv H := inversion H; subst; try contradiction.
Ltac invc H := inversion H; clear H; subst; try contradiction.

(* Ltac destructExists H id := destruct H as [id H]. *)
Tactic Notation "destruct" "exists" hyp(H) ident(id) :=
  destruct H as [id H].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) :=
  destruct H as [id1 [id2 H]].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) ident(id3) :=
  destruct H as [id1 [id2 [id3 H]]].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) ident(id3) ident (id4) :=
  destruct H as [id1 [id2 [id3 [id4 H]]]].

(* Todo: Support usecase `applyc (H a)`, by grabbing H from the head of arg *)
Ltac applyc H := apply H; clear H.
Ltac eapplyc H := eapply H; clear H.

Ltac specializec H x := specialize (H x); clear x.

Ltac generalize_max := 
  repeat match goal with 
  | [H: _ |- _] => generalize dependent H
  end.

Ltac max_induction x :=
  move x at top;
  generalize_max;
  induction x.

(* nat reflection *)

Lemma reflect_N_compare: forall n m,
  match n ?= m with
  | Eq => n = m
  | Lt => n < m
  | Gt => n > m
  end.
Proof.
  intros.
  destruct (n ?= m) eqn:case;
  [ apply nat_compare_eq
  | apply nat_compare_Lt_lt
  | apply nat_compare_Gt_gt];
  assumption.
Qed.

(* TODO: replace `subst` with something that just rewrites with new `x=y` hypothesis. *)
Ltac reflect_destruct_N_compare x y :=
  pose proof (reflect_N_compare x y); destruct (x ?= y) eqn:?; [subst | | ].

Ltac find_N_compare_destruct :=
  match goal with 
  | [_ : _ |- context [compare ?X ?Y]] => reflect_destruct_N_compare X Y
  | [_ : context [compare ?X ?Y] |- _] => reflect_destruct_N_compare X Y
  end.

(* Automatic simplificiations on the context *)

Ltac my_crush := repeat constructor + easy + lia + assumption. 

(* This cut has little to do with the cut tactic of the standard library *)
Tactic Notation "cut" hyp(H) "by" tactic(tac) :=
  match type of H with
  (* | forall (_: ?a), _ => *)
  | ?x -> _ =>
      let H' := fresh in 
      assert (H': x) by tac;
      specialize (H H');
      clear H'
  end.

Tactic Notation "auto_cut" "by" tactic(tac) := 
  repeat match goal with 
  | [H : ?x -> _ |- _] => cut H by tac
  | [H : ?x <-> _ |- _] => 
      destruct H as [H _];
      cut H by tac
  | [H : _ <-> ?x |- _] => 
      destruct H as [_ H];
      cut H by tac
  end.
Tactic Notation "auto_cut" := auto_cut by my_crush.

Theorem modus_tollens : forall {a b: Prop}, (a -> b) -> ~b -> ~a.
Proof. auto. Qed.

Tactic Notation "cut_modus_tollens" hyp(H) "by" tactic(tac) :=
  match type of H with
  | ?x -> ?y => 
      let H' := fresh in 
      assert (H' : not y) by tac;
      let H'' := fresh in
      pose proof (modus_tollens H H') as H'';
      clear H; clear H';
      rename H'' into H
  end.
Tactic Notation "cut_modus_tollens" hyp(H) := cut_modus_tollens H by my_crush.

Tactic Notation "simplify_implication" hyp(H) "by" tactic(tac) :=
  cut H by tac + cut_modus_tollens H by tac.
Tactic Notation "simplify_implication" hyp(H) :=
  simplify_implication H by my_crush.

Ltac is_prop x := 
  match type of x with
  | Prop => idtac
  | _ => fail
  end.

Tactic Notation "simplify_context" "by" tactic(tac) :=
  repeat match goal with 
  | [H : ?x = ?x |- _] => clear H
  | [H : ?x, H' : ?x |- _] => is_prop x; clear H'
  | [H : _ /\ _ |- _] => destruct H
  | [H : _ -> _ |- _] => simplify_implication H by tac
  | [H : _ <-> _ |- _] => simplify_implication H by tac
  end.
Tactic Notation "simplify_context" := simplify_context by my_crush.

(* Misc. *)

Ltac find_solve_inversion := 
  match goal with 
  | [H : _ |- _] => solve [inversion H; my_crush]
  end.

Ltac find_contradiction :=
  simplify_context; subst;
  solve [contradiction + discriminate + lia + find_solve_inversion].

(* Ltac expand x := unfold x; fold x. *)
Tactic Notation "expand" constr(x) := unfold x; fold x.

(* Ltac expand_in x H := unfold x in H; fold x in H. *)
Tactic Notation "expand" constr(x) "in" hyp(H) := unfold x in H; fold x in H.

(* Ltac expand_all x := unfold x in *; fold x in *. *)
Tactic Notation "expand" constr(x) "in" "*" := unfold x in *; fold x in *.

Lemma breakable_andb : forall x y, andb x y = true <-> x = true /\ y = true.
Proof.
  destruct x; destruct y; easy.
Qed.

Ltac break_andb := 
  repeat match goal with 
  | [H : andb _ _ = true |- _] => apply breakable_andb in H; destruct H
  | [_ : _ |- andb _ _ = true] => apply breakable_andb; split; try break_andb
  end.

Ltac fail_if_in_hyps H :=
  let t := type of H in
  lazymatch goal with 
  | [_: t |- _] => fail "This proposition is already assumed"
  | [_: _ |- _] => idtac
  end.

Tactic Notation "pose" "new" "proof" constr(H) :=
  fail_if_in_hyps H;
  pose proof H.

Tactic Notation "pose" "new" "proof" constr(H) "as" ident(H2) :=
  fail_if_in_hyps H;
  pose proof H as H2.
