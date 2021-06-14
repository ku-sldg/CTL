Require Import Coq.Init.Nat.
Require Import Coq.Arith.Compare_dec.
Require Import Psatz.

Ltac inv H := inversion H; subst.

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
  
Ltac auto_specialize := 
  repeat match goal with 
  | [H : ?x -> _ |- _] => 
      let H' := fresh in 
      assert (H' : x) by (easy + lia);
      specialize (H H');
      clear H'
  | [H : ?x <-> _ |- _] => 
      destruct H as [H _];
      let H' := fresh in 
      assert (H' : x) by (easy + lia);
      specialize (H H');
      clear H'
  | [H : _ <-> ?x |- _] => 
      destruct H as [_ H];
      let H' := fresh in 
      assert (H' : x) by (easy + lia);
      specialize (H H');
      clear H'
  end.

Ltac my_crush := repeat constructor + easy + lia + assumption. 

Ltac auto_ponens_with H tac := 
  match type of H with
  | ?x -> ?y => 
      let H' := fresh in 
      assert (H' : x) by tac;
      specialize (H H');
      clear H'
  end.
Ltac auto_ponens H := auto_ponens_with H my_crush.

Theorem modus_tollens : forall {a b: Prop}, (a -> b) -> not b -> not a.
Proof.
  unfold not.
  intros a b H H0 H1.
  apply H0.
  apply H.
  assumption.
Qed.

Ltac auto_tollens_with H tac :=
  match type of H with
  | ?x -> ?y => 
      let H' := fresh in 
      assert (H' : not y) by tac;
      let H'' := fresh in
      pose proof (modus_tollens H H') as H'';
      clear H; clear H';
      rename H'' into H
  end.
Ltac auto_tollens H := auto_tollens_with H my_crush.

Ltac simplify_implication_with H tac := auto_ponens_with H tac + auto_tollens_with H tac.
Ltac simplify_implication H := auto_ponens H + auto_tollens H.

Ltac is_prop x := 
  match type of x with
  | Prop => idtac
  | _ => fail
  end.

Ltac simplify_assumps_with tac :=
  repeat match goal with 
  | [H : ?x = ?x |- _] => clear H
  (* is_prop doesn't seem necessary? *)
  | [H : ?x, H' : ?x |- _] => is_prop x; clear H'
  | [H : _ /\ _ |- _] => destruct H
  | [H : _ -> _ |- _] => simplify_implication_with H tac
  | [H : _ <-> _ |- _] => 
      (destruct H as [H _]; simplify_implication_with H tac) +
      (destruct H as [_ H]; simplify_implication_with H tac)
  end.
Ltac simplify_assumps := simplify_assumps_with my_crush.

Ltac find_solve_inversion := 
  match goal with 
  | [H : _ |- _] => solve [inversion H; my_crush]
  end.

Ltac find_contradiction :=
  simplify_assumps; subst;
  solve [contradiction + discriminate + lia + find_solve_inversion].

Ltac expand x := unfold x; fold x.

Ltac expand_in x H := unfold x in H; fold x in H.

Ltac expand_all x := unfold x in *; fold x in *.

Lemma breakable_andb : forall x y, andb x y = true <-> x = true /\ y = true.
Proof.
  destruct x; destruct y; easy.
Qed.

Ltac break_andb := 
  repeat match goal with 
  | [H : andb _ _ = true |- _] => apply breakable_andb in H; destruct H
  | [_ : _ |- andb _ _ = true] => apply breakable_andb; split; try break_andb
  end.
