Require Import Psatz.

Ltac inv H := inversion H; subst; try contradiction.
Ltac invc H := inversion H; clear H; subst; try contradiction.

Tactic Notation "exists" ident(x1) :=
  exists x1.
Tactic Notation "exists" ident(x1) ident(x2) :=
  exists x1; exists x2.
Tactic Notation "exists" ident(x1) ident(x2) ident(x3) :=
  exists x1 x2; exists x3.
Tactic Notation "exists" ident(x1) ident(x2) ident(x3) ident(x4) :=
  exists x1 x2 x3; exists x4.

Tactic Notation "destruct" "multi" hyp(h1) hyp(h2) :=
  destruct h1; destruct h2.
Tactic Notation "destruct" "multi" hyp(h1) hyp(h2) hyp(h3) :=
  destruct multi h1 h2; destruct h3.
Tactic Notation "destruct" "multi" hyp(h1) hyp(h2) hyp(h3) hyp(h4) :=
  destruct multi h1 h2 h3; destruct h4.

Tactic Notation "destruct" "exists" hyp(H) ident(id) :=
  destruct H as [id H].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) :=
  destruct H as [id1 [id2 H]].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) ident(id3) :=
  destruct H as [id1 [id2 [id3 H]]].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) ident(id3) ident (id4) :=
  destruct H as [id1 [id2 [id3 [id4 H]]]].

Tactic Notation "destruct" "or" hyp(H) := destruct H as [H|H].

Tactic Notation "applyc" hyp(H) := apply H; clear H.
Tactic Notation "applyc" hyp(H) "in" hyp(H2) := apply H in H2; clear H.
Tactic Notation "eapplyc" hyp(H) := eapply H; clear H.
Tactic Notation "eapplyc" hyp(H) "in" hyp(H2) := eapply H in H2; clear H.

Ltac specializec H x := specialize (H x); clear x.

Ltac generalize_max := 
  repeat match goal with 
  | [H: _ |- _] => generalize dependent H
  end.

Ltac max_induction x :=
  move x at top;
  generalize_max;
  induction x.

Ltac max_split := try (split; max_split).

(* Automatic simplificiations on the context *)

Ltac my_crush := repeat constructor + easy + lia + assumption. 

Tactic Notation "cut_hyp" hyp(H):=
  match type of H with
  | ?x -> _ =>
      let H' := fresh in 
      assert (H': x); 
        [ idtac
        | specialize (H H'); clear H'
        ]
  end.

Tactic Notation "cut_hyp" hyp(H) "by" tactic(tac) :=
  cut_hyp H; [solve [tac]|].

Ltac _max_cut_hyp H :=
  try (cut_hyp H; [|_max_cut_hyp]).
Tactic Notation "max_cut_hyp" hyp(H) :=
  _max_cut_hyp.

Ltac _max_cut_hyp_by H tac :=
  try (cut_hyp H; [tac|_max_cut_hyp]).
Tactic Notation "max_cut_hyp" hyp(H) "by" tactic(tac) :=
  _max_cut_hyp_by H tac.

Tactic Notation "find_cut_hyp" "by" tactic(tac) := 
  repeat match goal with 
  | [H : ?x -> _ |- _] => cut_hyp H by tac
  | [H : ?x <-> _ |- _] => 
      destruct H as [H _];
      cut_hyp H by tac
  | [H : _ <-> ?x |- _] => 
      destruct H as [_ H];
      cut_hyp H by tac
  end.
Tactic Notation "find_cut_hyp" := find_cut_hyp by my_crush.

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
  cut_hyp H by tac + cut_modus_tollens H by tac.
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

Ltac find_destruct_and :=
  match goal with 
  | [H : _ /\ _ |- _] => destruct H
  end.

Ltac find_destruct_or :=
  match goal with 
  | [H : _ \/ _ |- _] => destruct or H
  end.

Ltac find_destruct_exists :=
  match goal with
  | [H : ex _ |- _] => destruct H
  end.

Ltac break_context :=
  repeat (
    repeat (repeat find_destruct_exists; repeat find_destruct_and);
    repeat find_destruct_or
  ).

(* intros do revert *)

Ltac n_times tac x n :=
  match constr:(n) with
  | 0 => idtac
  | S ?n' => tac x; n_times tac x n'
  end.

Ltac revert_n n :=
  n_times ltac:(fun _ =>
    match goal with 
    | H :_ |- _ => revert H
    end
  ) tt n.

Ltac _intros_do_revert_aux tac n :=
  match goal with
  | |- forall _,_ =>
      intro;
      _intros_do_revert_aux tac (S n)
  | _ =>
    tac;
    revert_n n
  end.

Tactic Notation "intros_do_revert" tactic(tac) := _intros_do_revert_aux tac 0.

(* NOTE: this only brings the front-most binders into the context *)
Tactic Notation "deep" "rewrite" uconstr(c) := intros_do_revert (rewrite c).

(* 
Ltac clear_all :=
  repeat match goal with
  | H :_ |- _ => clear H
  end.

Tactic Notation "transform_hyp" hyp(H) := 
  let t := type of H in
  let H' := fresh in
  eassert (H': t -> _); [clear_all; intro H | apply H' in H; clear H'].

Tactic Notation "transform_hyp" hyp(H) "by" tactic(tac) := 
  let t := type of H in
  let H' := fresh in
  eassert (H': t -> _) by (clear_all; intro H; tac);
  apply H' in H;
  clear H'.

Goal (forall x, True -> x + 0 = x) -> False.
intro H.

eassert (H': (forall x: nat, True -> x + 0 = x) -> (forall x: nat, True -> _)).
{ clear_all.
  intro H.
  intro x; specialize (H x).
  intro T; specialize (H T).
  rewrite PeanoNat.Nat.add_0_r in H. exact H. }
specialize (H' H); clear H; rename H' into H.
Admitted.

Tactic Notation "deep" "rewrite" "in" hyp(H) "by" tactic(tac) :=
   *)