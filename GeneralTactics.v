Require Import Psatz.

Ltac inv H := inversion H; subst; try contradiction.

(* Overwrite exists tactic to support multiple instantiations 
   (up to four)
 *)
Tactic Notation "exists" uconstr(x1) :=
  exists x1.
Tactic Notation "exists" uconstr(x1) uconstr(x2) :=
  exists x1; exists x2.
Tactic Notation "exists" uconstr(x1) uconstr(x2) uconstr(x3) :=
  exists x1 x2; exists x3.
Tactic Notation "exists" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) :=
  exists x1 x2 x3; exists x4.


(* destruct variants *)

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

(* Clear variants. Tactics postfixed with "c" clear a hypothesis
   after using it.
 *)

Ltac invc H := inv H; clear H.
Tactic Notation "applyc" hyp(H) := apply H; clear H.
Tactic Notation "applyc" hyp(H) "in" hyp(H2) := apply H in H2; clear H.
Tactic Notation "eapplyc" hyp(H) := eapply H; clear H.
Tactic Notation "eapplyc" hyp(H) "in" hyp(H2) := eapply H in H2; clear H.

Ltac specializec H x := specialize (H x); clear x.


(* Unfold one layer *)
Tactic Notation "expand" constr(x) := unfold x; fold x.
Tactic Notation "expand" constr(x) "in" hyp(H) := unfold x in H; fold x in H.
Tactic Notation "expand" constr(x) "in" "*" := unfold x in *; fold x in *.


(* `pose new proof`, variant of `pose proof` that fails if such a hypothesis
   already exists in the context. Useful for automation which saturates the 
   context with generated facts
 *)

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


(* Generalizes the entire context *)
Ltac generalize_max := 
  repeat match goal with 
  | [H: _ |- _] => generalize dependent H
  end.

(* Attempts to maximally generalize before beginning induction *)
Ltac max_induction x :=
  move x at top;
  generalize_max;
  induction x.

(* Maximally recursive split *)
Ltac _max_split := try (split; _max_split).
Tactic Notation "max" "split" := _max_split.


(* When `unset x` is invoked with hypothesis `x := t` (commonly introduced by 
   tactic `set`), replaces all instances of `x` with `t`, and clears `x`.
 *)
Ltac unset x := unfold x in *; clear x.


(* `gen`/`to` tactics. Generalizes the term (: A) by a predicate (: A -> Prop)
   Useful when generalizing an inductive principle.
   For instance, `gen z := (x :: y) to (Permutation (x :: y)) in H by reflexivity`
   replaces instances of (x :: y) in H with `z`, and adds the hypothesis 
   `Hgen: Permutation (x :: y) z`.
 *)

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P):=
  let I' := fresh I in 
  set (I' := l);
  let Hgen := fresh "Hgen" in
  assert (Hgen: P I'); 
    [ unset I'
    | clearbody I'].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P)
  "in" hyp(H) :=
  let I' := fresh I in 
  set (I' := l) in H;
  let Hgen := fresh "Hgen" in
  assert (Hgen: P I'); 
    [ unset I'
    | clearbody I'].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P)
  "in" "*" :=
  let I' := fresh I in 
  set (I' := l) in *;
  let Hgen := fresh "Hgen" in
  assert (Hgen: P I'); 
    [ unset I'
    | clearbody I'].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P)
  "by" tactic(tac) :=
  gen I := l to P; [solve [tac]|].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P)
  "in" hyp(H) "by" tactic(tac) :=
  gen I := l to P in H; [solve [tac]|].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P)
  "in" "*" "by" tactic(tac) :=
  gen I := l to P in *; [solve [tac]|].


(* A sylistic alias for `admit`. Used to distinguish admitted goals
   which you know how to solve and that you plan come back to once the 
   difficult proof goals are solved.
 *)
Ltac todo := admit.


(* `cuth`. Stands for "cut hypothesis" (unfortunately, the standard library alread
   has a tactic called `cut`). Conduct forward reasoning by eliminating the assumption 
   in an implication. Optionally, you can supply a tactic with the `by` clause.
   E.g.:
   with hypothesis `H: x = x -> foo`, one can invoke `cuth H by reflexivity`. 
   The hypothesis is then replaced with `H: foo`.
 *)

Tactic Notation "cuth" hyp(H):=
  match type of H with
  | ?x -> _ =>
      let H' := fresh in 
      assert (H': x); 
        [| specialize (H H'); clear H']
  end.

Tactic Notation "cuth" hyp(H) "by" tactic(tac) :=
  cuth H; [solve [tac]|].


(* "max" variant of `cuth`. Invokes cuth on each assumption of a chained implication *)

Ltac _max_cuth H := try (cuth H; [|_max_cuth]).
Tactic Notation "max" "cuth" hyp(H) := _max_cuth.

Ltac _max_cuth_by H tac := try (cuth H; [tac|_max_cuth]).
Tactic Notation "max" "cuth" hyp(H) "by" tactic(tac) := _max_cuth_by H tac.


(* Automatic simplificiations on the context.
   These tend to be more heavy weight, since the do more searching.
 *)

Ltac my_crush := repeat constructor + easy + lia + assumption. 

Tactic Notation "find_cuth" "by" tactic(tac) := 
  repeat match goal with 
  | [H : ?x -> _ |- _] => cuth H by tac
  | [H : ?x <-> _ |- _] => 
      destruct H as [H _];
      cuth H by tac
  | [H : _ <-> ?x |- _] => 
      destruct H as [_ H];
      cuth H by tac
  end.
Tactic Notation "find_cuth" := find_cuth by my_crush.

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
  cuth H by tac + cut_modus_tollens H by tac.
Tactic Notation "simplify_implication" hyp(H) :=
  simplify_implication H by my_crush.

(* fails if `x` is not a `Prop` *)
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

Lemma breakable_andb : forall x y, andb x y = true <-> x = true /\ y = true.
Proof.
  destruct x; destruct y; easy.
Qed.

Ltac break_andb := 
  repeat match goal with 
  | [H : andb _ _ = true |- _] => apply breakable_andb in H; destruct H
  | [_ : _ |- andb _ _ = true] => apply breakable_andb; split; try break_andb
  end.

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