Require Import Psatz.
Require Import Tactics.General.

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

(* Ltac n_times tac x n :=
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
*)

(* Ltac _intros_do_revert_aux tac n :=
  match goal with
  | |- forall _,_ =>
      intro;
      _intros_do_revert_aux tac (S n)
  | _ =>
    tac;
    revert_n n
  end. *)

(* Repeats some ltac, then calls the 
continutation with the number of invocations *)
Ltac repeat_count_then_aux tac cont n :=
  first [ tac; repeat_count_then_aux tac cont (S n)
        | cont n].

(* Ltac repeat_count_then tac cont :=  *)
Tactic Notation "repeat_count" tactic(tac) "then" tactic(cont) := 
  repeat_count_then_aux tac cont 0.

(* Definition taken from Chargueraud TLC library *)
Inductive Box : Type :=
  | box : forall {A: Type}, A -> Box.

Ltac _do_u n tac :=
  match n with 
  | box (S ?n') => tac; _do_u (box n') tac
  | _ => idtac 
  end.

(* This is precisely the do tactic, but it avoids typing the number *)
Tactic Notation "do_u" uconstr(n) tactic(tac) :=
  (* idtac "do_u"; *)
  _do_u (box n) tac.

(* Ltac intros_do_revert tac := *)
(* Tactic Notation "intros_do_revert" tactic(tac) :=
  repeat_count introv1 then (fun n =>
    tac; 
    do_u n (
      (* idtac;  *)
      match goal with 
      | H :_ |- _ => idtac "hi"; revert H
      end
    )
  ). *)

(* Somehow inserting an idtac/semicolon delays execution *)
Tactic Notation "just" tactic(tac) := idtac; tac.

Tactic Notation "intros_do_revert" tactic(tac) :=
  repeat_count introv1 then (fun n =>
    tac; 
    do_u n (just 
    (* do_u n ( *)
      match goal with 
      | H :_ |- _ => idtac "hi"; revert H
      end)
  ).

(* NOTE: this only brings the front-most binders into the context *)
Tactic Notation "deep" "rewrite" uconstr(c) := intros_do_revert (rewrite c).

(* Example *)
Goal (forall x, x + 0 = x) -> forall y z, (y + 0) + z = y + z.
  intro H.
  (* Fail (rewrite H). *)

  deep rewrite H.

  (* I realized setoid_rewrite can do this *)
  Restart.
  intro H.
  setoid_rewrite H.
Abort.


Goal (forall x, x + 0 = x) -> forall y z, (y + 0) + z = y + z.
  intro H.
  Fail (rewrite H).
  setoid_rewrite H.
  reflexivity.
Qed.
