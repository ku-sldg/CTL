Require Import Ctl.Definition.
(* Require Import MyTactics. *)

(* TODO: if H is a biimpl, destruct into two impls, try both *)
(* or is this case already handled? *)
Tactic Notation "tapply" constr(H) :=
  let H' := fresh in 
  pose proof @H as H';
  (* simpl should reduce implications (among other things) *)
  simpl in H';
  apply H';
  clear H'.

Tactic Notation "tapply" constr(H) "in" hyp(H2) :=
  let H' := fresh in 
  pose proof @H as H';
  (* simpl should reduce implications (among other things) *)
  simpl in H';
  apply H' in H2;
  clear H'.

Tactic Notation "tapplyc" constr(H) := tapply H; clear H.
Tactic Notation "tapplyc" constr(H) "in" hyp(H2) := tapply H in H2; clear H.

Tactic Notation "etapply" constr(H) :=
  let H' := fresh in 
  pose proof @H as H';
  (* simpl should reduce implications (among other things) *)
  simpl in H';
  eapply H';
  clear H'.

Tactic Notation "etapply" constr(H) "in" hyp(H2) :=
  let H' := fresh in 
  pose proof @H as H';
  (* simpl should reduce implications (among other things) *)
  simpl in H';
  eapply H' in H2;
  clear H'.

(* This conflict with the regular tapply definition *)
(* Tactic Notation "tapply" ident(H) "in" hyp(H2) := tapply_in H H2. *)

(* If simpl isn't called before specialize, and specializable binder isn't visible,
   then specialize will over-evaluate before specializing *)
Tactic Notation "tspecialize" hyp(H) constr(a) :=
  simpl in H; specialize (H a).
Tactic Notation "tspecialize" hyp(H) constr(a) constr(b) :=
  tspecialize H a;
  tspecialize H b.
Tactic Notation "tspecialize" hyp(H) constr(a) constr(b) constr(c) :=
  tspecialize H a b;
  tspecialize H c.
Tactic Notation "tspecialize" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
  tspecialize H a b c;
  tspecialize H d.
