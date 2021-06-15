Require Import Ctl.Definition.
(* Require Import MyTactics. *)

(* TODO: if H is a biimpl, destruct into two impls, try both *)
(* or is this case already handled? *)
Ltac tapply H :=
  let H' := fresh in 
  pose proof @H as H';
  (* simpl should reduce implications (among other things) *)
  simpl in H';
  apply H';
  clear H'.

Ltac tconsume H := tapply H; clear H.

Ltac etapply H :=
  let H' := fresh in 
  pose proof @H as H';
  (* simpl should reduce implications (among other things) *)
  simpl in H';
  eapply H';
  clear H'.

Ltac tapply_in H H2 :=
  let H' := fresh in 
  pose proof @H as H';
  (* simpl should reduce implications (among other things) *)
  simpl in H';
  apply H' in H2;
  clear H'.

(* This conflict with the regular tapply definition *)
(* Tactic Notation "tapply" ident(H) "in" hyp(H2) := tapply_in H H2. *)

(* If simpl isn't called before specialize, and specializable binder isn't visible,
   then specialize will over-evaluate before specializing *)
Ltac tspecialize H a := simpl in H; specialize (H a).
Tactic Notation "tspecialize2" hyp(H) ident(a) ident(b) :=
    tspecialize H a;
    tspecialize H b.
Tactic Notation "tspecialize3" hyp(H) ident(a) ident(b) ident(c) :=
    tspecialize2 H a b;
    tspecialize H c.
Tactic Notation "tspecialize4" hyp(H) ident(a) ident(b) ident(c) ident(d) :=
    tspecialize3 H a b c;
    tspecialize H d.
