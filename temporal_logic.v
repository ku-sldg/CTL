(* Require Import Psatz. *)
Require Import Coq.Program.Basics.
Open Scope program_scope.

Require Import my_tactics.

Notation time := nat (only parsing).
(* Definition present : time := 0. *)

(* Based on Prior's Tense Logic. *)
(* TODO: parameterize over time and present? *)
Inductive TProp : Type :=
  | TLift : (time -> Prop) -> TProp
  | TConj : TProp -> TProp -> TProp
  | TDisj : TProp -> TProp -> TProp
  | TNot  : TProp -> TProp
  | TImpl : TProp -> TProp -> TProp
  (* "It has at some time been the case that ..." *)
  | P : TProp -> TProp
  (* "It will at some time be the case that ..." *)
  | F : TProp -> TProp
  (* "It has always been the case that ..." *)
  | H : TProp -> TProp 
  (* "It will always be the case that ..." *)
  | G : TProp -> TProp
  | Until : TProp -> TProp -> TProp.

Reserved Notation "i ⊨ A" (at level 70).
(* TODO: remane TEntails *)
Fixpoint TDerives (now: time) (tp: TProp): Prop :=
  match tp with
  | TLift A => A now 
  | TConj A B => now ⊨ A /\ now ⊨ B
  | TDisj A B => now ⊨ A \/ now ⊨ B
  | TNot A => ~ now ⊨ A
  | TImpl A B => now ⊨ A -> now ⊨ B
  | P A => exists t, t < now /\ t ⊨ A
  | F A => exists t, now < t /\ t ⊨ A
  | H A => forall t, t < now -> t ⊨ A
  | G A => forall t, now < t -> t ⊨ A
  | Until A B => exists t1, t1 ⊨ A /\ forall t2, t2 < t1 -> t2 ⊨ B
  end
  where "i ⊨ A" := (TDerives i A).

Definition GP := G ∘ P.
Definition HF := H ∘ F.

Notation "^ A" := (TLift A) (at level 35).
Notation "A & B" := (TConj A B) (at level 45, right associativity).
Notation "A | B" := (TDisj A B) (at level 55, right associativity).
Notation "A --> B" := (TImpl A B) (at level 68,  right associativity).
Notation "A <--> B" := ((A --> B) & (B --> A)) (at level 65,  right associativity).
Notation "! A" := (TNot A) (at level 40).

Notation "⊨ A" := (forall t, t ⊨ A) (at level 69).

(* Todo: support tModus_ponens2 *)
Ltac tapply H :=
  let H' := fresh in
  pose proof H as H';
  (* TODO: limit expansion to TImpls *)
  expand_in TDerives H';
  apply H';
  clear H'.

Theorem tGeneralize: forall i A, ⊨ A -> i ⊨ A.
Proof.
  auto.
Qed.

Ltac tgeneralize := apply tGeneralize.

Theorem tModus_ponens: forall i A B, i⊨ A --> B -> i⊨ A -> i⊨ B.
Proof.
  auto.
Qed.

Theorem tModus_ponens_backwards: forall i A B, i⊨ A -> i⊨ A --> B -> i⊨ B.
Proof.
  auto.
Qed.

Theorem tModus_ponens2: forall A B, ⊨ A --> B -> ⊨ A -> ⊨ B.
Proof.
  intros A B Hab Ha.
  intro i.
  tapply Hab.
  tapply Ha.
Qed.

Theorem tModus_ponens2_backwards: forall A B, ⊨ A -> ⊨ A --> B -> ⊨ B.
Proof.
  intros.
  eapply tModus_ponens2; eauto.
Qed.

(* This tactic was leading to an error at Qed: "No such section variable or assumption" *)
(* Ltac overwrite H a := clear H; pose proof a as H. *)

(* Specialization cases: *)
(* 1. "⊨ A" with "i : time" to "i ⊨ A" (can be done with regular specialize) *)
(* 2. "i ⊨ A --> B" with "i ⊨ A" to "i ⊨ B" *)
(* 3. "⊨ A --> B" with "i ⊨ A" to "i ⊨ B" *)
(* 4. "⊨ A --> B" with "⊨ A" to "⊨ B" *)
Ltac tspecialize H a :=
  match type of a with
  | time =>
      match type of H with
      | ⊨ _ => specialize (H a)
      end
  | ?i ⊨ ?A =>
      match type of H with 
      | i ⊨ A --> _ => apply (tModus_ponens_backwards _ _ _ a) in H
      | ⊨ A --> _ => tspecialize H i; apply (tModus_ponens_backwards _ _ _ a) in H
      end
  | ⊨ ?A => 
      match type of H with 
      | ⊨ A --> _ => apply (tModus_ponens2_backwards _ _ a) in H
      end
  end.

Theorem TModus_tollens: forall (i: time) (A B: TProp),
  i⊨ A --> B -> i⊨ !B -> i⊨ !A.
Proof.
  simpl. auto.
Qed.

Theorem TImpl_trans: forall A B C, ⊨ (A --> B) --> (B --> C) --> A --> C.
Proof.
  intros A B C.
  intros i.
  intros Hab Hbc Ha.
  tapply Hbc.
  tapply Hab.
  assumption.
Qed.

Theorem G_distributes: forall A B, ⊨ G (A --> B) --> G A --> G B.
Proof.
  intros A B.
  simpl.
  intros i H1 H2 j HLt.
  apply H1.
  - assumption.
  - apply H2.
    assumption.
Qed.

Theorem H_distributes: forall A B, ⊨ H (A --> B) --> H A --> H B.
Proof.
  intros A B.
  simpl.
  intros i H1 H2 j HLt.
  apply H1.
  - assumption.
  - apply H2.
    assumption.
Qed.

Theorem GP_intro: forall A, ⊨ A --> GP A.
Proof.
  simpl.
  eauto.
Qed.

Theorem HF_intro: forall A, ⊨ A --> HF A.
Proof.
  simpl.
  eauto.
Qed.

Theorem alwaysH: forall A, ⊨ A -> ⊨ H A.
Proof.
  simpl.
  auto.
Qed.

Theorem alwaysG: forall A, ⊨ A -> ⊨ G A.
Proof.
  simpl.
  auto.
Qed.

Theorem always: forall A, ⊨ A -> ⊨ H A & A & G A.
Proof.
  simpl.
  auto.
Qed.

Theorem sometime: forall A, (exists i, i ⊨ A) -> ⊨ P A | A | F A.
Proof.
  intros A Hyp.
  destruct Hyp as [i Hyp].
  intro j.
  reflect_destruct_N_compare i j; simpl; eauto.
Qed.

Theorem P_origin: forall A, 0 ⊨ ! P A.
Proof.
  intro A.
  simpl.
  unfold not; intro H.
  destruct H as [t [H1 H2]].
  destruct t; inversion H1.
Qed.

Theorem H_origin: forall A, 0 ⊨ H A.
Proof.
  intro A.
  simpl.
  intros t H.
  destruct t; inversion H.
Qed.

Theorem BeckersP: forall A B, ⊨ A --> B -> ⊨ P A --> P B.
Proof.
  intros A B Hab.
  intros i [t [HLt Ha]].
  tspecialize Hab Ha.
  simpl; eauto.
Qed.

Theorem BeckersF: forall A B, ⊨ A --> B -> ⊨ F A --> F B.
Proof.
  intros A B Hab.
  intros i [t [HLt Ha]].
  tspecialize Hab Ha.
  simpl; eauto.
Qed.

Theorem BeckersH: forall A B, ⊨ A --> B -> ⊨ H A --> H B.
Proof.
  intros A B Hab.
  intros i Ha.
  intros t HLt.
  tapply Hab.
  apply Ha.
  assumption.
Qed.

Theorem BeckersG: forall A B, ⊨ A --> B -> ⊨ G A --> G B.
Proof.
  intros A B Hab.
  intros i Ha.
  intros t HLt.
  tapply Hab.
  apply Ha.
  assumption.
Qed.