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

Reserved Notation "⌊ A ⌋@ i" (at level 0).
Fixpoint TDesug (present: time) (tp: TProp): Prop :=
  match tp with
  | TLift p => p present 
  | TConj tp1 tp2 => ⌊tp1⌋@present /\ ⌊tp2⌋@present
  | TDisj tp1 tp2 => ⌊tp1⌋@present \/ ⌊tp2⌋@present
  | TNot tp => ~ ⌊tp⌋@present
  | TImpl tp1 tp2 => ⌊tp1⌋@present -> ⌊tp2⌋@present
  | P tp => exists t, t < present /\ ⌊tp⌋@t
  | F tp => exists t, present < t /\ ⌊tp⌋@t
  | H tp => forall t, t < present -> ⌊tp⌋@t
  | G tp => forall t, present < t -> ⌊tp⌋@t
  | Until tp1 tp2 => exists t1, ⌊tp1⌋@t1 /\ forall t2, t2 < t1 -> ⌊tp2⌋@t2
  end
  where "⌊ A ⌋@ i" := (TDesug i A).

Definition GP := G ∘ P.
Definition HF := H ∘ F.

Notation "^ A" := (TLift A) (at level 50).
Notation "A & B" := (TConj A B) (at level 80, right associativity).
Notation "A | B" := (TDisj A B) (at level 85, right associativity).
Notation "A --> B" := (TImpl A B) (at level 99,  right associativity).
Notation "A <--> B" := ((A --> B) & (B --> A)) (at level 95,  right associativity).
Notation "! A" := (TNot A) (at level 75).

Notation "⌊ A ⌋" := (forall t, ⌊A⌋@t) (at level 0).

(* TE_not has negative occurence *)
(* Inductive TEval (present: time): TProp -> Prop :=
  | TE_lift : forall (p: time -> Prop),
      p present ->
      TEval present (TLift p)
  | TE_conj : forall tp1 tp2: TProp,
       TEval present tp1 /\ TEval present tp2 ->
       TEval present (TConj tp1 tp2)
  | TE_disj : forall tp1 tp2: TProp,
       TEval present tp1 \/ TEval present tp2 ->
       TEval present (TDisj tp1 tp2)
  | TE_not : forall tp: TProp,
       (* not (TEval present tp) -> *)
       (TEval present tp -> False) ->
       TEval present (TNot tp)
  | TE_H : forall tp: TProp,
       (forall t: time, t < present -> TEval t tp) ->
       TEval present (H tp)
  | TE_G : forall tp: TProp,
       (forall t: time, present < t -> TEval t tp) ->
       TEval present (H tp). *)

Ltac tapply H :=
  let H' := fresh in
  pose proof H as H';
  (* TODO: limit expansion to TImpls *)
  expand_in TDesug H';
  apply H';
  clear H'.

Theorem TModus_ponens: forall i A B, 
  ⌊A --> B⌋@i -> ⌊A⌋@i -> ⌊B⌋@i.
Proof.
  (* intros i A B Hab Ha.
  tapply Hab.
  assumption. *)
  auto.
Qed.

Theorem TModus_tollens: forall (i: time) (A B: TProp),
  ⌊A --> B⌋@i -> ⌊!B⌋@i -> ⌊!A⌋@i.
Proof.
  simpl. auto.
Qed.

Theorem TImpl_trans: forall A B C, ⌊(A --> B) --> (B --> C) --> A --> C⌋.
Proof.
  intros A B C.
  intros i.
  intros Hab Hbc Ha.
  tapply Hbc.
  tapply Hab.
  assumption.
Qed.

Theorem G_distributes: forall A B, ⌊G (A --> B) --> G A --> G B⌋.
Proof.
  intros A B.
  simpl.
  intros i H1 H2 j HLt.
  apply H1.
  - assumption.
  - apply H2.
    assumption.
Qed.

(* Theorem G_distributes: forall i A B, ⌊G (A --> B)⌋@i -> ⌊G A --> G B⌋@i.
Proof.
  intros i A B.
  simpl.
  apply G_distributesT.
Qed. *)

Theorem H_distributes: forall A B, ⌊H (A --> B) --> H A --> H B⌋.
Proof.
  intros A B.
  simpl.
  intros i H1 H2 j HLt.
  apply H1.
  - assumption.
  - apply H2.
    assumption.
Qed.

(* Theorem H_distributes: forall i A B, ⌊H (A --> B)⌋@i -> ⌊H A --> H B⌋@i.
Proof.
  intros i A B.
  simpl.
  apply H_distributesT.
Qed. *)

Theorem GP_intro: forall A, ⌊A --> GP A⌋.
Proof.
  simpl.
  eauto.
Qed.

Theorem HF_intro: forall A, ⌊A --> HF A⌋.
Proof.
  simpl.
  eauto.
Qed.

Theorem alwaysH: forall A, ⌊A⌋ -> ⌊H A⌋.
Proof.
  simpl.
  auto.
Qed.

Theorem alwaysG: forall A, ⌊A⌋ -> ⌊G A⌋.
Proof.
  simpl.
  auto.
Qed.

Theorem always: forall A, ⌊A⌋ -> ⌊H A & A & G A⌋.
Proof.
  simpl.
  auto.
Qed.

Theorem sometime: forall A, (exists i, ⌊A⌋@i) -> ⌊P A | A | F A⌋.
Proof.
  intros A Hyp.
  destruct Hyp as [i Hyp].
  intro j.
  reflect_destruct_N_compare i j; simpl; eauto.
Qed.

Theorem P_origin: forall A, ⌊! P A⌋@0.
Proof.
  intro A.
  simpl.
  unfold not; intro H.
  destruct H as [t [H1 H2]].
  destruct t; inversion H1.
Qed.

Theorem H_origin: forall A, ⌊H A⌋@0.
Proof.
  intro A.
  simpl.
  intros t H.
  destruct t; inversion H.
Qed.

Theorem BeckersP: forall A B, ⌊A --> B⌋ -> ⌊P A --> P B⌋.
Proof.
  intros A B HImpl.
  intro i.
  simpl.
  intros [t [HLt HA]].
  specialize (HImpl t).
  eauto.
Qed.

Theorem BeckersH: forall A B, ⌊A --> B⌋ -> ⌊H A --> H B⌋.
Proof.
  intros A B HImpl.
  intro i.
  simpl.
  intros Hyp.
  intros t HLt.
  specialize (HImpl t).
  eapply TModus_ponens; eauto.
Qed.

