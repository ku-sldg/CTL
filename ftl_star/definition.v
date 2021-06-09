Require Import Coq.Program.Basics.
Open Scope program_scope.

Require Import extra.
Require Import my_tactics.

Definition path (state: Set) := neList state.

Definition currentState {state} (p : path state) := neHd p.

Definition extendsPath {state} (p1 p2: path state) := extendsNe p1 p2.

(* Should the path prop be decidable? *)
(* Alternate spec: validPaths given by state-step relation `state -> state -> Prop` *)
Inductive model : Set -> Type :=
  | Model : forall state: Set, (path state -> Prop) -> model state.

Definition getStateType {state} (M: model state) := state.
Definition validPaths {state} (M: model state) :=
  match M with
  | Model _ paths => paths
  end.

Inductive TProp (state: Set) : Type :=
  | TNot   : TProp state -> TProp state
  | TConj  : TProp state -> TProp state -> TProp state
  | TDisj  : TProp state -> TProp state -> TProp state
  | TImpl  : TProp state -> TProp state -> TProp state
  (* State formulae *)
  | TTop   : TProp state
  | TBot   : TProp state
  | TLift  : (state -> Prop) -> TProp state
  | A      : TProp state -> TProp state
  | E      : TProp state -> TProp state
  (* Path formulae *)
  | X      : TProp state -> TProp state
  | F      : TProp state -> TProp state
  | G      : TProp state -> TProp state
  | TUntil : TProp state -> TProp state -> TProp state.

(* Make state argument implicit *)
Arguments TNot   {state}%type_scope.
Arguments TConj  {state}%type_scope.
Arguments TDisj  {state}%type_scope.
Arguments TImpl  {state}%type_scope.
Arguments TTop   {state}%type_scope.
Arguments TBot   {state}%type_scope.
Arguments TLift  {state}%type_scope.
Arguments A      {state}%type_scope.
Arguments E      {state}%type_scope.
Arguments X      {state}%type_scope.
Arguments F      {state}%type_scope.
Arguments G      {state}%type_scope.
Arguments TUntil {state}%type_scope.

Definition futurePath M p s := validPaths M p /\ extendsPath p (neSome s)

Reserved Notation "M ; s ⊨ₛ P" (at level 70).
Reserved Notation "M ; x ⊨ₚ P" (at level 70).
Reserved Notation "M ; a ⊨ P" (at level 70).
Fixpoint TEntails {state: Set} (M: model state) (a: state + path state) (tp: TProp state): Prop :=
  match a with 
  | inl s => 
      match tp with
      | TNot P => ~ M;s ⊨ₛ P
      | TConj P Q => M;s ⊨ₛ P /\ M;s ⊨ₛ Q
      | TDisj P Q => M;s ⊨ₛ P \/ M;s ⊨ₛ Q
      | TImpl P Q => M;s ⊨ₛ P -> M;s ⊨ₛ Q
      | TTop => True
      | TBot => False
      | TLift P => P s
      | A P => forall (x: path state), futurePath M x s -> M;x ⊨ₚ P
      | E P => exists (x: path state), futurePath M x s /\ M;x ⊨ₚ P
      | _ => False
      end
  | inr x => 
      match tp with
      | TNot P => ~ M;x ⊨ₚ P
      | TConj P Q => M;x ⊨ₚ P /\ M;x ⊨ₚ Q
      | TDisj P Q => M;x ⊨ₚ P \/ M;x ⊨ₚ Q
      | TImpl P Q => M;x ⊨ₚ P -> M;x ⊨ₚ Q

      | _ => M; currentState x ⊨ₛ tp
      end
  end
  where "M ; s ⊨ₛ P" := (TEntails M (inl s) P)
    and "M ; x ⊨ₚ P" := (TEntails M (inr x) P)
    and "M ; a ⊨ P" := (TEntails M a P).

  match c with
  | TNot P => ~ M;x ⊨ P
  | TConj P Q => M;x ⊨ P /\ M;x ⊨ Q
  | TDisj P Q => M;x ⊨ P \/ M;x ⊨ Q
  | TImpl P Q => M;x ⊨ P -> M;x ⊨ Q
  | TLift P => P (currentState x)
  | A P => forall (y: path state), validPaths M y -> extendsPath y x -> M;y ⊨ P
  | E P => exists (y: path state), validPaths M y /\ extendsPath y x /\ M;y ⊨ P
  (* | F A => exists s, now < t /\ M;s ⊨ A *)
  (* | G A => forall s, now < t -> t ⊨ A *)
  (* | Until A B => exists t1, t1 ⊨ A /\ forall t2, t2 < t1 -> t2 ⊨ B *)


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
  expand_in TEntails H';
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