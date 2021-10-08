Require Import Privilege.
Require Import Axioms.

Require Import Ctl.BinaryRelations.
Require Import Glib.Glib.

Open Scope string_scope.

(* Dynamic environments (partial maps from variables to arbitrary types) *)

(* TODO: abstract as a section variable? *)
Definition var  := string.
Definition comp := string.

Definition env := var -> option (access × Σ V, V).

Declare Scope env_scope.
(* Delimit Scope env_scope with env. *)
Bind Scope env_scope with env.
Open Scope env_scope.


Definition env_empty: env := λ _, None.
Notation "•" := env_empty : env_scope.

Definition env_singleton {V} var (acc: access) (v: V): env := λ lookup,
  if lookup =? var then Some (acc, existT _ V v) else None.
Notation "var ↦ v" := (env_singleton var allAcc v)
  (at level 55, right associativity) : env_scope.

Definition map_access (Γ: env) (acc: access): env := λ lookup, 
  match Γ lookup with 
  | Some (_, v) => Some (acc, v)
  | None => None
  end.
Notation "acc ? Γ" := (map_access Γ acc)
  (at level 60) : env_scope.
  (* (at level 60, format "acc ?  Γ") : env_scope. *)

(* First env shadows definitions in second *)
Definition env_concat (Γ1 Γ2: env) : env := λ lookup,
  match Γ1 lookup with 
  | Some v => Some v 
  | None => Γ2 lookup
  end.
Notation "Γ1 ;; Γ2" := (env_concat Γ1 Γ2)
  (at level 65, right associativity) : env_scope.

Definition read {V} (Γ: env) (c: comp) (name: var) (v: V) : Prop :=
  exists! acc: access, 
    Γ name = Some (acc, existT _ V v) /\
    acc c p_read.

Definition write {V} (Γ: env) (c: comp) (name: var) (v: V) (Γ': env) : Prop :=
  exists! (acc: access) curr,
    Γ name = Some (acc, curr) /\ 
    acc c p_write /\ 
    Γ' = acc ? name ↦ v ;; Γ.

Definition remove_var (Γ: env) var : env := λ lookup,
  if lookup =? var then None else Γ lookup.

Lemma map_acc_env_singleton : forall acc x V (v: V),
  (acc ? x ↦ v) = env_singleton x acc v.
Proof using.
  intros *.
  extensionality y.
  unfold env_singleton.
  replace (
    acc ? (λ lookup, 
      if lookup =? x
      then Some (allAcc, existT _ V v) 
      else None))
  with
    (λ lookup, 
      if lookup =? x
      then Some (acc, existT _ V v) 
      else None
  ).
  - reflexivity.
  - extensionality lookup.
    unfold map_access.
    now destruct (lookup =? x).
Qed.

Lemma refl_string_eq : forall x y,
  x =? y ->
  x = y.
Proof using.
  intros * ?.
  now destruct (eqb_spec x y).
Qed.

Theorem env_singleton_inv : forall acc x y V (v: V) v',
  (acc ? x ↦ v) y = Some v' ->
  x = y /\ v' = (acc, existT _ V v).
Proof using.
  intros * H.
  rewrite map_acc_env_singleton in H.
  unfold env_singleton in H.
  destruct (y =? x) eqn:case; [|discriminate].
  apply refl_string_eq in case as ->.
  now inv H.
Qed.

Theorem env_prepend_singleton_unchanged : forall (Γ: env) x y acc V (v: V),
  x <> y ->
  Γ y = (acc ? x ↦ v ;; Γ) y.
Proof using.
  intros * Hneq.
  unfold env_concat.
  destruct ((acc ? x ↦ v) y) eqn:case. 
  - apply env_singleton_inv in case as [-> _].
    contradiction.
  - reflexivity.
Qed.

Theorem write_unchanged : forall Γ Γ' x y c V (v: V),
  write Γ c x v Γ' ->
  x <> y ->
  Γ y = Γ' y.
Proof using.
  intros * Hwrite Hneq.
  destruct Hwrite as [acc [[curr [(Hwrite1 & Hwrite2 & ->) _]] _]].
  now apply env_prepend_singleton_unchanged.
Qed.

Theorem write_unchanged_read : forall Γ Γ' x y c c' V (v: V) V' (v': V'),
  write Γ c x v Γ' ->
  x <> y ->
  read Γ c' y v' ->
  read Γ' c' y v'.
Proof using. 
  intros * Hwrite Hneq Hread.
  unfold read in *.
  destruct Hread as (acc & (Hlookup & Hacc) & Hunique).
  exists acc.
  max split.
  - rewrite <- Hlookup.
    symmetry.
    enow eapply write_unchanged.
  - assumption.
  - intros * [H _].
    erewrite <- write_unchanged in H; [|eassumption|eassumption].
    rewrite Hlookup in H.
    now inv H.
Qed.

Theorem write_unchanged_read' : forall Γ Γ' x y c c' V (v: V) V' (v': V'),
  write Γ c x v Γ' ->
  x <> y ->
  read Γ' c' y v' ->
  read Γ c' y v'.
Proof using. 
  intros * Hwrite Hneq Hread.
  unfold read in *.
  destruct Hread as (acc & (Hlookup & Hacc) & Hunique).
  exists acc.
  max split.
  - rewrite <- Hlookup.
    enow eapply write_unchanged.
  - assumption.
  - intros * [H _].
    erewrite <- write_unchanged in Hlookup; [|eassumption|eassumption].
    rewrite Hlookup in H.
    now inv H.
Qed.

Theorem no_lookup_no_read : forall Γ c x V (v: V),
  Γ x = None -> ~ read Γ c x v.
Proof using.
  intros * Heq Hread.
  destruct Hread as (acc & (Heq' & _) & _).
  rewrite Heq in Heq'.
  discriminate Heq'.
Qed.

Close Scope env_scope.
Close Scope string_scope.
