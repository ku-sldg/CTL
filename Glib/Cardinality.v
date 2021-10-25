Require Import Notation.
Require Import GeneralTactics.
Require Import Axioms.
Require Import Truncations.
Require Import Isomorphisms.

Require Import Coq.Logic.FinFun.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Lia.


(* Definition type_succ (A: Type) : Type := unit + A. *)
(* Definition fin_card (A: Type) (n: nat) := A ≃ {x | x < n}. *)

Definition countable (A: Type) := A ≃ nat. 

Theorem S_sig : forall n: nat,
  1 + {x | x < n} ≃ {x | x < S n}.
Proof using.
  intros *.
  apply ex_bijection_iso.
  define exists; [|split].
  - intros [_|[x xlt]].
    + exists n.
      constructor.
    + exists x.
      now apply PeanoNat.Nat.lt_lt_succ_r.
  - intros [|[x xlt]] [|[y ylt]].
    + intros _.
      now destruct n0, n1.
    + intros [= ->].
      lia.
    + intros [= ->].
      lia.
    + intros [= ->].
      f_equal.
      now apply exist_eq.
  - intros [x xlt].
    destruct (Compare_dec.lt_dec x n).
    + define exists.
      * right.
        now exists x.
      * simpl.
        now apply exist_eq.
    + define exists.
      * left. 
        constructor.
      * simpl.
        apply exist_eq.
        lia.
Qed.
      
Theorem nat_to_subset : forall n: nat,
  n ≃ {x | x < n}.
Proof using.
  intro n.
  induction n.
  - define exists by (intros []).
    define exists by (intros [? ?]; lia).
    split.
    + intros [x xlt].
      lia.
    + intros [].
  - rewrite S_type.
    transitivity ((1 + {x | x < n})%type).
    + now apply sum_iso_intro.
    + apply S_sig.
Qed.

Ltac iso_coerc_notation := 
  repeat match goal with 
  | ϕ: ?A ≃> ?B |- _ =>
      (progress change_no_check (let (x, _) := ϕ   in x) with (ϕ  : A -> B)) +
      (progress change_no_check (let (x, _) := ϕ⁻¹ in x) with (ϕ⁻¹: B -> A))
  end.


Ltac is_not_var x := assert_fails (is_var x).

Ltac is_proof_term p :=
  is_not_var p;
  match type of p with
  | ?P => match type of P with 
          | Prop => idtac
          end
  end.

(* This tactic is only able to hide closed proof terms. To build a more robust tactic 
   which abstracts open terms into closed/hideable predicates, one would likely need to 
   implement it in Ocaml
 *)
Ltac hide_proof_terms := 
  repeat match goal with 
  | |- context[?p] =>
      is_proof_term p;
      let ident := fresh "p" in
      set (ident := p);
      clearbody ident
  end.

Ltac hide_exist_proof_terms := 
  repeat match goal with 
  | |- context[exist _ _ ?p] =>
      is_not_var p;
      let ident := fresh "pexist" in 
      set (ident := p);
      clearbody ident
  end.

(* Theorem same_fin_card : forall A B n,
  fin_card A n ->
  fin_card B n ->
  A ≃ B.
Proof using.
  intros * ϕA ϕB.
  inhabit isomorphic__isomorphism in ϕA;
  inhabit isomorphic__isomorphism in ϕB.
  exists (ϕB⁻¹ ∘ ϕA) (ϕA⁻¹ ∘ ϕB).
  split; intros *; unfold "∘";
    apply eq_cancel_inv_left;
    now apply eq_cancel_left.
Qed.  *)

(* Theorem fin_succ_card : forall A n,
  fin_card A n ->
  fin_card (type_succ A) (S n).
Proof using.
  intros * ϕ.
  inhabit isomorphic__isomorphism in ϕ.
  define exists.
  { intros [tt|a].
    + exists 0.
      lia.
    + destruct (ϕ a) as [x xlt].
      exists (S x).
      lia.
  } 
  hide_exist_proof_terms.
  define exists.
  { intros [x xlt].
    destruct x.
    - now left.
    - right.
      apply ϕ⁻¹.
      exists x.
      lia.
  }
  split.
  - intros [x xlt].
    destruct x.
    + now apply exist_eq.
    + cbn.
      iso_coerc_notation.
      rewrite iso_cancel_inv.
      hide_proof_terms.
      now apply exist_eq.
  - intros [tt|a].
    + now destruct tt.
    + destruct (ϕ a) as [x xlt] eqn:case.
      hide_proof_terms.
      cbn.
      iso_coerc_notation.
      f_equal.
      apply eq_cancel_inv_left.
      rewrite case.
      now apply exist_eq.
Qed. *)

(* Theorem fin_sum_card : forall A B n m,
  fin_card A n ->
  fin_card B m ->
  fin_card (A + B) (n + m).
Proof using.
  intros * ϕA ϕB.
  inhabit isomorphic__isomorphism in ϕA;
  inhabit isomorphic__isomorphism in ϕB.
  define exists.
  { intros [a|b].
    - destruct (ϕA a) as [x xlt].
      exists x.
      lia.
    - destruct (ϕB b) as [x xlt].
      exists (n + x).
      lia.
  }
  define exists.
  { intros [x xlt].
    destruct (Compare_dec.lt_dec x n).
    - left.
      apply ϕA⁻¹.
      now exists x.
    - right.
      apply ϕB⁻¹.
      exists (x - n).
      lia.
  }
  split.
  - intros [x xlt].
    destruct (Compare_dec.lt_dec x n).
    + cbn.
      iso_coerc_notation.
      rewrite iso_cancel_inv.
      hide_proof_terms.
      now apply exist_eq.
    + cbn.
      iso_coerc_notation.
      rewrite iso_cancel_inv.
      hide_proof_terms.
      apply exist_eq.
      lia.
  - intros [a|b].
    + destruct (ϕA a) eqn:case.
      destruct (Compare_dec.lt_dec x n); [|contradiction].
      cbn.
      f_equal.
      iso_coerc_notation.
      apply eq_cancel_inv_left.
      rewrite case.
      now apply exist_eq.
    + destruct (ϕB b) eqn:case.
      destruct (Compare_dec.lt_dec (n + x) n); [lia|].
      cbn.
      hide_proof_terms.
      f_equal.
      iso_coerc_notation.
      apply eq_cancel_inv_left.
      rewrite case.
      apply exist_eq.
      lia.
Qed. *)

(* Theorem fin_prod_card : forall A B n m,
  fin_card A n ->
  fin_card B m ->
  fin_card (A * B) (n * m).
Proof using.
  intros * ϕA ϕB.
  inhabit isomorphic__isomorphism in ϕA;
  inhabit isomorphic__isomorphism in ϕB.
  define exists.
  { intros [a b].
    destruct (ϕA a) as [x xlt];
    destruct (ϕB b) as [y ylt].
    exists (x*m + y).
    clear - xlt ylt.
    nia.
  }
  define exists.
  { intros [x xlt].
    constructor.
    - apply ϕA⁻¹.
      exists (Nat.div x m).
      apply PeanoNat.Nat.div_lt_upper_bound; lia.
    - apply ϕB⁻¹.
      exists (Nat.modulo x m).
      apply PeanoNat.Nat.mod_upper_bound.
      lia.
  }
  split.
  - intros [x xlt].
    cbn.
    iso_coerc_notation.
    do 2 rewrite iso_cancel_inv.
    hide_proof_terms.
    apply exist_eq.
    clear - xlt.
    rewrite PeanoNat.Nat.mul_comm.
    symmetry.
    apply PeanoNat.Nat.div_mod.
    lia.
  - intros [a b].
    destruct (ϕA a) as [x xlt] eqn:case1;
    destruct (ϕB b) as [y ylt] eqn:case2.
    hide_proof_terms.
    cbn.
    iso_coerc_notation.
    f_equal.
    + apply eq_cancel_inv_left.
      rewrite case1.
      apply exist_eq.
      clear - ylt.
      rewrite PeanoNat.Nat.div_add_l.
      * rewrite (PeanoNat.Nat.div_small _ _ ylt).
        lia.
      * lia.
    + apply eq_cancel_inv_left.
      rewrite case2.
      apply exist_eq.
      clear - ylt.
      rewrite PeanoNat.Nat.add_comm.
      rewrite PeanoNat.Nat.mod_add.
      * now apply PeanoNat.Nat.mod_small.
      * lia.
Qed.  *)

Definition card_ord A B : Prop :=
  exists (P: B -> Prop), A ≃ {b | P b}.
Notation "A ⪯ B" := (card_ord A B) (at level 70, B at next level).

Definition card_ord_rev A B := B ⪯ A.
Notation "A ⪰ B" := (card_ord_rev A B) (at level 70, B at next level).

Definition card_strict_ord A B : Prop :=
  A ⪯ B /\ ~ A ≃ B.
Notation "A ≺ B" := (card_strict_ord A B) (at level 70, B at next level).

Definition card_strict_ord_rev A B : Prop := B ≺ A.
Notation "A ≻ B" := (card_strict_ord_rev A B) (at level 70, B at next level).

Theorem card_ord_injection : forall A B,
  A ⪯ B = ∃ f : A -> B, Injective f.
Proof using.
  intros *.
  extensionality; split.
  - intros [P ϕ].
    inhabit isomorphic__isomorphism in ϕ.
    exists (λ a, proj1_sig (ϕ a)).
    intros a a' H.
    cut (ϕ a = ϕ a').
    + apply iso_injective.
    + now apply exist_eq'.
  - intros [? ?].
    eexists.
    enow apply injection_image.
Qed.

Theorem card_ord_refl : reflexive Type card_ord.
Proof using.
  intros A.
  rewrite card_ord_injection.
  exists (λ x, x).
  now intros ? ? ->.
Qed.

Theorem card_ord_trans : transitive Type card_ord.
Proof using.
  intros A B C.
  repeat rewrite card_ord_injection.
  intros [f injf] [g injg].
  exists (g ∘ f).
  intros x y Heq.
  apply injf.
  now apply injg.
Qed.

Definition rel_ltotal {A B} (R: A -> B -> Prop) := 
  forall a, exists b, R a b.

Definition rel_rtotal {A B} (R: A -> B -> Prop) := 
  forall b, exists a, R a b.

Definition rel_total {A B} (R: A -> B -> Prop) := 
  rel_ltotal R /\ rel_rtotal R.

(* Lemma 
  ~‖P‖ = ‖P -> void‖. *)

Definition dec_injection_to_surjection : forall A B (f: A -> B),
  (* (forall b, {a | f a = b} + ({a | f a = b} -> void)) -> *)
  (forall b, {a | f a = b} + ({a | f a = b} -> 0)) ->
  Injective f ->
  A ->
  {g: B -> A | Surjective g}.
Proof using.
  intros * Hdec Hinj a0.
  define exists.
  - intro b.
    destruct (Hdec b) as [[a ?]|?].
    + exact a.
    + exact a0.
  - intros x.
    exists (f x).
    destruct (Hdec (f x)) as [case|case]; simpl.
    + destruct case.
      now apply Hinj.
    + forward case.
      * now exists x.
      * destruct case.
Defined.

Lemma injection_to_surjection : forall A B (f: A -> B),
  Injective f ->
  ‖A‖ ->
  (exists g: B -> A, Surjective g).
Proof using.
  intros * Hinj [a0].
  pose proof (dec_injection_to_surjection _ _ f) as g. 
  apply lift_trunc_arrow in g.
  - uninhabit g.
    specialize (g Hinj a0).
    destruct g as [g ?].
    now exists g.
  - apply choice.
    intro b.
    destruct classic (exists a, f a = b) as case.
    + destruct case as [a ?].
      inhabit.
      left.
      now exists a.
    + inhabit.
      right.
      intros [a ?].
      cut False.
      * contradiction.
      * apply case.
        now exists a.
Qed.

Lemma surjection_to_injection : forall A B (g: B -> A),
  Surjective g -> 
  exists f: A -> B, Injective f.
Proof using.
  intros * Hsur.
  unfold Surjective in Hsur.
  transform Hsur (Π y, ‖{x | g x = y}‖) by
    (intros; now rewrite trunc_sig_eq_exists).
  inhabit choice in Hsur.
  exists (λ a, proj1_sig (Hsur a)).
  intros x y H.
  destruct (Hsur x) as [x' ?], (Hsur y) as [y' ?].
  simpl in H.
  now subst.
Qed.

Inductive same_seq_aa {A B} (f: A -> B) (g: B -> A) : A -> A -> Prop := 
  | trivial_conn : forall a,
      same_seq_aa f g a a
  | seq_step_ba : forall a b a',
      g b = a' ->
      same_seq_ab f g a b ->
      same_seq_aa f g a a' 
with same_seq_ab {A B} (f: A -> B) (g: B -> A) : A -> B -> Prop := 
  | seq_step_ab : forall a a' b,
      f a' = b ->
      same_seq_aa f g a a' ->
      same_seq_ab f g a b.

Scheme same_seq_aa_mutual_ind := Induction for same_seq_aa Sort Prop 
  with same_seq_ab_mutual_ind := Induction for same_seq_ab Sort Prop.

Definition same_seq_bb {A B} (f: A -> B) (g: B -> A) b b' := 
  b = b' \/ exists a, g b = a /\ same_seq_ab f g a b'.

Theorem same_seq_aa_refl {A B} : forall (f: A -> B) (g: B -> A),
  reflexive A (same_seq_aa f g).
Proof using.
  intros * ?.
  constructor.
Qed.

Theorem same_seq_aa_sym {A B} : forall (f: A -> B) (g: B -> A),
  symmetric A (same_seq_aa f g).
Proof using.
  intros * x y H.
  pose proof (same_seq_aa_mutual_ind A B f g 
    (λ a a' p, forall b, f a' = b -> same_seq_aa f g a a' -> same_seq_ab f g a b)
    (λ a b q, forall a', g b = a' -> same_seq_aa f g a a')
    (* (λ a a' p, forall b, f a' = b -> same_seq_aa f g a' a -> same_seq_ab f g a b)
    (λ a b q, forall a', g b = a' -> same_seq_aa f g a' a) *)
  ) as Hind.
  max forward Hind; clear Hind.
  - intros * Heq H'.
    enow econstructor.
  - intros * Heq.
    intros.
    econstructor.
    + eassumption.
    + now apply H0.
  - intros * Heq.
    intros.
    econstructor.
    + eassumption.
    + now apply H0.
  - 
Admitted.

 
Theorem same_seq_aa_trans {A B} : forall (f: A -> B) (g: B -> A),
  transitive A (same_seq_aa f g).
Proof using.
  intros * x y z Hxy Hyz.
  (* Check (same_seq_aa_ind A B f g 
    (λ a a' p, forall b, same_seq_ab f g a' b -> same_seq_ab f g a b)
    (* (λ a b q, forall a', (exists x, g b = x -> same_seq_aa x a' -> same_seq_aa a a') *)
    (λ a b q, forall a', same_seq_ab f g a' b -> same_seq_aa f g a a')
  ). *)
  Check same_seq_aa_ind.
  induction Hyz.
Admitted.
 

(* Theorem same_seq_aa_ab_trans {A B} : forall (f: A -> B) (g: B -> A) a a' b,
  same_seq_aa f g a a' ->
  same_seq_ab f g a' b ->
  same_seq_ab f g a b.
Proof using.
  intros * H H'.
  induction H'.
  - apply
Admitted.  *)

(* Theorem same_seq_aa_trans {A B} : forall (f: A -> B) (g: B -> A),
  transitive A (same_seq_aa f g).
Proof using.
  intros * x y z Hxy Hyz.
  induction Hyz.
  - assumption.
  - econstructor.
    + eassumption.
    + enow eapply same_seq_aa_ab_trans.
Qed. *)

(* Anti-symmetry of the cardinal ordering *)
Theorem schroder_bernstein : forall A B,
  A ⪯ B ->
  B ⪯ A ->
  A ≃ B.
Proof using.
  intros *.

  (* intros * ϕ1 ϕ2.
  rewrite card_ord_injection in ϕ1, ϕ2.
  destruct ϕ1 as [ϕ1 Hinj1];
  destruct ϕ2 as [ϕ2 Hinj2].
  enough (Hsur: surjective ϕ1).
  - apply ex_bijection_iso.
    now exists ϕ1.
  - intros b. *)
  
(*
  intros * [PB ϕB] [PA ϕA].
  inhabit isomorphic__isomorphism in ϕB;
  inhabit isomorphic__isomorphism in ϕA.
  define exists.
  - intro a.
    destruct (ϕB a) as [b ?]. *)


Admitted.