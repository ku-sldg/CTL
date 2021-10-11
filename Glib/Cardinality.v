Require Import Notation.
Require Import GeneralTactics.
Require Import Axioms.
Require Import Truncations.
Require Import Isomorphisms.

Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Lia.


Definition type_succ (A: Type) : Type := unit + A.

Definition fin_card (A: Type) (n: nat) := A ≃ {x | x < n}.

Definition countable (A: Type) := A ≃ nat. 


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

Theorem same_fin_card : forall A B n,
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
Qed. 

Theorem fin_succ_card : forall A n,
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
Qed.

Theorem fin_sum_card : forall A B n m,
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
Qed.

Theorem fin_prod_card : forall A B n m,
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
Qed. 

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
  A ⪯ B = ∃ f : A -> B, injective f.
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


(* Definition same_sb_seq {A B} (f: A -> B) (g: B -> A) (a: A) (b: B) : Prop := *)

(* A × B / sb_seq

*)

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


