Require Import Coq.Logic.JMeq.


Notation "x ~= y" := (JMeq x y) (at level 70, no associativity).


Notation "'sigma' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity,
   only parsing)
  : type_scope.
   (* format "'[' 'sigma' '/ ' x .. y , '/  ' p ']'") *)

Notation "'Σ' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity,
   format "'[' 'Σ'  '/ ' x .. y , '/ '  p ']'")
  : type_scope.


Notation "x × y" := (prod x y) (at level 40, left associativity): type_scope.


Notation "'Π'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   only parsing)
  : type_scope.
   (* format "'[' 'Π'  '/ ' x .. y , '/ '  P ']'") *)

Notation "'∀'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   format "'[' '∀'  '/ ' x .. y , '/ '  P ']'")
  : type_scope.


Notation "'λ' x .. y , b" := (fun x => .. (fun y => b) ..)
  (at level 200, x binder, y binder, right associativity,
   format "'[' 'λ' '/ ' x .. y , '/ '  b ']'").


Definition is_true (b: bool) := b = true.
Coercion is_true : bool >-> Sortclass.

(* Notation "'𝔹'" := bool.
Notation "'ℕ'" := nat.
Notation "'ℙ'" := Prop. *)