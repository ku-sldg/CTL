Require Import Coq.Logic.JMeq.


Notation "x ~= y" := (JMeq x y) (at level 70, no associativity).

Notation "'sigma' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Notation "'Σ' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Σ'  '/ ' x .. y , '/ ' p ']'")
  : type_scope.
