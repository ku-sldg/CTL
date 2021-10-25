Notation "'∃' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity,
   format "'[' '∃'  x .. y , '/ '  p ']'")
  : type_scope.

Notation "'∃' ! x .. y , p" :=
  (ex (unique (fun x => .. (ex (unique (fun y => p))) ..)))
  (at level 200, x binder, right associativity,
   format "'[' '∃' !  x .. y , '/ ' p ']'")
  : type_scope.

Notation "{ ! x : A | P }" := (sig (unique (fun x : A => P)))
  (at level 0, x at level 99 as name,
   format "{  ! x  :  A  |  P }")
  : type_scope.

Notation "{ ! x | P }" := (sig (unique (fun x => P)))
  (at level 0, x at level 99 as name,
   format "{  ! x  |  P }")
  : type_scope.

Notation "'sigma' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity,
   only parsing)
  : type_scope.

Notation "'Σ' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity,
   format "'[' 'Σ'  x .. y , '/ '  p ']'")
  : type_scope.

Notation "'⟨' x , .. , y , z '⟩'" := (existT _ x (.. (existT _ y z) ..)) 
  (format "'⟨' x ,  .. ,  y ,  z '⟩'")
  : core_scope.


Notation "x × y" := (prod x y) (at level 40, left associativity): type_scope.


Notation "'Π' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   only parsing)
   (* format "'[' 'Π'  x .. y , '/ '  P ']'") *)
  : type_scope.

Notation "'∀' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   only parsing)
   (* format "'[' '∀'  x .. y , '/ '  P ']'") *)
  : type_scope.


Notation "'λ' x .. y , b" := (fun x => .. (fun y => b) ..)
  (at level 200, x binder, y binder, right associativity,
   format "'[' 'λ'  x .. y , '/ '  b ']'").


Definition is_true (b: bool) := b = true.
Coercion is_true : bool >-> Sortclass.

(* Notation "'𝔹'" := bool.
Notation "'ℕ'" := nat.
Notation "'ℙ'" := Prop. *)