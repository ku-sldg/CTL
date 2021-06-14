(* Non-empty list *)
Inductive neList (A: Type) : Type :=
  | neSome : A -> neList A
  | neCons : A -> neList A -> neList A.
Arguments neSome {A}%type_scope.
Arguments neCons {A}%type_scope.

Definition neHd {A} (l: neList A) :=
  match l with 
  | neSome a   => a
  | neCons a _ => a
  end.

Fixpoint neAppend {A} (l1 l2: neList A) := 
  match l1 with 
  | neSome a => neCons a l2
  | neCons a l1' => neCons a (neAppend l1' l2)
  end.

Definition neSnoc {A} (l: neList A) (a: A) := neAppend l (neSome a).

Inductive inNe {A} : A -> neList A -> Prop := 
  | neInSome : forall a, inNe a (neSome a)
  | neInCons : forall a l, inNe a (neCons a l)
  | neInTail : forall a b t, inNe a t -> inNe a (neCons b t).

Inductive extendsNe {A} : neList A -> neList A -> Prop :=
  | ex_Eq   : forall x, extendsNe x x
  | ex_Grow : forall a x y, extendsNe x y -> extendsNe (neCons a x) y.

(* Fixpoint pathsEq {state: Set} (statesEq: state -> state -> bool) (x y: path state) :=
  match (x,y) with
  | (pState s1, pState s2) => statesEq s1 s2
  | (pPath s1 x', pPath s2 y') => andb (statesEq s1 s2) (pathsEq statesEq x' y')
  | _ => false
  end. *)
