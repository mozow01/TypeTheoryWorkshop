Require Import Coq.Init.Nat Peano Arith.

Class Semigroup : Type := mkSemigroup {
  carrier : Type;
  op : carrier -> carrier -> carrier;
  assSemi : forall x y z : carrier, op (op x y) z  = op x (op y z)
}.

Instance Function_composition_semigroup (A : Type) : Semigroup.
Proof.
apply mkSemigroup with (carrier := A -> A )(op := fun f g => fun x => f (g x)).
reflexivity.
Qed.

Class monoid (S : Semigroup) : Type := mkmonoid {
  un : @carrier S;
  unax1 : forall x : @carrier S, @op S x un  = @op S un x;
  unax2 : forall x : @carrier S, @op S un x = x
}.

Lemma unax3 : forall (S : Semigroup) (M : monoid S) (x : carrier), op x un = x.
Proof. 
intros.
rewrite unax1.
apply unax2.
Qed.

Class Category := cat_mk {
  uHom := Type : Type;
  Obj : Type;
  Hom : Obj -> Obj -> uHom; 
  Id : forall x, Hom x x; 
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z); 

  (* associativity, identity*)
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f;
  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f;
}.

Lemma monoidIsACat (S : Semigroup) (M : monoid S) : Category.
Proof.
apply cat_mk.

