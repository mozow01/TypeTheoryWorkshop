Class Category := cat_mk {
  Obj : Type;
  uHom := Type : Type;
  Hom : Obj -> Obj -> uHom;
  Id : forall x, Hom x x;
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);

  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f ;
  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f ;
}.

Print unit.


Class Monoid : Type :=
  mk_Monoid {
    A : Type;
    e : A;
    op : A -> A -> A;
    assoc_m : forall x y z : A, op x (op y z) = op (op x y) z;
    left_id_ax : forall x : A, op e x = x;
    right_id_ax : forall x : A, op x e = x
  }.

Theorem Mono_is_a_Cat (M : Monoid) : Category.
Proof. 
apply cat_mk with 
(Obj:=unit) 
(Hom:=(fun (x : unit)(y : unit) => @A M )) 
(Id:=(fun (x : unit) => e)) 
(Compose:=(fun (x : unit) (y : unit) (z : unit) (f : @A M) (g : @A M) => (op f g))).
intros.
apply assoc_m.
intros.
apply right_id_ax.
intros.
apply left_id_ax.
Defined.

Axiom exten : forall (f g : nat -> nat), (fun n => f n) = (fun n => g n) -> f = g.  

Theorem Natfun_is_a_Cat : Category.
Proof. 
apply cat_mk with 
(Obj:=unit) 
(Hom:=(fun (x : unit)(y : unit) => (nat -> nat) )) 
(Id:=(fun (x : unit) => fun (x : nat) => x)) 
(Compose:=(fun (x : unit) (y : unit) (z : unit) (f : nat -> nat) (g : nat -> nat) => (fun n => f (g n)))).
intros.
apply exten.
reflexivity.
intros.
apply exten.
reflexivity.
intros.
apply exten.
reflexivity.
Defined.


Definition összeadás (n : nat) (m : nat) : nat := n + m.

Print list.

Check (fun (x : nat) => (összeadás x 3)).

Eval compute in (összeadás 2 3).

Print Nat.add.