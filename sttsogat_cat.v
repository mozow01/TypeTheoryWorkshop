(*SOGAT monadic provability

SOGAT = second order generalized algebraic theory

second order = use of (one order) functions like (Pf A -> Pf B) 
generalized = use of more than one universe set (Typ : Type; Pf : Typ -> Type)
algebraic = universe + operators + equalities

*)

Class STTSOGAT := mk_STTSOGAT {
  (*sorts*)
  Typ : Type;
  Pf : Typ -> Type;
  
  (*operations -- type formers*)
  Tru : Typ;
  Imp : Typ -> Typ -> Typ;
  Cnj : Typ -> Typ -> Typ;

  (*more operations -- constructors*)
  tru : Pf Tru;
  lam : forall A B : Typ, (Pf A -> Pf B) -> Pf (Imp A B);
  app : forall A B : Typ, Pf (Imp A B) -> Pf A -> Pf B;
  pr1 : forall A B : Typ, Pf (Cnj A B) -> Pf A;
  pr2 : forall A B : Typ, Pf (Cnj A B) -> Pf B;
  cnj : forall A B : Typ, Pf A -> Pf B -> Pf (Cnj A B);
  
  (*equalities*)
  beta : forall A B F p, (app A B) (lam A B F) p = F p;
  eta : forall A B f, lam A B (app A B f) = f; 

  beta_cnj1 : forall A B p q, (pr1 A B) (cnj A B p q) = p;
  beta_cnj2 : forall A B p q, (pr2 A B) (cnj A B p q) = q;
  eta_cnj : forall A B c, cnj A B (pr1 A B c) (pr2 A B c) = c;
}.

Polymorphic Class Category @{o h} := mk_cat {
  Obj : Type@{o};
  Hom : Obj -> Obj -> Type@{h};
  Id : forall x : Obj, Hom x x;
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
      (Compose f (Compose g h) ) = (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f ;
  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f ;
}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

Require Import Coq.Logic.FunctionalExtensionality. 

Instance STTSOGAT_is_a_cat (S : STTSOGAT) : Category.
Proof.
apply mk_cat with 
  (Obj := Typ)
  (Hom := fun A B : Typ => Pf (Imp A B))
  (Id := fun A : Typ => lam A A (fun p : Pf A => p))
  (Compose := fun {x y z} (g : Pf (Imp y z)) (f : Pf (Imp x y)) =>
     lam x z (fun p : Pf x => app y z g (app x y f p))).
- intros x y z w g f h.
  unfold Compose.
  f_equal.
  extensionality p.
  rewrite beta.
  rewrite beta.
  reflexivity.
- intros x y f.
  unfold Compose, Id.
  rewrite <- eta.
  f_equal.
  extensionality p.
  rewrite beta.
  reflexivity.
- intros x y f.
  unfold Compose, Id.
  rewrite <- eta.
  f_equal.
  extensionality p.
  rewrite beta.
  reflexivity.
Defined.

Class CovariantFunctor (C : Category) (D : Category) := mk_Functor {
  Fnctr_Obj : @Obj C -> @Obj D;
  Fnctr_Hom : forall (x y : @Obj C), (x → y) -> (Fnctr_Obj x → Fnctr_Obj y);
  Fnctr_id : forall (x : @Obj C), Fnctr_Hom x x (Id x) = Id (Fnctr_Obj x);
  Fnctr_comp : forall (x y z : @Obj C) (g : y → z) (f : x → y),
    Fnctr_Hom x z (g ∘ f) = (Fnctr_Hom y z g) ∘ (Fnctr_Hom x y f);
}.

Instance Cnj_a_Functor (S : STTSOGAT) (a : Typ) :
  CovariantFunctor (STTSOGAT_is_a_cat S) (STTSOGAT_is_a_cat S).
Proof.
apply mk_Functor with
  (Fnctr_Obj := fun x => Cnj x a)
  (Fnctr_Hom := fun x y (f : Pf (Imp x y)) =>
    lam (Cnj x a) (Cnj y a)
      (fun p : Pf (Cnj x a) =>
        cnj y a (app x y f (pr1 x a p)) (pr2 x a p))).
- intros x.
  unfold Fnctr_Hom, Fnctr_Obj.
  unfold Id.
  simpl.
  rewrite <- eta.
  simpl.
  f_equal.
  extensionality p.
  rewrite beta.
  rewrite eta_cnj.
  rewrite beta.
  reflexivity.
- 
  intros x y z g f.
  unfold Fnctr_Hom, Fnctr_Obj, Compose.
  cbn.
  f_equal.
  extensionality p.
  rewrite beta.
  rewrite beta.
  rewrite beta.
  rewrite beta_cnj1.
  rewrite beta_cnj2.
  reflexivity.
Qed.



