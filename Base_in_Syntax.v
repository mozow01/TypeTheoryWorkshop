Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Setoids.Setoid.

Class Category := cat_mk {
  Obj : Type;
  uHom := Type : Type;
  Hom : Obj -> Obj -> uHom;
  Id : forall x, Hom x x;
  Compose : forall {x y z}, (Hom y z) -> (Hom x y) -> (Hom x z);
  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;
  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;
  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f;
  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f;
  eq_cong: forall {x y z} (f g: Hom y z) (h i : Hom x y), 
        EqMor f g -> EqMor h i -> EqMor (Compose f h) (Compose g i);
}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) : type_scope.
Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) : type_scope.
Notation "f ≅ g" := (EqMor f g) (at level 40, no associativity) : type_scope.

Add Parametric Relation (C : Category) (x y : @Obj C) : (@Hom C x y) (@EqMor C x y)
  reflexivity proved by (@Eq_ref C x y)
  symmetry proved by (@Eq_sim C x y)
  transitivity proved by (@Eq_trans C x y)
  as eqmor_rel.

Instance compose_proper (C : Category) (x y z : @Obj C) : 
  Proper (@EqMor C y z ==> @EqMor C x y ==> @EqMor C x z) (@Compose C x y z).
Proof.
  repeat red. intros. apply eq_cong; assumption.
Defined.

Inductive BaseObj : Type := | One : BaseObj | S : BaseObj.

Inductive BaseTerm : BaseObj -> BaseObj -> Type :=
  | base_id {A} : BaseTerm A A
  | base_comp {A B C} : BaseTerm B C -> BaseTerm A B -> BaseTerm A C
  | base_bang {A} : BaseTerm A One
  | base_gen (n : nat) : BaseTerm One S. 

Inductive BaseTermEq : forall A B, BaseTerm A B -> BaseTerm A B -> Prop :=
  | basee_refl  {A B} (f : BaseTerm A B) : BaseTermEq A B f f
  | basee_sym   {A B} (f g : BaseTerm A B) : BaseTermEq A B f g -> BaseTermEq A B g f
  | basee_trans {A B} (f g h : BaseTerm A B) : BaseTermEq A B f g -> BaseTermEq A B g h -> BaseTermEq A B f h
  | basee_comp  {A B C} (f f' : BaseTerm B C) (g g' : BaseTerm A B) :
      BaseTermEq B C f f' -> BaseTermEq A B g g' -> BaseTermEq A C (base_comp f g) (base_comp f' g')
  | basee_id_l  {A B} (f : BaseTerm A B) : BaseTermEq A B (base_comp base_id f) f
  | basee_id_r  {A B} (f : BaseTerm A B) : BaseTermEq A B (base_comp f base_id) f
  | basee_assoc {A B C D} (f : BaseTerm C D) (g : BaseTerm B C) (h : BaseTerm A B) :
      BaseTermEq A D (base_comp (base_comp f g) h) (base_comp f (base_comp g h))
  | basee_term  {A} (f : BaseTerm A One) : BaseTermEq A One f base_bang.


Instance SyntacticCat : Category.
Proof.
  apply cat_mk with 
    (Obj := BaseObj) 
    (Hom := BaseTerm) 
    (Id := @base_id)       
    (Compose := @base_comp) 
    (EqMor := BaseTermEq). 
  - (* Eq_ref *)
    intros. apply basee_refl.
  - (* Eq_trans *)
    intros. eapply basee_trans; eassumption.
  - (* Eq_sim *)
    intros. apply basee_sym; assumption.
  - (* assoc *)
    intros. apply basee_sym. apply basee_assoc.
  - (* id_1 *)
    intros. apply basee_id_r.
  - (* id_2 *)
    intros. apply basee_id_l.
  - (* eq_cong *)
    intros. apply basee_comp; assumption.
Defined.

