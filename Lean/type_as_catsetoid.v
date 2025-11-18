From Hammer Require Import Hammer.

Class Category := cat_mk {
  uHom := Type : Type;
  Obj : Type;
  Hom : Obj -> Obj -> uHom;
  Id : forall x, Hom x x;
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);
  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;
  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;
  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
    EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f;
  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f;
  eq: forall {x y z} (f g: Hom y z) (h i : Hom x y), EqMor f g /\ EqMor h i ->
    EqMor (Compose f h) (Compose g i);
}.

Notation "f ≈ g" := (EqMor f g) (at level 70).
Notation "x → y" := (Hom x y) (at level 90, right associativity) : type_scope.
Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) : type_scope.


Instance Type_as_SetoidCat : Category.
Proof.
  apply cat_mk with
    (Obj := Type)
    (Hom := fun A B => A -> B)
    (Id := fun A => fun x => x)
    (Compose := fun _ _ _ f g => fun x => f (g x))
    (EqMor := fun A B (f g : A -> B) => forall x : A, f x = g x).
    all: hammer.
(*
    intros A B f.
    intros x. reflexivity.
  - intros A B f g h Hfg Hgh. 
    intros x.
    etransitivity. (* vagy apply eq_trans. *)
    + apply Hfg.
    + apply Hgh.
  - (* Eq_sim *)
    intros A B f g Hfg. (* Cél: forall x, g x = f x *)
    intros x.
    symmetry. apply Hfg.
  - (* assoc *)
    intros A B C D f g h. (* Cél: forall x, (f ∘ (g ∘ h)) x = ((f ∘ g) ∘ h) x *)
    intros x.
    reflexivity. (* Definíciósan egyenlőek a kifejezések *)
  - (* id_1 *)
    intros A B f. (* Cél: forall x, (f ∘ Id A) x = f x *)
    intros x.
    reflexivity.
  - (* id_2 *)
    intros A B f. (* Cél: forall x, (Id B ∘ f) x = f x *)
    intros x.
    reflexivity.
  - (* eq (congruence) *)
    intros A B C f g h i H.
    destruct H as [Hfg Hhi].
    intros x.
    simpl.
    rewrite Hhi.
    rewrite Hfg.
    reflexivity.*)
Defined.

Class CovariantFunctor_Setoid (C D : Category) := mk_CovariantFunctor_Setoid {
  Funr_Obj : @Obj C -> @Obj D;
  Funr_Hom : forall (x y : @Obj C), (x → y) -> (Funr_Obj x → Funr_Obj y);
  Funr_law : forall x y (f g : x → y),
    f ≈ g -> (Funr_Hom x y f) ≈ (Funr_Hom x y g); 
  Funr_id : forall (x : @Obj C), (Funr_Hom x x (Id x)) ≈ (Id (Funr_Obj x));
  Funr_comp : forall (x y z : @Obj C) (g : y → z) (f : x → y),
    (Funr_Hom x z (g ∘ f)) ≈ ((Funr_Hom y z g) ∘ (Funr_Hom x y f));
}.

Definition ProductF_Obj (A X : Type) : Type := A * X.

Definition ProductF_Map (A X Y : Type) (f : X -> Y)
  : (ProductF_Obj A X) -> (ProductF_Obj A Y) :=
  fun p => (fst p, f (snd p)).

Instance ProductFunctor (A : Type) : CovariantFunctor_Setoid Type_as_SetoidCat Type_as_SetoidCat.
Proof.
  apply mk_CovariantFunctor_Setoid with
    (Funr_Obj := ProductF_Obj A)
    (Funr_Hom := fun X Y => ProductF_Map A X Y).
  all: intros; simpl. 
  - unfold EqMor in H. simpl in H. intros. unfold ProductF_Map. hammer. (* rewrite H. reflexivity. *)
  - hammer.
  - hammer. (* intros; unfold ProductF_Map; unfold ProductF_Obj in x0; destruct x0; simpl; reflexivity. *)
Defined.

