Polymorphic Class Category @{o h} := mk_cat {
  Obj : Type@{o};
  Hom : Obj -> Obj -> Type@{h};
  Id : forall x : Obj, Hom x x;
  Dom {x y} (f: Hom x y) := x;
  CoDom {x y} (f: Hom x y) := y;
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

Instance Type_as_a_Cat : Category.
Proof.
apply mk_cat with 
  (Obj := Type) 
  (Hom := fun (A B : Type) => A -> B)
  (Id := fun (A : Type) => (fun (x : A) => x))
  (Compose := fun (A B C : Type) (f : B -> C) (g : A -> B) => (fun x : A => f (g x))).
all: intros; simpl; reflexivity.
Defined.

(*Nem kell így, de lehet, viszont ha akarjuk a funktor kategóriát és a Coq natív =-t, akkor kell funex (Coq.Logic.FunctionalExtensionality) is. forall x, M = L -> (fun x => M) = (fun x => L), ahol M és L tartalmazhat x-et, ekkor extensionality x taktika hozza elő a forall feltételt. *)

Polymorphic Class ContravariantFunctor @{oc hc od hd} (C : Category@{oc hc}) (D : Category@{od hd}) := mk_ContraFunctor {
  CoF_Obj : @Obj C -> @Obj D;
  CoF_Hom : forall (x y : @Obj C), @Hom C x y -> @Hom D (CoF_Obj y) (CoF_Obj x);
  CoF_id : forall (x : @Obj C), (@CoF_Hom x x (@Id C x)) = (@Id D (@CoF_Obj x));
  CoF_comp : forall (x y z : @Obj C) (f : @Hom C y z) (g : @Hom C x y), (@CoF_Hom x z (@Compose C _ _ _ f g)) =
    (@Compose D _ _ _ (@CoF_Hom x y g) (@CoF_Hom y z f));
}.

Instance PredicateFunctor (R : Type) : ContravariantFunctor Type_as_a_Cat Type_as_a_Cat.
Proof.
apply mk_ContraFunctor with 
  (CoF_Obj := fun (A : Type) => A -> R) 
  (CoF_Hom := fun (A B : Type) (f : A -> B) => (fun (p : B -> R) => fun x => p (f x))).
all: intros; simpl; reflexivity.
Defined. 

Require Import Coq.Logic.FunctionalExtensionality. 

Instance HomFunctor (C : Category) (A : @Obj C) : ContravariantFunctor C Type_as_a_Cat.
Proof.
apply mk_ContraFunctor with 
  (CoF_Obj := fun (X : Obj) => Hom X A) 
  (CoF_Hom := fun (X Y : Obj) (f : Hom X Y) => ((fun (g : Hom Y A) => Compose g f ) : Hom Y A -> Hom X A)).
- intros.
  extensionality g.
  rewrite id_1.
  simpl. reflexivity.
- intros.
  simpl.
  extensionality g0.
  apply assoc.
Defined. 

(* Itt kapcsolhatjuk ki *)
Reset FunctionalExtensionality.

Definition Isomorphism {C : Category} {A B : Obj} (f : Hom A B) := (exists g : Hom B A, ((f ∘ g) = Id B ) /\ ((g ∘ f) = Id A )). 

Definition Isomorphical {C : Category} (A B : Obj) := (exists f : Hom A B, Isomorphism f). 

Infix "x ≅ y" := (Isomorphical x y) (at level 80, right associativity).

Polymorphic Class NaturalTransformation @{oc hc od hd} (C : Category@{oc hc}) (D : Category@{od hd}) (F G : ContravariantFunctor C D) := mk_NatTrans {
  trans_mor : forall (x : @Obj C), @Hom D ((@CoF_Obj C D F) x) ((@CoF_Obj C D G) x);
  naturality_square : forall (x y : @Obj C) (f : @Hom C x y),
    (@Compose D _ _ _ (trans_mor x) (@CoF_Hom C D F x y f)) =
    (@Compose D _ _ _ (@CoF_Hom C D G x y f) (trans_mor y))
}.

Require Import Coq.Logic.FunctionalExtensionality.

Definition IdNaturalTransformation (C D: Category) (F : ContravariantFunctor C D) : NaturalTransformation C D F F. 
Proof.
apply (mk_NatTrans C D F F) with 
      (trans_mor:=(fun (x : @Obj C) => @Id D (@CoF_Obj C D F x))).
      intros x y f.
      simpl.
      rewrite (@id_2 D _ _ (@CoF_Hom C D F x y f)).
      rewrite (@id_1 D _ _ (@CoF_Hom C D F x y f)).
      reflexivity.
Defined.

Definition ComposeNaturalTransformation (C D : Category)
           (F G H : ContravariantFunctor C D)
           (theta : NaturalTransformation C D G H)
           (eta : NaturalTransformation C D F G)
           : NaturalTransformation C D F H.
Proof.
  apply (mk_NatTrans C D F H) with
    (trans_mor := fun x => @Compose D _ _ _ (theta.(trans_mor) x) (eta.(trans_mor) x)).
  intros x y f.
  rewrite assoc.
  rewrite <- naturality_square.
  rewrite <- assoc.
  rewrite naturality_square.
  rewrite assoc.
  reflexivity.
Defined.

(*Újabb nem konstruktív axióma: Proof Irralevance. p : A : Prop és q : A : Prop, akkor p = q.*)
Require Import Coq.Logic.ProofIrrelevance.

Lemma NatTrans_extensionality {C D : Category} {F G : ContravariantFunctor C D}
  (n1 n2 : NaturalTransformation C D F G) :
  (forall x, (@trans_mor C D F G n1) x = (@trans_mor C D F G n2) x) -> n1 = n2.
Proof.
  intros H_mor_eq.
  destruct n1 as [mor1 proof1].
  destruct n2 as [mor2 proof2].
  simpl in *.
  assert (H_mor_eq_asserted : mor1 = mor2).
  extensionality x.
  exact (H_mor_eq x).
  subst mor2.
  f_equal.
  apply proof_irrelevance. (* Proof Irrelevance *)
Defined.

Instance ContraFunctorCat (C D : Category) : Category.
Proof. 
apply mk_cat with (Obj:=ContravariantFunctor C D) (Hom:=fun (F G : ContravariantFunctor C D) => NaturalTransformation C D F G) (Id:=(fun (F : ContravariantFunctor C D) => IdNaturalTransformation C D F)) (Compose:=(fun (F G H : ContravariantFunctor C D) (theta : NaturalTransformation C D G H)
           (eta : NaturalTransformation C D F G) => (ComposeNaturalTransformation C D F G H theta eta))).
- intros F G H K eta theta gamma.
  apply NatTrans_extensionality.
  intro x.
  simpl.
  apply assoc.
- intros F G eta.
  apply NatTrans_extensionality.
  intro x.
  simpl.
  apply id_1.
- intros F G eta.
  apply NatTrans_extensionality.
  intro x.
  simpl.
  apply id_2.
Defined.
 
Polymorphic Definition Phi_Yoneda @{oc hc} 
  {C : Category@{oc hc}}
  {F : ContravariantFunctor C Type_as_a_Cat} 
  {A : @Obj C}
  (eta : @Hom (ContraFunctorCat C Type_as_a_Cat) (HomFunctor C A) F)
  : (@CoF_Obj C Type_as_a_Cat F A).
Proof.
 (*Phi(eta) := eta_A id_A *)
 exact ((@trans_mor C Type_as_a_Cat (HomFunctor C A) F eta) A (@Id C A)).
Defined.

Polymorphic Definition Psi_Yoneda @{oc hc} {C : Category@{oc hc}}
  {F : ContravariantFunctor C Type_as_a_Cat} {A : @Obj C}
  (x : @CoF_Obj C Type_as_a_Cat F A)
  : (@Hom (ContraFunctorCat C Type_as_a_Cat) (HomFunctor C A) F).
Proof.
  change (NaturalTransformation C Type_as_a_Cat (HomFunctor C A) F).
  apply mk_NatTrans with
    (trans_mor := fun (X : @Obj C) (f : @Hom C X A) => (@CoF_Hom C Type_as_a_Cat F X A f) x).
  intros.
  simpl.
  extensionality x1. (* FunEx *)
  rewrite CoF_comp.
  simpl.
  reflexivity.
Defined.

Lemma Yoneda_left_inverse {C : Category}
  {F : ContravariantFunctor C Type_as_a_Cat} {A : @Obj C} :
  forall (x : @CoF_Obj C Type_as_a_Cat F A),
    Phi_Yoneda (Psi_Yoneda x) = x.
Proof.
  intro x.
  unfold Phi_Yoneda, Psi_Yoneda.
  simpl.
  rewrite (@CoF_id C Type_as_a_Cat F A). (* Id invariance -- könnyű *)
  reflexivity.
Defined.

Lemma eq_f_ext (A B : Type) (f g : A → B) :
  f = g → forall x, f x = g x.
Proof.
  intros H x.
  rewrite H.
  reflexivity. 
Defined.
 

Lemma Yoneda_right_inverse @{oc hc} {C : Category@{oc hc}}
  {F : ContravariantFunctor C Type_as_a_Cat} {A : @Obj C} :
  forall (eta : @Hom (ContraFunctorCat C Type_as_a_Cat) (HomFunctor C A) F),
    Psi_Yoneda (Phi_Yoneda eta) = eta.
Proof.
  intro eta.
  (* Két természetes transzformáció egyenlőségéhez a segédlemmánkat használjuk. *)
  apply (@NatTrans_extensionality C Type_as_a_Cat).
  intros X.
  simpl.
  unfold Phi_Yoneda. 
  extensionality f.
  pose (H_nat := (@naturality_square C Type_as_a_Cat (HomFunctor C A) F) eta). 
  specialize (H_nat X A f). 
  enough (H_fun: forall x : A → A, @trans_mor C Type_as_a_Cat (HomFunctor C A) F eta X (x ∘ f) =
        @CoF_Hom C Type_as_a_Cat F X A f (@trans_mor C Type_as_a_Cat (HomFunctor C A) F eta A x)).
  rewrite <- H_fun.
  rewrite id_2.
  reflexivity.
  simpl in H_nat.
  apply eq_f_ext.
  exact H_nat.
Defined.

Theorem Yoneda_lemma : forall (C : Category)
  (F : ContravariantFunctor C Type_as_a_Cat)
  (A : @Obj C),
    @Isomorphical Type_as_a_Cat
      (@Hom (ContraFunctorCat C Type_as_a_Cat) (HomFunctor C A) F)
      (@CoF_Obj C Type_as_a_Cat F A).
Proof.
  intros C F A.
  unfold Isomorphical.
  exists (@Phi_Yoneda C F A).
  unfold Isomorphism.
  exists (@Psi_Yoneda C F A).
  split.
  - extensionality x.
    apply (Yoneda_left_inverse x).
  - extensionality eta.
    apply (Yoneda_right_inverse eta).
Defined. 
