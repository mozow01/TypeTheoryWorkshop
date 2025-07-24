
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

Class CartClosed {C : Category} := {

(* terminal *)

  Terminal_obj : Obj;

  Terminal_mor : forall {x}, x → Terminal_obj;
 
  unique_terminal : forall {x} (f : x → Terminal_obj), f = Terminal_mor;

(* initial *)

  Initial_obj : Obj;

  Initial_mor : forall {x}, Initial_obj → x;

  unique_initial : forall {x} (f : Initial_obj → x), f = Initial_mor;

(* product *)
 (*           pr_1                 pr_2
     A_1 <----------- A_1 x A_2 -------------> A_2
          \              /|\              /
         f_1  \  f_1 x f_2|           /   f_2
                 \        |    /
                          C                            *)

  Prod_obj : Obj -> Obj -> Obj;

  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;

  pr_1 {x y} : (Prod_obj x y) → x;
  pr_2 {x y} : (Prod_obj x y) → y;

  prod_ax : forall {x y z} (f : x → y) (g : x → z), 
    (pr_1 ∘ (Prod_mor f g) = f) /\ (pr_2 ∘ (Prod_mor f g) = g);
    
  prod_eq : forall {x y z} (g : x → Prod_obj y z),
    Prod_mor (pr_1 ∘ g) (pr_2 ∘ g) = g;

(* exponential *)
(* C                     C x A
     |                       |    \ 
     | λ f          λf ∏ Id_A|            \ f
    \|/                     \|/                    \
     B^A                 B^A x A ----------------------> B 
                                         eval                      *)

  Exp_obj : Obj -> Obj -> Obj;

  Ev: forall {y z}, (Prod_obj (Exp_obj z y) y) → z;

  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);

  exp_ax : forall {x y z} (g : (Prod_obj x y) → z), 
    Ev ∘ (Prod_mor ((Lam g) ∘ pr_1) ((Id y) ∘ pr_2)) = g;
  
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Ev ∘ (Prod_mor (h ∘ pr_1) ((Id y) ∘ pr_2))) = h

}.


Notation "⊤" := (Terminal_obj) (at level 40, no
associativity) : type_scope.

Notation "〇" := (Initial_obj) (at level 40, no associativity) : type_scope.

(* product: \prod *)
Notation "f '∏' g" := (Prod_mor f g) (at level 40, no associativity) : type_scope.

(* torii: \Pi *)
Notation "h 'Π' k" := (Prod_mor (h ∘ pr_1) (k ∘ pr_2)) (at level 40, no associativity) : type_scope.


Notation "x × y" := (Prod_obj x y) (at level 40, left associativity) :
type_scope. 

Notation "x 'e↑' y" := (Exp_obj x y) (at level 80, right associativity) :
type_scope.

Theorem unique_prod {C : Category} {CC : @CartClosed C} : forall x y z (f1 : x → y) (f2 : x → z) (g : x → Prod_obj y z),
    ((pr_1 ∘ g) = f1) /\ ((pr_2 ∘ g) = f2) ->  Prod_mor f1 f2 = g.
Proof.
intros.
destruct H as [H1 H2].
rewrite <- H1; rewrite <- H2.
apply prod_eq.
Defined.

Theorem compos_prod {C : Category} {CC : @CartClosed C} : forall x y z w (f : w → y ) (g : w → z ) (h : x → w),
  (f ∘ h) ∏ (g ∘ h) = ( f ∏ g ) ∘ h.
Proof.
intros.
apply unique_prod.
split.
assert (H:pr_1 ∘ (f ∏ g ∘ h) = pr_1 ∘ (f ∏ g) ∘ h).
apply assoc.
rewrite H.
assert (K:pr_1 ∘ (f ∏ g)=f).
apply prod_ax.
rewrite K.
auto.
assert (H: pr_2 ∘ ((f ∏ g) ∘ h) = pr_2 ∘ (f ∏ g) ∘ h).
apply assoc.
rewrite H.
assert (K:pr_2 ∘ (f ∏ g)=g).
apply prod_ax.
rewrite K.
auto.
Defined.

(*in_element_wise_bijection in Type*)
Definition in_element_wise_bijection A B := exists (f: A -> B), (forall (x y : A), f x = f y -> x = y) /\ (forall (y : B), exists x, f x = y).

Theorem Currying_ver_1 {C : Category} {CC : @CartClosed C} : forall x y z, in_element_wise_bijection (Hom (z × x) y) (Hom z (y e↑ x)).
Proof.
intros.
unfold in_element_wise_bijection.
exists (fun f => Lam f).
split.
intros.
assert (H1: Ev ∘ (Prod_mor ((Lam x0) ∘ pr_1) ((Id x) ∘ pr_2)) = x0).
apply exp_ax.
assert (H2: Ev ∘ (Prod_mor ((Lam y0) ∘ pr_1) ((Id x) ∘ pr_2)) = y0).
apply exp_ax.
rewrite <- H in H2.
congruence.
intros.
exists (Ev ∘ (Prod_mor (y0 ∘ pr_1) ((Id x) ∘ pr_2))).
apply unique_exp.
Defined.

Definition in_algebraic_bijection A B := exists (f: A -> B) (g: B -> A), (forall (x : A), g (f x) = x) /\ (forall (y : B), f (g y) = y).

Theorem Currying_ver_2 {C : Category} {CC : @CartClosed C} : forall x y z, in_algebraic_bijection (Hom (z × x) y) (Hom z (y e↑ x)).
Proof.
(* Házi *)
Abort.

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

Class ContravariantFunctor (C : Category) (D : Category) := mk_ContraFunctor {
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

Definition Isomorphism {C : Category} {A B : Obj} (f : Hom A B) := (exists g : Hom B A, ((f ∘ g) = Id B ) /\ ((g ∘ f) = Id A )). 

Definition Isomorphical {C : Category} (A B : Obj) := (exists f : Hom A B, Isomorphism f). 

Infix "x ≅ y" := (Isomorphical x y) (at level 80, right associativity).

Class NaturalTransformation (C : Category) (D : Category) (F G : ContravariantFunctor C D) := mk_NatTrans {
  trans_mor : forall (x : @Obj C), @Hom D ((@CoF_Obj C D F) x) ((@CoF_Obj C D G) x);
  naturality_square : forall (x y : @Obj C) (f : @Hom C x y),
    (@Compose D _ _ _ (trans_mor x) (@CoF_Hom C D F x y f)) =
    (@Compose D _ _ _ (@CoF_Hom C D G x y f) (trans_mor y))
}.

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

Class CovariantFunktor (C : Category) (D : Category) := mk_Functor {
  F_Obj : @Obj C -> @Obj D;
  F_Hom : forall (x y : @Obj C), (x → y) -> (F_Obj x → F_Obj y);
  F_id : forall (x : @Obj C), F_Hom x x (Id x) = Id (F_Obj x);
  F_comp : forall (x y z : @Obj C) (g : y → z) (f : x → y),
    F_Hom x z (g ∘ f) = (F_Hom y z g) ∘ (F_Hom x y f);
}.

Lemma pr_and_id {C : Category} {CC : @CartClosed C} : forall (A B : @Obj C), Id (A × B) = pr_1 ∏ pr_2.
Proof.
intros.
assert (H : (pr_1 ∘ (Id (A × B))) ∏ (pr_2 ∘ (Id (A × B))) = pr_1 ∏ pr_2).
rewrite id_1.
symmetry.
rewrite id_1.
reflexivity.
rewrite <- H.
symmetry.
rewrite prod_eq.
reflexivity.
Defined.


Instance ProdFunctor {C : Category} {CC : @CartClosed C} (A : @Obj C) : CovariantFunktor C C.
Proof.
(*Nem biztos, de próba szerencse, ki kell találni a morfizmust!*)
apply mk_Functor with (F_Obj := fun X => X × A) (F_Hom := fun x y f => (f ∘ pr_1) ∏ pr_2).
Abort.

Instance ExpFunctor {C : Category} {CC : @CartClosed C} (A : @Obj C) : CovariantFunktor C C.
Proof.
(*Nem biztos, de próba szerencse, ki kell találni a morfizmust!*)
apply mk_Functor with (F_Obj := fun X => X e↑ A)
(F_Hom := fun x y f => Lam (f ∘ Ev)).
Abort.

Class IsLeftAdjoint  (C D : Category) (F : CovariantFunktor D C) := mk_IsLeftAdjoint {

  rightadjobj : @Obj C -> @Obj D;
  epsilon : forall (X : @Obj C), (@F_Obj D C F (rightadjobj X)) → X;
  rightadjmor : forall {Y : @Obj D} {X : @Obj C} (f : (@F_Obj D C F Y) → X), Y → (rightadjobj X);

  lambek_1 : forall {Y X} (f : (@F_Obj D C F Y) → X),
    (epsilon X) ∘ (@F_Hom D C F _ _ (rightadjmor f)) = f;
  lambek_2 : forall {Y X} (h : Y → (rightadjobj X)),
    rightadjmor ((epsilon X) ∘ (@F_Hom D C F _ _ h)) = h}.



Class IsRightAdjoint {C D : Category} (G : CovariantFunktor C D) := mk_IsRightAdjoint {
  leftadjobj : @Obj D -> @Obj C;
  unit : forall (Y : @Obj D), Y → (@F_Obj C D G (leftadjobj Y));
  leftadjmor : forall {X : @Obj D} {Y : @Obj C} (g : X → (@F_Obj C D G Y)), (leftadjobj X) → Y;

  lambek_1_dual : forall {X : @Obj D} {Y : @Obj C} (g : X → (@F_Obj C D G Y)),
    (@F_Hom C D G _ _ (leftadjmor g)) ∘ (unit X) = g;
  lambek_2_dual : forall {X : @Obj D} {Y : @Obj C} (f : (leftadjobj X) → Y),
    leftadjmor ((@F_Hom C D G _ _ f) ∘ (unit X)) = f
}.




