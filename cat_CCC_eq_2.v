Section CCC.


Class Category := mk_cat {
  Obj : Type;

  uHom := Type : Type;

  Hom : Obj -> Obj -> uHom;

  Id : forall x, Hom x x;

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

Context {C : Category}.  

Class CartClosed := {

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

Context {CC : CartClosed}.

Lemma prod_ax_1 : forall {x y z} (f : x → y) (g : x → z), (pr_1 ∘ (Prod_mor f g) = f).
Proof.
intros.
apply prod_ax.
Defined.

Lemma prod_ax_2 : forall {x y z} (f : x → y) (g : x → z), (pr_2 ∘ (Prod_mor f g) = g).
Proof.
intros.
apply prod_ax.
Defined.

Theorem unique_prod : forall x y z (f1 : x → y) (f2 : x → z) (g : x → Prod_obj y z),
    ((pr_1 ∘ g) = f1) /\ ((pr_2 ∘ g) = f2) ->  Prod_mor f1 f2 = g.
Proof.
intros.
destruct H as [H1 H2].
rewrite <- H1; rewrite <- H2.
apply prod_eq.
Defined.

Theorem compos_prod : forall x y z w (f : w → y ) (g : w → z ) (h : x → w),
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

Theorem Currying_ver_1 : forall x y z, in_element_wise_bijection (Hom (z × x) y) (Hom z (y e↑ x)).
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

Definition in_algebraic_bijection_2 A B := exists (f: A -> B) (g: B -> A), (fun (x : A) => g (f x)) = (fun x => x) /\ (fun (y : B) => f (g y)) = (fun y => y).

Theorem Currying_ver_2 : forall x y z, in_algebraic_bijection (Hom (z × x) y) (Hom z (y e↑ x)).
Proof.
(* Házi *)
Abort.

Definition Isomorphism {C : Category} {A B : Obj} (f : Hom A B) := (exists g : Hom B A, ((f ∘ g) = Id B ) /\ ((g ∘ f) = Id A )). 

Definition Isomorphical {C : Category} (A B : Obj) := (exists f : Hom A B, Isomorphism f). 

Infix "x ≅ y" := (Isomorphical x y) (at level 80, right associativity).

(*szerda on*)

Definition swap {A B : Obj} : A × B → B × A :=
  Prod_mor pr_2 pr_1.

Definition swap_inv {A B : Obj} : B × A → A × B :=
  Prod_mor pr_2 pr_1.

Lemma prod_sym_alg_1 : forall A B : Obj, Isomorphical (A × B) (B × A).
Proof.
intros.
unfold Isomorphical.
exists swap.
unfold Isomorphism.
exists swap_inv.
split.
all: unfold swap, swap_inv; rewrite <- compos_prod; rewrite prod_ax_1, prod_ax_2.
 - enough (H : (pr_1 ∘ Id (B × A) ) ∏ (pr_2 ∘ Id (B × A)) = Id (B × A)).
   + rewrite id_1 in H.
     assert (H1 : (pr_2 ∘ Id (B × A)) = pr_2). 
      { rewrite id_1.
        reflexivity. }
     rewrite H1 in H.
     exact H.
   + apply prod_eq.
 - enough (H : (pr_1 ∘ Id (A × B) ) ∏ (pr_2 ∘ Id (A × B)) = Id (A × B)).
   + rewrite id_1 in H.
     assert (H1 : (pr_2 ∘ Id (A × B)) = pr_2). 
      { rewrite id_1.
        reflexivity. }
     rewrite H1 in H.
     exact H.
   + apply prod_eq.
Defined.

Theorem prod_sym_raised : forall A B X : Obj,
  in_element_wise_bijection (Hom X (B × A)) (Hom X (A × B)).
Proof.
  intros.
  unfold in_element_wise_bijection.
  exists (fun (g : X → B × A) => (@swap B A) ∘ g).
  split.
  - intros h k H.
    unfold swap in *.
    rewrite <- compos_prod in H.
    symmetry in H.
    rewrite <- compos_prod in H.
    assert (H1 : pr_1 ∘ ((pr_2 ∘ k) ∏ (pr_1 ∘ k)) = pr_1 ∘
    ((pr_2 ∘ h) ∏ (pr_1 ∘ h))).
    + rewrite H.
      reflexivity.
    + rewrite prod_ax_1 in H1.
      symmetry.
      rewrite prod_ax_1 in H1.
    assert (H2 : pr_2 ∘ ((pr_2 ∘ k) ∏ (pr_1 ∘ k)) = pr_2 ∘
    ((pr_2 ∘ h) ∏ (pr_1 ∘ h))).
    * rewrite H.
      reflexivity.
    * rewrite prod_ax_2 in H2.
      symmetry.
      rewrite prod_ax_2 in H2.
    assert (K :(pr_1 ∘ k) ∏ (pr_2 ∘ k) =
    (pr_1 ∘ h) ∏ (pr_2 ∘ h)).
    ** rewrite H1, H2.
       reflexivity.
    ** rewrite prod_eq in K.
       symmetry in K.
       rewrite prod_eq in K.
       exact K.
Abort.

Theorem prod_sym_raised_2 : forall A B X : Obj,
  in_algebraic_bijection (Hom X (B × A)) (Hom X (A × B)).
Proof.
intros.
unfold in_algebraic_bijection.
exists (fun (h : X → B × A) => (@swap B A) ∘ h).
exists (fun (k : X → A × B) => (@swap A B) ∘ k).
split.
intros h.
unfold swap in *.
(*Házi*)
Abort.

Require Import Coq.Logic.FunctionalExtensionality. 

Theorem prod_sym_raised_3 : forall A B X : Obj,
  in_algebraic_bijection_2 (Hom X (B × A)) (Hom X (A × B)).
Proof.
unfold in_algebraic_bijection_2.
intros.
exists (fun (h : X → B × A) => (@swap B A) ∘ h).
exists (fun (k : X → A × B) => (@swap A B) ∘ k).
split.
extensionality x.
(*Házi*)
Abort.

(*szerda off*)

Instance Type_as_a_Cat : Category.
Proof.
apply mk_cat with 
  (Obj := Type) 
  (Hom := fun (A B : Type) => A -> B)
  (Id := fun (A : Type) => (fun (x : A) => x))
  (Compose := fun (A B C : Type) (f : B -> C) (g : A -> B) => (fun x : A => f (g x))).
all: intros; simpl; reflexivity.
Defined.

(*Nem kell így, de lehet, viszont ha akarjuk a funktor kategóriát és a Coq natív =-t, akkor kell funex (Coq.Logic.FunctionalExtensionality) is.*)

Class ContravariantFunctor (C D : Category) := mk_ContraFunctor {
  CoF_Obj : @Obj C -> @Obj D;
  CoF_Hom : forall (x y : @Obj C), @Hom C x y -> @Hom D (CoF_Obj y) (CoF_Obj x);
  CoF_id : forall (x : @Obj C), (@CoF_Hom x x (@Id C x)) = (@Id D (@CoF_Obj x));
  CoF_comp : forall (x y z : @Obj C) (f : @Hom C y z) (g : @Hom C x y), (@CoF_Hom x z (@Compose C x y z f g)) = 
               (@Compose D (@CoF_Obj z) (@CoF_Obj y) (@CoF_Obj x) (@CoF_Hom x y g) (@CoF_Hom y z f)); 
}.

Instance PredicateFunctor (R : Type) : ContravariantFunctor Type_as_a_Cat Type_as_a_Cat.
Proof.
apply mk_ContraFunctor with 
  (CoF_Obj := fun (A : Type) => A -> R) 
  (CoF_Hom := fun (A B : Type) (f : A -> B) => (fun (p : B -> R) => fun x => p (f x))).
all: intros; simpl; reflexivity.
Defined. 

End CCC.

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



