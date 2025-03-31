Class Category := cat_mk {
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

Class biCartClosed := {

(* initial *)

  Initial_obj : Obj;

  Initial_mor : forall {x}, Initial_obj → x;
 
  unique_initial : forall {x} (f : Initial_obj →  x), f = Initial_mor;


(* terminal *)

  Terminal_obj : Obj;

  Terminal_mor : forall {x}, x → Terminal_obj;
 
  unique_terminal : forall {x} (f : x → Terminal_obj), f = Terminal_mor;

(* szorzat *)

  Prod_obj : Obj -> Obj -> Obj;

  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;

  pr_1 {x y} : (Prod_obj x y) → x;
  pr_2 {x y} : (Prod_obj x y) → y;

  prod_ax : forall {x y z} (f : x → y) (g : x → z), 
    (pr_1 ∘ (Prod_mor f g) = f) /\ (pr_2 ∘ (Prod_mor f g) = g);
    
  prod_eq : forall {x y z} (g : x → Prod_obj y z),
    Prod_mor (pr_1 ∘ g) (pr_2 ∘ g) = g;

(* összeg*)

  Sum_obj : Obj -> Obj -> Obj;

  Sum_mor : forall {x y z} (f:x → z) (g:y → z), Sum_obj x y → z;

  in_1 {x y} : x → (Sum_obj x y);
  in_2 {x y} : y → (Sum_obj x y);

  sum_ax : forall {x y z} (f : x → z) (g : y → z), 
    ((Sum_mor f g) ∘ in_1 = f) /\ ((Sum_mor f g) ∘ in_2 = g);
    
  sum_eq : forall {x y z} (g : Sum_obj x y → z),
    Sum_mor (g ∘ in_1) (g ∘ in_2) = g;

(* exponenciális *)

  Exp_obj : Obj -> Obj -> Obj;

  Exp_app : forall {y z}, (Prod_obj (Exp_obj z y) y) → z;

  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);

  exp_ax : forall {x y z} (g : (Prod_obj x y) → z), 
    Exp_app ∘ (Prod_mor ((Lam g) ∘ pr_1) ((Id y) ∘ pr_2)) = g;
  
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Exp_app ∘ (Prod_mor (h ∘ pr_1) ((Id y) ∘ pr_2))) = h

}.


Class EndoFunctor {C : Category} := {

EF_obj : @Obj C -> @Obj C;

EF_mor : forall {x y}, (Hom x y) -> (Hom (EF_obj x) (EF_obj y));

EF_id_ax : forall {x}, EF_mor (Id x) = Id (EF_obj x);

EF_comp_ax : forall {x y z : @Obj C} {f g},
      @EF_mor x z (f ∘ g) = (@EF_mor y z f) ∘ (@EF_mor x y g)
}.



Notation "⊤" := (Terminal_obj) (at level 400, no
associativity) : type_scope.

Notation "⊥" := (Initial_obj) (at level 400, no
associativity) : type_scope.

Notation "f '∏' g" := (Prod_mor f g) (at level 40, no associativity) : type_scope.

Notation "x × y" := (Prod_obj x y) (at level 40, left associativity) :
type_scope. 

Notation "x 'e↑' y" := (Exp_obj x y) (at level 80, right associativity) :
type_scope.


Context {CC : biCartClosed}.

Theorem unique_prod : forall x y z (f1 : x → y) (f2 : x → z) (g : x → Prod_obj y z),
    ((pr_1 ∘ g) = f1) /\ ((pr_2 ∘ g) = f2) ->  Prod_mor f1 f2 = g.
Proof.
intros.
destruct H as [H1 H2].
rewrite <- H1; rewrite <- H2.
apply prod_eq.
Qed.


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
Qed.

Definition equivalent (X Y : uHom) := exists (i : X -> Y), (forall x1 x2, i x1 = i x2 -> x1 = x2) /\ (forall y : Y, exists x : X, i x = y).

Definition isomorph x y := exists (i : x → y) (j : y → x), i ∘ j = Id y /\ j ∘ i = Id x.

Notation "x '≅' y" := (isomorph x y) (at level 40, left associativity) :
type_scope.

Theorem Currying : forall X Y Z, equivalent (Hom (Z×X) Y) (Hom Z (Y e↑ X)).
Proof.
intros.
unfold equivalent.
exists (fun f=> Lam f).
split.
intros.
assert (K1 : Exp_app ∘ (Prod_mor ((Lam x1) ∘ pr_1) ((Id X) ∘ pr_2)) = x1).
apply exp_ax.
assert (K2 : Exp_app ∘ (Prod_mor ((Lam x2) ∘ pr_1) ((Id X) ∘ pr_2)) = x2).
apply exp_ax.
congruence.
intros.
exists (Exp_app ∘ (Prod_mor (y ∘ pr_1) ((Id X) ∘ pr_2))).
apply unique_exp.
Qed.

Definition Singleton (H : uHom) := exists x : H, forall y : H, y = x.

Lemma initialHom : forall Y, Singleton (Hom Initial_obj Y).
Proof.
intros.
unfold Singleton.
exists Initial_mor.
intros.
apply unique_initial.
Qed.

Lemma  id_11 : forall x y (f : (Hom x y)), f = (Compose f (Id x)).
Proof.
assert (H: forall (x y : Obj) (f : x → y), f ∘ Id x = f).
exact id_1.
congruence.
Qed.


Theorem distributive_law : forall x y z w (f: Hom (z×x) y) (g: Hom w z), (Lam f) ∘ g = Lam (f ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2))).
Proof.
intros.




Theorem Egy_szer_x_egyenlő_x : forall X, ⊤ × X ≅ X.
Proof.
intros.
unfold isomorph.
exists (@pr_2 CC Terminal_obj X).
exists ((@Terminal_mor CC X) ∏ (Id X)).
split.
apply prod_ax.
assert (H: (Terminal_mor ∏ Id X) ∘ (@pr_2 CC Terminal_obj X) = 
(Terminal_mor ∘ (@pr_2 CC Terminal_obj X)) ∏ (Id X ∘ (@pr_2 CC Terminal_obj X))).
enough (K: (Terminal_mor ∘ (@pr_2 CC Terminal_obj X)) ∏ (Id X ∘ (@pr_2 CC Terminal_obj X)) = (Terminal_mor ∏ Id X) ∘ (@pr_2 CC Terminal_obj X)).
congruence.
apply compos_prod.
rewrite H.
assert (K:Id X ∘ (@pr_2 CC Terminal_obj X)=pr_2).
apply id_2.
rewrite K.
assert (L1:Terminal_mor ∘ (@pr_2 CC Terminal_obj X) = @Terminal_mor CC (⊤ × X)).
apply unique_terminal.
assert (L2:@pr_1 CC Terminal_obj X = @Terminal_mor CC (⊤ × X)).
apply unique_terminal.
rewrite <- L1 in L2.
assert (L: Terminal_mor ∘ (@pr_2 CC Terminal_obj X) = @pr_1 CC Terminal_obj X ).
congruence.
rewrite L.
assert (M1:(@pr_1 CC Terminal_obj X) ∘ Id (⊤ × X) = @pr_1 CC Terminal_obj X ).
apply id_1.
assert (M1':(@pr_1 CC Terminal_obj X = (@pr_1 CC Terminal_obj X) ∘ Id (⊤ × X))).
congruence.
rewrite M1'.
assert (M2:(@pr_2 CC Terminal_obj X) ∘ Id (⊤ × X) = @pr_2 CC Terminal_obj X ).
apply id_1.
assert (M2':(@pr_2 CC Terminal_obj X = (@pr_2 CC Terminal_obj X) ∘ Id (⊤ × X))).
congruence.
rewrite M2'.
apply prod_eq.
Qed.

Class F_algebra {C : Category} (F : @EndoFunctor C) := {

Carr_F_alg : @Obj C;

Mor_F_alg : Hom ((@EF_obj C F) Carr_F_alg) Carr_F_alg
}.

Definition F_algebras_Obj {C : Category} (F : @EndoFunctor C) := (@sigT (@Obj C) (fun (x:@Obj C) => Hom (@EF_obj C F x) x) ) : Type.

Definition F_algebras_Hom {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) (y : F_algebras_Obj F) 
:=@Hom C (projT1 x) (projT1 y).

Definition F_algebras_Id {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) : @F_algebras_Hom C F x x.
unfold F_algebras_Hom.
exact (@Id C (projT1 x)).
Defined.

Definition F_algebras_Comp {C : Category} (F : @EndoFunctor C) (x y z : F_algebras_Obj F)
(h : F_algebras_Hom F y z ) (k : F_algebras_Hom F x y ) : F_algebras_Hom F x z.
unfold F_algebras_Hom.
exact (h ∘ k).
Defined.


Definition F_algebras_form_a_Cat {C : Category} (F : @EndoFunctor C) : Category.
Proof.
apply (cat_mk (@F_algebras_Obj C F) (@F_algebras_Hom C F) (@F_algebras_Id C F) (@F_algebras_Comp C F) ).
2 : {
intros.
unfold F_algebras_Id.
unfold F_algebras_Comp.
apply id_1. }
2 : {
intros.
unfold F_algebras_Id.
unfold F_algebras_Comp.
apply id_2. }
intros.
unfold F_algebras_Comp.
apply assoc.
Qed.

Search identity.





