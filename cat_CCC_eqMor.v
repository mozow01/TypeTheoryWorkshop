Require Import Coq.Setoids.Setoid.
 

Class Category := cat_mk {
  Obj : Type;
  uHom := Type : Type;
  Hom : Obj -> Obj -> uHom;
  Id : forall x, Hom x x;
  Dom {x y} (f: Hom x y) := x;
  CoDom {x y} (f: Hom x y) := y;
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);
  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;

  (* ekvivalencia reláció tulajdonságai *)
  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;
  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;

  (* kategória axiómák *)
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f;
  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f;
  
  (* kongruencia *)
  eq: forall {x y z} (f g: Hom y z) (h i : Hom x y), EqMor f g /\ EqMor h i ->
        EqMor (Compose f h) (Compose g i);
}.


Notation "x → y" := (Hom x y) (at level 90, right associativity) : type_scope.
Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) : type_scope.
Notation "f ≡ g" := (EqMor f g) (at level 40, left associativity) : type_scope.

Add Parametric Relation {C : Category} {A B: Obj} : (Hom A B) (EqMor)
  reflexivity proved by (Eq_ref)
  symmetry proved by (Eq_sim)
  transitivity proved by (Eq_trans)
  as eq_set_rel.

Add Parametric Morphism {C: Category} {a b c: @Obj C} : (@Compose C a b c)
  with signature (EqMor) ==> (EqMor) ==> (EqMor) as compose_keeps_equality.
Proof.
intros.
apply eq.
split.
exact H.
exact H0.
Defined.


Lemma eq_2 : forall {C: Category} {x y z} (f: Hom x y) (g h : Hom y z), g ≡ h -> (g ∘ f) ≡ (h ∘ f).
Proof.
intros.
apply eq.
split.
exact H.
reflexivity.
Defined.

Class CartClosed (C : Category) := {

  (* terminális objektum *)
  Terminal_obj : Obj;
  Terminal_mor : forall {x}, x → Terminal_obj;
  unique_terminal : forall {x} (f : x → Terminal_obj), f ≡ Terminal_mor;

  (* iniciális objektum *)
  Initial_obj : Obj;
  Initial_mor : forall {x}, Initial_obj → x;
  unique_initial : forall {x} (f : Initial_obj → x), f ≡ Initial_mor;

  (* szorzat (product) *)
  Prod_obj : Obj -> Obj -> Obj;
  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;
  pr_1 {x y} : (Prod_obj x y) → x;
  pr_2 {x y} : (Prod_obj x y) → y;

  prod_ax : forall {x y z} (f : x → y) (g : x → z), 
    (pr_1 ∘ (Prod_mor f g) ≡ f) /\ (pr_2 ∘ (Prod_mor f g) ≡ g);
    
  prod_eq : forall {x y z} (g : x → Prod_obj y z),
    Prod_mor (pr_1 ∘ g) (pr_2 ∘ g) ≡ g;

  (* exponenciális objektum *)
  Exp_obj : Obj -> Obj -> Obj;
  Ev : forall {y z}, (Prod_obj (Exp_obj z y) y) → z;
  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);

  exp_ax : forall {x y z} (g : (Prod_obj x y) → z), 
    Ev ∘ (Prod_mor ((Lam g) ∘ pr_1) ((Id y) ∘ pr_2)) ≡ g;
  
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Ev ∘ (Prod_mor (h ∘ pr_1) ((Id y) ∘ pr_2))) ≡ h
}. 


Notation "⊤" := (Terminal_obj) (at level 40, no associativity) : type_scope.
Notation "〇" := (Initial_obj) (at level 40, no associativity) : type_scope.
Notation "x × y" := (Prod_obj x y) (at level 40, left associativity) : type_scope.
Notation "x 'e↑' y" := (Exp_obj x y) (at level 80, right associativity) : type_scope.

(* product: \prod *)
Notation "f '∏' g" := (Prod_mor f g) (at level 40, no associativity) : type_scope.
(* torii: \Pi *)
Notation "h 'Π' k" := (Prod_mor (h ∘ pr_1) (k ∘ pr_2)) (at level 40, no associativity) : type_scope.

