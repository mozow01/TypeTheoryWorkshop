Require Import List.
Import ListNotations.

Inductive Typ : Set :=
  | At : nat -> Typ
  | Top : Typ
  | Imp : Typ -> Typ -> Typ
  | Cnj : Typ -> Typ -> Typ.

Inductive Trm : Set :=
  | top : Trm
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm
  | cnj : Trm -> Trm -> Trm
  | proj_1 : Trm -> Trm
  | proj_2 : Trm -> Trm.

Definition Cntxt := list Typ.

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | STT_top : forall Γ, Tyty Γ top Top
  | STT_hypO : forall Γ A, Tyty (A :: Γ) (hyp 0) A
  | STT_hypS :
      forall Γ A B i,
      Tyty Γ (hyp i) A -> Tyty (B :: Γ) (hyp (S i)) A
  | STT_lam :
      forall Γ t A B,
      Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (Imp A B)
  | STT_app :
      forall Γ t s A B,
      Tyty Γ t (Imp A B) -> Tyty Γ s A -> Tyty Γ (app t s) B
  | STT_cnj :
      forall Γ t s A B,
      Tyty Γ t A -> Tyty Γ s B -> Tyty Γ (cnj t s) (Cnj A B)
  | STT_proj1 :
      forall Γ t A B,
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_1 t) A
  | STT_proj2 :
      forall Γ t A B,
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_2 t) B.

Notation "Γ '⊢' t '[:]' A" := (Tyty Γ t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

Notation "A ⊃ B" := (Imp A B) (at level 70, right associativity) :
type_scope.

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

Notation "x → y" := (Hom x y) (at level 70, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 71, left associativity) :
type_scope.

Definition Obj_STT := Typ.

Definition Hom_STT (x y : Obj_STT) := { t : Trm | ⊢ t [:] (x ⊃ y)}.

Definition Id_STT_term (x : Obj_STT) := (lam x (hyp 0)).

Lemma Id_STT_type (x : Obj_STT) : ⊢ (Id_STT_term x) [:] (x ⊃ x).
Proof.
unfold Id_STT_term.
apply STT_lam.
apply STT_hypO.
Defined.

Definition Id_STT (x : Typ) : {t : Trm | ⊢ t [:] (x ⊃ x)} :=
  exist (fun t => ⊢ t [:] (x ⊃ x)) (Id_STT_term x) (Id_STT_type x).

Lemma weakening_weak : forall Γ Δ t A,
  Γ ⊢ t [:] A -> (Γ ++ Δ) ⊢ t [:] A.
Proof.
  assert (K : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l).
  simpl; auto.
  intros Γ Δ t A H.
  induction H.
  all: try rewrite K; try rewrite <- app_assoc; try rewrite <- K.
  - apply STT_top.
  - apply STT_hypO.
  - apply STT_hypS.
    auto.
  - apply STT_lam.
    rewrite K in IHTyty.
    rewrite <- app_assoc in IHTyty.
    rewrite <- K in IHTyty.
    auto.
  - apply STT_app with (A := A).
    all: auto.
  - apply STT_cnj.
    all: auto.
  - apply STT_proj1 with (Γ := Γ ++ Δ ) (B:=B).
    auto.
 - apply STT_proj2 with (Γ := Γ ++ Δ ) (A:=A).
    auto.
Defined.

Definition Compose_STT_term {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) := lam x (app (proj1_sig f) (app (proj1_sig g) (hyp 0))).

Definition Compose_STT_type {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) : ⊢ (Compose_STT_term f g) [:] (x ⊃ z).
Proof.
unfold Compose_STT_term.
apply STT_lam.
assert (Kf : ⊢ (proj1_sig f) [:] (y ⊃ z)).
 { exact (proj2_sig f). }
assert (Kg : ⊢ (proj1_sig g) [:] (x ⊃ y)).
 { exact (proj2_sig g). }
assert (Kfx : [x] ⊢ (proj1_sig f) [:] (y ⊃ z)).
 { apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig f); auto. }
assert (Kgx : [x] ⊢ (proj1_sig g) [:] (x ⊃ y)).
 { apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig g); auto. }
apply STT_app with (A:=y). auto.
apply STT_app with (A:=x). auto.
apply STT_hypO.
Defined.

Definition Compose_STT {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) : {t : Trm | ⊢ t [:] (x ⊃ z)} :=
  exist (fun t => ⊢ t [:] (x ⊃ z)) (Compose_STT_term f g) (Compose_STT_type f g).

Axiom ProofIrrelevance : forall (Γ : Cntxt) (A : Typ) (x y : { t : Trm | Γ ⊢ t [:] A}), x = y.

Instance STT_as_a_Cat : Category. 
Proof.
apply cat_mk with (Obj := Obj_STT) (Hom := Hom_STT) (Id := Id_STT) (Compose := @Compose_STT).
all: intros; unfold Compose_STT; unfold Compose_STT_term; simpl; unfold Compose_STT_type; simpl; apply ProofIrrelevance.
Defined.

Class CartClosedCat (C : Category) := CartClosedCat_mk {
  Top_obj : Obj;
  Top_mor : forall {x}, x → Top_obj;
  Prod_obj : Obj -> Obj -> Obj;
  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;
  First {x y} : (Prod_obj x y) → x;
  Second {x y} : (Prod_obj x y) → y;
  Exp_obj : Obj -> Obj -> Obj;
  Exp_app : forall {y z}, (Prod_obj (Exp_obj z y) y) → z;
  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);

  unique_top : forall {x} (f : x → Top_obj), f = Top_mor;
  prod_ax_1 : forall {x y z} (f : x → y) (g : x → z), 
    ((First ∘ (Prod_mor f g)) = f);
  prod_ax_2 : forall {x y z} (f : x → y) (g : x → z),((Second ∘ (Prod_mor f g)) = g);
  unique_prod : forall {x y z} (f : x → y) (g : x → z) (h : x → Prod_obj y z),
    ((First ∘ h) = f) /\ ((Second ∘ h) = g) -> h = (Prod_mor f g);
  exp_ax : forall {x y z} (g : ((Prod_obj x y) → z)), 
    (Exp_app ∘ (Prod_mor (Compose (Lam g) First) (Compose (Id y) Second))) = g;
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Exp_app ∘ (Prod_mor (Compose h First) (Compose (Id y) Second))) = h
}.

Lemma pr_1 : forall A, A -> True.
Proof.
firstorder.
Show Proof.
Qed.

Lemma top_1 : forall A : Typ,  ⊢ (lam A top) [:] (Imp A Top).
Proof.
intros.
apply STT_lam.
apply STT_top.
Defined.

Lemma prod_3 : forall {A B C} t s, (⊢ t [:] (Imp A B)) -> (⊢ s [:] (Imp A C)) -> (⊢ t [:] (Imp A (Cnj B C))).
Proof.
intros.

Defined.

Instance STT_as_a_CCC : CartClosedCat STT_as_a_Cat. 
Proof.
apply CartClosedCat_mk with (Top_obj := Top) (Prod_obj := Cnj) (Exp_obj := (fun A B => Imp B A)).

Defined.
