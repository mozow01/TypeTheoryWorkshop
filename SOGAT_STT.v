Inductive Fm : Set :=
  | Tru : Fm
  | Imp : Fm -> Fm -> Fm
  | Cnj : Fm -> Fm -> Fm.

Parameter Pfvar : Fm -> Set.

(* Inductive Pf {Pfvar : Fm -> Set} : Fm -> Set := 
 *)

Inductive Pf : Fm -> Set := 
  | tt : Pf Tru
  | hyp : forall (A : Fm), (Pfvar A -> Pf A)
  | lam : forall (A B : Fm), (Pfvar A -> Pf B) -> Pf (Imp A B)
  | app : forall A B : Fm, Pf (Imp A B) -> Pf A -> Pf B
  | andi : forall (A B : Fm), Pf A -> Pf B -> Pf (Cnj A B)
  | ande : forall A B C : Fm, Pf (Cnj A B) -> (Pfvar A -> Pfvar B -> Pf C) -> Pf C.

Lemma app_konv : forall A B : Fm,  (Pf A -> Pf B) -> Pf (Imp A B).
Proof.
intros.
apply lam.
intros.
apply hyp in H0.
apply H.
auto.
Defined.

Definition Obj_STT := Fm.

Definition Hom_STT (A B : Obj_STT) := Pf (Imp A B).

Lemma Id_proof : forall A, Pf (Imp A A).
Proof.
intros.
apply lam.
intros x.
apply hyp.
exact x.
Show Proof.
Defined.

Definition Id_STT (A : Obj_STT) := lam A A (fun x : Pfvar A => hyp A x).

Lemma Comp_proof : forall A B C, Pf (Imp A B) -> Pf (Imp B C) -> Pf (Imp A C).
Proof.
intros.
apply lam.
intros x.
apply app with (A:=B).
auto.
apply app with (A:=A).
auto.
apply hyp.
auto.
Show Proof.
Defined.

Definition Compose_STT {A B C : Obj_STT} (f : Hom_STT B C) (g : Hom_STT A B)  := (lam A C (fun x : Pfvar A => app B C f (app A B g (hyp A x)))).

Axiom ProofIrrelevance : forall (A : Fm) (x y : Pf A), x = y.

Lemma id_1_STT : forall A B (f : (Hom_STT A B)), Compose_STT f (Id_STT A) = f.
Proof.
intros.
unfold Compose_STT, Id_STT.
apply ProofIrrelevance with (A:=Imp A B).
Defined.

Lemma id_2_STT : forall A B (f : (Hom_STT A B)), Compose_STT (Id_STT B) f = f.
Proof.
intros.
apply ProofIrrelevance with (A:=Imp A B).
Defined.

Lemma assoc_STT : forall A B C D (f : Hom_STT C D) (g : Hom_STT B C) (h : Hom_STT A B) , (Compose_STT f (Compose_STT g h)) = (Compose_STT (Compose_STT f g) h).
Proof.
intros.
apply ProofIrrelevance with (A:=Imp A D).
Defined.

Class Category := cat_mk {
  uHom := Type : Type;
  Obj : Type;
  Hom : Obj -> Obj -> uHom; 
  Id : forall x, Hom x x; 
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z); 

  (* associativity, identity*)
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f;
  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f;
}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

Instance STT_as_a_Cat : Category. 
Proof.
apply cat_mk with (Obj := Obj_STT) (Hom := Hom_STT) (Id := Id_STT) (Compose := @Compose_STT).
apply assoc_STT.
apply id_1_STT.
apply id_2_STT.
Defined.

Lemma conj_1 :  forall A B : Fm, Pf (Imp (Cnj A B) A).
Proof.
intros.
apply lam.
intros.
apply hyp in H.
apply ande with (C:=A) in H.
auto.
intros.
apply hyp in H0.
auto.
Show Proof.
Defined.

Lemma conj_2 :  forall A B : Fm, Pf (Imp (Cnj A B) B).
Proof.
intros.
apply lam.
intros.
apply hyp in H.
apply ande with (C:=B) in H.
auto.
intros.
apply hyp in H1.
auto.
Show Proof.
Defined.

Lemma conj_3 : forall A B C : Fm, Pf (Imp C A) -> Pf (Imp C B) -> Pf (Imp C (Cnj A B)).
Proof.
intros.
apply lam.
intros.
apply andi.
apply app with (A:=C) in H.
auto.
apply hyp in H1.
auto.
apply app with (A:=C) in H0.
auto.
apply hyp in H1.
auto.
Show Proof.
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
  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y)
}.

Lemma tru_1 : forall A : Fm, Pf (Imp A Tru).
Proof.
intros.
apply lam.
intros.
apply hyp in H.
apply tt.
Defined.


Lemma imp_1 : forall B C : Fm, Pf (Imp (Cnj (Imp B C) B) C).
Proof.
intros.
apply lam.
intros.
apply hyp in H.
apply ande with (A:=Imp B C) (B:=B) (C:= C) in H.
auto.
intros.
apply hyp in H0.
apply hyp in H1.
apply app with (A:=B) (B:=C).
all: auto.
Defined.

Lemma imp_2 : forall A B C : Fm,
Pf (Imp (Cnj A B) C) -> Pf (Imp A (Imp B C)).
Proof.
intros.
apply lam.
intros.
apply hyp in H0.
apply lam.
intros.
apply hyp in H1.
apply app with (A:= Cnj A B ) (B:=C).
auto.
apply andi.
all: auto.
Defined.


Instance STT_is_a_CCC : CartClosedCat STT_as_a_Cat. 
Proof.
apply CartClosedCat_mk with (Top_obj := Tru) (Prod_obj := Cnj) (Exp_obj := (fun A B => Imp B A)).
apply tru_1.
intros.
apply conj_3 with (C:=x) (A:=y) (B:=z).
all: auto.
intros.
apply conj_1 with (A:=x) (B:=y).
intros.
apply conj_2 with (A:=x) (B:=y).
apply imp_1.
apply imp_2.
Defined.

(* Context {C : Category}.

Context {CCC : CartClosedCat C}. *)

Structure VAL {C : Category} {CCC : CartClosedCat C} : Type := makeVAL 
  { V :> Fm -> Obj;
    VAL_top : V Tru = Top_obj;
    VAL_imp : forall {A B}, V (Imp A B) = Exp_obj (V B) (V A);
    VAL_cnj : forall {A B}, V (Cnj A B) = Prod_obj (V A) (V B);
  }.

Theorem Soundness {C : Category} {CCC : CartClosedCat C} {v : VAL} : forall A B, (Pf A -> Pf B) -> Hom (v A) (v B).
Proof.
intros.
induction H.
rewrite VAL_top.
apply Top_mor.
rewrite VAL_imp.











