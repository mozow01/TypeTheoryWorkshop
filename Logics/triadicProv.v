Require Import List.
Import ListNotations.

Inductive Typ : Set :=
  | At : nat -> Typ
  | Top : Typ
  | Imp : Typ -> Typ -> Typ
  | Cnj : Typ -> Typ -> Typ
  | Dis : Typ -> Typ -> Typ.

Inductive Trm : Set :=
  | top : Trm
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm
  | cnj : Trm -> Trm -> Trm
  | proj_1 : Trm -> Trm
  | proj_2 : Trm -> Trm
  | dis : Trm -> Trm -> Trm -> Trm
  | in_1 : Typ -> Trm -> Trm
  | in_2 : Typ -> Trm -> Trm.

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
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_2 t) B
  | STT_dis :
      forall Γ t s r A B C,
      Tyty Γ t (Dis A B) -> Tyty (A :: Γ) s C -> Tyty (B :: Γ) r C -> Tyty Γ (dis t s r) C
  | STT_in1 :
      forall Γ t A B,
      Tyty Γ t A -> Tyty Γ (in_1 B t) (Dis A B) 
  | STT_in2 :
      forall Γ t A B,
      Tyty Γ t B -> Tyty Γ (in_2 A t) (Dis A B) .

Notation "Γ '⊢' t '[:]' A" := (Tyty Γ t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

Notation "A ⊃ B" := (Imp A B) (at level 70, right associativity) :
type_scope.
