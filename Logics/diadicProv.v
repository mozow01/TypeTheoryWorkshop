Require Import List.
Import ListNotations.

Inductive Fm : Set :=
  | At : nat -> Fm
  | Top : Fm
  | Imp : Fm -> Fm -> Fm
  | Cnj : Fm -> Fm -> Fm
  | Dis : Fm -> Fm -> Fm.

Definition Cntxt := list Fm.

Inductive Pr : Cntxt -> Fm -> Prop :=
  | STT_top : forall Γ, Pr Γ Top
  | STT_hypO : forall Γ A, Pr (A :: Γ) A
  | STT_hypS :
      forall Γ A B,
      Pr Γ  A -> Pr (B :: Γ) A
  | STT_lam :
      forall Γ A B,
      Pr (A :: Γ) B -> Pr Γ (Imp A B)
  | STT_app :
      forall Γ A B,
      Pr Γ (Imp A B) -> Pr Γ A -> Pr Γ B
  | STT_cnj :
      forall Γ A B,
      Pr Γ A -> Pr Γ B -> Pr Γ (Cnj A B)
  | STT_proj1 :
      forall Γ A B,
      Pr Γ (Cnj A B) -> Pr Γ A
  | STT_proj2 :
      forall Γ A B,
      Pr Γ (Cnj A B) -> Pr Γ B
  | STT_dis :
      forall Γ A B C,
       Pr Γ (Cnj A B) -> Pr (A :: Γ) C -> Pr (B :: Γ) C -> Pr Γ C
  | STT_in1 :
      forall Γ A B,
       Pr Γ A -> Pr Γ (Dis A B)
  | STT_in2 :
      forall Γ A B,
       Pr Γ B -> Pr Γ (Dis A B).

Notation "Γ '⊢' t '[:]' A" := (Pr Γ t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Pr nil t A) (at level 70, no associativity) : type_scope.

Notation "A ⊃ B" := (Imp A B) (at level 70, right associativity) :
type_scope.

Example Currying : forall (A B C : Fm) Γ, Pr Γ (Imp A (Imp B C)) -> Pr Γ (Imp (Cnj A B) C).
Proof.
intros.
apply STT_lam.
Abort.

