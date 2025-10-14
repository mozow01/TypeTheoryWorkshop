import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
open CategoryTheory

class SttSogat (Fm : Type) where
  Pf : Fm → Type

  -- Operations (type-formers)
  Tru : Fm
  Imp : Fm → Fm → Fm
  Cnj : Fm → Fm → Fm

  -- More operations (constructors and destructors)
  tru : Pf Tru
  lam : ∀ A B, (Pf A → Pf B) → Pf (Imp A B)
  app : ∀ A B, Pf (Imp A B) → Pf A → Pf B
  pr1 : ∀ A B, Pf (Cnj A B) → Pf A
  pr2 : ∀ A B, Pf (Cnj A B) → Pf B
  cnj : ∀ A B, Pf A → Pf B → Pf (Cnj A B)

  -- Equalities
  tru_uniq  : ∀ (p : Pf Tru), p = tru
  beta      : ∀ A B (F : Pf A → Pf B) p, app A B (lam A B F) p = F p
  eta       : ∀ A B f, lam A B (app A B f) = f
  beta_cnj1 : ∀ A B p q, pr1 A B (cnj A B p q) = p
  beta_cnj2 : ∀ A B p q, pr2 A B (cnj A B p q) = q
  eta_cnj   : ∀ A B c, cnj A B (pr1 A B c) (pr2 A B c) = c

namespace SttSogat

notation "⊤" => SttSogat.Tru
infixr:30 " ∧ " => SttSogat.Cnj
infixr:30 " ⇒ " => SttSogat.Imp
notation "Pf" => SttSogat.Pf

open SttSogat

instance SttSogatAsCat (S : Type) [SttSogat S] : Category S where
  Hom A B := Pf (Imp A B)
  id A := lam A A id
  comp {A B C} f g := (lam A C (fun (pA : Pf A) =>
    app B C g (app A B f pA)))
  comp_id {A B} f := by
    simp [beta, eta]
  id_comp {A B} f := by
    simp [beta, eta]
  assoc {W X Y Z} f g h := by
    simp [beta, eta]

def ImpLeftConj (S : Type) [SttSogat S] : forall (A X Y : S), Pf (Imp X Y) -> Pf ((A ∧ X) ⇒ (A ∧ Y)) := by
  intros A X Y h
  apply lam
  intros k
  apply cnj
  apply pr1 A X
  exact k;
  apply app X Y h
  apply pr2 A X
  exact k

end SttSogat
