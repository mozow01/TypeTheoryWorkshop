import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Set.Disjoint
import Mathlib.Tactic


class KolmogorovFiniteAxioms {α : Type u_1} [MeasurableSpace α] (P : Set α → ℝ) : Prop where
  axiom1_non_neg : ∀ (A : Set α), MeasurableSet A → P A ≥ 0
  axiom2_prob_univ : P Set.univ = 1
  axiom3_finite_add : ∀ (A B : Set α),
                      MeasurableSet A →
                      MeasurableSet B →
                      Disjoint A B →
                      P (A ∪ B) = P A + P B

theorem prob_empty {α : Type u_1} (M : MeasurableSpace α) (P : Set α → ℝ) (K:KolmogorovFiniteAxioms P) :
  P ∅ = 0 := by
   have h_add : P (Set.univ ∪ ∅) = P Set.univ + P ∅ := by
    apply K.axiom3_finite_add
    exact MeasurableSet.univ
    exact MeasurableSet.empty
    apply Set.disjoint_empty Set.univ
   rw [Set.union_empty] at h_add
   rw [K.axiom2_prob_univ] at h_add
   linarith [h_add]
