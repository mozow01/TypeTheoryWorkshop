import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

structure MyProbabilitySpace (Ω : Type*) [MeasurableSpace Ω] where
  P : Set Ω → ℝ

  P_nonneg : forall (A : Set Ω), (MeasurableSet A) →
    P A ≥ 0

  P_add : forall (A B : Set Ω), (MeasurableSet A) → (MeasurableSet B) → (Disjoint A B) →
    P (A ∪ B) = P A + P B

  P_univ : P (@Set.univ Ω) = 1

section MyProbabilityProofs

variable {Ω : Type*} [MeasurableSpace Ω] (S : MyProbabilitySpace Ω)

open MyProbabilitySpace

theorem prob_empty : P S ∅ = 0 := by
  let P := S.P
  let P_add := S.P_add

  have h_add : P (Set.univ ∪ ∅) = P Set.univ + P ∅ := by
    apply P_add
    exact MeasurableSet.univ
    exact MeasurableSet.empty
    apply Set.disjoint_empty Set.univ
  rw [Set.union_empty Set.univ] at h_add
  exact self_eq_add_right.mp h_add
end MyProbabilityProofs
