import Mathlib

open Set Filter
open Topology Filter Classical Real

noncomputable section

open Real
theorem tendsto_add_at_top : forall (f g : ℝ → ℝ),
  Tendsto f atTop atTop → Tendsto g atTop atTop → Tendsto (λ x => f x + g x) atTop atTop := by
intros f g h1 h2
--rw?
rw [@tendsto_atTop_atTop]
intros K
rewrite [@tendsto_atTop_atTop] at h1 h2
have h1b := h1 (K/2)
have h2b := h2 (K/2)
apply Exists.elim h1b
intros i1 H1
apply Exists.elim h2b
intros i2 H2
use (max i1 i2)
intros x H3
have K1 : i1 ≤ (max i1 i2) := by
  {
    exact le_max_left i1 i2
  }
have K2 : i2 ≤ (max i1 i2) := by
  {
    exact le_max_right i1 i2
  }
have K11 : i1 ≤ x := by
  {
    exact Preorder.le_trans i1 (max i1 i2) x K1 H3
  }
have K21 : i2 ≤ x := by
  {
    exact Preorder.le_trans i2 (max i1 i2) x K2 H3
  }
have M1 : (K/2) + (K/2) ≤ f x + g x := by
  {
    exact add_le_add (H1 x K11) (H2 x K21)
  }
have M2 : (K/2) + (K/2) = K := by
  {
    rw [@add_halves']
  }
exact le_of_eq_of_le (id (Eq.symm M2)) M1
