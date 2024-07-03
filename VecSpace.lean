import Mathlib

-- The field (usually ℝ or ℂ)
variable (k : Type) [Field k]

-- Vector spaces
variable (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
-- Vector space axioms
section
  variable (a b : k) (v w : V)

  example : a • (v + w) = a • v + a • w :=
    smul_add a v w

  example : (a + b) • v = a • v + b • v :=
  add_smul a b v

  example : (1 : k) • v = v :=
  one_smul k v

  example : a • b • v = (a * b) • v :=
  smul_smul a b v
end

-- Subspaces
section
  variable (X Y : Subspace k V)

  example : Prop := X ≤ Y

  example : Subspace k V := X ⊓ Y
  example : Subspace k V := X ⊔ Y
  example : Subspace k V := ⊥
  example : Subspace k V := ⊤

  example (_ : X = ⊤) : Prop := ↑X = V

  example (v : V) : Prop := v ∈ X
end


-- Linear maps
section
  open FiniteDimensional
  variable (a : k)
  variable (W : Type) [AddCommGroup W] [Module k W] [FiniteDimensional k V]

  variable (φ : V →ₗ[k] W)


  -- Axioms
  example : φ (a • v) = a • φ v :=
  φ.map_smul a v

  example : φ (v + w) = φ v + φ w :=
  φ.map_add v w

  example (A B : Subspace k V) (hV : finrank k V = 9) (hA : finrank k A = 5) (hB : finrank k B = 5) :
      A ⊓ B ≠ ⊥ := by
    intro h
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hA, hB, h, finrank_bot k V] at h1
    norm_num at h1
    have h2 := Submodule.finrank_le (A ⊔ B)
    rw [h1, hV] at h2
    linarith


end
