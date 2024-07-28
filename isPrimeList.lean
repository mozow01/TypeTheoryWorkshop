import Mathlib

open Nat

#print Nat.Prime
-- def Nat.Prime : ℕ → Prop :=
-- fun p ↦ Irreducible p

#print Irreducible
-- structure Irreducible.{u_1} : {α : Type u_1} → [inst : Monoid α] → α → Prop
-- number of parameters: 3
-- constructor:
-- Irreducible.mk : ∀ {α : Type u_1} [inst : Monoid α] {p : α},
--   ¬IsUnit p → (∀ (a b : α), p = a * b → IsUnit a ∨ IsUnit b) → Irreducible p
-- fields:
-- not_unit : ¬IsUnit p
-- isUnit_or_isUnit' : ∀ (a b : α), p = a * b → IsUnit a ∨ IsUnit b

-- map operation by function Nat.Prime on the list 0,1,2,...n.
def isPrimeList (n : ℕ) : List Bool :=
  (List.range (n + 1)).map Nat.Prime

#eval isPrimeList 6
-- [false, false, true, true, false, true, false]
