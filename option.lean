import Mathlib

def Opt (A B : Type) : Option (A → B) → (Option A → Option B) := by
  intros  x y
  apply Option.elim x
  exact none
  intros f
  apply Option.elim y
  { exact none }
  {
  intros a
  exact some (f a)
  }
