import Mathlib.Tactic.Linarith
open Nat

def sum_first_n : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sum_first_n n

#eval sum_first_n 10

-- mathlib nélkül
theorem sum_first_n_correct : forall  n : Nat,
      2 * sum_first_n n = n*(n+1) := by
  intros n
  induction n with
  | zero =>
    exact rfl
  | succ n a =>
    rw[sum_first_n]
    rw[Nat.mul_add]
    rw[a]
    rw[Nat.mul_comm]
    rw[Nat.add_comm]
    rw[Nat.mul_comm]
    rw[<-Nat.mul_add]

-- mathlibbel
theorem sum_first_n_correct2 : forall  n : Nat,
      2 * sum_first_n n = n*(n+1) := by
      intros n
      induction n with
  | zero =>
    exact rfl
  | succ n a =>
    rw [sum_first_n]
    -- rw?
    rw [Nat.left_distrib]
    rw [a]
    linarith

theorem sum_first_n_correct3 : ∀ n : Nat, 2 * sum_first_n n = n*(n+1) := by
      intros n
      induction n
      case zero => -- Opcionálisan megjelölhető, hogy melyik esettel szeretnénk foglalkozni
        rfl
      case succ n a => -- Ha szükségünk van a feltételekre, akkor szükséges az elnevezéshez
        rw [sum_first_n,Nat.left_distrib,a]
        linarith
