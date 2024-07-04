import Mathlib

theorem problem_mod : ∀ n : ℕ , 7^(2*n+1) + 3^(2*n+1) ≡ 0 [MOD 10] := by

  intros n
  rw [Nat.pow_add']
  rw [Nat.pow_mul]
  rw [Nat.add_comm]
  rw [Nat.pow_add']
  rw [Nat.pow_mul]
  norm_num

  have H1 : (49^n ≡ 9^n [MOD 10]) := Nat.ModEq.pow n rfl

  have H2 : 7 * 49 ^ n + 3 * 49^n ≡ 0 [MOD 10] := by
    rw [← Nat.right_distrib]
    norm_num
    rw [@Nat.modEq_zero_iff_dvd]
    exact Nat.dvd_mul_right 10 (49 ^ n)

  have H3 : 7 * 49 ^ n + 3 * 9 ^ n ≡ 7 * 49 ^ n + 3 * 49^n [MOD 10] := by
    refine Nat.ModEq.add_left (7 * 49 ^ n) ?h
    exact Nat.ModEq.mul rfl (id (Nat.ModEq.symm H1))

  have H4 : 3 * 9 ^ n + 7 * 49 ^ n ≡ 7 * 49 ^ n + 3 * 9 ^ n [MOD 10] := by
     rw [Nat.add_comm]

  apply Nat.ModEq.trans
  exact H4
  exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm H2)) (id (Nat.ModEq.symm H3)))
