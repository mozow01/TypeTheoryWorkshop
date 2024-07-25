
import Mathlib

open Nat

theorem log2_3_irrational : ¬ ∃ (p q : ℕ), q ≠ 0 ∧ (2 ^ p = 3 ^ q) := by
    refine Not.intro ?h
    intros H1
    apply Exists.elim H1
    intro p H2
    apply Exists.elim H2
    intros q K1
    apply And.elim at K1
    exact K1
    intros K1 K2
    have three_div_3q : 3 ∣ 3 ^ q := by
      exact dvd_pow_self 3 K1
    have three_div_2p : 3 ∣ 2 ^ p := by
      rw [K2]
      exact three_div_3q
    have three_not_div_two : ¬ (3 ∣ 2) := by
      norm_num
    have three_prime : (Nat.Prime 3) := by
      exact prime_three
    have three_div_2p : 3 ∣ 2 := by
      apply Prime.dvd_of_dvd_pow
      exact prime_iff.mp three_prime
      exact three_div_2p
    contradiction
