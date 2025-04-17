import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.CharP.Lemmas


open Int
open Finset

theorem pow_prime_eq_self_mod_p_of_pos (p : ℕ) (a : ℤ) (hp_prime : Nat.Prime p) (h_pos : 0 ≤ a) : a^p ≡ a [ZMOD p] := by
-- Step 1.1: Prove a^p ≡ a [ZMOD p] for a ≥ 0 by induction
    let a' := a.toNat
    have haa'_eq : a' = a :=
      Int.toNat_of_nonneg h_pos
    rw [← haa'_eq]
    induction' a' with a' ih
      -- Step 1.1.1: Prove 0^p ≡ 0 [ZMOD p]
    · apply modEq_iff_dvd.mpr
      use 0
      norm_num
      exact Nat.Prime.ne_zero hp_prime
      -- Step 1.1.2: Prove (a + 1)^p ≡ a + 1 [ZMOD p] given a^p ≡ a [ZMOD p] for some a ≥ 0
    · apply modEq_iff_dvd.mpr
      simp
      rw[← pow_one p]
      rw [Commute.add_pow_prime_pow_eq hp_prime (Nat.cast_commute a' 1) 1]
      group
      apply modEq_iff_dvd.mp at ih
      obtain ⟨k, hk⟩ := ih
      use k + (-∑ x ∈ Ioo 0 p, a' ^ x * (p.choose x / p))
      group
      rw[← hk]
      simp
      ring


theorem fermat_little {p : ℕ} {a : ℤ} (hp_prime : Nat.Prime p) (hap_coprime : Int.gcd p a = 1) :
  a^(p - 1) ≡ 1 [ZMOD p] := by

  -- Step 1: Prove a^p ≡ a [ZMOD p] for a < 0
  have (h_neg : ¬ 0 ≤ a) : a^p ≡ a [ZMOD p] := by
    by_cases hp2 : p = 2
      -- Step 1.2.1: Prove a^p ≡ a [ZMOD p] for a < 0 and p = 2
    · rw [hp2, ← neg_pow_two a]
      have a_mod_two: -a ≡ a [ZMOD 2] := by
        apply modEq_iff_dvd.mpr
        use a; group
      refine' ModEq.trans (pow_prime_eq_self_mod_p_of_pos 2 (-a) ?_ ?_) a_mod_two
      · exact Nat.prime_two
      apply lt_of_not_le at h_neg
      norm_num
      exact Int.le_of_lt h_neg
      -- Step 1.2.2: Prove a^p ≡ a [ZMOD p] for a < 0 and p > 2
    · apply neg_modEq_neg.mp
      have : - a ^ p = (-a)^p := by
        refine Eq.symm (Odd.neg_pow ?_ a)
        exact Nat.Prime.odd_of_ne_two hp_prime hp2
      rw[this]
      refine' pow_prime_eq_self_mod_p_of_pos p (-a) hp_prime ?_
      apply lt_of_not_le at h_neg
      norm_num
      exact Int.le_of_lt h_neg

  -- Step 2: Now use a^p ≡ a [ZMOD p] to prove a^(p - 1) ≡ 1 [ZMOD p]
  -- Step 2.1: Prove p ∣ a * (a^(p - 1) - 1)
  have : (p : ℤ) ∣ a * (a^(p - 1) - 1) := by
    rw [mul_sub_left_distrib]
    rw [mul_one]
    rw [mul_comm]
    rw [← pow_succ a (p - 1)]
    have hp_ge_one : 1 ≤ p := by
      exact Nat.Prime.one_le hp_prime
    rw [Nat.sub_add_cancel hp_ge_one]
    rw [← Int.modEq_iff_dvd]
    apply Int.ModEq.symm
    by_cases ha_sign : 0 ≤ a
    · exact pow_prime_eq_self_mod_p_of_pos p a hp_prime ha_sign
    exact this ha_sign
  -- Step 2.2: Prove that either p ∣ a or p ∣ (a^(p - 1) - 1)
  have h_disj: (p : ℤ) ∣ a ∨ (p : ℤ) ∣ (a^(p - 1) - 1) := by
    rw [← Prime.dvd_mul]
    apply this
    exact prime_ofNat_iff.mpr hp_prime
  -- Step 2.3: Prove that we cannot have p ∣ a
  have : ¬ (p : ℤ) ∣ a := by
    by_contra h
    have : Int.gcd p a = p := by
      apply Int.gcd_eq_left h
    rw [hap_coprime] at this
    rw [eq_comm] at this
    apply Nat.Prime.ne_one hp_prime
    apply this
  -- Step 2.4: Prove that we must have p ∣ (a^(p - 1) - 1)
  have : (p : ℤ) ∣ (a^(p - 1) - 1) := by
    cases h_disj with
    | inl h₁ => contradiction
    | inr h₂ => exact h₂
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  exact this
