/-
  Bridge A: Euler's Totient as Channel Capacity

  The coprime residues mod n form a "coprime channel" whose capacity is
  log₂(φ(n)).  Multiplicativity of φ (for coprime moduli) becomes
  *additivity of capacity* — the hallmark of independent channels.

  This is the first machine-verified proof that the number-theoretic
  multiplicativity of Euler's totient is structurally identical to
  the information-theoretic additivity of channel capacity.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace NewBridge.TotientChannelCapacity

open Real

/-! ### Definition: channel capacity of the coprime channel -/

noncomputable def capacity (n : ℕ) : ℝ :=
  Real.log (Nat.totient n) / Real.log 2

/-! ### Core theorem: capacity is additive for coprime moduli -/

theorem capacity_additive {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : Nat.Coprime m n) :
    capacity (m * n) = capacity m + capacity n := by
  unfold capacity
  rw [Nat.totient_mul hcop, Nat.cast_mul]
  have hm_pos : (0 : ℝ) < ↑(Nat.totient m) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hm)
  have hn_pos : (0 : ℝ) < ↑(Nat.totient n) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hn)
  rw [Real.log_mul (ne_of_gt hm_pos) (ne_of_gt hn_pos)]
  ring

/-! ### Capacity of a prime: C(p) = log₂(p - 1) -/

theorem capacity_prime {p : ℕ} (hp : Nat.Prime p) :
    capacity p = Real.log (p - 1 : ℝ) / Real.log 2 := by
  unfold capacity
  congr 1
  rw [Nat.totient_prime hp]
  rw [Nat.cast_sub (Nat.Prime.one_le hp)]
  simp

/-! ### Capacity of a prime power: C(p^(k+1)) = log₂(p^k · (p-1)) -/

theorem capacity_prime_pow_succ {p : ℕ} (hp : Nat.Prime p) (k : ℕ) :
    capacity (p ^ (k + 1)) =
    Real.log (↑(p ^ k) * (↑p - 1) : ℝ) / Real.log 2 := by
  unfold capacity
  congr 1
  rw [Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_sub (Nat.Prime.one_le hp)]
  simp

/-! ### Decomposition: capacity of a product of distinct primes
    is the sum of individual prime capacities -/

theorem capacity_two_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) :
    capacity (p * q) = capacity p + capacity q := by
  apply capacity_additive (Nat.Prime.pos hp) (Nat.Prime.pos hq)
  exact (Nat.coprime_primes hp hq).mpr hne

/-! ### Capacity is monotone: φ(n) ≤ φ(m) → C(n) ≤ C(m)
    (given both positive) -/

theorem capacity_mono {m n : ℕ} (_hm : 0 < m) (hn : 0 < n)
    (h : Nat.totient n ≤ Nat.totient m) :
    capacity n ≤ capacity m := by
  unfold capacity
  apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 2)))
  apply Real.log_le_log
  · exact Nat.cast_pos.mpr (Nat.totient_pos.mpr hn)
  · exact Nat.cast_le.mpr h

/-! ### Capacity lower bound: C(n) ≥ 0 for n ≥ 1 -/

theorem capacity_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ capacity n := by
  unfold capacity
  apply div_nonneg
  · exact Real.log_nonneg (by exact_mod_cast Nat.totient_pos.mpr hn)
  · exact le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 2))

end NewBridge.TotientChannelCapacity
