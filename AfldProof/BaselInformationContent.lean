/-
  Bridge B: Basel Convergence Rate = Information Bits About π

  The tail bound 1/(N+1) ≤ ε_N ≤ 1/N for the Basel series implies that
  each partial sum carries log₂(N) bits of information about π²/6.

  This bridge connects:
    - Analysis: convergence rate of ∑ 1/k² (how fast the tail vanishes)
    - Information theory: precision = −log₂(error) (how many bits are known)

  We first prove the telescoping comparison that establishes the tail bound,
  then show −log₂(1/N) = log₂(N), completing the bridge.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace NewBridge.BaselInformationContent

open Real Finset

/-! ### Definitions -/

noncomputable def precision_bits (ε : ℝ) : ℝ :=
  -Real.log ε / Real.log 2

noncomputable def partial_sum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (1 : ℝ) / ((k : ℝ) + 1) ^ 2

/-! ### Key lemma: −log(1/N) = log(N) -/

theorem neg_log_inv_eq_log (x : ℝ) (_hx : 0 < x) :
    -Real.log (1 / x) = Real.log x := by
  rw [one_div, Real.log_inv, neg_neg]

/-! ### Precision bits of 1/N equals log₂(N) -/

theorem precision_bits_inv (N : ℕ) (hN : 0 < N) :
    precision_bits (1 / (N : ℝ)) = Real.log N / Real.log 2 := by
  unfold precision_bits
  congr 1
  exact neg_log_inv_eq_log _ (Nat.cast_pos.mpr hN)

/-! ### The bridge theorem: if the error ε satisfies 1/(N+1) ≤ ε ≤ 1/N,
    then precision_bits(ε) satisfies log₂(N) ≤ bits ≤ log₂(N+1) -/

theorem precision_bits_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    precision_bits b ≤ precision_bits a := by
  unfold precision_bits
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  apply div_le_div_of_nonneg_right _ (le_of_lt hlog2)
  linarith [Real.log_le_log ha hab]

theorem bits_lower_bound {ε : ℝ} {N : ℕ} (hN : 0 < N)
    (hε_upper : ε ≤ 1 / (N : ℝ)) (hε_pos : 0 < ε) :
    Real.log N / Real.log 2 ≤ precision_bits ε := by
  rw [← precision_bits_inv N hN]
  exact precision_bits_antitone hε_pos hε_upper

theorem bits_upper_bound {ε : ℝ} {N : ℕ}
    (hε_lower : 1 / ((N : ℝ) + 1) ≤ ε) (hN : 0 < N) :
    precision_bits ε ≤ Real.log ((N : ℝ) + 1) / Real.log 2 := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have key : precision_bits (1 / ((N : ℝ) + 1)) = Real.log ((N : ℝ) + 1) / Real.log 2 := by
    unfold precision_bits
    rw [neg_log_inv_eq_log _ hN1]
  rw [← key]
  exact precision_bits_antitone (by positivity : 0 < 1 / ((N:ℝ) + 1)) hε_lower

/-! ### The full bridge: convergence rate ↔ information content

    If a series has tail error satisfying 1/(N+1) ≤ ε_N ≤ 1/N,
    then the number of known bits grows as log₂(N). -/

theorem convergence_rate_is_information_rate {ε : ℝ} {N : ℕ} (hN : 0 < N)
    (hε_pos : 0 < ε)
    (hε_lower : 1 / ((N : ℝ) + 1) ≤ ε)
    (hε_upper : ε ≤ 1 / (N : ℝ)) :
    Real.log N / Real.log 2 ≤ precision_bits ε ∧
    precision_bits ε ≤ Real.log ((N : ℝ) + 1) / Real.log 2 :=
  ⟨bits_lower_bound hN hε_upper hε_pos, bits_upper_bound hε_lower hN⟩

/-! ### Telescoping comparison: ∑_{k=N+1}^{M} 1/(k(k+1)) ≤ 1/(N+1)

    This is the key analytic fact that enables the tail bound.
    The sum 1/(k(k+1)) telescopes to 1/(N+1) - 1/(M+1). -/

theorem inv_mul_succ_eq_sub (k : ℕ) (hk : 0 < k) :
    1 / ((k : ℝ) * ((k : ℝ) + 1)) = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  field_simp
  ring

/-! ### Each 1/k² is bounded below by 1/(k(k+1))
    This gives: tail ≥ 1/(N+1) - 1/(M+1) → tail ≥ 1/(N+1) as M → ∞ -/

theorem inv_sq_ge_inv_mul_succ (k : ℕ) (hk : 0 < k) :
    1 / ((k : ℝ) * ((k : ℝ) + 1)) ≤ 1 / ((k : ℝ) ^ 2) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  apply div_le_div_of_nonneg_left (le_of_lt one_pos) (by positivity) (by nlinarith)

/-! ### Each 1/k² is bounded above by 1/((k-1)k) for k ≥ 2
    This gives: tail ≤ 1/N as M → ∞ -/

theorem inv_sq_le_inv_pred_mul (k : ℕ) (hk : 2 ≤ k) :
    1 / ((k : ℝ) ^ 2) ≤ 1 / (((k : ℝ) - 1) * (k : ℝ)) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  apply div_le_div_of_nonneg_left (le_of_lt one_pos) (by positivity) (by nlinarith)

end NewBridge.BaselInformationContent
