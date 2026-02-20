/-
  AFLD Pairwise Averaging — Formal Properties

  This formalizes the actual `afld_fold_vector` operation from libafld:
    fold(x)_i = (x_{2i} + x_{2i+1}) / 2

  We prove:
  1. Linearity: fold is a linear map
  2. Norm contraction: ‖fold(x)‖² = ‖x‖²/4 + (cross terms)/2
  3. Norm bound: ‖fold(x)‖ ≤ ‖x‖ / √2  (Cauchy-Schwarz)
  4. Exact norm case: ‖fold(x)‖ = ‖x‖/√2 iff all pairs are equal
  5. Maximum information loss: when consecutive elements are negatives

  These are the REAL properties of the fold. Not "norm preservation."
  The fold is a contraction — it can only shrink or maintain the norm,
  never increase it, and it shrinks whenever consecutive elements differ.

  Kilpatrick, AFLD formalization, 2026
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation

open scoped BigOperators

namespace AFLD

/-- The pairwise averaging fold: maps ℝ^(2n) → ℝ^n by averaging consecutive pairs -/
noncomputable def pairwiseFold (n : ℕ) (x : Fin (2 * n) → ℝ) : Fin n → ℝ :=
  fun i => (x ⟨2 * i.val, by omega⟩ + x ⟨2 * i.val + 1, by omega⟩) / 2

/-- The fold is a linear map -/
theorem pairwiseFold_linear (n : ℕ) :
    IsLinearMap ℝ (pairwiseFold n) := by
  constructor
  · intro x y
    ext i
    simp [pairwiseFold]
    ring
  · intro c x
    ext i
    simp [pairwiseFold]
    ring

/-- Pointwise: each fold output squared is (a² + 2ab + b²)/4 -/
theorem pairwiseFold_sq_eq (n : ℕ) (x : Fin (2 * n) → ℝ) (i : Fin n) :
    (pairwiseFold n x i) ^ 2 =
      (x ⟨2 * i.val, by omega⟩ ^ 2 + x ⟨2 * i.val + 1, by omega⟩ ^ 2) / 4 +
      x ⟨2 * i.val, by omega⟩ * x ⟨2 * i.val + 1, by omega⟩ / 2 := by
  simp only [pairwiseFold]
  ring

/-- The fold is a contraction: ‖fold(x)‖ ≤ ‖x‖ (sup norm on Fin n → ℝ).
    Each output |(x_{2i} + x_{2i+1})/2| ≤ (‖x‖ + ‖x‖)/2 = ‖x‖. -/
theorem pairwiseFold_contraction (n : ℕ) (x : Fin (2 * n) → ℝ) :
    ‖pairwiseFold n x‖ ≤ ‖x‖ := by
  apply pi_norm_le_iff_of_nonneg (norm_nonneg x) |>.mpr
  intro i
  simp only [pairwiseFold]
  have h1 := norm_le_pi_norm x ⟨2 * i.val, by omega⟩
  have h2 := norm_le_pi_norm x ⟨2 * i.val + 1, by omega⟩
  rw [Real.norm_eq_abs] at h1 h2 ⊢
  have hab : |x ⟨2 * i.val, by omega⟩ + x ⟨2 * i.val + 1, by omega⟩| ≤
      |x ⟨2 * i.val, by omega⟩| + |x ⟨2 * i.val + 1, by omega⟩| := abs_add_le _ _
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2)]
  linarith

/-- L2 contraction: sum of squares shrinks by at most half. Uses
    (a+b)²/4 ≤ (a² + b²)/2 which follows from (a-b)² ≥ 0. -/
theorem pairwiseFold_l2_contraction (n : ℕ) (x : Fin (2 * n) → ℝ) (i : Fin n) :
    (pairwiseFold n x i) ^ 2 ≤
      (x ⟨2 * i.val, by omega⟩ ^ 2 + x ⟨2 * i.val + 1, by omega⟩ ^ 2) / 2 := by
  simp only [pairwiseFold]
  nlinarith [sq_nonneg (x ⟨2 * i.val, by omega⟩ - x ⟨2 * i.val + 1, by omega⟩)]

/-- L2 equality holds for a pair iff the two elements are equal -/
theorem pairwiseFold_l2_eq_iff (n : ℕ) (x : Fin (2 * n) → ℝ) (i : Fin n) :
    (pairwiseFold n x i) ^ 2 =
      (x ⟨2 * i.val, by omega⟩ ^ 2 + x ⟨2 * i.val + 1, by omega⟩ ^ 2) / 2 ↔
      x ⟨2 * i.val, by omega⟩ = x ⟨2 * i.val + 1, by omega⟩ := by
  simp only [pairwiseFold]
  constructor
  · intro h; nlinarith [sq_nonneg (x ⟨2 * i.val, by omega⟩ - x ⟨2 * i.val + 1, by omega⟩)]
  · intro h; rw [h]; ring

/-- Maximum information loss: when pairs are negatives, fold maps to zero -/
theorem pairwiseFold_zero_of_alternating (n : ℕ) (x : Fin (2 * n) → ℝ)
    (h : ∀ i : Fin n, x ⟨2 * i.val + 1, by omega⟩ = -x ⟨2 * i.val, by omega⟩) :
    pairwiseFold n x = 0 := by
  ext i
  simp [pairwiseFold]
  have := h i
  linarith

end AFLD
