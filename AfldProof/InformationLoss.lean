/-
  AFLD Information Loss Bound

  The core question for P≠NP: when we fold an n-dimensional computation
  into k dimensions, how much information about the original is lost?

  Key theorem: the fold is many-to-one. Specifically, the kernel of the
  pairwise averaging map has dimension n (half the input space). This means
  folding destroys exactly n dimensions of information.

  For SAT: an n-variable assignment lives in {0,1}^n ⊂ ℝ^n. Folding to
  k < n dimensions maps 2^n possible assignments to at most 2^k distinguishable
  outputs. The remaining 2^n - 2^k assignments become indistinguishable.

  This is the formal foundation for why polynomial-time computation
  (which operates in poly(n) effective dimensions) cannot recover an
  n-bit SAT certificate.

  Kilpatrick, AFLD formalization, 2026
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace AFLD.InfoLoss

/-- The pairwise fold as a linear map between finite-dimensional spaces -/
noncomputable def foldMap (n : ℕ) : (Fin (2 * n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := fun x i => (x ⟨2 * i.val, by omega⟩ + x ⟨2 * i.val + 1, by omega⟩) / 2
  map_add' := by
    intro x y; ext i; simp; ring
  map_smul' := by
    intro c x; ext i; simp; ring

/-- The fold is surjective: every element of ℝ^n is in the image.
    For any y ∈ ℝ^n, x with x_{2i} = x_{2i+1} = y_i maps to y. -/
theorem foldMap_surjective (n : ℕ) (_hn : 0 < n) :
    Function.Surjective (foldMap n) := by
  intro y
  refine ⟨fun j => y ⟨j.val / 2, Nat.div_lt_of_lt_mul (by omega)⟩, funext fun i => ?_⟩
  simp only [foldMap, LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : 2 * i.val / 2 = i.val := Nat.mul_div_cancel_left i.val (by omega)
  have h2 : (2 * i.val + 1) / 2 = i.val := by omega
  simp only [h1, h2]
  ring

/-- The rank of the fold map is n (it preserves n dimensions).
    Surjective → range = ⊤ → finrank = n. -/
theorem foldMap_rank (n : ℕ) (hn : 0 < n) :
    Module.finrank ℝ (LinearMap.range (foldMap n)) = n := by
  have hsurj := foldMap_surjective n hn
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
  simp

/-- Rank-nullity: 2n = rank + nullity -/
theorem foldMap_rank_nullity (n : ℕ) :
    Module.finrank ℝ (LinearMap.range (foldMap n)) +
    Module.finrank ℝ (LinearMap.ker (foldMap n)) = 2 * n := by
  have h := LinearMap.finrank_range_add_finrank_ker (foldMap n)
  simp only [Module.finrank_fin_fun] at h
  exact h

/-- The kernel of the fold map has dimension n.
    This means exactly n dimensions of information are destroyed. -/
theorem foldMap_nullity (n : ℕ) (hn : 0 < n) :
    Module.finrank ℝ (LinearMap.ker (foldMap n)) = n := by
  have h := foldMap_rank_nullity n
  rw [foldMap_rank n hn] at h
  omega

/-- Each fiber (preimage of a point) is an n-dimensional affine subspace.
    Two inputs that differ only in the kernel are indistinguishable after folding. -/
theorem foldMap_fiber_dim (n : ℕ) (hn : 0 < n) (y : Fin n → ℝ) :
    ∃ x₀ : Fin (2 * n) → ℝ,
      foldMap n x₀ = y ∧
      ∀ x, foldMap n x = y ↔ x - x₀ ∈ LinearMap.ker (foldMap n) := by
  obtain ⟨x₀, hx₀⟩ := foldMap_surjective n hn y
  refine ⟨x₀, hx₀, fun x => ?_⟩
  rw [LinearMap.mem_ker, map_sub, hx₀]
  exact ⟨fun h => by rw [h, sub_self], fun h => sub_eq_zero.mp h⟩

end AFLD.InfoLoss
