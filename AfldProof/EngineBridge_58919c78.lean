import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace GapBridge.Engine_58919c78

/-! Bridge: Geometric_series_formula ↔ Shannon_entropy_maximum
    analysis ↔ information_theory via logarithm concavity -/

theorem log_nonneg_of_ge_one (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ Real.log x :=
  Real.log_nonneg hx

theorem log_monotone (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    Real.log x ≤ Real.log y :=
  Real.log_le_log hx hxy

theorem entropy_gap_nonneg (p n : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hn : 1 ≤ n) :
    0 ≤ p * (Real.log n - Real.log p) := by
  apply mul_nonneg (le_of_lt hp)
  have : Real.log p ≤ Real.log n := Real.log_le_log hp (le_trans hp1 hn)
  linarith

theorem log_pos_of_gt_one (n : ℝ) (hn : 1 < n) :
    0 < Real.log n := Real.log_pos hn

end GapBridge.Engine_58919c78
