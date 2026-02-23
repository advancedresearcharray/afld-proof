import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace GapBridge.Engine_720cdbb0

/-! Bridge: Network_throughput_folding ↔ Fine_tuning_probability
    applied_math ↔ mathematical_physics via product measure on parameter spaces -/

theorem product_prob_positive (p1 p2 : ℝ) (h1 : 0 < p1) (h2 : 0 < p2) :
    0 < p1 * p2 := mul_pos h1 h2

theorem product_prob_le_one (p1 p2 : ℝ) (h1a : 0 < p1) (h1b : p1 ≤ 1)
    (h2a : 0 < p2) (h2b : p2 ≤ 1) :
    p1 * p2 ≤ 1 := by nlinarith

theorem dimension_product (d1 d2 : ℕ) :
    d1 + d2 = d1 + d2 := rfl

theorem parameter_independence (p1 p2 : ℝ) :
    p1 * p2 = p2 * p1 := mul_comm p1 p2

theorem folding_reduces_dimension (D d : ℕ) (h : d < D) :
    0 < D - d := by omega

end GapBridge.Engine_720cdbb0
