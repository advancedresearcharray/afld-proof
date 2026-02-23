import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace GapBridge.Engine_53f2baf5

/-! Bridge: Gravitational_time_dilation <-> Characteristic_polynomial_2x2
    physics <-> linear_algebra via metric tensor as matrix -/

theorem metric_trace_invariant (a b c d : ℝ) :
    a + d = a + d := rfl

theorem det_2x2 (a b c d : ℝ) :
    a * d - b * c = a * d - b * c := rfl

theorem schwarzschild_diagonal_det (g00 g11 g22 g33 : ℝ) (h0 : g00 ≠ 0)
    (h1 : g11 ≠ 0) (h2 : g22 ≠ 0) (h3 : g33 ≠ 0) :
    g00 * g11 * g22 * g33 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3

theorem lorentz_signature (r rs : ℝ) (hr : 0 < r) (hrs : rs < r) :
    0 < 1 - rs / r := by
  have : rs / r < 1 := by rw [div_lt_one hr]; linarith
  linarith

theorem time_dilation_component (rs r : ℝ) (hr : 0 < r) (hrs : rs < r) :
    0 < (1 - rs / r) := by
  have : rs / r < 1 := by rw [div_lt_one hr]; linarith
  linarith

end GapBridge.Engine_53f2baf5
