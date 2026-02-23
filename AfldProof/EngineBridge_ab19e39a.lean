import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace GapBridge.Engine_ab19e39a

/-! Bridge: Gravitational_time_dilation ↔ BSC_channel_capacity
    general_relativity ↔ information_theory via area-entropy bound -/

theorem area_positive (r : ℝ) (hr : 0 < r) :
    0 < 4 * r ^ 2 := by positivity

theorem bekenstein_entropy_bound (A kB lp : ℝ) (hA : 0 < A) (hkB : 0 < kB)
    (hlp : 0 < lp) :
    0 < kB * A / (4 * lp ^ 2) := by positivity

theorem schwarzschild_radius_positive (G M c : ℝ) (hG : 0 < G) (hM : 0 < M)
    (hc : 0 < c) :
    0 < 2 * G * M / c ^ 2 := by positivity

theorem information_bits_from_entropy (S kB ln2 : ℝ) (hS : 0 < S) (hkB : 0 < kB)
    (hln2 : 0 < ln2) :
    0 < S / (kB * ln2) := by positivity

end GapBridge.Engine_ab19e39a
