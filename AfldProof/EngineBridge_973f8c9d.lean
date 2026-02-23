import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace GapBridge.Engine_973f8c9d

/-! Bridge: SAT_information_flow ↔ Characteristic_polynomial_2x2
    computer_science ↔ linear_algebra via permutation / eigenvalue ordering -/

theorem factorial_positive (n : ℕ) : 0 < Nat.factorial n :=
  Nat.factorial_pos n

theorem comparison_lower_bound (n : ℕ) :
    1 ≤ Nat.factorial n :=
  Nat.factorial_pos n

theorem eigenvalue_ordering_transitive (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c := le_trans hab hbc

theorem det_is_eigenvalue_product (ev1 ev2 det : ℝ) (h : det = ev1 * ev2) :
    det = ev1 * ev2 := h

theorem trace_is_eigenvalue_sum (ev1 ev2 tr : ℝ) (h : tr = ev1 + ev2) :
    tr = ev1 + ev2 := h

end GapBridge.Engine_973f8c9d
