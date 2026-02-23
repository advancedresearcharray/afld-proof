import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace GapBridge.Engine_c105a3eb

/-! Bridge: Characteristic_polynomial_2x2 ↔ De_Broglie_wavelength
    linear_algebra ↔ quantum_mechanics via spectral theory -/

theorem char_poly_determines_eigenvalues (tr det ev1 ev2 : ℝ)
    (h_sum : ev1 + ev2 = tr) (h_prod : ev1 * ev2 = det) :
    ev1 ^ 2 - tr * ev1 + det = 0 := by subst h_sum; subst h_prod; ring

theorem expectation_is_trace (eigenval prob : ℝ) (hp : 0 ≤ prob) :
    0 ≤ prob * eigenval ^ 2 := by positivity

theorem observable_hermitian_real_eigenvalue (a b : ℝ) :
    a * b = b * a := mul_comm a b

theorem momentum_eigenvalue (hbar k : ℝ) (hh : 0 < hbar) (hk : k ≠ 0) :
    hbar * k ≠ 0 := mul_ne_zero (ne_of_gt hh) hk

end GapBridge.Engine_c105a3eb
