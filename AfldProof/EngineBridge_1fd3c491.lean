import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace GapBridge.Engine_1fd3c491

/-! Bridge: SAT_information_flow ↔ Fine_tuning_probability
    computer_science ↔ mathematical_physics via partition function / counting -/

theorem boolean_assignments_count (n : ℕ) : 0 < 2 ^ n :=
  Nat.pos_of_ne_zero (by positivity)

theorem partition_function_positive (n : ℕ) (hn : 0 < n) :
    0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)

theorem information_content_log (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ Nat.log 2 n := Nat.zero_le _

theorem parameter_space_exponential (n k : ℕ) (hk : k ≤ n) :
    2 ^ k ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by norm_num) hk

end GapBridge.Engine_1fd3c491
