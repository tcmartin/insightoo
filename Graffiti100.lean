import Mathlib

open scoped BigOperators

namespace Graffiti100

set_option maxHeartbeats 1000000 in
lemma small_arithmetic
    {a L m : ℕ}
    (ha2 : 2 ≤ a) (ha16 : a < 16)
    (hLpos : 1 ≤ L) (hLa : L ≤ a)
    (hamL : a ≤ m * L) :
    (a : ℝ) * (4 * (a : ℝ) - 4 - 2 * (L : ℝ)) ^ 2 <
      ((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) ^ 2 +
        (a : ℝ) * (m : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2 := by
  have hL0 : 0 < L := by omega
  have hm : a ⌈/⌉ L ≤ m := by
    rw [ceilDiv_le_iff_le_mul hL0]
    simpa [mul_comm] using hamL
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  have ht : (0 : ℝ) ≤ (t : ℝ) := by positivity
  interval_cases a <;> interval_cases L
  all_goals try omega
  all_goals norm_num [Nat.ceilDiv_eq_add_pred_div] at *
  all_goals ring_nf
  all_goals nlinarith [sq_nonneg (t : ℝ)]

end Graffiti100
