import Mathlib

open scoped BigOperators

namespace Graffiti100

lemma small_arithmetic
    {a L m : ℕ}
    (ha2 : 2 ≤ a) (ha16 : a < 16)
    (hLpos : 1 ≤ L) (hLa : L ≤ a)
    (hamL : a ≤ m * L) :
    (a : ℝ) * (4 * (a : ℝ) - 4 - 2 * (L : ℝ)) ^ 2 ≤
      ((a * (a - 1) + m * (a - L) : ℕ) : ℝ) ^ 2 := by
  have hL0 : 0 < L := by omega
  have hm : a ⌈/⌉ L ≤ m := by
    rw [ceilDiv_le_iff_le_mul hL0]
    simpa [mul_comm] using hamL
  interval_cases a <;> interval_cases L
  all_goals
    have hmR : ((a ⌈/⌉ L : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    norm_num [Nat.ceilDiv_eq_add_pred_div] at hmR ⊢
    nlinarith [sq_nonneg ((m : ℝ) - 1), sq_nonneg ((m : ℝ) - 2),
      sq_nonneg ((m : ℝ) - 3), sq_nonneg ((m : ℝ) - 4),
      sq_nonneg ((m : ℝ) - 5), sq_nonneg ((m : ℝ) - 6),
      sq_nonneg ((m : ℝ) - 7), sq_nonneg ((m : ℝ) - 8),
      sq_nonneg ((m : ℝ) - 9), sq_nonneg ((m : ℝ) - 10),
      sq_nonneg ((m : ℝ) - 11), sq_nonneg ((m : ℝ) - 12),
      sq_nonneg ((m : ℝ) - 13), sq_nonneg ((m : ℝ) - 14),
      sq_nonneg ((m : ℝ) - 15)]

end Graffiti100
