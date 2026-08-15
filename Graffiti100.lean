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
  all_goals norm_num [Nat.ceilDiv_eq_add_pred_div] at *
  all_goals ring_nf
  all_goals nlinarith [sq_nonneg (t : ℝ)]

#check SimpleGraph.exists_isNIndepSet_indepNum
#check SimpleGraph.IsNIndepSet.isIndepSet
#check SimpleGraph.IsNIndepSet.card_eq
#check SimpleGraph.IsIndepSet.card_le_indepNum
#check SimpleGraph.isIndepSet_induce
#check SimpleGraph.isNIndepSet_induce
#check Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
#check Finset.card_filter_add_card_filter_not
#check Finset.card_union_of_disjoint
#check Finset.card_erase_of_mem
#check Finset.card_le_card
#check Finset.sum_union
#check Finset.disjoint_compl_right
#check Finset.card_eq_sum_ones
#check Finset.le_max'
#check SimpleGraph.mem_neighborFinset
#check SimpleGraph.card_neighborFinset_eq_degree
#check SimpleGraph.mem_support
#check SimpleGraph.Preconnected.support_eq_univ
#check SimpleGraph.Preconnected.degree_pos_of_nontrivial
#check sq_sum_le_card_mul_sum_sq
#check Real.sq_sqrt
#check Int.lt_ceil
#check Int.le_ceil

end Graffiti100
