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

lemma large_arithmetic
    {a L m : ℕ}
    (ha16 : 16 ≤ a) (hLpos : 1 ≤ L) (hLa : L ≤ a) :
    (a : ℝ) * (4 * (a : ℝ) - 4 - 2 * (L : ℝ)) ^ 2 <
      ((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) ^ 2 +
        (a : ℝ) * (m : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2 := by
  have hA16 : (16 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha16
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLpos
  have hLA : (L : ℝ) ≤ (a : ℝ) := by exact_mod_cast hLa
  have hA0 : (0 : ℝ) < (a : ℝ) := by nlinarith
  have hM0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hd0 : (0 : ℝ) ≤ (a : ℝ) - (L : ℝ) := sub_nonneg.mpr hLA
  have hT0 :
      (0 : ℝ) ≤ 4 * (a : ℝ) - 4 - 2 * (L : ℝ) := by
    nlinarith
  have hminus :
      (0 : ℝ) < 4 * ((a : ℝ) - 1) -
        (4 * (a : ℝ) - 4 - 2 * (L : ℝ)) := by
    nlinarith
  have hplus :
      (0 : ℝ) < 4 * ((a : ℝ) - 1) +
        (4 * (a : ℝ) - 4 - 2 * (L : ℝ)) := by
    nlinarith
  have hfactor :
      (0 : ℝ) <
        (4 * ((a : ℝ) - 1) - (4 * (a : ℝ) - 4 - 2 * (L : ℝ))) *
          (4 * ((a : ℝ) - 1) + (4 * (a : ℝ) - 4 - 2 * (L : ℝ))) :=
    mul_pos hminus hplus
  have hsq_lt :
      (4 * (a : ℝ) - 4 - 2 * (L : ℝ)) ^ 2 <
        (4 * ((a : ℝ) - 1)) ^ 2 := by
    nlinarith
  have hmul_sq :
      (a : ℝ) * (4 * (a : ℝ) - 4 - 2 * (L : ℝ)) ^ 2 <
        (a : ℝ) * (4 * ((a : ℝ) - 1)) ^ 2 :=
    (mul_lt_mul_left hA0).2 hsq_lt
  have h16A : (16 : ℝ) * (a : ℝ) ≤ (a : ℝ) ^ 2 := by
    have hp : (0 : ℝ) ≤ (a : ℝ) * ((a : ℝ) - 16) :=
      mul_nonneg hA0.le (sub_nonneg.mpr hA16)
    nlinarith
  have hscale :
      (a : ℝ) * (4 * ((a : ℝ) - 1)) ^ 2 ≤
        ((a : ℝ) * ((a : ℝ) - 1)) ^ 2 := by
    calc
      (a : ℝ) * (4 * ((a : ℝ) - 1)) ^ 2 =
          (16 * (a : ℝ)) * ((a : ℝ) - 1) ^ 2 := by ring
      _ ≤ ((a : ℝ) ^ 2) * ((a : ℝ) - 1) ^ 2 :=
        mul_le_mul_of_nonneg_right h16A (sq_nonneg _)
      _ = ((a : ℝ) * ((a : ℝ) - 1)) ^ 2 := by ring
  have hbase0 :
      (0 : ℝ) ≤ (a : ℝ) * ((a : ℝ) - 1) := by
    positivity
  have hmd0 :
      (0 : ℝ) ≤ (m : ℝ) * ((a : ℝ) - (L : ℝ)) :=
    mul_nonneg hM0 hd0
  have hdiffprod :
      (0 : ℝ) ≤
        (((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) -
            (a : ℝ) * ((a : ℝ) - 1)) *
          (((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) +
            (a : ℝ) * ((a : ℝ) - 1)) := by
    apply mul_nonneg
    · nlinarith
    · nlinarith
  have hSsq :
      ((a : ℝ) * ((a : ℝ) - 1)) ^ 2 ≤
        ((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) ^ 2 := by
    nlinarith
  have hextra :
      (0 : ℝ) ≤ (a : ℝ) * (m : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2 := by
    positivity
  calc
    (a : ℝ) * (4 * (a : ℝ) - 4 - 2 * (L : ℝ)) ^ 2 <
        (a : ℝ) * (4 * ((a : ℝ) - 1)) ^ 2 := hmul_sq
    _ ≤ ((a : ℝ) * ((a : ℝ) - 1)) ^ 2 := hscale
    _ ≤ ((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) ^ 2 := hSsq
    _ ≤ ((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) ^ 2 +
          (a : ℝ) * (m : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2 :=
      le_add_of_nonneg_right hextra

lemma arithmetic
    {a L m : ℕ}
    (ha2 : 2 ≤ a) (hLpos : 1 ≤ L) (hLa : L ≤ a) (hamL : a ≤ m * L) :
    (a : ℝ) * (4 * (a : ℝ) - 4 - 2 * (L : ℝ)) ^ 2 <
      ((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) ^ 2 +
        (a : ℝ) * (m : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2 := by
  by_cases ha16 : a < 16
  · exact small_arithmetic ha2 ha16 hLpos hLa hamL
  · exact large_arithmetic (by omega) hLpos hLa

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
