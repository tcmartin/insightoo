import Mathlib

open SimpleGraph
open scoped BigOperators

namespace Graffiti100

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Independence number of the graph induced by the neighbors of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

/-- Euclidean norm of the degree vector. -/
noncomputable def degreeL2Norm (G : SimpleGraph α) : ℝ :=
  Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2)

lemma neighbor_filter_card_le_local
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {I : Finset α} (hI : G.IsIndepSet I) (x : α) :
    (I.filter fun i => G.Adj x i).card ≤ indepNeighborsCard G x := by
  classical
  let T : Finset α := I.filter fun i => G.Adj x i
  let e : {i // i ∈ T} ↪ G.neighborSet x :=
    ⟨fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩,
      fun a b h => Subtype.ext (congrArg Subtype.val h)⟩
  let S : Finset (G.neighborSet x) := T.attach.map e
  have hSind : (G.induce (G.neighborSet x)).IsIndepSet (S : Set _) := by
    rw [SimpleGraph.isIndepSet_induce]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    apply hI
    · simpa [S, e, T] using hu
    · simpa [S, e, T] using hv
    · exact huv
  have hc := hSind.card_le_indepNum
  simpa [S, T, indepNeighborsCard] using hc

lemma indepNeighborsCard_le_indepNum
    (G : SimpleGraph α) [DecidableRel G.Adj] (x : α) :
    indepNeighborsCard G x ≤ G.indepNum := by
  classical
  obtain ⟨S, hS⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := G.induce (G.neighborSet x))
  have hSG : G.IsNIndepSet (indepNeighborsCard G x)
      (S.map ⟨Subtype.val, Subtype.val_injective⟩) := by
    apply (SimpleGraph.isNIndepSet_induce G).mp
    simpa [indepNeighborsCard] using hS
  rw [← hSG.card_eq]
  exact hSG.isIndepSet.card_le_indepNum

end Graffiti100
