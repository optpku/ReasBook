import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_2.ch4_sec4_4_2_algorithm_4_4_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_3.ch4_sec4_4_3_definition_4_4_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_2.ch4_sec4_3_2_remark_4_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SimpleGraph.Subgraph (IsMinimumWeightMatchingOfCardinality matchingWeight)
open scoped BigOperators

universe u

section Remark421

variable {α : Type*} [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α]
variable {V : Type u} [Finite V]
variable (G : SimpleGraph V)

/-- Remark 4.21. If `M` is minimum-weight among the matchings of cardinality `k`, and every circuit
of the auxiliary digraph `D_M` yields a matching of the same cardinality whose weight differs from
that of `M` by the circuit length, then `D_M` does not contain any negative-length circuit. -/
theorem minimum_weight_matching_auxiliary_digraph_has_no_negative_length_circuit
    (w : Sym2 V → α)
    (k : ℕ)
    (U W : Set V)
    (M : G.Subgraph)
    (hM_min : IsMinimumWeightMatchingOfCardinality w k M)
    (ℓ : ∀ {x y : V}, (matching_auxiliary_digraph G U W M).Edge x y → α)
    (h_circuit_exchange :
      ∀ ⦃u : V⦄ (C : (matching_auxiliary_digraph G U W M).Path u u),
        C.IsCircuit →
        ∃ N : G.Subgraph,
          N.IsMatching ∧
            N.edgeSet.ncard = k ∧
              matchingWeight w N = matchingWeight w M + C.addWeight ℓ) :
    (matching_auxiliary_digraph G U W M).HasNoNegativeLengthCircuit ℓ := by
  intro u C hC
  -- Compare `M` to the same-cardinality matching produced by exchanging along the circuit `C`.
  obtain ⟨N, hN_matching, hN_card, hN_weight⟩ := h_circuit_exchange C hC
  have h_weight_le : matchingWeight w M ≤ matchingWeight w N :=
    hM_min.minimum N hN_matching hN_card
  -- Rewriting the competitor's weight as `matchingWeight w M + length` reduces the claim to
  -- cancelling the common matching-weight term.
  exact nonneg_of_le_add_right (h_weight_le.trans_eq hN_weight)

end Remark421
