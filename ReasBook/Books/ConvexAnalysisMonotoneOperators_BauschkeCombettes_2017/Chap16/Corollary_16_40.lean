/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_38

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialCalculus

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem closure_graph_add_indicator_subdifferentiabilityDomain_eq_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    closure (graph ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal)) = closure (graph f.asEReal) := by
  let s : Set (graph f.asEReal) := {p | SubdifferentiableAt f p.1.1}
  have hs_dense : Dense s := graph_subdifferentiableAt_dense_in_graph_of_mem_gammaZero hf
  have hsub : graph ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal) ⊆ graph f.asEReal := by
    intro p hp
    rcases p with ⟨x, ξ⟩
    have hp' : (((f + ι[SetValuedOperator.dom (∂ f)]).asEReal) x : EReal) = ξ := hp
    by_cases hx : x ∈ SetValuedOperator.dom (∂ f)
    · simpa [add_apply, indicator_apply, hx] using hp'
    · have hfx_ne_bot : (f x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
      have htop : (⊤ : EReal) = ξ := by
        have hp'' := hp'
        simp [add_apply, indicator_apply, hx, EReal.add_top_of_ne_bot hfx_ne_bot] at hp''
      exact False.elim ((EReal.coe_ne_top ξ) htop.symm)
  have himage :
      Subtype.val '' s = graph ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (mem_graph_add_indicator_subdifferentiabilityDomain_iff q).2 hq
    · intro hp
      have hp_graph : p ∈ graph f.asEReal := hsub hp
      refine ⟨⟨p, hp_graph⟩, ?_, rfl⟩
      exact (mem_graph_add_indicator_subdifferentiabilityDomain_iff ⟨p, hp_graph⟩).1 hp
  have hgraph_subset :
      graph f.asEReal ⊆ closure (graph ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal)) := by
    intro p hp
    have hs_closure : closure s = Set.univ := by
      rw [dense_iff_closure_eq] at hs_dense
      exact hs_dense
    have : (⟨p, hp⟩ : graph f.asEReal) ∈ closure s := by
      rw [hs_closure]
      simp
    rwa [closure_subtype, himage] at this
  apply le_antisymm
  · exact closure_minimal (Subset.trans hsub subset_closure) isClosed_closure
  · exact closure_minimal hgraph_subset isClosed_closure

-- Proof sketch: the graph-density result for the canonical constrained function
-- `(f + ι[SetValuedOperator.dom (∂ f)]).asEReal` identifies its graph closure with
-- `graph f.asEReal`. Fenchel conjugates can then be read as support functions of the
-- corresponding graphs, and support functions agree on closures.
/-- Corollary 16.40: if `f ∈ Γ₀(H)`, then the Fenchel conjugate of `f` is unchanged after adding
the indicator of the subdifferential domain `dom (∂ f)`. -/
theorem conjugate_eq_conjugate_add_indicator_subdifferentiabilityDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f.asEReal∗ = ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal)∗ := by
  have hclosure := closure_graph_add_indicator_subdifferentiabilityDomain_eq_of_mem_gammaZero hf
  have hbot_add : ∀ x, ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal) x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ SetValuedOperator.dom (∂ f)
    · simpa [add_apply, indicator_apply, hx] using
        (show (f x : EReal) ≠ ⊥ from ne_of_gt (f x).2)
    · have hfx_ne_bot : (f x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
      simp [add_apply, indicator_apply, hx, EReal.add_top_of_ne_bot hfx_ne_bot]
  ext u
  let ℓ : H × ℝ → EReal := fun p ↦ ((⟪p, (u, -1)⟫_ℝ : ℝ) : EReal)
  have hc : Continuous (fun _ : H × ℝ ↦ ((u, (-1 : ℝ)) : H × ℝ)) := continuous_const
  have hℓ_lsc : LowerSemicontinuous ℓ := by
    simpa [ℓ] using
      (continuous_coe_real_ereal.comp (continuous_id.inner hc)).lowerSemicontinuous
  have hgraph := congrFun
    (conjugate_eq_support_function_graph (fun x ↦ ne_of_gt (f x).2)) u
  have hgraph_add := congrFun
    (conjugate_eq_support_function_graph hbot_add) u
  rw [hgraph, hgraph_add, supportFunction_eq_sSup_image, supportFunction_eq_sSup_image]
  change
    sSup (ℓ '' graph f.asEReal) =
      sSup (ℓ '' graph ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal))
  have hsSup_graph :
      sSup (ℓ '' graph f.asEReal) = sSup (ℓ '' closure (graph f.asEReal)) := by
    symm
    exact sSup_image_closure_eq_of_lowerSemicontinuous hℓ_lsc _
  have hsSup_closure :
      sSup (ℓ '' closure (graph f.asEReal)) =
        sSup (ℓ '' closure (graph ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal))) := by
    rw [hclosure]
  have hsSup_add :
      sSup (ℓ '' closure (graph ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal))) =
        sSup (ℓ '' graph ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal)) :=
    sSup_image_closure_eq_of_lowerSemicontinuous hℓ_lsc _
  exact hsSup_graph.trans (hsSup_closure.trans hsSup_add)

end SubdifferentialCalculus

end ERealFunction
