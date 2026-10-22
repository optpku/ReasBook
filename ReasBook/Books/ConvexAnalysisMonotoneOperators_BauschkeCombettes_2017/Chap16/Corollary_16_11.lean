/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: if `(x, u)` lies in `(∂ f).graph`, then `u ∈ (∂ f) x`, so Proposition 16.4 puts
-- `x` in `effectiveDomain f`. Proposition 16.10 rewrites the same membership as the
-- Fenchel--Young equality `(f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal)`. Since the
-- right-hand side is finite, the conjugate cannot be `⊤`, so `u ∈ dom f.asEReal∗`.
/-- Corollary 16.11: if an `]-∞,+∞]`-valued function has nonempty effective domain, then the graph
of its subdifferential is contained in the product of the effective domain of `f` and the domain
of its Fenchel conjugate `f*`. -/
theorem graph_subdifferential_subset_dom_prod_dom_conjugate_of_effectiveDomain_nonempty
    (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) :
    SetValuedOperator.graph (∂ f) ⊆ (effectiveDomain f) ×ˢ dom (f.asEReal∗) := by
  rintro ⟨x, u⟩ hxu
  rw [SetValuedOperator.mem_graph] at hxu
  change x ∈ effectiveDomain f ∧ u ∈ dom (f.asEReal∗)
  have hx_subdom : x ∈ SetValuedOperator.dom (∂ f) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨u, hxu⟩
  have hx : x ∈ effectiveDomain f :=
    subdifferential_domain_subset_effectiveDomain f hdom hx_subdom
  have hfy :
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
    (mem_subdifferential_iff_fenchel_young_eq f x u).mp hxu
  have hu_top : f.asEReal∗ u ≠ ⊤ := by
    intro hu_top
    have hsum_top : (f x : EReal) + f.asEReal∗ u = ⊤ := by
      rw [hu_top]
      exact EReal.add_top_of_ne_bot (ne_of_gt (f x).2)
    exact EReal.coe_ne_top _ <| hfy.symm.trans hsum_top
  exact ⟨hx, (mem_dom_iff_ne_top _ _).2 hu_top⟩

end SubdifferentialConjugation

end ERealFunction
