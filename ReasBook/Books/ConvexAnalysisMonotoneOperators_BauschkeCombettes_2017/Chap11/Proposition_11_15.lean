/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Theorem_11_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: this is a bridge from the source-facing `Γ₀(H)` hypothesis to the core bounded
-- lower-level-set existence theorem. If `C ∩ effectiveDomain f` is empty, then `f.asEReal = ⊤`
-- everywhere on `C`, so every point of the nonempty constraint set is a constrained minimizer. If
-- `C ∩ effectiveDomain f` is nonempty, choose a feasible point to define a finite level `ξ`,
-- bound `C ∩ lowerLevelSet (fun y ↦ (f y : EReal)) ξ` either from coercivity via Proposition
-- 11.12 or directly from boundedness of `C`, and apply Theorem 11.10.
/-- Proposition 11.15: if `f ∈ Γ₀(H)`, if `C` is a nonempty closed convex set, and if either (i)
the coerced function `x ↦ (f x : EReal)` is coercive or (ii) `C` is bounded, then `f` attains a
minimum over `C`. -/
theorem argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H} (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty)
    (hcase : Coercive f.asEReal ∨ Bornology.IsBounded C) :
    (Argmin[C] f.asEReal).Nonempty := by
  by_cases hC_dom : (C ∩ effectiveDomain f).Nonempty
  · rcases hC_dom with ⟨x, hxC, hxdom⟩
    let ξ : ℝ := (f x : EReal).toReal
    have hx_level : x ∈ lowerLevelSet f.asEReal ξ := by
      rw [mem_lowerLevelSet_iff]
      exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hxdom))
    have hlevel_nonempty : (C ∩ lowerLevelSet f.asEReal ξ).Nonempty := ⟨x, hxC, hx_level⟩
    have hlevel_bounded : Bornology.IsBounded (C ∩ lowerLevelSet f.asEReal ξ) := by
      rcases hcase with hf_coe | hC_bounded
      · have hbounded : Bornology.IsBounded (lowerLevelSet f.asEReal ξ) :=
          (coercive_iff_bounded_lowerLevelSet f.asEReal).1 hf_coe ξ
        exact hbounded.subset (fun _ hy ↦ hy.2)
      · exact hC_bounded.subset (fun _ hy ↦ hy.1)
    have hconv_epi : Convex ℝ (epigraph f.asEReal) := by
      refine (convex_epigraph_iff_jensen_on_dom f.asEReal).2 ?_
      intro y z hy hz a ha ha_lt_one
      have hy' : y ∈ effectiveDomain f := by
        simpa [effectiveDomain, dom] using hy
      have hz' : z ∈ effectiveDomain f := by
        simpa [effectiveDomain, dom] using hz
      simpa using hf.2.ineq hy' hz' ha ha_lt_one
    have hf_quasi : QuasiconvexOn ℝ Set.univ f.asEReal := by
      rw [quasiconvexOn_univ_iff_convex_lowerLevelSet ℝ]
      intro η
      exact convex_lowerLevelSet_of_convex_epigraph f.asEReal hconv_epi η
    exact
      argminOn_nonempty_of_quasiconvexOn_univ_of_nonempty_bounded_inter_lowerLevelSet
        hf_quasi hf.1 hC_closed hC_convex ξ hlevel_nonempty hlevel_bounded
  · rcases hC_nonempty with ⟨x, hxC⟩
    have htop : ∀ {y : H}, y ∈ C → f.asEReal y = ⊤ := by
      intro y hyC
      have hy_not_dom : y ∉ effectiveDomain f := by
        intro hy_dom
        exact hC_dom ⟨y, hyC, hy_dom⟩
      exact le_antisymm le_top <| not_lt.mp <| by
        simpa [mem_effectiveDomain_iff] using hy_not_dom
    refine ⟨x, ?_⟩
    rw [mem_argminOn_iff, isMinOn_iff]
    refine ⟨hxC, ?_⟩
    intro y hyC
    simp [htop hxC, htop hyC]

end ERealFunction
