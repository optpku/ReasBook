/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Example_8_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: use Example 12.2 to rewrite `fun x ↦ (Metric.infEDist x C : EReal)` as the
-- infimal convolution of the indicator of `C` with the norm, observe from Example 8.3 and
-- Example 8.9 that these two functions are convex when `C` is convex, and apply Proposition
-- 12.11.
/-- Corollary 12.12: if `C` is convex, then the extended-real distance function `d_C` is convex on
the ambient space. -/
theorem convex_epigraph_distanceToSet (C : Set H) (hC : Convex ℝ C) :
    Convex ℝ (epigraph (fun x ↦ (Metric.infEDist x C : EReal))) := by
  by_cases hC_nonempty : C.Nonempty
  · have hindicator_dom : effectiveDomain (ι[C]) = C := by
      ext x
      by_cases hx : x ∈ C <;> simp [effectiveDomain, indicator, hx]
    have hindicator_epi : Convex ℝ (epigraph (fun x ↦ (ι[C] x : EReal))) := by
      simpa [epigraph, indicator_apply] using
        (convex_epigraph_indicator_iff_convex C).2 hC
    have hindicator_jensen :=
      (convex_epigraph_iff_jensen_on_dom (fun x ↦ (ι[C] x : EReal))).1 hindicator_epi
    have hindicator :
        ConvexOn (ι[C]) (effectiveDomain (ι[C])) := by
      refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hx ↦ hx, ?_⟩
      intro x hx y hy α hα0 hα1
      exact hindicator_jensen
        (by simpa [hindicator_dom, effectiveDomain, dom] using hx)
        (by simpa [hindicator_dom, effectiveDomain, dom] using hy)
        hα0 hα1
    let κ : H → Set.Ioi (⊥ : EReal) := scaledNormKernel (1 : NNReal)
    have hnorm_real : _root_.ConvexOn ℝ (Set.univ : Set H) (norm : H → ℝ) := convexOn_univ_norm
    have hscaledNorm_epi :
        Convex ℝ (epigraph (fun x : H ↦ (κ x : EReal))) := by
      simpa [κ, epigraph, scaledNormKernel, one_mul] using hnorm_real.convex_epigraph
    have hscaledNorm_jensen :=
      (convex_epigraph_iff_jensen_on_dom (fun x : H ↦ (κ x : EReal))).1 hscaledNorm_epi
    have hscaledNorm : ConvexOn κ (effectiveDomain κ) := by
      refine ⟨by simp [κ, scaledNormKernel, Function.effectiveDomain_toEReal], fun _ hx ↦ hx, ?_⟩
      intro x hx y hy α hα0 hα1
      exact hscaledNorm_jensen
        (by simp [κ, dom, scaledNormKernel])
        (by simp [κ, dom, scaledNormKernel])
        hα0 hα1
    have hconv := convex_epigraph_infimalConvolution (ι[C]) κ hindicator hscaledNorm
    change Convex ℝ (epigraph (infimalConvolution
      (fun x ↦ (ι[C] x : EReal)) (fun x ↦ (κ x : EReal)))) at hconv
    dsimp [κ] at hconv
    have hdist := distanceToSet_eq_indicator_infimalConvolution_norm C
    change (fun x ↦ (Metric.infEDist x C : EReal)) =
      infimalConvolution (fun x ↦ (ι[C] x : EReal))
        (fun x ↦ (scaledNormKernel (1 : NNReal) x : EReal)) at hdist
    rw [← hdist] at hconv
    exact hconv
  · simpa [epigraph, Set.not_nonempty_iff_eq_empty.mp hC_nonempty, Metric.infEDist_empty] using
      (convex_empty : Convex ℝ (∅ : Set (H × ℝ)))

end

end ERealFunction
