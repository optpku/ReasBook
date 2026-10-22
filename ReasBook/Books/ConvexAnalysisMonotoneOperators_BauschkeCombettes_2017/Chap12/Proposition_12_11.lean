/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_37

-- Declarations for this item will be appended below by the statement pipeline.

open Set

noncomputable section

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

private theorem convexOn_separableSum_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal))
    (hf : ConvexOn f (effectiveDomain f)) (hg : ConvexOn g (effectiveDomain g)) :
    ConvexOn (f ⊕ g) (effectiveDomain (f ⊕ g)) := by
  refine ⟨?_, subset_rfl, ?_⟩
  · rcases hf.nonempty with ⟨x, hx⟩
    rcases hg.nonempty with ⟨y, hy⟩
    refine ⟨(x, y), ?_⟩
    exact (mem_effectiveDomain_pointwiseAdd_iff (f ∘ Prod.fst) (g ∘ Prod.snd) (x, y)).2 <| by
      constructor
      · simpa [Function.comp] using hx
      · simpa [Function.comp] using hy
  · intro x hx y hy α hα0 hα1
    have hx' := (mem_effectiveDomain_pointwiseAdd_iff (f ∘ Prod.fst) (g ∘ Prod.snd) x).1 hx
    have hy' := (mem_effectiveDomain_pointwiseAdd_iff (f ∘ Prod.fst) (g ∘ Prod.snd) y).1 hy
    have hfx : x.1 ∈ effectiveDomain f := by
      simpa [Function.comp] using hx'.1
    have hgx : x.2 ∈ effectiveDomain g := by
      simpa [Function.comp] using hx'.2
    have hfy : y.1 ∈ effectiveDomain f := by
      simpa [Function.comp] using hy'.1
    have hgy : y.2 ∈ effectiveDomain g := by
      simpa [Function.comp] using hy'.2
    calc
      ((f ⊕ g) (α • x + (1 - α) • y) : EReal)
          = (f (α • x.1 + (1 - α) • y.1) : EReal) +
              (g (α • x.2 + (1 - α) • y.2) : EReal) := by
              simp
      _ ≤ ((α : EReal) * (f x.1 : EReal) + (((1 - α : ℝ) : EReal) * (f y.1 : EReal))) +
            ((α : EReal) * (g x.2 : EReal) + (((1 - α : ℝ) : EReal) * (g y.2 : EReal))) := by
              exact add_le_add (hf.ineq hfx hfy hα0 hα1) (hg.ineq hgx hgy hα0 hα1)
      _ = (α : EReal) * ((f x.1 : EReal) + (g x.2 : EReal)) +
            (((1 - α : ℝ) : EReal) * ((f y.1 : EReal) + (g y.2 : EReal))) := by
              have hα_nonneg : (0 : EReal) ≤ (α : EReal) := EReal.coe_nonneg.mpr hα0.le
              have hβ_nonneg : (0 : EReal) ≤ (((1 - α : ℝ) : EReal)) :=
                EReal.coe_nonneg.mpr (sub_nonneg.mpr hα1.le)
              have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top α
              have hβ_ne_top : (((1 - α : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top (1 - α)
              rw [EReal.left_distrib_of_nonneg_of_ne_top hα_nonneg hα_ne_top,
                EReal.left_distrib_of_nonneg_of_ne_top hβ_nonneg hβ_ne_top]
              simp [add_assoc, add_left_comm]
      _ = (α : EReal) * ((f ⊕ g) x : EReal) +
            (((1 - α : ℝ) : EReal) * ((f ⊕ g) y : EReal)) := by
              simp

-- Proof sketch: apply the partial-infimum convexity argument to the jointly convex map
-- `F (x, y) = f y + g (x - y)`, using the no-`-∞` hypotheses to stay in the textbook codomain
-- `]-∞, +∞]`.
/-- Proposition 12.11: if `f` and `g` are convex `]-∞,+∞]`-valued functions, then the real-height
epigraph of their infimal convolution is convex. -/
theorem convex_epigraph_infimalConvolution
    (f g : H → Set.Ioi (⊥ : EReal))
    (hf : ConvexOn f (effectiveDomain f)) (hg : ConvexOn g (effectiveDomain g)) :
    Convex ℝ (epigraph (infimalConvolution f.asEReal g.asEReal)) := by
  let L : (H × H) →ᵃ[ℝ] H :=
    ((LinearMap.fst ℝ H H) + (LinearMap.snd ℝ H H)).toAffineMap
  rw [infimalConvolution_eq_infimalPostcomposition_separableSum]
  change Convex ℝ (epigraph (L ▷ (f ⊕ g)))
  exact
    convex_epigraph_infimalPostcomposition (f ⊕ g) L
      (convexOn_separableSum_effectiveDomain f g hf hg).convex_epigraph_asEReal

end ERealFunction
