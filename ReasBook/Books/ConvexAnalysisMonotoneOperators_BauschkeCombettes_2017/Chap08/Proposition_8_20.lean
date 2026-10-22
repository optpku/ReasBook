/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}
variable [AddCommGroup H] [Module ℝ H]
variable [AddCommGroup K] [Module ℝ K]

/-- Helper for Proposition 8.20: domain membership for `g ∘ L` is exactly domain membership for
`g` after applying `L`. -/
private lemma mem_dom_comp_affineMap_iff (g : K → Set.Ioi (⊥ : EReal)) (L : H →ᵃ[ℝ] K) (x : H) :
    x ∈ dom (fun z : H ↦ (g (L z) : EReal)) ↔ L x ∈ dom (fun y : K ↦ (g y : EReal)) := by
  -- Both domain predicates unfold to the same requirement that `g (L x)` is strictly below `+∞`.
  simp [dom]

/-- Helper for Proposition 8.20: an affine map sends the textbook convex combination
`α • x + (1 - α) • y` to the corresponding convex combination of its endpoint values. -/
private lemma map_affine_combination_affineMap
    (L : H →ᵃ[ℝ] K) (x y : H) (α : ℝ) :
    L (α • x + (1 - α) • y) = α • L x + (1 - α) • L y := by
  -- Rewrite the combination as a line map and use that affine maps preserve line maps.
  simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
    L.apply_lineMap y x α

/-- Helper for Proposition 8.20: Jensen's inequality on the domain is preserved under
precomposition by an affine map. -/
private lemma jensen_on_dom_comp_affineMap
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →ᵃ[ℝ] K)
    (hconv : Convex ℝ (epigraph (fun y : K ↦ (g y : EReal)))) :
    ∀ ⦃x y : H⦄,
      x ∈ dom (fun z : H ↦ (g (L z) : EReal)) →
      y ∈ dom (fun z : H ↦ (g (L z) : EReal)) →
      ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
        (fun z : H ↦ (g (L z) : EReal)) (α • x + (1 - α) • y) ≤
          (α : EReal) * (fun z : H ↦ (g (L z) : EReal)) x +
            (((1 - α : ℝ) : EReal) * (fun z : H ↦ (g (L z) : EReal)) y) := by
  -- Extract Jensen's inequality for `g` from Proposition 8.4.
  have hgJ :=
    (convex_epigraph_iff_jensen_on_dom (fun y : K ↦ (g y : EReal))).1 hconv
  intro x y hx hy α hα hα_lt_one
  have hxL : L x ∈ dom (fun y : K ↦ (g y : EReal)) :=
    (mem_dom_comp_affineMap_iff g L x).1 hx
  have hyL : L y ∈ dom (fun y : K ↦ (g y : EReal)) :=
    (mem_dom_comp_affineMap_iff g L y).1 hy
  -- Push the convex combination through `L` and apply Jensen to the points `L x` and `L y`.
  simpa [map_affine_combination_affineMap] using hgJ hxL hyL hα hα_lt_one

-- Proof sketch: apply Proposition 8.4 to reduce convexity of the epigraph of `g ∘ L` to Jensen's
-- inequality on its effective domain, then obtain that inequality from convexity of `g` after
-- rewriting the affine combination through `L`.
/-- Proposition 8.20: if `g : 𝓚 → ]-∞,+∞]` is convex and `L : 𝓗 → 𝓚` is affine, then the
composition `g ∘ L` is convex; equivalently, the real-height epigraph of `x ↦ g (L x)` is convex
whenever the real-height epigraph of `g` is convex. -/
theorem convex_epigraph_comp_affineMap
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →ᵃ[ℝ] K)
    (hconv : Convex ℝ (epigraph (fun y : K ↦ (g y : EReal)))) :
    Convex ℝ (epigraph (fun x : H ↦ (g (L x) : EReal))) := by
  -- Proposition 8.4 turns the convexity goal into the Jensen inequality for `g ∘ L`.
  refine (convex_epigraph_iff_jensen_on_dom (fun x : H ↦ (g (L x) : EReal))).2 ?_
  -- The helper is exactly the textbook argument: use affineity of `L`, then convexity of `g`.
  exact jensen_on_dom_comp_affineMap g L hconv

end ERealFunction
