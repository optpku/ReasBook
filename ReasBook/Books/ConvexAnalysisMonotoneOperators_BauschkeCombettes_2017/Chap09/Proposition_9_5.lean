/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Helper for Proposition 9.5: domain membership for `f ∘ L` is exactly domain membership for
`f` after applying the continuous linear map `L`. -/
private lemma mem_dom_comp_continuousLinearMap_iff
    (f : K → EReal) (L : H →L[ℝ] K) (x : H) :
    x ∈ dom (f ∘ L) ↔ L x ∈ dom f := by
  -- Both sides unfold to the same inequality `f (L x) < ⊤`.
  simp [dom]

/-- Helper for Proposition 9.5: a continuous linear map preserves the affine combination used in
the Jensen inequality for convexity. -/
private lemma map_convex_combination_continuousLinearMap
    (L : H →L[ℝ] K) (x y : H) (a : ℝ) :
    L (a • x + (1 - a) • y) = a • L x + (1 - a) • L y := by
  -- Push the scalar multiples and the sum through `L`.
  simp [map_add, map_smul]

-- Proof sketch: lower semicontinuity follows from `LowerSemicontinuous.comp` because a
-- continuous linear map is continuous. Jensen convexity is preserved by precomposition with a
-- linear map since `L (a • x + (1 - a) • y) = a • L x + (1 - a) • L y`.
/-- Precomposing a member of `gamma K` with a continuous linear map yields a member of `gamma H`. -/
theorem mem_gamma_comp_continuousLinearMap
    (f : K → EReal) (L : H →L[ℝ] K) (hf : f ∈ gamma K) :
    f ∘ L ∈ gamma H := by
  -- Unpack `gamma` into Jensen convexity and lower semicontinuity.
  rw [mem_gamma_iff] at hf ⊢
  rcases hf with ⟨hf_convex, hf_lsc⟩
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    -- Rewrite the convex combination through `L` and apply convexity of `f`.
    simpa [Function.comp, map_convex_combination_continuousLinearMap] using
      hf_convex (x := L x) (y := L y) (a := a) ha0 ha1
  · -- Lower semicontinuity is preserved under composition with the continuous map `L`.
    exact hf_lsc.comp L.continuous

-- Proof sketch: use the nonempty intersection to choose `x₀` with `L x₀ ∈ dom f`; then
-- `(f ∘ L) x₀ = f (L x₀) < ⊤`, so the composed function has nonempty domain. The exclusion of
-- `⊥` is inherited pointwise from `hf_proper`.
/-- If `dom f` meets the range of `L`, then precomposition with `L` preserves properness. -/
theorem isProper_comp_continuousLinearMap_of_dom_inter_range_nonempty
    (f : K → EReal) (L : H →L[ℝ] K) (hf_proper : IsProper f)
    (hdom : (dom f ∩ Set.range L).Nonempty) :
    IsProper (f ∘ L) := by
  -- Unpack properness into the pointwise exclusion of `⊥` and nonemptiness of the domain.
  rw [isProper_iff] at hf_proper ⊢
  refine ⟨?_, ?_⟩
  · intro x
    -- The composition cannot attain `⊥` because `f` already avoids `⊥`.
    exact hf_proper.1 (L x)
  · rcases hdom with ⟨y, hy_dom, hy_range⟩
    rcases hy_range with ⟨x₀, rfl⟩
    -- Use the intersection witness to produce a point in the domain of `f ∘ L`.
    exact ⟨x₀, (mem_dom_comp_continuousLinearMap_iff f L x₀).2 hy_dom⟩

-- Proof sketch: combine `mem_gamma_comp_continuousLinearMap` for lower semicontinuity and
-- convexity with `isProper_comp_continuousLinearMap_of_dom_inter_range_nonempty` for properness.
/-- Proposition 9.5: if `f` is proper, lower semicontinuous, and convex on `K`, and `dom f` meets
the range of a continuous linear map `L : H →L[ℝ] K`, then `f ∘ L` is proper, lower
semicontinuous, and convex on `H`. -/
theorem isProper_and_mem_gamma_comp_continuousLinearMap_of_dom_inter_range_nonempty
    (f : K → EReal) (L : H →L[ℝ] K) (hf_proper : IsProper f) (hf_gamma : f ∈ gamma K)
    (hdom : (dom f ∩ Set.range L).Nonempty) :
    IsProper (f ∘ L) ∧ f ∘ L ∈ gamma H := by
  -- The textbook proof splits into the properness part and the `gamma` part.
  refine ⟨?_, ?_⟩
  · exact isProper_comp_continuousLinearMap_of_dom_inter_range_nonempty f L hf_proper hdom
  · exact mem_gamma_comp_continuousLinearMap f L hf_gamma

end ERealFunction
