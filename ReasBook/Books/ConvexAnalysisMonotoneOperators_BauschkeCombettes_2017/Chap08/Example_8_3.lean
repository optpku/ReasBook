/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {X : Type u}

-- Proof sketch: unfold the real-height epigraph, split on whether `x ∈ C`, and use that the
-- indicator is `0` on `C` and `⊤` on `Cᶜ`.
/-- Example 8.3 (1): the epigraph of the extended-real indicator of `C` is exactly
`C × ℝ_+`. -/
theorem epigraph_indicator_eq_prod_nonneg (C : Set X) :
    { p : X × ℝ | (indicator Cᶜ fun _ : X ↦ (⊤ : EReal)) p.1 ≤ (p.2 : EReal) } =
      C ×ˢ Set.Ici (0 : ℝ) := by
  -- Check membership pointwise and split on whether the base point lies in `C`.
  ext p
  rcases p with ⟨x, t⟩
  by_cases hx : x ∈ C
  · -- On `C`, the indicator is `0`, so the epigraph condition is exactly `0 ≤ t`.
    simp [hx]
  · -- Outside `C`, the indicator is `⊤`, and no finite height can dominate `⊤`.
    simp [hx]

section Convexity

variable [AddCommMonoid X] [Module ℝ X]

/-- Helper for Example 8.3: if `C × ℝ_+` is convex, then its zero-height slice shows that
`C` itself is convex. -/
lemma convex_of_convex_prod_nonneg (C : Set X)
    (hprod : Convex ℝ (C ×ˢ Set.Ici (0 : ℝ))) :
    Convex ℝ C := by
  -- Test convexity on the zero-height points that encode the original set `C`.
  rw [convex_iff_add_mem] at hprod ⊢
  intro x hx y hy a b ha hb hab
  have hx0 : (x, (0 : ℝ)) ∈ C ×ˢ Set.Ici (0 : ℝ) := by
    simp [hx]
  have hy0 : (y, (0 : ℝ)) ∈ C ×ˢ Set.Ici (0 : ℝ) := by
    simp [hy]
  -- Convex combinations stay in the product set, and the second coordinate stays at `0`.
  have hxy : a • (x, (0 : ℝ)) + b • (y, (0 : ℝ)) ∈ C ×ˢ Set.Ici (0 : ℝ) :=
    hprod hx0 hy0 ha hb hab
  simpa [Set.mem_prod, Prod.smul_mk] using hxy

-- Proof sketch: for the forward implication, identify the epigraph with `C × ℝ_+` and use that
-- products of convex sets are convex; for the reverse implication, use convexity of the epigraph
-- and test it on the points `(x₁, 0)` and `(x₂, 0)` with `x₁, x₂ ∈ C`.
/-- Example 8.3 (2): the extended-real indicator of `C` is convex, equivalently its real-height
epigraph is convex, if and only if `C` is convex. -/
theorem convex_epigraph_indicator_iff_convex (C : Set X) :
    Convex ℝ { p : X × ℝ | (indicator Cᶜ fun _ : X ↦ (⊤ : EReal)) p.1 ≤ (p.2 : EReal) } ↔
      Convex ℝ C := by
  constructor
  · intro hepigraph
    -- Rewrite the epigraph into `C × ℝ_+` and project convexity from its zero-height slice.
    have hprod : Convex ℝ (C ×ˢ Set.Ici (0 : ℝ)) := by
      simpa [epigraph_indicator_eq_prod_nonneg C] using hepigraph
    exact convex_of_convex_prod_nonneg C hprod
  · intro hC
    -- Identify the epigraph with the product set and use convexity of both factors.
    rw [epigraph_indicator_eq_prod_nonneg C]
    exact hC.prod (convex_Ici (0 : ℝ))

end Convexity
