/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_34

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Corollary 3.35: a weak limit of points in a closed convex set of a real inner-product space
belongs to the set. -/
-- Proof sketch: `Theorem_3_34` already identifies norm-closed convex sets with weakly closed
-- subsets after transport to `WeakSpace`. Once the weak image of `C` is closed, the limit point
-- lies in that image by closure, and injectivity of `toWeakSpace` pulls the conclusion back to `C`.
theorem mem_of_tendsto_weakly_of_isClosed_convex {C : Set 𝓗}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {xₙ : ℕ → 𝓗} {x : 𝓗} (hxₙ : ∀ n, xₙ n ∈ C)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) atTop
      (nhds (toWeakSpace ℝ 𝓗 x))) :
    x ∈ C := by
  have hC_weakClosed : IsClosed ((toWeakSpace ℝ 𝓗) '' C) :=
    (isClosed_iff_weak_image_isClosed_of_convex hC_convex).1 hC_closed
  have hxWeak :
      toWeakSpace ℝ 𝓗 x ∈ closure ((toWeakSpace ℝ 𝓗) '' C) := by
    exact mem_closure_of_tendsto hweak <|
      Filter.Eventually.of_forall fun n ↦ ⟨xₙ n, hxₙ n, rfl⟩
  rw [hC_weakClosed.closure_eq] at hxWeak
  rcases hxWeak with ⟨y, hyC, hyx⟩
  exact (toWeakSpace ℝ 𝓗).injective hyx ▸ hyC
