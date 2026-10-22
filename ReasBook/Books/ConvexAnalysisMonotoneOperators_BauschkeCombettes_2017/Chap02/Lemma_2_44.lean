/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open scoped Topology

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {A : Type v} [Preorder A]

/-- Lemma 2.44: in a real Hilbert space, if `xₐ → x` and `uₐ → u` in norm and the net `xₐ` is
bounded, then `inner ℝ (xₐ a) (uₐ a)` converges to `inner ℝ x u`. -/
-- The boundedness hypothesis is part of the source statement. The canonical proof is the stronger
-- mathlib theorem `Filter.Tendsto.inner`, coming from joint continuity of the inner product.
theorem tendsto_inner_of_bounded_left
    {xₐ uₐ : A → H} {x u : H}
    (_hxₐ_bdd : Bornology.IsBounded (Set.range xₐ))
    (hxₐ : Tendsto xₐ atTop (𝓝 x))
    (huₐ : Tendsto uₐ atTop (𝓝 u)) :
    Tendsto (fun a ↦ inner ℝ (xₐ a) (uₐ a)) atTop (𝓝 (inner ℝ x u)) := by
  simpa using Filter.Tendsto.inner hxₐ huₐ
