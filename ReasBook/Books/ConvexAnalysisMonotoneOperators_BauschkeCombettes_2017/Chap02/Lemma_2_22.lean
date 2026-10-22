/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-- Lemma 2.22: the real-linear specialization of the uniform boundedness principle for a
pointwise bounded family of bounded operators from a Banach space into a normed space. -/
-- This is the textbook real-linear form of mathlib's canonical theorem `banach_steinhaus`.
theorem uniform_boundedness_principle {ι : Type u} {𝓧 : Type v} {𝓨 : Type w}
    [NormedAddCommGroup 𝓧] [NormedSpace ℝ 𝓧] [CompleteSpace 𝓧]
    [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨] {T : ι → 𝓧 →L[ℝ] 𝓨}
    (hT : ∀ x : 𝓧, ∃ C : ℝ, ∀ i : ι, ‖T i x‖ ≤ C) :
    ∃ C : ℝ, ∀ i : ι, ‖T i‖ ≤ C := by
  simpa using banach_steinhaus hT
