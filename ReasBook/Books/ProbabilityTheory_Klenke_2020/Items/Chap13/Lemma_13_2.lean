/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

/-- Lemma 13.2: for a subset of a complete metric space realizing the Polish topology, total
boundedness with respect to the metric is equivalent to relative compactness, formalized as
compactness of the closure. -/
-- Proof sketch: If `A` is totally bounded, then `closure A` is again totally bounded; since it is
-- closed in a complete metric space, it is compact. Conversely, a compact closure is totally
-- bounded, and every subset of a totally bounded set is totally bounded.
lemma totallyBounded_iff_isCompact_closure {E : Type u} [MetricSpace E] [CompleteSpace E]
    {A : Set E} : TotallyBounded A ↔ IsCompact (closure A) := by
  rw [← totallyBounded_closure]
  exact ⟨fun hA ↦ hA.isCompact_of_isClosed isClosed_closure, IsCompact.totallyBounded⟩
