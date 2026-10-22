/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Semantic recall hits verified for this item: `convex_iInter`, `convex_iInter₂`, and the
-- chapter-local binary specialization `convex_intersection`.

variable {n : ℕ}

universe u

section

variable {ι : Type u} (t : Finset ι) {S : ι → Set (EuclideanSpace ℝ (Fin n))}

/-- Chapter01 Exercise 1.11: if `(S i)_{i ∈ t}` is a finite family of convex subsets of
`EuclideanSpace ℝ (Fin n)`, then `⋂ i ∈ t, S i` is convex. -/
theorem convex_iInter_finset (hS : ∀ i ∈ t, Convex ℝ (S i)) :
    Convex ℝ (⋂ i ∈ t, S i) := by
  -- The bounded finite intersection already matches mathlib's canonical owner theorem.
  simpa using (convex_iInter₂ hS : Convex ℝ (⋂ i ∈ t, S i))

end
