/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_44

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {X : Type u} [MetricSpace X] [CompleteSpace X]

/-- Corollary 1.45: in a complete metric space, the intersection of a sequence of dense open
subsets is again a dense `Gδ` subset. -/
-- Proof sketch: use
-- `interior_closure_iInter_eq_interior_iInter_closure_of_isOpen`
-- to identify
-- `interior (closure (⋂ n, C n))` with `interior (⋂ n, closure (C n)) = univ`, hence
-- `closure (⋂ n, C n) = univ`, and conclude with `IsGδ.iInter_of_isOpen`.
theorem dense_isGδ_iInter_of_dense_open (C : ℕ → Set X)
    (h_open : ∀ n, IsOpen (C n)) (h_dense : ∀ n, Dense (C n)) :
    Dense (⋂ n, C n) ∧ IsGδ (⋂ n, C n) := by
  constructor
  · rw [dense_iff_closure_eq]
    have hclosure : ∀ n, closure (C n) = univ := fun n ↦ Dense.closure_eq (h_dense n)
    have hinterior :
        interior (closure (⋂ n, C n)) = univ := by
      calc
        interior (closure (⋂ n, C n))
            = interior (⋂ n, closure (C n)) :=
              interior_closure_iInter_eq_interior_iInter_closure_of_isOpen C h_open
        _ = univ := by simp [hclosure]
    refine subset_antisymm (subset_univ _) ?_
    simpa [hinterior] using
      (interior_subset : interior (closure (⋂ n, C n)) ⊆ closure (⋂ n, C n))
  · -- The `Gδ` part is the countable intersection of the given open sets.
    exact IsGδ.iInter_of_isOpen h_open
