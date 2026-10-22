/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_47
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

variable {H : Type u}

/-- Theorem 5.5: if a sequence in a real Hilbert space is Fejér monotone with respect to a
nonempty set `C` and every weak sequential cluster point of the sequence belongs to `C`, then the
sequence converges weakly to some point of `C`. -/
-- Proof sketch: Proposition 5.4(ii) gives convergence of each distance sequence
-- `n ↦ dist (x n) z` for `z ∈ C` from the Fejér monotonicity hypothesis. Then apply `opial_lemma`
-- with the weak sequential cluster-point assumption.
theorem tendsto_weakly_of_fejerMonotone_of_weakSequentialClusterPts_mem
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {C : Set H}
    (hC : C.Nonempty) (x : ℕ → H)
    (hfejer : FejerMonotone C x)
    (hcluster :
      ∀ z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) → z ∈ C) :
    ∃ z ∈ C, Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H z)) := by
  refine opial_lemma hC x ?_ hcluster
  intro z hz
  simpa [dist_eq_norm] using FejerMonotone.dist_tendsto hfejer hz
