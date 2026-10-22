/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_46

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 1.35: if a sequence in a sequentially compact subset has a unique
sequential cluster point, expressed by the canonical predicate `IsSequentialClusterPt`, then the
whole sequence converges to that point. -/
-- Proof sketch: argue by contradiction. If `u` does not converge to `x`, choose a neighborhood of
-- `x` missed infinitely often and extract a subsequence in `C \ U`. Sequential compactness of `C`
-- gives a further convergent subsequence with limit `y`; by uniqueness of sequential cluster
-- points, `y = x`. This contradicts eventual membership in `U` for a subsequence converging to
-- `x`.
theorem tendsto_of_unique_sequential_cluster_point {C : Set X} (hC : IsSeqCompact C)
    {u : ℕ → X} (huC : ∀ n, u n ∈ C) {x : X}
    (hunique : ∀ y : X, IsSequentialClusterPt u y → y = x) :
    Tendsto u atTop (nhds x) := by
  -- Assume the sequence does not converge and extract a neighborhood missed infinitely often.
  by_contra hu_not
  rcases Filter.not_tendsto_iff_exists_frequently_notMem.1 hu_not with ⟨U, hUx, hfreqU⟩
  rcases Filter.extraction_of_frequently_atTop hfreqU with ⟨φ, hφmono, hφU⟩
  have huφC : ∀ n, (u ∘ φ) n ∈ C := by
    intro n
    exact huC (φ n)
  -- Sequential compactness gives a convergent subsubsequence of the bad subsequence.
  rcases hC huφC with ⟨y, _, ψ, hψmono, hconv⟩
  have hy_eq_x : y = x := by
    apply hunique y
    exact ⟨φ ∘ ψ, hφmono.comp hψmono, by simpa [Function.comp] using hconv⟩
  have hconvx : Tendsto (u ∘ (φ ∘ ψ)) atTop (nhds x) := by
    simpa [Function.comp, hy_eq_x] using hconv
  -- The convergent subsubsequence is eventually in every neighborhood of `x`.
  have hEventIn : ∀ᶠ n in atTop, u ((φ ∘ ψ) n) ∈ U := by
    exact hconvx.eventually_mem hUx
  have hEventOut : ∀ᶠ n in atTop, u ((φ ∘ ψ) n) ∉ U := by
    exact Filter.Eventually.of_forall fun n ↦ by
      simpa [Function.comp] using hφU (ψ n)
  -- The subsequence cannot be eventually both inside and outside `U`.
  rcases (hEventIn.and hEventOut).exists with ⟨n, hnIn, hnOut⟩
  exact hnOut hnIn
