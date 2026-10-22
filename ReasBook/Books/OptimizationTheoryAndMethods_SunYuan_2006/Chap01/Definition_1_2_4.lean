/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.InnerProductSpace.PiL2

open Filter

universe v

-- Mathlib recall: `Metric.cauchySeq_iff`, `cauchySeq_tendsto_of_complete`, and
-- `Metric.complete_of_cauchySeq_tendsto` provide the canonical API behind these
-- source-facing specializations.

section Definition124

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/- Mathlib recall for Chapter01 Definition 1.2.4: `Metric.cauchySeq_iff` is the
canonical `ε`-`N` characterization of `CauchySeq` in metric spaces, applied in
particular to sequences in `ℝ^n`. -/
#check Metric.cauchySeq_iff
#check cauchySeq_tendsto_of_complete
#check Metric.complete_of_cauchySeq_tendsto

/-- Chapter01 Definition 1.2.4 (1): in `ℝ^n`, a sequence is Cauchy iff it
satisfies the textbook `ε`-`N` characterization. -/
theorem euclideanCauchySeq_iff (x : ℕ → Point) :
    CauchySeq x ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ m > N, ∀ l > N, ‖x m - x l‖ < ε := by
    rw [Metric.cauchySeq_iff]
    constructor
    · intro hx ε hε
      rcases hx ε hε with ⟨N, hN⟩
      exact ⟨N, fun m hm l hl ↦ by
        simpa [dist_eq_norm] using hN m hm.le l hl.le⟩
    · intro hx ε hε
      rcases hx ε hε with ⟨N, hN⟩
      exact ⟨N + 1, fun m hm l hl ↦ by
        simpa [dist_eq_norm] using hN m (lt_of_lt_of_le (Nat.lt_succ_self N) hm)
          l (lt_of_lt_of_le (Nat.lt_succ_self N) hl)⟩

/-- Chapter01 Definition 1.2.4 (2): in `ℝ^n`, a sequence converges if and only if it is Cauchy. -/
theorem euclideanTendsto_iff_cauchySeq (x : ℕ → Point) :
    (∃ y, Tendsto x atTop (nhds y)) ↔ CauchySeq x := by
  constructor
  · rintro ⟨y, hy⟩
    exact hy.cauchySeq
  · intro hx
    simpa using cauchySeq_tendsto_of_complete hx

end Definition124

/-- Chapter01 Definition 1.2.4 (3): more generally, a noncomplete normed
additive group, hence in particular a noncomplete normed space, admits a
Cauchy sequence that does not converge in the space. -/
theorem exists_cauchySeq_not_tendsto_of_not_complete
    (E : Type v) [NormedAddCommGroup E]
    (hE : ¬ CompleteSpace E) :
    ∃ x : ℕ → E, CauchySeq x ∧ ¬ ∃ y : E, Tendsto x atTop (nhds y) := by
  classical
  by_contra h
  apply hE
  refine Metric.complete_of_cauchySeq_tendsto fun x hx ↦ ?_
  by_contra hx_tendsto
  exact h ⟨x, hx, hx_tendsto⟩
