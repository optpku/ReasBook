/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_34

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped ProbabilityTheory
open MeasureTheory

section

variable {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable {f : E → ℝ} {x : ℕ → Ω → E} {g : ℕ → Ω → E}

-- Proof sketch: expand `StochasticProjectedSubgradientOracle.unbiased k` and rewrite membership in
-- `euclideanSubdifferentialAt` using the Chapter 3 bridge lemmas
-- `mem_euclideanSubdifferentialAt_iff`, `mem_strongDualSubdifferential`, `mem_subdifferential`,
-- and `is_subgradient_at_coe_iff`; then use `toDualMap_apply_apply` to identify the pairing with
-- the inner product.
/-- Proposition 8.7: for a real-valued objective, clause (A) of Assumption 8.34 is equivalent to
saying that, for each `k`, the conditional expectation of the stochastic subgradient given `x^k`
satisfies the pointwise subgradient inequality at `x^k` almost surely, i.e. for every `z`, one has
`f z ≥ f (x^k) + ⟪E[g^k | x^k], z - x^k⟫`. Since `f` is real-valued here, `dom(f) = E`. -/
theorem stochastic_projected_subgradient_unbiased_iff_ae_subgradient_inequality (k : ℕ) :
    (∀ᵐ ω ∂μ,
      μ[g k | MeasurableSpace.comap (x k) inferInstance] ω ∈
        euclideanSubdifferentialAt f (x k ω)) ↔
      ∀ᵐ ω ∂μ,
        ∀ z : E,
          f z ≥
            f (x k ω) +
              inner ℝ
                (μ[g k | MeasurableSpace.comap (x k) inferInstance] ω)
                (z - x k ω) := by
  -- Rewrite the stochastic clause pointwise through the Chapter 3 Euclidean-subgradient bridge.
  have hpointwise :
      ∀ ω : Ω,
        μ[g k | MeasurableSpace.comap (x k) inferInstance] ω ∈
            euclideanSubdifferentialAt f (x k ω) ↔
          ∀ z : E,
            f z ≥
              f (x k ω) +
                inner ℝ
                  (μ[g k | MeasurableSpace.comap (x k) inferInstance] ω)
                  (z - x k ω) := by
    intro ω
    -- The owner predicate is exactly the real-valued subgradient inequality after identifying the
    -- Riesz pairing with the inner product.
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
      mem_subdifferential, is_subgradient_at_coe_iff]
    simp [InnerProductSpace.toDualMap_apply_apply]
  constructor
  · intro hmem
    -- Transport the pointwise bridge along the almost-everywhere membership event.
    filter_upwards [hmem] with ω hω
    exact (hpointwise ω).1 hω
  · intro hineq
    -- The reverse implication is the same pointwise bridge used in the opposite direction.
    filter_upwards [hineq] with ω hω
    exact (hpointwise ω).2 hω

end
