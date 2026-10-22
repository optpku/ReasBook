/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

/-- Definition 6.53: the accumulated weights `A_t = ∑_{k=0}^t a_k` attached to the sequence
`a_t`. -/
def accumulatedWeights (a : ℕ → ℝ) : ℕ → ℝ :=
  fun t ↦ ∑ k ∈ Finset.range (t + 1), a k

namespace WeightSequenceNotation

/- Source-facing Lean notation for the textbook accumulated weights `A_t`. -/
scoped notation:max "A[" a:arg "](" t:arg ")" => accumulatedWeights a t

end WeightSequenceNotation

open scoped WeightSequenceNotation

/-- Expanding `A[a](t)` gives the partial sum `∑_{k=0}^t a_k`. -/
theorem accumulatedWeights_apply
    (a : ℕ → ℝ) (t : ℕ) :
    A[a](t) = ∑ k ∈ Finset.range (t + 1), a k := rfl

/-- The normalized coefficients `τ_t = a_{t+1} / A_{t+1}` attached to the weights `a_t`. -/
def weightCoefficient (a : ℕ → ℝ) (t : ℕ) : ℝ :=
  a (t + 1) / accumulatedWeights a (t + 1)

namespace WeightSequenceNotation

/- Source-facing Lean notation for the textbook coefficients `τ_t`. -/
scoped notation:max "τ[" a:arg "](" t:arg ")" => weightCoefficient a t

end WeightSequenceNotation

/-- Expanding `τ[a](t)` gives the ratio `a_{t+1} / A[a](t + 1)`. -/
theorem weightCoefficient_apply
    (a : ℕ → ℝ) (t : ℕ) :
    τ[a](t) = a (t + 1) / accumulatedWeights a (t + 1) := rfl

/-- The Chapter 6 weighted oracle-error accumulation with initial term `V₀`, weights `a_t`,
per-step coefficient `G_ν`, diameter bound `D`, and exponent `ν`. This is the canonical owner
reused later by the source-facing error terms `B_{ν,t}` and `C_{v,t}`. -/
def linearOptimizationOracleErrorBound
    (V0 : ℝ) (a : ℕ → ℝ) (Gν D ν : ℝ) (t : ℕ) : ℝ :=
  a 0 * V0 +
    Finset.sum (Finset.Icc 1 t)
        (fun k ↦ Real.rpow (a k) (1 + ν) / Real.rpow (A[a](k)) ν) *
      Gν * Real.rpow D (1 + ν)

/-- Expanding `linearOptimizationOracleErrorBound V₀ a G_ν D ν t` gives the defining Chapter 6
weighted error formula with `A_k = A[a](k)`. -/
theorem linearOptimizationOracleErrorBound_def
    (V0 : ℝ) (a : ℕ → ℝ) (Gν D ν : ℝ) (t : ℕ) :
    linearOptimizationOracleErrorBound V0 a Gν D ν t =
      a 0 * V0 +
        Finset.sum (Finset.Icc 1 t)
            (fun k ↦ Real.rpow (a k) (1 + ν) / Real.rpow (A[a](k)) ν) *
          Gν * Real.rpow D (1 + ν) :=
  rfl

end
