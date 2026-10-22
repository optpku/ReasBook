/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/- Definition 5.1 (1): For an integrable real random variable, the textbook expectation or mean
`𝔼[X] = ∫ X dP` is the canonical Bochner integral, written in Lean as `μ[X] = ∫ ω, X ω ∂μ`. -/
recall MeasureTheory.integral

/-- A real random variable is centered if it is integrable and its expectation is zero. -/
def IsCentered (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Integrable X μ ∧ μ[X] = 0

/- Definition 5.1 (2): The textbook kth moment `m_k = 𝔼[X^k]` is the canonical moment
`ProbabilityTheory.moment X k μ = μ[X ^ k]`; the kth absolute moment is the expectation of
`|X|^k`. -/
recall ProbabilityTheory.moment

/-- The kth absolute moment of a real random variable. -/
def absoluteMoment (X : Ω → ℝ) (k : ℕ) (μ : Measure Ω) : ℝ :=
  moment (fun ω ↦ |X ω|) k μ

/-- The kth absolute moment is the expectation of `|X|^k`. -/
theorem absoluteMoment_eq_expectation_abs_pow (X : Ω → ℝ) (k : ℕ) (μ : Measure Ω) :
    absoluteMoment X k μ = μ[fun ω ↦ |X ω| ^ k] := by
  simp [absoluteMoment, moment_def]

/- Definition 5.1 (3): The textbook variance is the canonical quantity `Var[X; μ]`. -/
recall ProbabilityTheory.variance

/- On a probability space and for square-integrable `X`, mathlib also provides the textbook formula
`Var[X; μ] = μ[X ^ 2] - μ[X] ^ 2`. -/
recall ProbabilityTheory.variance_eq_sub

/-- The standard deviation of a real random variable is the square root of its variance. -/
def standardDeviation (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  Real.sqrt (Var[X; μ])

/- Definition 5.1 (4): The textbook covariance is the canonical quantity `cov[X, Y; μ] =
∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ`; two square-integrable random variables are uncorrelated when
this covariance is zero. -/
recall ProbabilityTheory.covariance

/-- Two real random variables are uncorrelated if they are square integrable and their covariance
vanishes. -/
def IsUncorrelated (X Y : Ω → ℝ) (μ : Measure Ω) : Prop :=
  MemLp X 2 μ ∧ MemLp Y 2 μ ∧ cov[X, Y; μ] = 0

/-- For square-integrable real random variables, failing to be uncorrelated means that the
covariance is nonzero. -/
theorem not_isUncorrelated_iff {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ¬ IsUncorrelated X Y μ ↔ cov[X, Y; μ] ≠ 0 := by
  simp [IsUncorrelated, hX, hY]
