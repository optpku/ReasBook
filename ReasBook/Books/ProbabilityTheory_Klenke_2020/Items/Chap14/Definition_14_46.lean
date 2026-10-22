/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_32

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped MeasureTheory Topology

universe u v

section

variable {I : Type v} [AddSemigroup I]
variable {E : Type u} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- Definition 14.46: a family of probability measures indexed by an additive semigroup of times
is a convolution semigroup if the law at time `s + t` is the additive convolution of the laws at
times `s` and `t`. In the textbook this is applied to probability distributions on `ℝ^d`. -/
class IsConvolutionSemigroup (ν : I → ProbabilityMeasure E) : Prop where
  /-- The semigroup law is given by the canonical probability-measure convolution. -/
  convolution_eq :
    ∀ s t : I, ν (s + t) = ν s * ν t

namespace IsConvolutionSemigroup

variable {ν : I → ProbabilityMeasure E}

/-- Coercing the convolution-semigroup law to measures recovers the usual additive convolution
identity for the underlying measures. -/
@[simp] theorem convolution_eq_toMeasure [hν : IsConvolutionSemigroup ν] (s t : I) :
    (ν (s + t) : Measure E) = (ν s : Measure E) ∗ (ν t : Measure E) := by
  simpa using congrArg (fun μ : ProbabilityMeasure E ↦ (μ : Measure E)) (hν.convolution_eq s t)

end IsConvolutionSemigroup

section WithZero

variable [AddMonoid I]

/-- A convolution semigroup with zero starts at the Dirac probability measure at `0`. -/
class IsConvolutionSemigroupWithZero (ν : I → ProbabilityMeasure E) : Prop
    extends IsConvolutionSemigroup ν where
  /-- The time-zero law is the unit for probability-measure convolution. -/
  zero_eq : ν 0 = 1

namespace IsConvolutionSemigroupWithZero

variable {ν : I → ProbabilityMeasure E}

/-- The time-zero law of a convolution semigroup with zero is the Dirac probability measure at
`0`. -/
@[simp] theorem zero_eq_diracProba [hν : IsConvolutionSemigroupWithZero ν] :
    ν 0 = diracProba (0 : E) := by
  simpa using hν.zero_eq

end IsConvolutionSemigroupWithZero

end WithZero

section Continuous

variable [TopologicalSpace E] [OpensMeasurableSpace E]

/-- A convolution semigroup on `[0, ∞)` is continuous if it converges weakly to the Dirac mass at
`0` as `t → 0`. -/
class IsContinuousConvolutionSemigroup (ν : NNReal → ProbabilityMeasure E) : Prop
    extends IsConvolutionSemigroup ν where
  /-- Weak continuity at the origin. -/
  tendsto_zero : Tendsto ν (𝓝 (0 : NNReal)) (𝓝 (diracProba (0 : E)))

namespace IsContinuousConvolutionSemigroup

variable {ν : NNReal → ProbabilityMeasure E}
variable [T2Space (ProbabilityMeasure E)]

/-- A continuous convolution semigroup already has the Dirac probability measure at time `0`. -/
@[simp] theorem zero_eq_diracProba [hν : IsContinuousConvolutionSemigroup ν] :
    ν 0 = diracProba (0 : E) := by
  have h_zero : Tendsto (fun _ : ℕ ↦ ν 0) atTop (𝓝 (ν 0)) := tendsto_const_nhds
  have h_dirac : Tendsto (fun _ : ℕ ↦ ν 0) atTop (𝓝 (diracProba (0 : E))) :=
    hν.tendsto_zero.comp tendsto_const_nhds
  exact tendsto_nhds_unique h_zero h_dirac

/-- The zero-time law of a continuous convolution semigroup is derived, so it canonically yields a
convolution semigroup with zero. -/
instance toIsConvolutionSemigroupWithZero [hν : IsContinuousConvolutionSemigroup ν] :
    IsConvolutionSemigroupWithZero ν where
  toIsConvolutionSemigroup := hν.toIsConvolutionSemigroup
  zero_eq := by
    simp only [zero_eq_diracProba, ProbabilityMeasure.one_eq_diracProba]

end IsContinuousConvolutionSemigroup

end Continuous

/-- A one-dimensional convolution semigroup is nonnegative if each of its time marginals gives zero
mass to the negative half-line `(-∞, 0)`. -/
class IsNonnegativeConvolutionSemigroup (ν : I → ProbabilityMeasure ℝ) : Prop
    extends IsConvolutionSemigroup ν where
  /-- Each marginal is supported in `[0, ∞)`. -/
  measure_Iio_zero : ∀ t : I, (ν t : Measure ℝ) (Set.Iio 0) = 0

end
