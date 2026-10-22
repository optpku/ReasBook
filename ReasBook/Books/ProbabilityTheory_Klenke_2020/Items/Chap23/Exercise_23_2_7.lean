/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Lemma_23_9

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Exercise 23.2.7: the positive-parameter filter is nontrivial. -/
private instance positiveParameterFilter_neBot :
    Filter.NeBot (positiveParameterFilter : Filter PositiveParameter) := by
  -- Proof comment: `positiveParameterFilter` is the pullback of the punctured neighborhood filter
  -- at `0`, and that base filter contains the whole positive half-line.
  rw [positiveParameterFilter]
  rw [Filter.comap_neBot_iff_compl_range, Subtype.range_coe]
  intro hcompl
  have hcompl' : Set.Iic (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := by
    simpa [PositiveParameter, Set.compl_Ioi] using hcompl
  have hinter :
      Set.Iic (0 : ℝ) ∩ Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := by
    exact Filter.inter_mem hcompl' (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
  have hinter_eq : Set.Iic (0 : ℝ) ∩ Set.Ioi (0 : ℝ) = (∅ : Set ℝ) := by
    ext x
    simp
  have hempty : (∅ : Set ℝ) ∈ 𝓝[>] (0 : ℝ) := by
    simpa [hinter_eq] using hinter
  have hempty_not : (∅ : Set ℝ) ∉ 𝓝[>] (0 : ℝ) := by
    letI : Filter.NeBot (𝓝[>] (0 : ℝ)) := by infer_instance
    exact Filter.empty_notMem _
  exact hempty_not hempty

/-- Helper for Exercise 23.2.7: coercing a positive parameter to `ℝ` sends the positive-parameter
filter to the right-neighborhood filter at `0`. -/
private theorem map_positiveParameterFilter :
    Filter.map ((↑) : PositiveParameter → ℝ) positiveParameterFilter = 𝓝[>] (0 : ℝ) := by
  -- Proof comment: `positiveParameterFilter` is defined as a comap along the subtype coercion, so
  -- mapping back by that coercion recovers the original right-neighborhood filter.
  rw [positiveParameterFilter]
  refine le_antisymm Filter.map_comap_le ?_
  simpa [PositiveParameter, Subtype.range_coe] using
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))

/-- Helper for Exercise 23.2.7: every interval `(-∞, δ)` with `δ > 0` is a right-neighborhood of
`0`. -/
private theorem Iio_mem_nhdsWithin_right_zero {δ : ℝ} (hδ : 0 < δ) :
    Set.Iio δ ∈ 𝓝[>] (0 : ℝ) := by
  -- Proof comment: `0` lies in `(-∞, δ)`, and intersecting with `Set.Ioi 0` keeps precisely the
  -- punctured interval `(0, δ)`.
  refine mem_nhdsWithin.2 ?_
  refine ⟨Set.Iio δ, isOpen_Iio, ?_, ?_⟩
  · simpa using hδ
  · intro x hx
    exact hx.1

private def rescaledWalkTime (ε : PositiveParameter) : NNReal :=
  Real.toNNReal ε⁻¹

/-- The rescaled position map `ω ↦ ε X_{1 / ε}(ω)` of the continuous-time symmetric walk. -/
def continuousTimeSymmetricRandomWalkRescaled
    (X : NNReal → Ω → ℤ) (ε : PositiveParameter) : Ω → ℝ :=
  fun ω ↦ ε * (X (rescaledWalkTime ε) ω : ℝ)

/-- The increment law at time `t` of the continuous-time symmetric random walk on `ℤ`, realized as
the difference of two independent Poisson variables with common parameter `t / 2`. -/
def continuousTimeSymmetricRandomWalkIncrementLaw (t : NNReal) : ProbabilityMeasure ℤ :=
  ⟨((poissonPMF (t / 2)).bind fun n ↦
      (poissonPMF (t / 2)).map fun m ↦ (n : ℤ) - m).toMeasure,
    inferInstance⟩

/-- A process on `ℤ` is the continuous-time symmetric random walk when it starts at `0`, has
independent increments, and each increment over `(s,t]` has the canonical symmetric
difference-of-Poisson law with jump rates `1 / 2` to the right and left. -/
class IsContinuousTimeSymmetricRandomWalk
    (μ : Measure Ω) (X : NNReal → Ω → ℤ) : Prop where
  /-- The walk is a stochastic process. -/
  stochastic : IsStochasticProcess X
  /-- The walk starts from the origin. -/
  zero : X 0 = 0
  /-- The walk has independent increments. -/
  indepIncrements : HasIndepIncrements X μ
  /-- The increment over `(s,t]` has the canonical symmetric continuous-time random-walk law. -/
  increment_law :
    ∀ ⦃s t : NNReal⦄, s ≤ t →
      HasLaw
        (fun ω ↦ X t ω - X s ω)
        (continuousTimeSymmetricRandomWalkIncrementLaw (t - s))
        μ

namespace IsContinuousTimeSymmetricRandomWalk

/-- Every time slice of a continuous-time symmetric random walk is measurable. -/
theorem measurable
    {μ : Measure Ω} {X : NNReal → Ω → ℤ}
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) (t : NNReal) :
    Measurable (X t) :=
  hX.stochastic t

/-- The increment law forces the underlying measure of a continuous-time symmetric random walk to
be a probability measure. -/
theorem isProbabilityMeasure
    {μ : Measure Ω} {X : NNReal → Ω → ℤ}
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) :
    IsProbabilityMeasure μ := by
  exact (hX.increment_law (show (0 : NNReal) ≤ 1 by norm_num)).isProbabilityMeasure

end IsContinuousTimeSymmetricRandomWalk

/-- The rescaled position map `ω ↦ ε X_{1 / ε}(ω)` is measurable when the coordinate maps of `X`
are measurable. -/
theorem measurable_continuousTimeSymmetricRandomWalkRescaled
    (X : NNReal → Ω → ℤ) (hXmeas : ∀ t, Measurable (X t)) (ε : PositiveParameter) :
    Measurable (continuousTimeSymmetricRandomWalkRescaled X ε) := by
  have hcast : Measurable (fun z : ℤ ↦ (z : ℝ)) :=
    measurable_of_countable (fun z : ℤ ↦ (z : ℝ))
  simpa [continuousTimeSymmetricRandomWalkRescaled] using
    measurable_const.mul (hcast.comp <| hXmeas (rescaledWalkTime ε))

/-- The law family `ε ↦ P_{ε X_{1/ε}}` of the rescaled continuous-time walk on the positive
parameter space `ε > 0`, built from the source-facing owner
`IsContinuousTimeSymmetricRandomWalk μ X`. -/
def continuousTimeSymmetricRandomWalkRescaledLaw
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) :
    PositiveProbabilityFamily ℝ :=
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  fun ε ↦
    ProbabilityMeasure.map ⟨μ, inferInstance⟩
      (measurable_continuousTimeSymmetricRandomWalkRescaled X hX.measurable ε).aemeasurable

/-- The candidate good rate function
`x ↦ 1 + x arsinh(x) - sqrt (1 + x^2)`, viewed as an `ℝ≥0∞`-valued map. -/
def continuousTimeSymmetricRandomWalkRateFunction (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 + x * Real.arsinh x - Real.sqrt (1 + x ^ (2 : ℕ)))

-- Proof sketch: unfold `continuousTimeSymmetricRandomWalkRescaledLaw`; it is the pushforward of
-- `P` by the map `ω ↦ ε * X_(1 / ε)(ω)` with the chapter's `NNReal` time parameter
-- `rescaledWalkTime ε`.
/-- Expanding `continuousTimeSymmetricRandomWalkRescaledLaw` gives the pushforward law of the
rescaled position `ε X_{1/ε}`. -/
theorem continuousTimeSymmetricRandomWalkRescaledLaw_def
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) (ε : PositiveParameter) :
    continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε =
      ProbabilityMeasure.map ⟨μ, hX.isProbabilityMeasure⟩
        (measurable_continuousTimeSymmetricRandomWalkRescaled X hX.measurable ε).aemeasurable := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  rfl

-- Proof sketch: unfold `continuousTimeSymmetricRandomWalkRateFunction`; this is exactly the
-- explicit formula displayed in the exercise, rewritten as an `ℝ≥0∞`-valued map.
/-- Expanding `continuousTimeSymmetricRandomWalkRateFunction` gives the explicit textbook formula
`x ↦ 1 + x arsinh(x) - sqrt (1 + x^2)`. -/
theorem continuousTimeSymmetricRandomWalkRateFunction_def (x : ℝ) :
    continuousTimeSymmetricRandomWalkRateFunction x =
      ENNReal.ofReal (1 + x * Real.arsinh x - Real.sqrt (1 + x ^ (2 : ℕ))) := rfl

/-- Helper for Exercise 23.2.7: the real-valued branch of the displayed rate formula. -/
private def continuousTimeSymmetricRandomWalkRateReal (x : ℝ) : ℝ :=
  1 + x * Real.arsinh x - Real.sqrt (1 + x ^ (2 : ℕ))

/-- Helper for Exercise 23.2.7: the real branch of the rate is continuous on `ℝ`. -/
private theorem continuousTimeSymmetricRandomWalkRateReal_continuous :
    Continuous continuousTimeSymmetricRandomWalkRateReal := by
  -- Proof comment: the branch is assembled from continuous arithmetic operations, `arsinh`,
  -- and the real square root.
  simpa [continuousTimeSymmetricRandomWalkRateReal] using
    (continuous_const.add (continuous_id.mul Real.continuous_arsinh)).sub
      (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2)))

/-- Helper for Exercise 23.2.7: the derivative of the real branch simplifies to `arsinh`. -/
private theorem hasDerivAt_continuousTimeSymmetricRandomWalkRateReal (x : ℝ) :
    HasDerivAt continuousTimeSymmetricRandomWalkRateReal (Real.arsinh x) x := by
  -- Proof comment: differentiate `x * arsinh x` and `sqrt (1 + x^2)` separately, then cancel the
  -- identical `x / √(1 + x^2)` terms.
  have hmulBase := (Real.hasDerivAt_arsinh x).mul (hasDerivAt_id x)
  have hone :
      HasDerivAt (fun y : ℝ ↦ 1 + y ^ (2 : ℕ)) (2 * x) x := by
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using
      ((hasDerivAt_id x).pow 2).const_add 1
  have hsq :
      HasDerivAt (fun y : ℝ ↦ Real.sqrt (1 + y ^ (2 : ℕ)))
        (x * (Real.sqrt (1 + x ^ (2 : ℕ)))⁻¹) x := by
    have hne : 1 + x ^ (2 : ℕ) ≠ 0 := by
      nlinarith [sq_nonneg x]
    have hsq' :
        HasDerivAt (fun y : ℝ ↦ Real.sqrt (1 + y ^ (2 : ℕ)))
          ((2 * x) / (2 * Real.sqrt (1 + x ^ (2 : ℕ)))) x := by
      exact hone.sqrt hne
    convert hsq' using 1 <;> ring
  convert ((hasDerivAt_const x (1 : ℝ)).add hmulBase).sub hsq using 1
  · ext y
    simp [Pi.mul_apply, continuousTimeSymmetricRandomWalkRateReal, div_eq_mul_inv, one_mul,
      sub_eq_add_neg, pow_two, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
      add_assoc]
  · simp [id, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- Helper for Exercise 23.2.7: the real branch is an even function. -/
private theorem continuousTimeSymmetricRandomWalkRateReal_even (x : ℝ) :
    continuousTimeSymmetricRandomWalkRateReal (-x) =
      continuousTimeSymmetricRandomWalkRateReal x := by
  -- Proof comment: both contributions `x * arsinh x` and `√(1 + x^2)` are even.
  simp [continuousTimeSymmetricRandomWalkRateReal, Real.arsinh_neg]

/-- Helper for Exercise 23.2.7: once `x` is past the threshold `sinh 2`, the real branch dominates
the identity function. -/
private theorem continuousTimeSymmetricRandomWalkRateReal_ge_of_ge_sinh_two {x : ℝ}
    (hx : Real.sinh 2 ≤ x) :
    x ≤ continuousTimeSymmetricRandomWalkRateReal x := by
  -- Proof comment: `arsinh` is increasing, so the tail hypothesis gives `arsinh x ≥ 2`, while
  -- `√(1 + x^2) ≤ x + 1` is the elementary quadratic bound on the square-root term.
  have hxnonneg : 0 ≤ x := le_trans (by positivity) hx
  have harsinh_ge : 2 ≤ Real.arsinh x := by
    simpa using (Real.arsinh_le_arsinh).2 hx
  have hmul : 2 * x ≤ x * Real.arsinh x := by
    have := mul_le_mul_of_nonneg_left harsinh_ge hxnonneg
    nlinarith
  have hsqrt_le : Real.sqrt (1 + x ^ (2 : ℕ)) ≤ x + 1 := by
    refine Real.sqrt_le_iff.mpr ?_
    constructor
    · linarith
    · nlinarith [sq_nonneg x]
  rw [continuousTimeSymmetricRandomWalkRateReal]
  linarith

/-- Helper for Exercise 23.2.7: outside the compact core `|x| < sinh 2`, the real branch
dominates `|x|`. -/
private theorem continuousTimeSymmetricRandomWalkRateReal_ge_abs_of_abs_ge_sinh_two {x : ℝ}
    (hx : Real.sinh 2 ≤ |x|) :
    |x| ≤ continuousTimeSymmetricRandomWalkRateReal x := by
  -- Proof comment: on the positive side `|x| = x`; on the negative side rewrite `|x| = -x` and
  -- use the evenness of the rate to reduce to the positive-tail estimate.
  by_cases hxnonneg : 0 ≤ x
  · simpa [abs_of_nonneg hxnonneg] using
      continuousTimeSymmetricRandomWalkRateReal_ge_of_ge_sinh_two
        (x := x) (by simpa [abs_of_nonneg hxnonneg] using hx)
  · have hxneg : x < 0 := lt_of_not_ge hxnonneg
    simpa [abs_of_neg hxneg, continuousTimeSymmetricRandomWalkRateReal_even x] using
      continuousTimeSymmetricRandomWalkRateReal_ge_of_ge_sinh_two
        (x := -x) (by simpa [abs_of_neg hxneg] using hx)

/-- Helper for Exercise 23.2.7: the explicit rate branch is monotone on the nonnegative ray. -/
private theorem continuousTimeSymmetricRandomWalkRateReal_monotoneOn_nonneg :
    MonotoneOn continuousTimeSymmetricRandomWalkRateReal (Set.Ici 0) := by
  -- Proof comment: on `Ici 0`, the derivative is `arsinh`, and `arsinh x` is nonnegative exactly
  -- when `x` is nonnegative.
  refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    continuousTimeSymmetricRandomWalkRateReal_continuous.continuousOn
    (fun x _ ↦ by
      have hdiff : DifferentiableAt ℝ continuousTimeSymmetricRandomWalkRateReal x :=
        (hasDerivAt_continuousTimeSymmetricRandomWalkRateReal x).differentiableAt
      exact hdiff.differentiableWithinAt) ?_
  intro x hx
  rw [interior_Ici, Set.mem_Ioi] at hx
  rw [(hasDerivAt_continuousTimeSymmetricRandomWalkRateReal x).deriv]
  exact (Real.arsinh_nonneg_iff).2 (le_of_lt hx)

/-- Helper for Exercise 23.2.7: every finite sublevel of the rate function is contained in a
compact interval cut out by the tail estimate. -/
private theorem continuousTimeSymmetricRandomWalkRateFunction_compactSublevel :
    (a : NNReal) → IsCompact (continuousTimeSymmetricRandomWalkRateFunction ⁻¹' Set.Iic (a : ENNReal)) := by
  intro a
  let B : ℝ := max (a : ℝ) (Real.sinh 2)
  have hcont :
      Continuous continuousTimeSymmetricRandomWalkRateFunction := by
    simpa [continuousTimeSymmetricRandomWalkRateFunction, continuousTimeSymmetricRandomWalkRateReal]
      using (ENNReal.continuous_ofReal.comp continuousTimeSymmetricRandomWalkRateReal_continuous)
  have hsubset :
      continuousTimeSymmetricRandomWalkRateFunction ⁻¹' Set.Iic (a : ENNReal) ⊆ Set.Icc (-B) B := by
    intro x hx
    have hxrate : continuousTimeSymmetricRandomWalkRateFunction x ≤ (a : ENNReal) := by
      simpa [Set.mem_preimage] using hx
    have hreal : continuousTimeSymmetricRandomWalkRateReal x ≤ (a : ℝ) := by
      simpa [continuousTimeSymmetricRandomWalkRateFunction, continuousTimeSymmetricRandomWalkRateReal]
        using (ENNReal.ofReal_le_coe.mp hxrate)
    have habs_le : |x| ≤ B := by
      by_cases htail : Real.sinh 2 ≤ |x|
      · exact (le_trans
          (continuousTimeSymmetricRandomWalkRateReal_ge_abs_of_abs_ge_sinh_two htail) hreal).trans
            (le_max_left _ _)
      · exact (lt_of_not_ge htail).le.trans (le_max_right _ _)
    exact abs_le.mp habs_le
  -- Proof comment: the rate is continuous, so the sublevel set is closed; the tail estimate keeps
  -- it inside one compact interval.
  exact (isCompact_Icc : IsCompact (Set.Icc (-B) B)).of_isClosed_subset
    (IsClosed.preimage hcont isClosed_Iic) hsubset

-- Proof sketch: the real-valued branch is continuous and coercive, so the `ℝ≥0∞`-valued rate
-- function is lower semicontinuous and its finite sublevel sets are compact in `ℝ`.
/-- The explicit rate function of the rescaled continuous-time symmetric walk is a good rate
function on `ℝ`. -/
instance continuousTimeSymmetricRandomWalkRateFunction_isGoodRateFunction :
    IsGoodRateFunction continuousTimeSymmetricRandomWalkRateFunction := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the displayed rate function is the `ENNReal.ofReal` image of a continuous
    -- real branch, hence lower semicontinuous.
    exact
      Continuous.lowerSemicontinuous <|
        by
          simpa [continuousTimeSymmetricRandomWalkRateFunction,
            continuousTimeSymmetricRandomWalkRateReal] using
            (ENNReal.continuous_ofReal.comp continuousTimeSymmetricRandomWalkRateReal_continuous)
  · -- Proof comment: the compact-sublevel helper packages both the continuity and the tail bound.
    intro a
    exact continuousTimeSymmetricRandomWalkRateFunction_compactSublevel a

-- Proof sketch: compute the second derivative of the real-valued branch
-- `x ↦ 1 + x arsinh(x) - sqrt (1 + x^2)` as `(1 + x^2)^(-1/2)`, which is nonnegative on `ℝ`,
-- and conclude convexity on the whole line.
/-- The finite real-valued branch of the rate function is convex on `ℝ`. -/
theorem continuousTimeSymmetricRandomWalkRateFunction_convex :
    ConvexOn ℝ univ
      (fun x : ℝ ↦ 1 + x * Real.arsinh x - Real.sqrt (1 + x ^ (2 : ℕ))) := by
  -- Proof comment: the derivative of the branch is `arsinh`, and `arsinh` is monotone on `ℝ`,
  -- so the branch is convex by the standard derivative criterion.
  have hdiff : Differentiable ℝ continuousTimeSymmetricRandomWalkRateReal := by
    intro x
    exact (hasDerivAt_continuousTimeSymmetricRandomWalkRateReal x).differentiableAt
  have hmono : Monotone (deriv continuousTimeSymmetricRandomWalkRateReal) := by
    intro x y hxy
    rw [(hasDerivAt_continuousTimeSymmetricRandomWalkRateReal x).deriv,
      (hasDerivAt_continuousTimeSymmetricRandomWalkRateReal y).deriv]
    exact (Real.arsinh_le_arsinh).2 hxy
  simpa [continuousTimeSymmetricRandomWalkRateReal] using hmono.convexOn_univ_of_deriv hdiff

/-- Helper for Exercise 23.2.7: the explicit rate branch is the affine tilt cost at the optimizer
`t = arsinh x`. -/
private theorem continuousTimeSymmetricRandomWalkRateReal_eq_affineAtArsinh (x : ℝ) :
    continuousTimeSymmetricRandomWalkRateReal x =
      Real.arsinh x * x - (Real.cosh (Real.arsinh x) - 1) := by
  -- Proof comment: substitute the hyperbolic identity
  -- `cosh (arsinh x) = sqrt (1 + x^2)` into the displayed branch formula.
  rw [continuousTimeSymmetricRandomWalkRateReal]
  ring_nf
  rw [Real.cosh_arsinh]

/-- Helper for Exercise 23.2.7: the one-time marginal `X t` of a continuous-time symmetric random
walk has the canonical difference-of-Poisson increment law at time `t`. -/
private theorem continuousTimeSymmetricRandomWalk_timeSliceLaw
    {μ : Measure Ω} {X : NNReal → Ω → ℤ}
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) (t : NNReal) :
    HasLaw (X t) (continuousTimeSymmetricRandomWalkIncrementLaw t) μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  -- Proof comment: specialize the increment law to the interval `(0, t]` and rewrite the start
  -- point `X 0` to `0`.
  simpa [hX.zero] using
    (show
      HasLaw
        (fun ω ↦ X t ω - X 0 ω)
        (continuousTimeSymmetricRandomWalkIncrementLaw (t - 0))
        μ from
      hX.increment_law (show (0 : NNReal) ≤ t from bot_le))

/-- Helper for Exercise 23.2.7: the rescaled time parameter `rescaledWalkTime ε` is exactly the
positive reciprocal `ε⁻¹` on the real line. -/
private theorem rescaledWalkTime_coe (ε : PositiveParameter) :
    ((rescaledWalkTime ε : NNReal) : ℝ) = (ε : ℝ)⁻¹ := by
  -- Proof comment: `rescaledWalkTime` is defined by `Real.toNNReal` applied to a nonnegative
  -- reciprocal.
  have hε_nonneg : 0 ≤ (ε : ℝ)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt ε.2)
  simp [rescaledWalkTime, Real.toNNReal_of_nonneg hε_nonneg]

/-- Helper for Exercise 23.2.7: the rescaled one-time law is the pushforward of the canonical
increment law at time `1 / ε` by the scaling map `z ↦ ε z`. -/
private theorem continuousTimeSymmetricRandomWalkRescaledLaw_eq_map_incrementLaw
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) (ε : PositiveParameter) :
    (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ) =
      ((continuousTimeSymmetricRandomWalkIncrementLaw (rescaledWalkTime ε) : Measure ℤ).map
        (fun z : ℤ ↦ ε * (z : ℝ))) := by
  have hscaleMeas : Measurable (fun z : ℤ ↦ ε * (z : ℝ)) := by
    have hcast : Measurable (fun z : ℤ ↦ (z : ℝ)) :=
      measurable_of_countable (fun z : ℤ ↦ (z : ℝ))
    simpa using measurable_const.mul hcast
  have hscaleLaw :
      HasLaw
        (fun z : ℤ ↦ ε * (z : ℝ))
        (((continuousTimeSymmetricRandomWalkIncrementLaw (rescaledWalkTime ε) : Measure ℤ).map
          (fun z : ℤ ↦ ε * (z : ℝ))) : Measure ℝ)
        (continuousTimeSymmetricRandomWalkIncrementLaw (rescaledWalkTime ε) : Measure ℤ) := by
    exact ⟨hscaleMeas.aemeasurable, rfl⟩
  have hrescaledLaw :
      HasLaw
        (continuousTimeSymmetricRandomWalkRescaled X ε)
        (((continuousTimeSymmetricRandomWalkIncrementLaw (rescaledWalkTime ε) : Measure ℤ).map
          (fun z : ℤ ↦ ε * (z : ℝ))) : Measure ℝ)
        μ := by
    -- Proof comment: compose the canonical one-time marginal law with the deterministic scaling
    -- map on `ℤ`.
    simpa [continuousTimeSymmetricRandomWalkRescaled, Function.comp] using
      HasLaw.comp hscaleLaw (continuousTimeSymmetricRandomWalk_timeSliceLaw hX (rescaledWalkTime ε))
  -- Proof comment: compare the two pushforward descriptions of the same rescaled random variable.
  rw [continuousTimeSymmetricRandomWalkRescaledLaw_def]
  simpa using hrescaledLaw.map_eq

/-- Helper for Exercise 23.2.7: the moment-generating function of the rescaled law can be computed
from the canonical increment law at time `1 / ε` through the scaling map `z ↦ ε z`. -/
private theorem continuousTimeSymmetricRandomWalkRescaledLaw_mgf_eq_incrementLaw
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    (ε : PositiveParameter) (s : ℝ) :
    mgf id (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε) s =
      mgf (fun z : ℤ ↦ ε * (z : ℝ))
        (continuousTimeSymmetricRandomWalkIncrementLaw (rescaledWalkTime ε)) s := by
  have hscaleMeas :
      AEMeasurable (fun z : ℤ ↦ ε * (z : ℝ))
        (continuousTimeSymmetricRandomWalkIncrementLaw (rescaledWalkTime ε) : Measure ℤ) := by
    have hcast : Measurable (fun z : ℤ ↦ (z : ℝ)) :=
      measurable_of_countable (fun z : ℤ ↦ (z : ℝ))
    simpa using (measurable_const.mul hcast).aemeasurable
  -- Proof comment: once the rescaled law is rewritten as a pushforward, `mgf_id_map` turns the
  -- moment-generating function into the one for the scaled increment random variable.
  rw [continuousTimeSymmetricRandomWalkRescaledLaw_eq_map_incrementLaw μ X hX ε]
  simpa using
    congrFun
      (ProbabilityTheory.mgf_id_map
        (μ := (continuousTimeSymmetricRandomWalkIncrementLaw (rescaledWalkTime ε) : Measure ℤ))
        (X := fun z : ℤ ↦ ε * (z : ℝ))
        hscaleMeas)
      s

/-- Helper for Exercise 23.2.7: if two `ℕ`-indexed families are independently distributed as
sequence-valued random elements and each family is internally independent, then the paired family
is independent as well. -/
private theorem iIndepFun_pair_of_iIndepFun_of_indepFun
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (Y : ℕ → Ω → β)
    (hX_iIndep : iIndepFun X μ)
    (hX_meas : ∀ n, AEMeasurable (X n) μ)
    (hY_iIndep : iIndepFun Y μ)
    (hY_meas : ∀ n, AEMeasurable (Y n) μ)
    (hSeq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ Y n ω) μ) :
    iIndepFun (fun n ω ↦ (X n ω, Y n ω)) μ := by
  -- Proof comment: reduce to each finite index set, use the sequence-valued independence to
  -- obtain independence of the restricted tuples, and then rewrite the tuple law as a product of
  -- the two product laws.
  rw [iIndepFun_iff_finset]
  intro s
  have hX_restrict' : iIndepFun (fun i : s ↦ X i) μ :=
    hX_iIndep.precomp Subtype.val_injective
  have hX_restrict : iIndepFun (s.restrict X) μ := by
    simpa [Finset.restrict] using hX_restrict'
  have hY_restrict' : iIndepFun (fun i : s ↦ Y i) μ :=
    hY_iIndep.precomp Subtype.val_injective
  have hY_restrict : iIndepFun (s.restrict Y) μ := by
    simpa [Finset.restrict] using hY_restrict'
  rw [iIndepFun_iff_map_fun_eq_pi_map]
  · change μ.map (fun ω (i : s) ↦ (X i ω, Y i ω)) =
      Measure.pi (fun i : s ↦ μ.map (fun ω ↦ (X i ω, Y i ω)))
    let φ : (ℕ → α) → (s → α) := fun f i ↦ f i
    let ψ : (ℕ → β) → (s → β) := fun f i ↦ f i
    have hRestrict_indep :
        IndepFun (fun ω (i : s) ↦ X i ω) (fun ω (i : s) ↦ Y i ω) μ := by
      have hφ : Measurable φ := by
        fun_prop
      have hψ : Measurable ψ := by
        fun_prop
      simpa [φ, ψ] using hSeq_indep.comp hφ hψ
    have hMap_eq :
        μ.map (fun ω ↦ (fun i : s ↦ X i ω, fun i : s ↦ Y i ω)) =
          (Measure.pi fun i : s ↦ μ.map (X i)).prod
            (Measure.pi fun i : s ↦ μ.map (Y i)) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map
        (aemeasurable_pi_lambda _ fun i : s ↦ hX_meas i)
        (aemeasurable_pi_lambda _ fun i : s ↦ hY_meas i)).mp hRestrict_indep,
        (iIndepFun_iff_map_fun_eq_pi_map fun i : s ↦ hX_meas i).mp hX_restrict,
        (iIndepFun_iff_map_fun_eq_pi_map fun i : s ↦ hY_meas i).mp hY_restrict]
    have hPair_map_eq (i : s) :
        μ.map (fun ω ↦ (X i ω, Y i ω)) = (μ.map (X i)).prod (μ.map (Y i)) := by
      have hPair_indep : X i ⟂ᵢ[μ] Y i := by
        simpa using hSeq_indep.comp (measurable_pi_apply (i : ℕ)) (measurable_pi_apply (i : ℕ))
      rw [(indepFun_iff_map_prod_eq_prod_map_map (hX_meas i) (hY_meas i)).mp hPair_indep]
    let e := MeasurableEquiv.arrowProdEquivProdArrow α β s
    have hPair_aemeas :
        AEMeasurable (fun ω (i : s) ↦ (X i ω, Y i ω)) μ :=
      aemeasurable_pi_lambda _ fun i : s ↦ (hX_meas i).prodMk (hY_meas i)
    rw [← e.map_measurableEquiv_injective.eq_iff]
    rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hPair_aemeas]
    change μ.map (fun ω ↦ (fun i : s ↦ X i ω, fun i : s ↦ Y i ω)) =
      Measure.map e (Measure.pi (fun i : s ↦ μ.map (fun ω ↦ (X i ω, Y i ω))))
    refine hMap_eq.trans ?_
    symm
    calc
      Measure.map e (Measure.pi fun i : s ↦ μ.map (fun ω ↦ (X i ω, Y i ω))) =
          Measure.map e (Measure.pi fun i : s ↦ (μ.map (X i)).prod (μ.map (Y i))) := by
            simp [hPair_map_eq]
      _ = (Measure.pi fun i : s ↦ μ.map (X i)).prod (Measure.pi fun i : s ↦ μ.map (Y i)) :=
        (measurePreserving_arrowProdEquivProdArrow α β s
          (fun i : s ↦ μ.map (X i)) (fun i : s ↦ μ.map (Y i))).map_eq
  · intro i
    exact (hX_meas i).prodMk (hY_meas i)

/-- Helper for Exercise 23.2.7: the canonical increment law is the convolution of the integer-cast
Poisson law with its reflected copy. -/
private theorem continuousTimeSymmetricRandomWalkIncrementLaw_eq_productPushforward
    (t : NNReal) :
    (continuousTimeSymmetricRandomWalkIncrementLaw t : Measure ℤ) =
      Measure.map (fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2)
        ((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2))) := by
  -- Proof comment: on the countable target `ℤ`, it is enough to compare singleton masses. The
  -- `bind` definition gives the outer sum over the first Poisson variable, while the product
  -- measure gives the same sum through `Measure.prod_apply` and `lintegral_countable'`.
  classical
  refine Measure.ext_of_singleton fun z ↦ ?_
  have hdiff : Measurable (fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2) := measurable_of_countable _
  change
    (((poissonPMF (t / 2)).bind fun n ↦
        (poissonPMF (t / 2)).map fun m ↦ (n : ℤ) - m).toMeasure) ({z} : Set ℤ) =
      (Measure.map (fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2)
        ((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2)))) ({z} : Set ℤ)
  rw [PMF.toMeasure_bind_apply (p := poissonPMF (t / 2))
    (f := fun n ↦ (poissonPMF (t / 2)).map fun m ↦ (n : ℤ) - m)
    (s := ({z} : Set ℤ)) (measurableSet_singleton z)]
  rw [Measure.map_apply hdiff (measurableSet_singleton z)]
  rw [Measure.prod_apply
    (μ := poissonMeasure (t / 2)) (ν := poissonMeasure (t / 2))
    (s := (fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2) ⁻¹' ({z} : Set ℤ))
    (measurableSet_preimage hdiff (measurableSet_singleton z))]
  rw [MeasureTheory.lintegral_countable'
    (μ := poissonMeasure (t / 2))
    (f := fun n : ℕ ↦
      poissonMeasure (t / 2)
        (Prod.mk n ⁻¹' ((fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2) ⁻¹' ({z} : Set ℤ))))]
  refine tsum_congr fun n ↦ ?_
  have hpre :
      Prod.mk n ⁻¹' ((fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2) ⁻¹' ({z} : Set ℤ)) =
        (fun m : ℕ ↦ (n : ℤ) - m) ⁻¹' ({z} : Set ℤ) := by
    ext m
    simp
  have hinner :
      PMF.map (fun m : ℤ ↦ (n : ℤ) - m) (do
          let a ← poissonPMF (t / 2)
          pure (a : ℤ)) =
        (poissonPMF (t / 2)).map (fun m : ℕ ↦ (n : ℤ) - m) := by
    simpa [PMF.monad_map_eq_map, Function.comp_def] using
      (PMF.map_comp
        (p := poissonPMF (t / 2))
        (f := fun a : ℕ ↦ (a : ℤ))
        (g := fun m : ℤ ↦ (n : ℤ) - m))
  rw [hpre]
  rw [mul_comm]
  rw [hinner]
  congr 1
  · simpa [poissonMeasure] using
      (PMF.toMeasure_map_apply
        (p := poissonPMF (t / 2))
        (f := fun m : ℕ ↦ (n : ℤ) - m)
        (s := ({z} : Set ℤ))
        (hf := measurable_of_countable _)
        (hs := measurableSet_singleton z))
  · simpa [poissonMeasure] using
      (PMF.toMeasure_apply_singleton
        (poissonPMF (t / 2)) n (measurableSet_singleton n)).symm

/-- Helper for Exercise 23.2.7: the canonical increment law is the convolution of the integer-cast
Poisson law with its reflected copy. -/
private theorem continuousTimeSymmetricRandomWalkIncrementLaw_eq_conv_map_neg
    (t : NNReal) :
    (continuousTimeSymmetricRandomWalkIncrementLaw t : Measure ℤ) =
      (poissonMeasure (t / 2)).map (fun n : ℕ ↦ (n : ℤ)) ∗
        ((poissonMeasure (t / 2)).map (fun n : ℕ ↦ -(n : ℤ))) := by
  -- Proof comment: rewrite `(n, m) ↦ n - m` as addition after mapping the product measure through
  -- `(n, m) ↦ ((n : ℤ), -(m : ℤ))`, then unfold additive convolution.
  rw [continuousTimeSymmetricRandomWalkIncrementLaw_eq_productPushforward]
  calc
    Measure.map (fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2)
        ((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2))) =
      Measure.map (fun p : ℤ × ℤ ↦ p.1 + p.2)
        (((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2))).map
          (Prod.map (fun n : ℕ ↦ (n : ℤ)) (fun n : ℕ ↦ -(n : ℤ)))) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ =
      Measure.map (fun p : ℤ × ℤ ↦ p.1 + p.2)
        (((poissonMeasure (t / 2)).map (fun n : ℕ ↦ (n : ℤ))).prod
          ((poissonMeasure (t / 2)).map (fun n : ℕ ↦ -(n : ℤ)))) := by
            congr 1
            simpa using
              (Measure.map_prod_map
                (μa := poissonMeasure (t / 2)) (μc := poissonMeasure (t / 2))
                (f := fun n : ℕ ↦ (n : ℤ))
                (g := fun n : ℕ ↦ -(n : ℤ))
                (by fun_prop) (by fun_prop)).symm
    _ =
      (poissonMeasure (t / 2)).map (fun n : ℕ ↦ (n : ℤ)) ∗
        ((poissonMeasure (t / 2)).map (fun n : ℕ ↦ -(n : ℤ))) := by
          rfl

/-- Helper for Exercise 23.2.7: singleton masses of `poissonMeasure r` are the explicit Poisson
weights `poissonPMFReal r n`. -/
private theorem poissonMeasure_apply_singleton_eq (r : NNReal) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Proof comment: rewrite `poissonMeasure` as the measure attached to the canonical Poisson pmf.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Exercise 23.2.7: a summable singleton-mass weighted norm series on `ℕ` yields an
integrable function for the corresponding finite measure. -/
private theorem integrable_natMeasure_of_summableNorm (μ : Measure ℕ) [IsFiniteMeasure μ]
    (f : ℕ → ℝ) (hf : Summable (fun n : ℕ ↦ (μ {n}).toReal * ‖f n‖)) :
    Integrable f μ := by
  -- Proof comment: expand the finite measure into singleton atoms and collapse the norm integral
  -- to the assumed summable series.
  refine ⟨(measurable_of_countable f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, ← Measure.sum_smul_dirac (μ := μ), lintegral_sum_measure]
  have hterm :
      (fun n : ℕ ↦ ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ {n} • Measure.dirac n) =
        fun n : ℕ ↦ ENNReal.ofReal ((μ {n}).toReal * ‖f n‖) := by
    funext n
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    have hmass : μ {n} = ENNReal.ofReal (μ {n}).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    calc
      μ {n} * ENNReal.ofReal ‖f n‖ = ENNReal.ofReal (μ {n}).toReal * ENNReal.ofReal ‖f n‖ := by
        simpa using congrArg (fun t : ℝ≥0∞ ↦ t * ENNReal.ofReal ‖f n‖) hmass
      _ = ENNReal.ofReal ((μ {n}).toReal * ‖f n‖) := by
        simpa using (ENNReal.ofReal_mul (p := (μ {n}).toReal) (q := ‖f n‖)
          (norm_nonneg _)).symm
  rw [hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hf]
  simp

/-- Helper for Exercise 23.2.7: the Poisson law cast from `ℕ` to `ℝ` has the exact exponential
moment `exp (λ (e^u - 1))`. -/
private theorem poissonMeasure_realCast_mgf (lam : NNReal) (u : ℝ) :
    mgf (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure lam) u =
      Real.exp ((lam : ℝ) * (Real.exp u - 1)) := by
  have hseries :
      HasSum (fun n : ℕ ↦ Real.exp (-((lam : ℝ))) * (((lam : ℝ) * Real.exp u) ^ n / ↑n.factorial))
        (Real.exp (-((lam : ℝ))) * Real.exp ((lam : ℝ) * Real.exp u)) := by
    simpa [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * Real.exp u)).mul_left
        (Real.exp (-((lam : ℝ))))
  have hsummable :
      Summable (fun n : ℕ ↦
        (poissonMeasure lam {n}).toReal * ‖Real.exp (u * (n : ℝ))‖) := by
    refine hseries.summable.congr ?_
    intro n
    rw [poissonMeasure_apply_singleton_eq]
    rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg, poissonPMFReal]
    have hfac : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm u (n : ℝ), Real.exp_nat_mul, mul_pow]
    field_simp [hfac]
  have hint :
      Integrable (fun n : ℕ ↦ Real.exp (u * (n : ℝ))) (poissonMeasure lam) := by
    exact integrable_natMeasure_of_summableNorm (μ := poissonMeasure lam) _ hsummable
  -- Proof comment: rewrite the Poisson integral as a singleton series and collapse it by the
  -- exponential power series.
  calc
    mgf (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure lam) u
      = ∫ n, Real.exp (u * (n : ℝ)) ∂poissonMeasure lam := by
          rfl
    _ = ∑' n : ℕ, ((poissonMeasure lam) {n}).toReal * Real.exp (u * (n : ℝ)) := by
          simpa [Measure.real, smul_eq_mul] using
            (integral_countable (μ := poissonMeasure lam) hint)
    _ = ∑' n : ℕ, Real.exp (-((lam : ℝ))) * (((lam : ℝ) * Real.exp u) ^ n / ↑n.factorial) := by
          refine tsum_congr fun n ↦ ?_
          rw [poissonMeasure_apply_singleton_eq]
          rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg, poissonPMFReal]
          have hfac : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
          rw [mul_comm u (n : ℝ), Real.exp_nat_mul, mul_pow]
          field_simp [hfac]
    _ = Real.exp (-((lam : ℝ))) * Real.exp ((lam : ℝ) * Real.exp u) := hseries.tsum_eq
    _ = Real.exp ((lam : ℝ) * (Real.exp u - 1)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- Helper for Exercise 23.2.7: the canonical increment law has cumulant-generating function
`u ↦ t (cosh u - 1)`. -/
private theorem continuousTimeSymmetricRandomWalkIncrementLaw_mgf
    (t : NNReal) (u : ℝ) :
    mgf (fun z : ℤ ↦ (z : ℝ)) (continuousTimeSymmetricRandomWalkIncrementLaw t) u =
      Real.exp ((t : ℝ) * (Real.cosh u - 1)) := by
  have hdiff :
      AEMeasurable
        (fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2)
        ((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2))) := by
    exact (measurable_of_countable _).aemeasurable
  have hcast :
      AEStronglyMeasurable
        (fun z : ℤ ↦ Real.exp (u * (z : ℝ)))
        (Measure.map (fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2)
          ((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2)))) := by
    exact (measurable_of_countable _).aestronglyMeasurable
  -- Proof comment: move the mgf through the product-pushforward normal form, factor the kernel
  -- into the right and left Poisson coordinates, and then evaluate the two one-dimensional mgfs.
  rw [continuousTimeSymmetricRandomWalkIncrementLaw_eq_productPushforward]
  calc
    mgf (fun z : ℤ ↦ (z : ℝ))
        (Measure.map (fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2)
          ((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2)))) u
      = mgf (((fun z : ℤ ↦ (z : ℝ)) ∘ fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2))
          ((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2))) u := by
            exact ProbabilityTheory.mgf_map (μ := ((poissonMeasure (t / 2)).prod
              (poissonMeasure (t / 2))))
              (Y := fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2)
              (X := fun z : ℤ ↦ (z : ℝ)) hdiff hcast
    _ = mgf (fun p : ℕ × ℕ ↦ (((p.1 : ℤ) - p.2 : ℤ) : ℝ))
          ((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2))) u := by
            rfl
    _ = ∫ p, Real.exp (u * ((((p.1 : ℤ) - p.2 : ℤ) : ℝ)))
          ∂((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2))) := by
            rfl
    _ = ∫ p, Real.exp (u * (p.1 : ℝ)) * Real.exp ((-u) * (p.2 : ℝ))
          ∂((poissonMeasure (t / 2)).prod (poissonMeasure (t / 2))) := by
            refine integral_congr_ae ?_
            filter_upwards with p
            norm_num [sub_eq_add_neg, mul_add, Real.exp_add, mul_comm, mul_left_comm, mul_assoc]
    _ =
        (∫ n, Real.exp (u * (n : ℝ)) ∂poissonMeasure (t / 2)) *
          ∫ m, Real.exp ((-u) * (m : ℝ)) ∂poissonMeasure (t / 2) := by
            simpa using
              (MeasureTheory.integral_prod_mul
                (μ := poissonMeasure (t / 2))
                (ν := poissonMeasure (t / 2))
                (f := fun n : ℕ ↦ Real.exp (u * (n : ℝ)))
                (g := fun m : ℕ ↦ Real.exp ((-u) * (m : ℝ))))
    _ =
        mgf (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (t / 2)) u *
          mgf (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (t / 2)) (-u) := by
            rfl
    _ =
        Real.exp (((t / 2 : NNReal) : ℝ) * (Real.exp u - 1)) *
          Real.exp (((t / 2 : NNReal) : ℝ) * (Real.exp (-u) - 1)) := by
            rw [poissonMeasure_realCast_mgf (lam := t / 2) (u := u)]
            rw [poissonMeasure_realCast_mgf (lam := t / 2) (u := -u)]
    _ = Real.exp ((((t / 2 : NNReal) : ℝ) * (Real.exp u - 1)) +
          (((t / 2 : NNReal) : ℝ) * (Real.exp (-u) - 1))) := by
            rw [← Real.exp_add]
    _ = Real.exp ((t : ℝ) * (Real.cosh u - 1)) := by
            have hdiv : (t / 2 : NNReal) = t * (1 / 2 : NNReal) := by
              rw [div_eq_mul_inv]
              norm_num
            have hhalfMul : (((t * (1 / 2 : NNReal) : NNReal) : ℝ)) = (t : ℝ) * (1 / 2 : ℝ) := by
              rw [NNReal.coe_mul]
              norm_num
            congr 1
            rw [hdiv, Real.cosh_eq, hhalfMul]
            ring

/-- Helper for Exercise 23.2.7: the canonical increment law has cumulant-generating function
`u ↦ t (cosh u - 1)`. -/
private theorem continuousTimeSymmetricRandomWalkIncrementLaw_cgf
    (t : NNReal) (u : ℝ) :
    cgf (fun z : ℤ ↦ (z : ℝ)) (continuousTimeSymmetricRandomWalkIncrementLaw t) u =
      (t : ℝ) * (Real.cosh u - 1) := by
  -- Proof comment: the previous mgf computation is already an exact exponential, so taking
  -- logarithms yields the cgf immediately.
  rw [cgf, continuousTimeSymmetricRandomWalkIncrementLaw_mgf, Real.log_exp]

/-- Helper for Exercise 23.2.7: the rescaled family has the exact exponential moment obtained by
evaluating the increment-law mgf at the tilted slope `ε u`. -/
private theorem continuousTimeSymmetricRandomWalkRescaledLaw_mgf
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    (ε : PositiveParameter) (u : ℝ) :
    mgf id (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε) u =
      Real.exp ((ε : ℝ)⁻¹ * (Real.cosh ((ε : ℝ) * u) - 1)) := by
  -- Proof comment: rewrite the rescaled law through the canonical increment law and use the
  -- scaling rule `mgf (ε X)(u) = mgf X (ε u)`.
  calc
    mgf id (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε) u
        = mgf (fun z : ℤ ↦ ε * (z : ℝ))
            (continuousTimeSymmetricRandomWalkIncrementLaw (rescaledWalkTime ε)) u := by
              exact continuousTimeSymmetricRandomWalkRescaledLaw_mgf_eq_incrementLaw μ X hX ε u
    _ = mgf (fun z : ℤ ↦ (z : ℝ))
          (continuousTimeSymmetricRandomWalkIncrementLaw (rescaledWalkTime ε)) ((ε : ℝ) * u) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (ProbabilityTheory.mgf_const_mul
                (μ := (continuousTimeSymmetricRandomWalkIncrementLaw (rescaledWalkTime ε) :
                  Measure ℤ))
                (X := fun z : ℤ ↦ (z : ℝ)) (α := (ε : ℝ)) (t := u))
    _ = Real.exp (((rescaledWalkTime ε : NNReal) : ℝ) * (Real.cosh ((ε : ℝ) * u) - 1)) := by
          rw [continuousTimeSymmetricRandomWalkIncrementLaw_mgf]
    _ = Real.exp ((ε : ℝ)⁻¹ * (Real.cosh ((ε : ℝ) * u) - 1)) := by
          rw [rescaledWalkTime_coe]

/-- Helper for Exercise 23.2.7: the rescaled family has cumulant-generating function
`u ↦ ε⁻¹ (cosh (ε u) - 1)`. -/
private theorem continuousTimeSymmetricRandomWalkRescaledLaw_cgf
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    (ε : PositiveParameter) (u : ℝ) :
    cgf id (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε) u =
      (ε : ℝ)⁻¹ * (Real.cosh ((ε : ℝ) * u) - 1) := by
  -- Proof comment: the exact rescaled mgf is an exponential, so the logarithm again removes the
  -- outer `exp`.
  rw [cgf, continuousTimeSymmetricRandomWalkRescaledLaw_mgf, Real.log_exp]

/-- Helper for Exercise 23.2.7: the exact rescaled cgf differentiates to `u ↦ sinh (ε u)`. -/
private theorem deriv_continuousTimeSymmetricRandomWalkRescaledLawExactCgf
    (ε : PositiveParameter) :
    deriv (fun s : ℝ ↦ (ε : ℝ)⁻¹ * (Real.cosh ((ε : ℝ) * s) - 1)) =
      fun s : ℝ ↦ Real.sinh ((ε : ℝ) * s) := by
  -- Proof comment: differentiate `cosh (ε s)` pointwise by the chain rule and cancel the
  -- prefactor `ε⁻¹`.
  funext s
  have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
  have hmul :
      HasDerivAt (fun u : ℝ ↦ (ε : ℝ) * u) (ε : ℝ) s := by
    simpa [one_mul] using (hasDerivAt_id' s).const_mul (ε : ℝ)
  have hbase :
      HasDerivAt
        (fun u : ℝ ↦ Real.cosh ((ε : ℝ) * u) - 1)
        (Real.sinh ((ε : ℝ) * s) * (ε : ℝ)) s := by
    simpa using ((Real.hasDerivAt_cosh ((ε : ℝ) * s)).comp s hmul).sub_const 1
  convert (hbase.const_mul ((ε : ℝ)⁻¹)).deriv using 1
  simp [div_eq_mul_inv, hεne, mul_assoc, mul_comm, mul_left_comm]

/-- Helper for Exercise 23.2.7: the exact rescaled cgf has second derivative
`u ↦ ε cosh (ε u)`. -/
private theorem iteratedDerivTwo_continuousTimeSymmetricRandomWalkRescaledLawExactCgf
    (ε : PositiveParameter) :
    iteratedDeriv 2 (fun s : ℝ ↦ (ε : ℝ)⁻¹ * (Real.cosh ((ε : ℝ) * s) - 1)) =
      fun s : ℝ ↦ (ε : ℝ) * Real.cosh ((ε : ℝ) * s) := by
  -- Proof comment: differentiate the first-derivative formula `sinh (ε s)` once more.
  funext s
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    deriv_continuousTimeSymmetricRandomWalkRescaledLawExactCgf]
  have hmul :
      HasDerivAt (fun u : ℝ ↦ (ε : ℝ) * u) (ε : ℝ) s := by
    simpa [one_mul] using (hasDerivAt_id' s).const_mul (ε : ℝ)
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((Real.hasDerivAt_sinh ((ε : ℝ) * s)).comp s hmul).deriv

/-- Helper for Exercise 23.2.7: the rescaled one-time law has finite exponential moments at every
real tilt. -/
private theorem continuousTimeSymmetricRandomWalkRescaledLaw_integrableExpSet_univ
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    (ε : PositiveParameter) :
    integrableExpSet id (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε) = Set.univ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    by_contra hu
    have hZero :
        mgf id (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε) u = 0 :=
      mgf_undef (μ := (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
        (X := id) (t := u) hu
    have hMgf :
        mgf id (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε) u =
          Real.exp ((ε : ℝ)⁻¹ * (Real.cosh ((ε : ℝ) * u) - 1)) :=
      continuousTimeSymmetricRandomWalkRescaledLaw_mgf μ X hX ε u
    rw [hZero] at hMgf
    exact (Real.exp_pos _).ne' hMgf.symm

/-- Helper for Exercise 23.2.7: tilting the rescaled law at slope `t / ε` centers it at
`sinh t` and gives variance `ε cosh t`. -/
private theorem continuousTimeSymmetricRandomWalkRescaledLaw_tiltedMeanVariance
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    (t : ℝ) (ε : PositiveParameter) :
    let ν : Measure ℝ := (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ)
    (ν.tilted (fun x ↦ (t / (ε : ℝ)) * x))[id] = Real.sinh t ∧
      Var[id; ν.tilted (fun x ↦ (t / (ε : ℝ)) * x)] = (ε : ℝ) * Real.cosh t := by
  let ν : Measure ℝ := (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ)
  have htInt : t / (ε : ℝ) ∈ interior (integrableExpSet id ν) := by
    -- Proof comment: the exact mgf is finite for every tilt, so the interior domain is all of
    -- `ℝ`.
    rw [continuousTimeSymmetricRandomWalkRescaledLaw_integrableExpSet_univ
      (μ := μ) (X := X) (hX := hX) ε]
    simp [ν]
  have hcgf :
      cgf id ν = fun s : ℝ ↦ (ε : ℝ)⁻¹ * (Real.cosh ((ε : ℝ) * s) - 1) := by
    -- Proof comment: normalize the cgf once so the tilted moment formulas can read off the
    -- derivatives syntactically.
    funext s
    simpa [ν] using continuousTimeSymmetricRandomWalkRescaledLaw_cgf
      (μ := μ) (X := X) hX ε s
  have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
  refine ⟨?_, ?_⟩
  · -- Proof comment: the tilted mean is the first derivative of the exact cgf at `t / ε`.
    have hMoment :
        (ν.tilted (fun x ↦ (t / (ε : ℝ)) * x))[id] = deriv (cgf id ν) (t / (ε : ℝ)) := by
      simpa [id] using
        (integral_tilted_mul_self (μ := ν) (X := id) (t := t / (ε : ℝ)) htInt)
    rw [hMoment, hcgf, deriv_continuousTimeSymmetricRandomWalkRescaledLawExactCgf]
    simp [div_eq_mul_inv, hεne, mul_assoc, mul_comm, mul_left_comm]
  · -- Proof comment: the tilted variance is the second derivative of the same exact cgf.
    have hVariance :
        Var[id; ν.tilted (fun x ↦ (t / (ε : ℝ)) * x)] =
          iteratedDeriv 2 (cgf id ν) (t / (ε : ℝ)) := by
      simpa [id] using
        (variance_tilted_mul (μ := ν) (X := id) (t := t / (ε : ℝ)) htInt)
    rw [hVariance, hcgf, iteratedDerivTwo_continuousTimeSymmetricRandomWalkRescaledLawExactCgf]
    simp [div_eq_mul_inv, hεne, mul_assoc, mul_comm, mul_left_comm]

/-- Helper for Exercise 23.2.7: taking the union of two events costs only the vanishing penalty
`ε log 2` on top of the larger scaled exponent. -/
private theorem scaledLogMassAlong_union_le_logTwo_add_max
    {E : Type*} [MeasurableSpace E] {ι : Type*}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) (s t : Set E) (i : ι) :
    scaledLogMassAlong μ ε (s ∪ t) i ≤
      ((((ε i : ℝ) * Real.log 2 : ℝ) : EReal)) +
        max (scaledLogMassAlong μ ε s i) (scaledLogMassAlong μ ε t i) := by
  let α : EReal := ((ε i : ℝ) : EReal)
  let a : ℝ≥0∞ := μ i s
  let b : ℝ≥0∞ := μ i t
  have hα : (0 : EReal) ≤ α := by
    have hα_real : 0 ≤ (ε i : ℝ) := le_of_lt (show 0 < (ε i : ℝ) from (ε i).2)
    simpa [α] using (show (0 : EReal) ≤ ((ε i : ℝ) : EReal) from by
      exact_mod_cast hα_real)
  have hUnionMass : μ i (s ∪ t) ≤ a + b := by
    simpa [a, b] using measure_union_le s t (μ := μ i)
  have hAddLe : a + b ≤ (2 : ℝ≥0∞) * max a b := by
    calc
      a + b ≤ max a b + max a b := by
        exact add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = (2 : ℝ≥0∞) * max a b := by
        simp [two_mul]
  have hLog :
      ENNReal.log (μ i (s ∪ t)) ≤ ENNReal.log ((2 : ℝ≥0∞) * max a b) := by
    exact ENNReal.log_monotone (hUnionMass.trans hAddLe)
  have hMul :
      α * ENNReal.log (μ i (s ∪ t)) ≤ α * ENNReal.log ((2 : ℝ≥0∞) * max a b) := by
    exact mul_le_mul_of_nonneg_left hLog hα
  have hα_ne_top : α ≠ ⊤ := by
    simp [α]
  have hlogTwo :
      ENNReal.log (2 : ℝ≥0∞) = ((Real.log 2 : ℝ) : EReal) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
    simpa using (ENNReal.log_ofReal_of_pos (show 0 < (2 : ℝ) by norm_num))
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def, scaledLogMassAlong_def]
  refine le_trans hMul ?_
  rw [ENNReal.log_mul_add, EReal.left_distrib_of_nonneg_of_ne_top hα hα_ne_top, hlogTwo]
  rcases le_total a b with hab | hba
  · -- Proof comment: when the right event has larger mass, it controls the union exponent.
    have hmono : α * ENNReal.log a ≤ α * ENNReal.log b := by
      exact mul_le_mul_of_nonneg_left (ENNReal.log_monotone hab) hα
    rw [max_eq_right hab, max_eq_right hmono]
    simpa [α, mul_comm, mul_left_comm, mul_assoc]
  · -- Proof comment: the symmetric branch uses the left event as the dominant exponent.
    have hmono : α * ENNReal.log b ≤ α * ENNReal.log a := by
      exact mul_le_mul_of_nonneg_left (ENNReal.log_monotone hba) hα
    rw [max_eq_left hba, max_eq_left hmono]
    simpa [α, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 23.2.7: every scaled logarithmic mass is nonpositive for a family of
probability measures because event masses are at most `1`. -/
private theorem scaledLogMassAlong_nonpos_of_probability
    {E : Type*} [MeasurableSpace E] {ι : Type*}
    (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (ε : ι → PositiveParameter) (s : Set E) (i : ι) :
    scaledLogMassAlong μ ε s i ≤ 0 := by
  -- Proof comment: `μ i s ≤ 1`, hence `log (μ i s) ≤ 0`; multiplying by the positive speed keeps
  -- the inequality.
  rw [scaledLogMassAlong_def]
  have hs_le_one : μ i s ≤ 1 := by
    calc
      μ i s ≤ μ i Set.univ := measure_mono (by simp)
      _ = 1 := by simpa using (IsProbabilityMeasure.measure_univ (μ := μ i))
  have hlog_nonpos : ENNReal.log (μ i s) ≤ 0 := by
    rw [ENNReal.log_le_zero_iff]
    exact hs_le_one
  have hε_nonneg : (0 : EReal) ≤ ((ε i : ℝ) : EReal) := by
    exact_mod_cast le_of_lt (ε i).2
  calc
    ((ε i : ℝ) : EReal) * ENNReal.log (μ i s) ≤ ((ε i : ℝ) : EReal) * 0 := by
      exact mul_le_mul_of_nonneg_left hlog_nonpos hε_nonneg
    _ = 0 := by simp

/-- Helper for Exercise 23.2.7: enlarging an event can only increase the scaled logarithmic mass. -/
private theorem scaledLogMassAlong_mono_of_subset
    {E : Type*} [MeasurableSpace E] {ι : Type*}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) {s t : Set E}
    (hst : s ⊆ t) (i : ι) :
    scaledLogMassAlong μ ε s i ≤ scaledLogMassAlong μ ε t i := by
  -- Proof comment: both measure and `ENNReal.log` are monotone, and the speed parameter is
  -- nonnegative.
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def]
  have hlog : ENNReal.log (μ i s) ≤ ENNReal.log (μ i t) := by
    exact ENNReal.log_monotone (measure_mono hst)
  have hε_nonneg : (0 : EReal) ≤ ((ε i : ℝ) : EReal) := by
    exact_mod_cast le_of_lt (ε i).2
  exact mul_le_mul_of_nonneg_left hlog hε_nonneg

/-- Helper for Exercise 23.2.7: if a probability measure puts less than `1 / 2` mass on the
complement of a measurable set, then the set itself carries at least `1 / 2` mass. -/
private theorem one_half_le_measure_of_compl_lt_half
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Set ℝ} (hs : MeasurableSet s)
    (hcompl : μ sᶜ < (1 / 2 : ℝ≥0∞)) :
    (1 / 2 : ℝ≥0∞) ≤ μ s := by
  have hsum : μ s + μ sᶜ = 1 := by
    simpa using prob_add_prob_compl (μ := μ) hs
  have hsum_real :
      (μ s).toReal + (μ sᶜ).toReal = 1 := by
    simpa [ENNReal.toReal_add, measure_ne_top μ _] using congrArg ENNReal.toReal hsum
  have hcompl_real : (μ sᶜ).toReal < (1 / 2 : ℝ) := by
    have hcompl' : μ sᶜ < ENNReal.ofReal (1 / 2 : ℝ) := by
      simpa using hcompl
    simpa using
      (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).2 hcompl'
  have hset_real : (1 / 2 : ℝ) ≤ (μ s).toReal := by
    linarith
  have hset : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ s := by
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).2 hset_real
  simpa using hset

/-- Helper for Exercise 23.2.7: the lower comparison term `ε log (1 / 2)` is eventually above any
strictly negative test value along the positive-parameter filter. -/
private theorem eventually_lt_scaledLogHalf {y : EReal} (hy : y < 0) :
    ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
      y < ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞) := by
  have hbase :
      Filter.Tendsto (fun ε : ℝ ↦ (ε : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞))
        (𝓝[>] (0 : ℝ)) (nhds (0 : EReal)) :=
    ENNReal.tendsto_smallNoiseLogConst (b := (1 / 2 : ℝ≥0∞)) (by norm_num) (by simp)
  have hcoe :
      Filter.Tendsto ((↑) : PositiveParameter → ℝ) positiveParameterFilter (𝓝[>] (0 : ℝ)) := by
    simpa [Filter.Tendsto, positiveParameterFilter] using
      (Filter.map_comap_le :
        Filter.map ((↑) : PositiveParameter → ℝ)
            (Filter.comap ((↑) : PositiveParameter → ℝ) (𝓝[>] (0 : ℝ))) ≤
          𝓝[>] (0 : ℝ))
  have htendsto :
      Filter.Tendsto
        (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞))
        positiveParameterFilter (nhds (0 : EReal)) := by
    -- Proof comment: reindex the standard small-noise limit along the positive-parameter filter.
    simpa using hbase.comp hcoe
  -- Proof comment: `Ioi y` is a neighborhood of `0`, so eventual membership yields the strict
  -- lower comparison needed for the change-of-measure estimate.
  exact htendsto (Ioi_mem_nhds hy)

/-- Helper for Exercise 23.2.7: under the tilt at slope `t / ε`, the rescaled law eventually puts
at least half of its mass on the centered window around `sinh t`. -/
private theorem continuousTimeSymmetricRandomWalk_tiltedWindow_eventually_ge_half
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    {t δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in positiveParameterFilter,
      (1 / 2 : ℝ≥0∞) ≤
        ((continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ).tilted
          (fun x ↦ (t / (ε : ℝ)) * x))
          (Set.Ioo (Real.sinh t - δ) (Real.sinh t + δ)) := by
  have hcoe :
      Filter.Tendsto ((↑) : PositiveParameter → ℝ) positiveParameterFilter (𝓝[>] (0 : ℝ)) := by
    -- Proof comment: the positive-parameter filter is exactly the right-neighborhood filter at
    -- `0` after coercion.
    simpa [Filter.Tendsto] using (le_of_eq map_positiveParameterFilter)
  have hEventuallySmall :
      ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
        ((ε : ℝ) * Real.cosh t) / δ ^ (2 : ℕ) < (1 / 2 : ℝ) := by
    have hbound : 0 < δ ^ (2 : ℕ) / (2 * Real.cosh t) := by
      positivity
    have hEventuallyEps :
        ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
          (ε : ℝ) < δ ^ (2 : ℕ) / (2 * Real.cosh t) := by
      exact hcoe (Iio_mem_nhdsWithin_right_zero hbound)
    filter_upwards [hEventuallyEps] with ε hε
    have hδsq_pos : 0 < δ ^ (2 : ℕ) := by positivity
    apply (div_lt_iff₀ hδsq_pos).2
    have hcosh_pos : 0 < Real.cosh t := Real.cosh_pos t
    have hmul :
        (ε : ℝ) * Real.cosh t <
          (δ ^ (2 : ℕ) / (2 * Real.cosh t)) * Real.cosh t := by
      exact mul_lt_mul_of_pos_right hε hcosh_pos
    have hcancel :
        (δ ^ (2 : ℕ) / (2 * Real.cosh t)) * Real.cosh t = δ ^ (2 : ℕ) / 2 := by
      field_simp [(show Real.cosh t ≠ 0 by positivity)]
    calc
      (ε : ℝ) * Real.cosh t < (δ ^ (2 : ℕ) / (2 * Real.cosh t)) * Real.cosh t := hmul
      _ = δ ^ (2 : ℕ) / 2 := hcancel
      _ = (1 / 2 : ℝ) * δ ^ (2 : ℕ) := by ring
  filter_upwards [hEventuallySmall] with ε hεsmall
  let ν : Measure ℝ := (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ)
  let νt : Measure ℝ := ν.tilted (fun x ↦ (t / (ε : ℝ)) * x)
  have hInt :
      Integrable (fun x : ℝ ↦ Real.exp ((t / (ε : ℝ)) * x)) ν := by
    -- Proof comment: the exact rescaled law has finite exponential moments at every tilt.
    have hmem : t / (ε : ℝ) ∈ integrableExpSet id ν := by
      rw [continuousTimeSymmetricRandomWalkRescaledLaw_integrableExpSet_univ
        (μ := μ) (X := X) (hX := hX) ε]
      simp [ν]
    exact integrable_of_mem_integrableExpSet hmem
  letI : IsProbabilityMeasure νt := isProbabilityMeasure_tilted hInt
  have htInt : t / (ε : ℝ) ∈ interior (integrableExpSet id ν) := by
    -- Proof comment: the same all-tilts integrability also puts the chosen tilt in the interior
    -- domain required by the `tilted` moment API.
    rw [continuousTimeSymmetricRandomWalkRescaledLaw_integrableExpSet_univ
      (μ := μ) (X := X) (hX := hX) ε]
    simp [ν]
  have hMeanVar :=
      continuousTimeSymmetricRandomWalkRescaledLaw_tiltedMeanVariance
        (μ := μ) (X := X) hX t ε
  have hMean : νt[id] = Real.sinh t := by
    simpa [ν, νt] using hMeanVar.1
  have hVar : Var[id; νt] = (ε : ℝ) * Real.cosh t := by
    simpa [ν, νt] using hMeanVar.2
  have hMemLp : MemLp id 2 νt := by
    -- Proof comment: finite exponential moments put the tilted identity random variable in
    -- `L²`, so Chebyshev applies.
    simpa [νt] using
      (memLp_tilted_mul (μ := ν) (X := id) (t := t / (ε : ℝ)) htInt 2)
  let center : ℝ := νt[id]
  have hChebyshev :
      νt {x | δ ≤ |x - center|} ≤
        ENNReal.ofReal (((ε : ℝ) * Real.cosh t) / δ ^ (2 : ℕ)) := by
    -- Proof comment: Chebyshev controls the complement of the centered window by the tilted
    -- variance divided by `δ²`.
    simpa [center, hVar, νt] using
      (meas_ge_le_variance_div_sq (μ := νt) (X := id) hMemLp (c := δ) hδ)
  have hcomplSubset :
      (Set.Ioo (Real.sinh t - δ) (Real.sinh t + δ))ᶜ ⊆ {x | δ ≤ |x - center|} := by
    -- Proof comment: outside the interval `(sinh t - δ, sinh t + δ)`, the centered distance from
    -- `sinh t` is at least `δ`.
    intro x hx
    have hxnot : x ∉ Set.Ioo (Real.sinh t - δ) (Real.sinh t + δ) := by simpa using hx
    change δ ≤ |x - νt[id]|
    rw [hMean]
    by_cases hleft : x ≤ Real.sinh t - δ
    · have hnonpos : x - Real.sinh t ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      linarith
    · have hright : Real.sinh t + δ ≤ x := by
        by_contra hright
        exact hxnot ⟨lt_of_not_ge hleft, lt_of_not_ge hright⟩
      have hnonneg : 0 ≤ x - Real.sinh t := by linarith
      rw [abs_of_nonneg hnonneg]
      linarith
  have hBoundLt :
      ENNReal.ofReal (((ε : ℝ) * Real.cosh t) / δ ^ (2 : ℕ)) < (1 / 2 : ℝ≥0∞) := by
    simpa using
      (ENNReal.ofReal_lt_ofReal_iff (show 0 < (1 / 2 : ℝ) by positivity)).2 hεsmall
  have hcomplLt :
      νt (Set.Ioo (Real.sinh t - δ) (Real.sinh t + δ))ᶜ < (1 / 2 : ℝ≥0∞) := by
    exact lt_of_le_of_lt (le_trans (measure_mono hcomplSubset) hChebyshev) hBoundLt
  exact one_half_le_measure_of_compl_lt_half
    (μ := νt)
    (s := Set.Ioo (Real.sinh t - δ) (Real.sinh t + δ))
    measurableSet_Ioo hcomplLt

/-- Helper for Exercise 23.2.7: the exact cgf gives the left-tail Chernoff bound in scaled
logarithmic form. -/
private theorem continuousTimeSymmetricRandomWalk_closedLeftHalfline_le_tilt
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    {a t : ℝ} (ht : t ≤ 0) (ε : PositiveParameter) :
    scaledLogMassAlong
        (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
        id (Set.Iic a) ε ≤
      -(((t * a - (Real.cosh t - 1) : ℝ) : EReal)) := by
  let ν : Measure ℝ := (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ)
  have hInt : Integrable (fun x : ℝ ↦ Real.exp ((t / (ε : ℝ)) * x)) ν := by
    -- Proof comment: the exact rescaled mgf is strictly positive, so the integrand cannot fall
    -- into the undefined branch.
    by_contra hNotInt
    have hZero : mgf id ν (t / (ε : ℝ)) = 0 := by
      exact mgf_undef (μ := ν) (X := id) (t := t / (ε : ℝ)) hNotInt
    have hMgf :
        mgf id ν (t / (ε : ℝ)) =
          Real.exp ((ε : ℝ)⁻¹ * (Real.cosh t - 1)) := by
      have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
      rw [continuousTimeSymmetricRandomWalkRescaledLaw_mgf]
      congr 1
      field_simp [hεne]
    rw [hZero] at hMgf
    exact (Real.exp_pos _).ne' hMgf.symm
  have hChernoff :
      ν.real (Set.Iic a) ≤ Real.exp (-(t / (ε : ℝ)) * a + cgf id ν (t / (ε : ℝ))) := by
    simpa using
      (measure_le_le_exp_cgf (μ := ν) (X := id) (ε := a) (t := t / (ε : ℝ))
        (div_nonpos_of_nonpos_of_nonneg ht (le_of_lt ε.2)) hInt)
  have hMassLe :
      ν (Set.Iic a) ≤ ENNReal.ofReal (Real.exp (-(t / (ε : ℝ)) * a + cgf id ν (t / (ε : ℝ)))) := by
    rw [← MeasureTheory.ofReal_measureReal (μ := ν) (s := Set.Iic a)]
    exact ENNReal.ofReal_le_ofReal hChernoff
  have hLogMass :
      ENNReal.log (ν (Set.Iic a)) ≤
        (((-(t / (ε : ℝ)) * a + cgf id ν (t / (ε : ℝ)) : ℝ) : EReal)) := by
    calc
      ENNReal.log (ν (Set.Iic a)) ≤
          ENNReal.log (ENNReal.ofReal (Real.exp (-(t / (ε : ℝ)) * a + cgf id ν (t / (ε : ℝ))))) :=
        ENNReal.log_monotone hMassLe
      _ = (((-(t / (ε : ℝ)) * a + cgf id ν (t / (ε : ℝ)) : ℝ) : EReal)) := by
        rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have hε_nonneg : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hEvalCgf :
      cgf id ν (t / (ε : ℝ)) = (ε : ℝ)⁻¹ * (Real.cosh t - 1) := by
    have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
    rw [continuousTimeSymmetricRandomWalkRescaledLaw_cgf]
    congr 1
    field_simp [hεne]
  have hAlg :
      (ε : ℝ) * (-(t / (ε : ℝ)) * a + (ε : ℝ)⁻¹ * (Real.cosh t - 1)) =
        -(t * a - (Real.cosh t - 1)) := by
    have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
    field_simp [hεne]
    ring
  calc
    scaledLogMassAlong
        (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
        id (Set.Iic a) ε
      = ((ε : ℝ) : EReal) * ENNReal.log (ν (Set.Iic a)) := by
          simp [ν, scaledLogMassAlong_def]
    _ ≤ ((ε : ℝ) : EReal) *
          (((-(t / (ε : ℝ)) * a + cgf id ν (t / (ε : ℝ)) : ℝ) : EReal)) := by
            exact mul_le_mul_of_nonneg_left hLogMass hε_nonneg
    _ = -(((t * a - (Real.cosh t - 1) : ℝ) : EReal)) := by
          rw [hEvalCgf]
          exact_mod_cast hAlg

/-- Helper for Exercise 23.2.7: the exact cgf gives the right-tail Chernoff bound in scaled
logarithmic form. -/
private theorem continuousTimeSymmetricRandomWalk_closedRightHalfline_le_tilt
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    {b t : ℝ} (ht : 0 ≤ t) (ε : PositiveParameter) :
    scaledLogMassAlong
        (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
        id (Set.Ici b) ε ≤
      -(((t * b - (Real.cosh t - 1) : ℝ) : EReal)) := by
  let ν : Measure ℝ := (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ)
  have hInt : Integrable (fun x : ℝ ↦ Real.exp ((t / (ε : ℝ)) * x)) ν := by
    -- Proof comment: as in the left-tail case, the exact mgf formula excludes the undefined
    -- branch.
    by_contra hNotInt
    have hZero : mgf id ν (t / (ε : ℝ)) = 0 := by
      exact mgf_undef (μ := ν) (X := id) (t := t / (ε : ℝ)) hNotInt
    have hMgf :
        mgf id ν (t / (ε : ℝ)) =
          Real.exp ((ε : ℝ)⁻¹ * (Real.cosh t - 1)) := by
      have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
      rw [continuousTimeSymmetricRandomWalkRescaledLaw_mgf]
      congr 1
      field_simp [hεne]
    rw [hZero] at hMgf
    exact (Real.exp_pos _).ne' hMgf.symm
  have hChernoff :
      ν.real (Set.Ici b) ≤ Real.exp (-(t / (ε : ℝ)) * b + cgf id ν (t / (ε : ℝ))) := by
    simpa using
      (measure_ge_le_exp_cgf (μ := ν) (X := id) (ε := b) (t := t / (ε : ℝ))
        (div_nonneg ht (le_of_lt ε.2)) hInt)
  have hMassLe :
      ν (Set.Ici b) ≤ ENNReal.ofReal (Real.exp (-(t / (ε : ℝ)) * b + cgf id ν (t / (ε : ℝ)))) := by
    rw [← MeasureTheory.ofReal_measureReal (μ := ν) (s := Set.Ici b)]
    exact ENNReal.ofReal_le_ofReal hChernoff
  have hLogMass :
      ENNReal.log (ν (Set.Ici b)) ≤
        (((-(t / (ε : ℝ)) * b + cgf id ν (t / (ε : ℝ)) : ℝ) : EReal)) := by
    calc
      ENNReal.log (ν (Set.Ici b)) ≤
          ENNReal.log (ENNReal.ofReal (Real.exp (-(t / (ε : ℝ)) * b + cgf id ν (t / (ε : ℝ))))) :=
        ENNReal.log_monotone hMassLe
      _ = (((-(t / (ε : ℝ)) * b + cgf id ν (t / (ε : ℝ)) : ℝ) : EReal)) := by
        rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have hε_nonneg : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hEvalCgf :
      cgf id ν (t / (ε : ℝ)) = (ε : ℝ)⁻¹ * (Real.cosh t - 1) := by
    have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
    rw [continuousTimeSymmetricRandomWalkRescaledLaw_cgf]
    congr 1
    field_simp [hεne]
  have hAlg :
      (ε : ℝ) * (-(t / (ε : ℝ)) * b + (ε : ℝ)⁻¹ * (Real.cosh t - 1)) =
        -(t * b - (Real.cosh t - 1)) := by
    have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
    field_simp [hεne]
    ring
  calc
    scaledLogMassAlong
        (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
        id (Set.Ici b) ε
      = ((ε : ℝ) : EReal) * ENNReal.log (ν (Set.Ici b)) := by
          simp [ν, scaledLogMassAlong_def]
    _ ≤ ((ε : ℝ) : EReal) *
          (((-(t / (ε : ℝ)) * b + cgf id ν (t / (ε : ℝ)) : ℝ) : EReal)) := by
            exact mul_le_mul_of_nonneg_left hLogMass hε_nonneg
    _ = -(((t * b - (Real.cosh t - 1) : ℝ) : EReal)) := by
          rw [hEvalCgf]
          exact_mod_cast hAlg

/-- Helper for Exercise 23.2.7: every point of an open set in `ℝ` lies in a smaller symmetric
open interval still contained in the set. -/
private theorem exists_Ioo_subset_of_isOpen_mem
    {s : Set ℝ} (hsOpen : IsOpen s) {x : ℝ} (hx : x ∈ s) :
    ∃ δ > 0, Set.Ioo (x - δ) (x + δ) ⊆ s := by
  rcases Metric.isOpen_iff.mp hsOpen x hx with ⟨δ, hδpos, hball⟩
  refine ⟨δ, hδpos, ?_⟩
  intro y hy
  apply hball
  -- Proof comment: any point in the symmetric interval has distance less than `δ` from `x`.
  show dist y x < δ
  have habs : |y - x| < δ := by
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  simpa [Real.dist_eq] using habs

/-- Helper for Exercise 23.2.7: the real branch of the rate vanishes at the origin. -/
private theorem continuousTimeSymmetricRandomWalkRateReal_zero :
    continuousTimeSymmetricRandomWalkRateReal 0 = 0 := by
  simp [continuousTimeSymmetricRandomWalkRateReal]

/-- Helper for Exercise 23.2.7: the real branch of the rate is nonnegative everywhere. -/
private theorem continuousTimeSymmetricRandomWalkRateReal_nonneg (x : ℝ) :
    0 ≤ continuousTimeSymmetricRandomWalkRateReal x := by
  by_cases hx : 0 ≤ x
  · have hmono :=
      continuousTimeSymmetricRandomWalkRateReal_monotoneOn_nonneg
        (show (0 : ℝ) ∈ Set.Ici 0 by simp)
        (show x ∈ Set.Ici 0 by simpa using hx) hx
    simpa [continuousTimeSymmetricRandomWalkRateReal_zero] using hmono
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hnonneg : 0 ≤ -x := by linarith
    have hmono :=
      continuousTimeSymmetricRandomWalkRateReal_monotoneOn_nonneg
        (show (0 : ℝ) ∈ Set.Ici 0 by simp)
        (show -x ∈ Set.Ici 0 by simpa using hnonneg) hnonneg
    have hnonnegNeg : 0 ≤ continuousTimeSymmetricRandomWalkRateReal (-x) := by
      simpa [continuousTimeSymmetricRandomWalkRateReal_zero] using hmono
    simpa [continuousTimeSymmetricRandomWalkRateReal_even x] using hnonnegNeg

/-- Helper for Exercise 23.2.7: coercing the `ENNReal`-valued rate to `EReal` recovers the real
branch. -/
private theorem continuousTimeSymmetricRandomWalkRateFunction_coe_ereal (x : ℝ) :
    (((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) =
      ((continuousTimeSymmetricRandomWalkRateReal x : ℝ) : EReal) := by
  -- Proof comment: the `ENNReal`-valued owner is defined by `ENNReal.ofReal`, and the real branch
  -- is already known to be nonnegative, so coercing to `EReal` simply returns that branch.
  change (((ENNReal.ofReal (continuousTimeSymmetricRandomWalkRateReal x) : ENNReal) : EReal)) =
      ((continuousTimeSymmetricRandomWalkRateReal x : ℝ) : EReal)
  rw [ENNReal.ofReal_eq_coe_nnreal (continuousTimeSymmetricRandomWalkRateReal_nonneg x)]
  rfl

/-- Helper for Exercise 23.2.7: the explicit rate depends only on `|x|`. -/
private theorem continuousTimeSymmetricRandomWalkRateReal_abs (x : ℝ) :
    continuousTimeSymmetricRandomWalkRateReal |x| =
      continuousTimeSymmetricRandomWalkRateReal x := by
  by_cases hx : 0 ≤ x
  · simp [abs_of_nonneg hx]
  · have hxlt : x < 0 := lt_of_not_ge hx
    simpa [abs_of_neg hxlt, continuousTimeSymmetricRandomWalkRateReal_even x]

/-- Helper for Exercise 23.2.7: a closed set in `ℝ` that misses `0` stays a positive distance
away from the origin. -/
private theorem exists_pos_le_abs_of_isClosed_of_zero_not_mem {F : Set ℝ} (hF : IsClosed F)
    (h0 : (0 : ℝ) ∉ F) :
    ∃ r > 0, ∀ x ∈ F, r ≤ |x| := by
  have hnhds : Fᶜ ∈ 𝓝 (0 : ℝ) := hF.isOpen_compl.mem_nhds (by simpa using h0)
  rw [Metric.mem_nhds_iff] at hnhds
  rcases hnhds with ⟨r, hrpos, hrsub⟩
  refine ⟨r, hrpos, ?_⟩
  intro x hx
  -- Proof comment: points of `F` cannot lie in the open ball around `0` contained in `Fᶜ`.
  by_contra hxlt
  have hxball : x ∈ Metric.ball (0 : ℝ) r := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hxlt
  exact (hrsub hxball) hx

/-- Helper for Exercise 23.2.7: the centered interval around `x` has the correct lower
pointwise exponent bound for the optimizer `t = arsinh x`. -/
private theorem continuousTimeSymmetricRandomWalk_centeredInterval_exponent_le_affineError
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    {x δ z : ℝ} (hδ : 0 < δ) {ε : PositiveParameter}
    (hz : z ∈ Set.Ioo (x - δ) (x + δ)) :
    ((Real.arsinh x) / (ε : ℝ)) * z -
        cgf id (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε)
          ((Real.arsinh x) / (ε : ℝ)) ≤
      (continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ) / (ε : ℝ) := by
  let ν : Measure ℝ := (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ)
  have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
  have hzAbs : |z - x| < δ := by
    rw [abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  have hmulAbs :
      |Real.arsinh x * (z - x)| ≤ |Real.arsinh x| * δ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hzAbs.le (abs_nonneg _)
  have hmulLe :
      Real.arsinh x * (z - x) ≤ |Real.arsinh x| * δ := by
    exact le_trans (le_abs_self _) hmulAbs
  have hNumerator :
      Real.arsinh x * z - (Real.cosh (Real.arsinh x) - 1) ≤
        continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ := by
    rw [continuousTimeSymmetricRandomWalkRateReal_eq_affineAtArsinh]
    have hsplit :
        Real.arsinh x * z =
          Real.arsinh x * x + Real.arsinh x * (z - x) := by
      ring
    rw [hsplit]
    linarith
  have hArg :
      (ε : ℝ) * (Real.arsinh x / (ε : ℝ)) = Real.arsinh x := by
    field_simp [hεne]
  have hRewrite :
      ((Real.arsinh x) / (ε : ℝ)) * z -
          cgf id (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε)
            ((Real.arsinh x) / (ε : ℝ)) =
        (Real.arsinh x * z - (Real.cosh (Real.arsinh x) - 1)) / (ε : ℝ) := by
    rw [continuousTimeSymmetricRandomWalkRescaledLaw_cgf, hArg]
    field_simp [hεne]
  -- Proof comment: after evaluating the cgf at the optimizer, the exponent becomes the affine
  -- cost `I(x) + arsinh(x) * (z - x)` divided by `ε`, and `|z - x| < δ` controls the error term.
  rw [hRewrite]
  exact div_le_div_of_nonneg_right hNumerator (le_of_lt ε.2)

/-- Helper for Exercise 23.2.7: a half-mass lower bound under the tilted law yields the fixed-`ε`
centered-interval scaled-log lower bound. -/
private theorem continuousTimeSymmetricRandomWalk_centeredInterval_scaledLog_ge_halfCorrection
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    {x δ : ℝ} (hδ : 0 < δ) (ε : PositiveParameter)
    (hHalf :
      (1 / 2 : ℝ≥0∞) ≤
        ((continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ).tilted
          (fun z ↦ ((Real.arsinh x) / (ε : ℝ)) * z))
          (Set.Ioo (x - δ) (x + δ))) :
    (((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞)) -
        ((continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ : ℝ) : EReal) ≤
      scaledLogMassAlong
        (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
        id (Set.Ioo (x - δ) (x + δ)) ε := by
  let ν : Measure ℝ := (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ)
  let A : Set ℝ := Set.Ioo (x - δ) (x + δ)
  let c : ℝ := continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ
  have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
  have hInt :
      Integrable (fun z : ℝ ↦ Real.exp (((Real.arsinh x) / (ε : ℝ)) * z)) ν := by
    have hmem :
        (Real.arsinh x) / (ε : ℝ) ∈ integrableExpSet id ν := by
      rw [continuousTimeSymmetricRandomWalkRescaledLaw_integrableExpSet_univ
        (μ := μ) (X := X) (hX := hX) ε]
      simp [ν]
    exact integrable_of_mem_integrableExpSet hmem
  have hTiltApply :
      (ν.tilted (fun z ↦ ((Real.arsinh x) / (ε : ℝ)) * z)) A =
        ∫⁻ z in A,
          ENNReal.ofReal
            (Real.exp
              (((Real.arsinh x) / (ε : ℝ)) * z -
                cgf id ν ((Real.arsinh x) / (ε : ℝ)))) ∂ν := by
    -- Proof comment: this is the owner-level tilted-event formula rewritten directly in terms of
    -- the exact cgf of the rescaled law.
    simpa [A, ν] using
      (ProbabilityTheory.tilted_mul_apply_cgf'
        (μ := ν) (X := id) (t := (Real.arsinh x) / (ε : ℝ))
        (s := A) measurableSet_Ioo hInt)
  have hMassLe :
      (ν.tilted (fun z ↦ ((Real.arsinh x) / (ε : ℝ)) * z)) A ≤
        ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ν A := by
    calc
      (ν.tilted (fun z ↦ ((Real.arsinh x) / (ε : ℝ)) * z)) A =
          ∫⁻ z in A,
            ENNReal.ofReal
              (Real.exp
                (((Real.arsinh x) / (ε : ℝ)) * z -
                  cgf id ν ((Real.arsinh x) / (ε : ℝ)))) ∂ν := hTiltApply
      _ ≤ ∫⁻ _z in A, ENNReal.ofReal (Real.exp (c / (ε : ℝ))) ∂ν := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
            exact ENNReal.ofReal_le_ofReal <|
              Real.exp_le_exp.mpr <|
                continuousTimeSymmetricRandomWalk_centeredInterval_exponent_le_affineError
                  (μ := μ) (X := X) hX hδ (ε := ε) hz
      _ = ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ν A := by
            simp [A, MeasureTheory.lintegral_const]
  have hLog :
      ENNReal.log (1 / 2 : ℝ≥0∞) ≤
        (((c / (ε : ℝ) : ℝ) : EReal)) + ENNReal.log (ν A) := by
    calc
      ENNReal.log (1 / 2 : ℝ≥0∞) ≤
          ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ν A) := by
            exact ENNReal.log_monotone (le_trans hHalf hMassLe)
      _ = (((c / (ε : ℝ) : ℝ) : EReal)) + ENNReal.log (ν A) := by
            rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have hεNonneg : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hUpper :
      ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞) ≤
        ((c : ℝ) : EReal) +
          scaledLogMassAlong
            (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id A ε := by
    have hMul :
        ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞) ≤
          ((ε : ℝ) : EReal) *
            ((((c / (ε : ℝ) : ℝ) : EReal)) + ENNReal.log (ν A)) := by
      exact mul_le_mul_of_nonneg_left hLog hεNonneg
    calc
      ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞) ≤
          ((ε : ℝ) : EReal) *
            ((((c / (ε : ℝ) : ℝ) : EReal)) + ENNReal.log (ν A)) := hMul
      _ = ((ε : ℝ) : EReal) * (((c / (ε : ℝ) : ℝ) : EReal)) +
            ((ε : ℝ) : EReal) * ENNReal.log (ν A) := by
              rw [EReal.left_distrib_of_nonneg_of_ne_top hεNonneg (by simp)]
      _ = ((c : ℝ) : EReal) +
            scaledLogMassAlong
              (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
              id A ε := by
              have hAlg : (ε : ℝ) * (c / (ε : ℝ)) = c := by
                field_simp [hεne]
              have hAlgEReal :
                  ((ε : ℝ) : EReal) * (((c / (ε : ℝ) : ℝ) : EReal)) =
                    ((c : ℝ) : EReal) := by
                exact_mod_cast hAlg
              rw [hAlgEReal, scaledLogMassAlong_def]
              simp [A, ν]
  -- Proof comment: taking `log` turns the tilted half-mass lower bound into an affine lower bound
  -- for the original interval mass, and the finite correction term is moved to the left-hand side.
  have hUpper' :
      ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞) ≤
        ((continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ : ℝ) : EReal) +
          scaledLogMassAlong
            (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id (Set.Ioo (x - δ) (x + δ)) ε := by
    simpa [A, c, add_assoc, add_comm, add_left_comm] using hUpper
  exact EReal.sub_le_of_le_add' hUpper'

/-- Helper for Exercise 23.2.7: the centered interval around `x` has the correct lower
change-of-measure exponent up to the affine error `|arsinh x| δ`. -/
private theorem continuousTimeSymmetricRandomWalk_centeredInterval_liminf_ge_affineError
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    {x δ : ℝ} (hδ : 0 < δ) :
    -((continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ : ℝ) : EReal) ≤
      Filter.liminf
        (scaledLogMassAlong
          (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
          id (Set.Ioo (x - δ) (x + δ)))
        positiveParameterFilter := by
  let c : ℝ := continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ
  have hHalfEventually :
      ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
        (1 / 2 : ℝ≥0∞) ≤
          ((continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ).tilted
            (fun z ↦ ((Real.arsinh x) / (ε : ℝ)) * z))
            (Set.Ioo (x - δ) (x + δ)) := by
    -- Proof comment: specialize the existing tilted half-mass theorem at the optimizer
    -- `t = arsinh x`, so the tilted window is exactly the centered interval around `x`.
    simpa [sub_eq_add_neg, Real.sinh_arsinh] using
      (continuousTimeSymmetricRandomWalk_tiltedWindow_eventually_ge_half
        (μ := μ) (X := X) hX (t := Real.arsinh x) (δ := δ) hδ)
  rw [Filter.le_liminf_iff']
  intro y hy
  have hyShift : y + ((c : ℝ) : EReal) < 0 := by
    -- Proof comment: rewrite the target comparison `y < -c` as a negative shifted value so the
    -- standard `ε log (1/2)` error term can absorb it.
    exact EReal.add_lt_of_lt_sub <| by simpa [c, sub_eq_add_neg] using hy
  filter_upwards [eventually_lt_scaledLogHalf hyShift, hHalfEventually] with ε hyε hHalf
  have hyCompare :
      y <
        (((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞)) -
          ((c : ℝ) : EReal) := by
    exact
      (EReal.lt_sub_iff_add_lt (.inl (by simp)) (.inl (by simp))).2 <|
        by simpa [add_comm, add_left_comm, add_assoc] using hyε
  exact hyCompare.le.trans <|
    continuousTimeSymmetricRandomWalk_centeredInterval_scaledLog_ge_halfCorrection
      (μ := μ) (X := X) hX hδ ε hHalf

/-- Helper for Exercise 23.2.7: the deterministic union penalty `ε log 2` vanishes along the
positive-parameter filter. -/
private theorem scaledLogTwoCorrection_tendsto_zero :
    Filter.Tendsto
      (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (2 : ℝ≥0∞))
      positiveParameterFilter (nhds (0 : EReal)) := by
  have hlogTwo : ENNReal.log (2 : ℝ≥0∞) = ((Real.log 2 : ℝ) : EReal) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
    simpa using (ENNReal.log_ofReal_of_pos (show 0 < (2 : ℝ) by norm_num))
  have hbaseReal :
      Filter.Tendsto (fun ε : ℝ ↦ ε * Real.log 2) (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) := by
    have hContAt : ContinuousAt (fun ε : ℝ ↦ ε * Real.log 2) 0 := by
      simpa using (continuousAt_id.mul continuousAt_const)
    simpa using hContAt.continuousWithinAt.tendsto
  have hbase :
      Filter.Tendsto (fun ε : ℝ ↦ ((ε * Real.log 2 : ℝ) : EReal))
        (𝓝[>] (0 : ℝ)) (nhds (0 : EReal)) := by
    simpa using (EReal.tendsto_coe.2 hbaseReal)
  have hcoe :
      Filter.Tendsto ((↑) : PositiveParameter → ℝ) positiveParameterFilter (𝓝[>] (0 : ℝ)) := by
    simpa [Filter.Tendsto] using (le_of_eq map_positiveParameterFilter)
  -- Proof comment: reindex the ordinary real limit `ε * log 2 → 0` along the chapter's
  -- positive-parameter filter.
  simpa [hlogTwo, EReal.coe_mul] using hbase.comp hcoe

/-- Helper for Exercise 23.2.7: any strict comparison value above the closed-set rate infimum can
be converted into a symmetric tail cutoff. -/
private theorem continuousTimeSymmetricRandomWalk_exists_symmetricTailSubset_of_lt_rateInf_closed
    {C : Set ℝ} {y : ℝ}
    (hC : IsClosed C) (hCne : C.Nonempty) (h0 : (0 : ℝ) ∉ C)
    (hy :
      ((y : EReal)) >
        -sInf
          ((fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) '' C)) :
    ∃ r > 0,
      C ⊆ Set.Iic (-r) ∪ Set.Ici r ∧
        -(((continuousTimeSymmetricRandomWalkRateReal r : ℝ) : EReal)) < (y : EReal) := by
  by_cases hyPos : 0 < y
  · rcases exists_pos_le_abs_of_isClosed_of_zero_not_mem hC h0 with ⟨r, hr, hrabs⟩
    refine ⟨r, hr, ?_, ?_⟩
    · intro x hx
      have hxabs : r ≤ |x| := hrabs x hx
      -- Proof comment: once `|x|` is at least the cutoff radius, `x` must lie in one of the two
      -- closed tails.
      by_cases hxle : x ≤ -r
      · exact Or.inl hxle
      · have hxr : r ≤ x := by
          by_contra hxr
          have hxIoo : x ∈ Set.Ioo (-r) r := by
            exact ⟨lt_of_not_ge hxle, lt_of_not_ge hxr⟩
          have hlt : |x| < r := by
            exact abs_lt.2 hxIoo
          exact (not_lt_of_ge hxabs) hlt
        exact Or.inr hxr
    · -- Proof comment: a positive comparison value dominates every negative tail exponent.
      have hltReal : -continuousTimeSymmetricRandomWalkRateReal r < y := by
        have hnonneg : 0 ≤ continuousTimeSymmetricRandomWalkRateReal r :=
          continuousTimeSymmetricRandomWalkRateReal_nonneg r
        linarith
      exact_mod_cast hltReal
  · have hyNonpos : y ≤ 0 := le_of_not_gt hyPos
    have hyInf :
        (((-y : ℝ)) : EReal) <
          sInf
            ((fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) '' C) := by
      simpa using EReal.neg_strictAnti hy
    rcases hCne with ⟨x₀, hx₀⟩
    rcases exists_between hyInf with ⟨z, hyz, hzInf⟩
    have hzTop : z ≠ ⊤ := by
      exact ne_top_of_lt (lt_of_lt_of_le hzInf (sInf_le ⟨x₀, hx₀, rfl⟩))
    have hzBot : z ≠ ⊥ := ne_bot_of_gt hyz
    let a : ℝ := z.toReal
    have haEq : ((a : ℝ) : EReal) = z := by
      simpa [a] using EReal.coe_toReal hzTop hzBot
    have haPos : 0 < a := by
      have hnonneg : 0 ≤ -y := by linarith
      have hlt : (0 : EReal) < (a : ℝ) := by
        rw [haEq]
        exact lt_of_le_of_lt (by exact_mod_cast hnonneg) hyz
      exact_mod_cast hlt
    let B : ℝ := max (Real.sinh 2) a
    have hBnonneg : 0 ≤ B := by
      dsimp [B]
      exact le_trans (by positivity) (le_max_left _ _)
    have hRateB_ge_a : a ≤ continuousTimeSymmetricRandomWalkRateReal B := by
      have hBsinh : Real.sinh 2 ≤ B := by
        dsimp [B]
        exact le_max_left _ _
      have hBtail : B ≤ continuousTimeSymmetricRandomWalkRateReal B :=
        continuousTimeSymmetricRandomWalkRateReal_ge_of_ge_sinh_two hBsinh
      have haB : a ≤ B := by
        dsimp [B]
        exact le_max_right _ _
      exact le_trans haB hBtail
    have haMem :
        a ∈ Set.Icc
          (continuousTimeSymmetricRandomWalkRateReal 0)
          (continuousTimeSymmetricRandomWalkRateReal B) := by
      rw [continuousTimeSymmetricRandomWalkRateReal_zero]
      exact ⟨haPos.le, hRateB_ge_a⟩
    rcases
        (continuousTimeSymmetricRandomWalkRateReal_continuous.continuousOn.surjOn_Icc
          (s := Set.Icc (0 : ℝ) B)
          (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) B by simpa [hBnonneg])
          (show B ∈ Set.Icc (0 : ℝ) B by simpa [hBnonneg]))
          haMem with
      ⟨r, hrMem, hrEq⟩
    have hrNonneg : 0 ≤ r := hrMem.1
    have hrPos : 0 < r := by
      by_contra hr0
      have hrZero : r = 0 := le_antisymm (le_of_not_gt hr0) hrNonneg
      have : a = 0 := by simpa [hrZero, continuousTimeSymmetricRandomWalkRateReal_zero] using hrEq.symm
      exact haPos.ne' this
    refine ⟨r, hrPos, ?_, ?_⟩
    · intro x hx
      have haxE :
          ((a : ℝ) : EReal) <
            ((continuousTimeSymmetricRandomWalkRateReal |x| : ℝ) : EReal) := by
        rw [haEq]
        have hrate :
            z < ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal) := by
          exact lt_of_lt_of_le hzInf (sInf_le ⟨x, hx, rfl⟩)
        simpa [continuousTimeSymmetricRandomWalkRateFunction_coe_ereal,
          continuousTimeSymmetricRandomWalkRateReal_abs] using hrate
      have hax :
          a < continuousTimeSymmetricRandomWalkRateReal |x| := by
        exact_mod_cast haxE
      have hrabs : r ≤ |x| := by
        by_contra hlt
        have hlt' : |x| < r := lt_of_not_ge hlt
        have hrateLe :
            continuousTimeSymmetricRandomWalkRateReal |x| ≤
              continuousTimeSymmetricRandomWalkRateReal r := by
          exact
            continuousTimeSymmetricRandomWalkRateReal_monotoneOn_nonneg
              (show |x| ∈ Set.Ici 0 by exact abs_nonneg x)
              (show r ∈ Set.Ici 0 by exact hrNonneg)
              hlt'.le
        have : a < a := by
          simpa [hrEq] using lt_of_lt_of_le hax hrateLe
        exact lt_irrefl _ this
      -- Proof comment: `r ≤ |x|` excludes the open core `(-r, r)`, so `x` belongs to one tail.
      by_cases hxle : x ≤ -r
      · exact Or.inl hxle
      · have hxr : r ≤ x := by
          by_contra hxr
          have hxIoo : x ∈ Set.Ioo (-r) r := by
            exact ⟨lt_of_not_ge hxle, lt_of_not_ge hxr⟩
          have hlt : |x| < r := by
            exact abs_lt.2 hxIoo
          exact (not_lt_of_ge hrabs) hlt
        exact Or.inr hxr
    · -- Proof comment: the chosen level `a` lies strictly above `-y`, and `a = I(r)` by
      -- construction, so the tail exponent at `r` is strictly below `y`.
      have hay : -y < a := by
        rw [← haEq] at hyz
        exact_mod_cast hyz
      have hltReal : -continuousTimeSymmetricRandomWalkRateReal r < y := by
        have hrate : -y < continuousTimeSymmetricRandomWalkRateReal r := by simpa [hrEq] using hay
        linarith
      exact_mod_cast hltReal

/-- Helper for Exercise 23.2.7: the symmetric two-tail event has the expected Chernoff upper
bound. -/
private theorem continuousTimeSymmetricRandomWalk_symmetricTail_limsup_le_neg_rate
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X)
    {r : ℝ} (hr : 0 < r) :
    Filter.limsup
      (scaledLogMassAlong
        (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
        id (Set.Iic (-r) ∪ Set.Ici r))
      positiveParameterFilter ≤
      -(((continuousTimeSymmetricRandomWalkRateReal r : ℝ) : EReal)) := by
  let L : Set ℝ := Set.Iic (-r)
  let R : Set ℝ := Set.Ici r
  have hLeftPointwise :
      ∀ ε : PositiveParameter,
        scaledLogMassAlong
            (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id L ε ≤
          -(((continuousTimeSymmetricRandomWalkRateReal r : ℝ) : EReal)) := by
    intro ε
    -- Proof comment: optimize the left-tail Chernoff bound at the negative slope
    -- `t = -arsinh r`.
    have ht : -Real.arsinh r ≤ 0 := by
      have harsinh_nonneg : 0 ≤ Real.arsinh r := (Real.arsinh_nonneg_iff).2 hr.le
      linarith
    calc
      scaledLogMassAlong
          (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
          id L ε
        ≤ -((((-Real.arsinh r) * (-r) - (Real.cosh (-Real.arsinh r) - 1) : ℝ) : EReal)) := by
            simpa [L] using
              continuousTimeSymmetricRandomWalk_closedLeftHalfline_le_tilt
                (μ := μ) (X := X) hX (a := -r) (t := -Real.arsinh r) ht ε
      _ = -(((continuousTimeSymmetricRandomWalkRateReal r : ℝ) : EReal)) := by
            congr 1
            rw [continuousTimeSymmetricRandomWalkRateReal_eq_affineAtArsinh,
              Real.cosh_neg, neg_mul_neg]
  have hRightPointwise :
      ∀ ε : PositiveParameter,
        scaledLogMassAlong
            (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id R ε ≤
          -(((continuousTimeSymmetricRandomWalkRateReal r : ℝ) : EReal)) := by
    intro ε
    -- Proof comment: the right-tail Chernoff bound uses the positive optimizer `t = arsinh r`.
    have ht : 0 ≤ Real.arsinh r := (Real.arsinh_nonneg_iff).2 hr.le
    calc
      scaledLogMassAlong
          (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
          id R ε
        ≤ -((((Real.arsinh r) * r - (Real.cosh (Real.arsinh r) - 1) : ℝ) : EReal)) := by
            simpa [R] using
              continuousTimeSymmetricRandomWalk_closedRightHalfline_le_tilt
                (μ := μ) (X := X) hX (b := r) (t := Real.arsinh r) ht ε
      _ = -(((continuousTimeSymmetricRandomWalkRateReal r : ℝ) : EReal)) := by
            congr 1
            rw [continuousTimeSymmetricRandomWalkRateReal_eq_affineAtArsinh]
  have hUnionPointwise :
      ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
        scaledLogMassAlong
            (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id (L ∪ R) ε ≤
          ((ε : ℝ) : EReal) * ENNReal.log (2 : ℝ≥0∞) +
            max
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id L ε)
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id R ε) := by
    exact Filter.Eventually.of_forall fun ε ↦ by
      have hlogTwo : ENNReal.log (2 : ℝ≥0∞) = ((Real.log 2 : ℝ) : EReal) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
        simpa using (ENNReal.log_ofReal_of_pos (show 0 < (2 : ℝ) by norm_num))
      simpa [L, R, hlogTwo, EReal.coe_mul] using
        scaledLogMassAlong_union_le_logTwo_add_max
          (μ := fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
          id L R ε
  have hLeftLimsup :
      Filter.limsup
          (scaledLogMassAlong
            (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id L)
          positiveParameterFilter ≤
        -(((continuousTimeSymmetricRandomWalkRateReal r : ℝ) : EReal)) :=
    Filter.limsup_le_of_le
      (hf := by
        simpa [Filter.IsCoboundedUnder] using
          (Filter.isCobounded_le_of_bot :
            (Filter.map
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id L)
              positiveParameterFilter).IsCobounded (· ≤ ·)))
      (Filter.Eventually.of_forall hLeftPointwise)
  have hRightLimsup :
      Filter.limsup
          (scaledLogMassAlong
            (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id R)
          positiveParameterFilter ≤
        -(((continuousTimeSymmetricRandomWalkRateReal r : ℝ) : EReal)) :=
    Filter.limsup_le_of_le
      (hf := by
        simpa [Filter.IsCoboundedUnder] using
          (Filter.isCobounded_le_of_bot :
            (Filter.map
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id R)
              positiveParameterFilter).IsCobounded (· ≤ ·)))
      (Filter.Eventually.of_forall hRightPointwise)
  calc
    Filter.limsup
        (scaledLogMassAlong
          (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
          id (Set.Iic (-r) ∪ Set.Ici r))
        positiveParameterFilter
      = Filter.limsup
          (scaledLogMassAlong
            (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id (L ∪ R))
          positiveParameterFilter := by simp [L, R]
    _ ≤ Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (2 : ℝ≥0∞) +
              max
                (scaledLogMassAlong
                  (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                  id L ε)
                (scaledLogMassAlong
                  (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                  id R ε))
          positiveParameterFilter := by
            exact Filter.limsup_le_limsup hUnionPointwise
    _ =
        Filter.limsup
          (fun ε : PositiveParameter ↦
            max
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id L ε)
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id R ε))
          positiveParameterFilter := by
            simpa [add_comm] using
              ENNReal.limsup_add_tendsto_zero_right
                (f := fun ε : PositiveParameter ↦
                  max
                    (scaledLogMassAlong
                      (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                      id L ε)
                    (scaledLogMassAlong
                      (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                      id R ε))
                (g := fun ε : PositiveParameter ↦
                  ((ε : ℝ) : EReal) * ENNReal.log (2 : ℝ≥0∞))
                scaledLogTwoCorrection_tendsto_zero
    _ = max
          (Filter.limsup
            (scaledLogMassAlong
              (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
              id L)
            positiveParameterFilter)
          (Filter.limsup
            (scaledLogMassAlong
              (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
              id R)
            positiveParameterFilter) := by
              simpa using
                (limsup_max
                  (f := positiveParameterFilter)
                  (u := scaledLogMassAlong
                    (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                    id L)
                  (v := scaledLogMassAlong
                    (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                    id R))
    _ ≤ -(((continuousTimeSymmetricRandomWalkRateReal r : ℝ) : EReal)) := by
          exact max_le hLeftLimsup hRightLimsup

/-- A Poisson right/left decomposition is a bridge to the intrinsic owner
`IsContinuousTimeSymmetricRandomWalk`. -/
theorem isContinuousTimeSymmetricRandomWalk_of_eq_poissonDifference
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    {Nright Nleft : NNReal → Ω → ℕ}
    (hNright : IsPoissonProcess (1 / 2 : NNReal) μ Nright)
    (hNleft : IsPoissonProcess (1 / 2 : NNReal) μ Nleft)
    (hindep : IndepFun (fun ω t ↦ Nright t ω) (fun ω t ↦ Nleft t ω) μ)
    (hX : X = fun t ω ↦ (Nright t ω : ℤ) - Nleft t ω) :
    IsContinuousTimeSymmetricRandomWalk μ X := by
  letI : IsProbabilityMeasure μ := hNright.isProbabilityMeasure
  refine
    { stochastic := ?_
      zero := ?_
      indepIncrements := ?_
      increment_law := ?_ }
  · intro t
    -- Proof comment: each coordinate of the difference process is measurable because both Poisson
    -- coordinates are measurable and `ℤ` is a countable measurable space.
    have hCastNatInt : Measurable (fun n : ℕ ↦ (n : ℤ)) := measurable_of_countable _
    let hRight : Measurable fun ω ↦ (Nright t ω : ℤ) :=
      hCastNatInt.comp (hNright.stochastic t)
    let hLeft : Measurable fun ω ↦ (Nleft t ω : ℤ) :=
      hCastNatInt.comp (hNleft.stochastic t)
    simpa [hX] using hRight.sub hLeft
  · -- Proof comment: both Poisson coordinates start from `0`, so the difference process does as
    -- well.
    funext ω
    simp [hX, hNright.zero, hNleft.zero]
  · refine HasIndepIncrements.of_nat ?_
    intro t ht _htconst
    let Rinc : ℕ → Ω → ℕ := fun i ω ↦ Nright (t (i + 1)) ω - Nright (t i) ω
    let Linc : ℕ → Ω → ℕ := fun i ω ↦ Nleft (t (i + 1)) ω - Nleft (t i) ω
    let Δ : ℕ → Ω → ℤ := fun i ω ↦ (Rinc i ω : ℤ) - Linc i ω
    have hRindep : iIndepFun Rinc μ := by
      simpa [Rinc] using hNright.indepIncrements.nat (t := t) ht
    have hLindep : iIndepFun Linc μ := by
      simpa [Linc] using hNleft.indepIncrements.nat (t := t) ht
    have hRmeas : ∀ i, AEMeasurable (Rinc i) μ := fun i ↦
      ((hNright.stochastic (t (i + 1))).sub (hNright.stochastic (t i))).aemeasurable
    have hLmeas : ∀ i, AEMeasurable (Linc i) μ := fun i ↦
      ((hNleft.stochastic (t (i + 1))).sub (hNleft.stochastic (t i))).aemeasurable
    let incSeq : (NNReal → ℕ) → ℕ → ℕ := fun f i ↦ f (t (i + 1)) - f (t i)
    have hIncSeqMeas : Measurable incSeq := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact (measurable_pi_apply (t (i + 1))).sub (measurable_pi_apply (t i))
    have hIncSeqIndep :
        IndepFun (fun ω i ↦ Rinc i ω) (fun ω i ↦ Linc i ω) μ := by
      simpa [Rinc, Linc, incSeq] using hindep.comp hIncSeqMeas hIncSeqMeas
    have hPair :
        iIndepFun (fun i ω ↦ (Rinc i ω, Linc i ω)) μ :=
      iIndepFun_pair_of_iIndepFun_of_indepFun
        (μ := μ) Rinc Linc hRindep hRmeas hLindep hLmeas hIncSeqIndep
    have hDelta : iIndepFun Δ μ := by
      simpa [Δ] using
        hPair.comp (fun _ ↦ fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2) (fun _ ↦ measurable_of_countable _)
    -- Proof comment: monotonicity of the Poisson coordinates identifies the `ℤ`-valued increment
    -- of the difference process with the difference of the two nonnegative increment counts.
    convert hDelta using 1
    funext i ω
    have hRmono : Nright (t i) ω ≤ Nright (t (i + 1)) ω := hNright.mono (ht (Nat.le_succ i)) ω
    have hLmono : Nleft (t i) ω ≤ Nleft (t (i + 1)) ω := hNleft.mono (ht (Nat.le_succ i)) ω
    simp [Δ, Rinc, Linc, hX, Int.ofNat_sub hRmono, Int.ofNat_sub hLmono, sub_eq_add_neg]
    abel
  · intro s t hst
    let Rinc : Ω → ℕ := fun ω ↦ Nright t ω - Nright s ω
    let Linc : Ω → ℕ := fun ω ↦ Nleft t ω - Nleft s ω
    have hRlaw :
        HasLaw Rinc (poissonMeasure ((t - s) / 2)) μ := by
      simpa [Rinc, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (hNright.poisson_increment hst)
    have hLlaw :
        HasLaw Linc (poissonMeasure ((t - s) / 2)) μ := by
      simpa [Linc, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (hNleft.poisson_increment hst)
    let castInt : ℕ → ℤ := fun n ↦ (n : ℤ)
    let negCastInt : ℕ → ℤ := fun n ↦ -(n : ℤ)
    have hCastLaw :
        HasLaw castInt ((poissonMeasure ((t - s) / 2)).map castInt)
          (poissonMeasure ((t - s) / 2)) := by
      exact ⟨(measurable_of_countable _).aemeasurable, rfl⟩
    have hNegCastLaw :
        HasLaw negCastInt ((poissonMeasure ((t - s) / 2)).map negCastInt)
          (poissonMeasure ((t - s) / 2)) := by
      exact ⟨(measurable_of_countable _).aemeasurable, rfl⟩
    have hIncIndep : Rinc ⟂ᵢ[μ] Linc := by
      let inc : (NNReal → ℕ) → ℕ := fun f ↦ f t - f s
      have hIncMeas : Measurable inc := (measurable_pi_apply t).sub (measurable_pi_apply s)
      simpa [Rinc, Linc, inc] using hindep.comp hIncMeas hIncMeas
    have hCastIndep :
        (fun ω ↦ castInt (Rinc ω)) ⟂ᵢ[μ] (fun ω ↦ negCastInt (Linc ω)) := by
      have hCastMeas : Measurable castInt := measurable_of_countable _
      have hNegCastMeas : Measurable negCastInt := measurable_of_countable _
      simpa [castInt, negCastInt] using
        hIncIndep.comp hCastMeas hNegCastMeas
    have hLawCast :
        HasLaw (fun ω ↦ castInt (Rinc ω))
          ((poissonMeasure ((t - s) / 2)).map castInt) μ :=
      HasLaw.comp hCastLaw hRlaw
    have hLawNeg :
        HasLaw (fun ω ↦ negCastInt (Linc ω))
          ((poissonMeasure ((t - s) / 2)).map negCastInt) μ :=
      by simpa [negCastInt] using (HasLaw.comp hNegCastLaw hLlaw)
    have hAddLaw :
        HasLaw
          (fun ω ↦ castInt (Rinc ω) + negCastInt (Linc ω))
          (((poissonMeasure ((t - s) / 2)).map castInt) ∗
            ((poissonMeasure ((t - s) / 2)).map negCastInt)) μ :=
      hCastIndep.hasLaw_fun_add hLawCast hLawNeg
    -- Proof comment: the increment law is the additive convolution of the right increment and the
    -- reflected left increment, exactly as in the canonical owner definition.
    have hIncEq :
        (fun ω ↦ castInt (Rinc ω) + negCastInt (Linc ω)) =
          fun ω ↦ X t ω - X s ω := by
      funext ω
      have hRmono : Nright s ω ≤ Nright t ω := hNright.mono hst ω
      have hLmono : Nleft s ω ≤ Nleft t ω := hNleft.mono hst ω
      simp [Rinc, Linc, castInt, negCastInt, hX, Int.ofNat_sub hRmono, Int.ofNat_sub hLmono,
        sub_eq_add_neg]
      abel
    simpa [hIncEq, continuousTimeSymmetricRandomWalkIncrementLaw_eq_conv_map_neg] using hAddLaw

-- Proof sketch: compute the logarithmic moment generating function of the canonical increment law,
-- identify its Legendre transform as the explicit rate function below, and apply the chapter's
-- large-deviation theorem to the rescaled one-time marginals of the continuous-time symmetric
-- random walk.
/-- Exercise 23.2.7: for a continuous-time symmetric random walk on `ℤ` with jump rates `1 / 2`
to the right and left, the family of laws `P_{ε X_{1/ε}}` satisfies the large deviations
principle as `ε ↓ 0`, with rate function
`I(x) = 1 + x arsinh(x) - sqrt (1 + x^2)`. -/
theorem continuousTimeSymmetricRandomWalk_rescaled_satisfiesLDP
    (μ : Measure Ω)
    (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) :
    HasLargeDeviationsPrinciple
      (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX)
      continuousTimeSymmetricRandomWalkRateFunction := by
  refine
    { lowerSemicontinuous :=
        continuousTimeSymmetricRandomWalkRateFunction_isGoodRateFunction.lowerSemicontinuous
      open_lower_bound := ?_
      closed_upper_bound := ?_ }
  · intro U hU
    by_cases hEmpty : U = ∅
    · simp [hEmpty]
    have hUne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    rw [Filter.le_liminf_iff']
    intro y hy
    by_cases hyBot : y = ⊥
    · rcases hUne with ⟨x, hxU⟩
      rcases exists_Ioo_subset_of_isOpen_mem hU hxU with ⟨δ, hδ, hSubset⟩
      have hIntervalLiminf :
          (⊥ : EReal) <
            Filter.liminf
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Ioo (x - δ) (x + δ)))
              positiveParameterFilter := by
        have hLower :
            -((continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ : ℝ) : EReal) ≤
              Filter.liminf
                (scaledLogMassAlong
                  (fun ε ↦
                    (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                  id (Set.Ioo (x - δ) (x + δ)))
                positiveParameterFilter :=
          continuousTimeSymmetricRandomWalk_centeredInterval_liminf_ge_affineError
            (μ := μ) (X := X) hX hδ
        have hFinite :
            (⊥ : EReal) <
              -((continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ : ℝ) :
                EReal) := by
          have hRate :
              (⊥ : EReal) <
                -((continuousTimeSymmetricRandomWalkRateReal x : ℝ) : EReal) := by
            simpa using (EReal.bot_lt_coe (-continuousTimeSymmetricRandomWalkRateReal x))
          have hErr :
              (⊥ : EReal) <
                -((|Real.arsinh x| * δ : ℝ) : EReal) := by
            simpa using (EReal.bot_lt_coe (-(|Real.arsinh x| * δ : ℝ)))
          have hSum :
              (((continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ : ℝ) :
                EReal)) =
                ((continuousTimeSymmetricRandomWalkRateReal x : ℝ) : EReal) +
                  ((|Real.arsinh x| * δ : ℝ) : EReal) := by
            simp
          have hNeg :
              -((continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * δ : ℝ) :
                EReal) =
                -((continuousTimeSymmetricRandomWalkRateReal x : ℝ) : EReal) +
                  -((|Real.arsinh x| * δ : ℝ) : EReal) := by
            rw [hSum]
            simpa using
              EReal.neg_add
                (x := ((continuousTimeSymmetricRandomWalkRateReal x : ℝ) : EReal))
                (y := ((|Real.arsinh x| * δ : ℝ) : EReal))
                (.inl (by simp)) (.inl (by simp))
          rw [hNeg]
          exact (EReal.bot_lt_add_iff).2 ⟨hRate, hErr⟩
        exact lt_of_lt_of_le hFinite hLower
      have hEventuallyInterval :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            (⊥ : EReal) <
              scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Ioo (x - δ) (x + δ)) ε := by
        exact Filter.eventually_lt_of_lt_liminf hIntervalLiminf
      have hEventuallyMono :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Ioo (x - δ) (x + δ)) ε ≤
              scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id U ε := by
        exact Filter.Eventually.of_forall fun ε ↦
          scaledLogMassAlong_mono_of_subset
            (μ := fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id hSubset ε
      filter_upwards [hEventuallyInterval, hEventuallyMono] with ε hεInterval hεMono
      simpa [hyBot] using hεInterval.le.trans hεMono
    have hyTop : y ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hy le_top)
    let yr : ℝ := y.toReal
    have hyr : ((yr : ℝ) : EReal) = y := by
      simpa [yr] using EReal.coe_toReal hyTop hyBot
    have hyInf :
        sInf
            ((fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) '' U) <
          -y := by
      simpa using EReal.neg_strictAnti hy
    obtain ⟨z, hzInf, hzy⟩ := exists_between hyInf
    obtain ⟨w, hwImage, hwz⟩ :=
      exists_lt_of_csInf_lt
        (s := ((fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) '' U))
        (show
          Set.Nonempty
            (((fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) '' U))
            from
          hUne.image (fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) :
            EReal)))
        hzInf
    rcases hwImage with ⟨x, hxU, rfl⟩
    have hyRate :
        y < -(((continuousTimeSymmetricRandomWalkRateReal x : ℝ) : EReal)) := by
      have hyzNeg : y < -z := by
        simpa using EReal.neg_strictAnti hzy
      have hzwNeg :
          -z < -(((continuousTimeSymmetricRandomWalkRateReal x : ℝ) : EReal)) := by
        simpa [continuousTimeSymmetricRandomWalkRateFunction_coe_ereal] using
          EReal.neg_strictAnti hwz
      exact hyzNeg.trans hzwNeg
    have hyRateReal : yr < -continuousTimeSymmetricRandomWalkRateReal x := by
      have hyRateE :
          ((yr : ℝ) : EReal) <
            -(((continuousTimeSymmetricRandomWalkRateReal x : ℝ) : EReal)) := by
        rw [hyr]
        exact hyRate
      exact_mod_cast hyRateE
    rcases exists_Ioo_subset_of_isOpen_mem hU hxU with ⟨r, hrPos, hSubset⟩
    let a : ℝ := |Real.arsinh x|
    let gap : ℝ := -continuousTimeSymmetricRandomWalkRateReal x - yr
    have hGapPos : 0 < gap := by
      dsimp [gap]
      linarith
    by_cases haZero : a = 0
    · let d : ℝ := r / 2
      have hdPos : 0 < d := by
        dsimp [d]
        positivity
      have hdLtR : d < r := by
        dsimp [d]
        linarith
      have hIntervalSubset : Set.Ioo (x - d) (x + d) ⊆ U := by
        apply Set.Subset.trans ?_ hSubset
        intro z hz
        constructor <;> linarith [hz.1, hz.2, hdLtR]
      have hyAtD :
          y <
            -((continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * d : ℝ) : EReal) := by
        rw [show |Real.arsinh x| = a by rfl, haZero, zero_mul, add_zero]
        exact hyRate
      have hIntervalLiminf :
          y <
            Filter.liminf
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Ioo (x - d) (x + d)))
              positiveParameterFilter := by
        exact lt_of_lt_of_le hyAtD
          (continuousTimeSymmetricRandomWalk_centeredInterval_liminf_ge_affineError
            (μ := μ) (X := X) hX hdPos)
      have hEventuallyInterval :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            y <
              scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Ioo (x - d) (x + d)) ε := by
        exact Filter.eventually_lt_of_lt_liminf hIntervalLiminf
      have hEventuallyMono :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Ioo (x - d) (x + d)) ε ≤
              scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id U ε := by
        exact Filter.Eventually.of_forall fun ε ↦
          scaledLogMassAlong_mono_of_subset
            (μ := fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id hIntervalSubset ε
      filter_upwards [hEventuallyInterval, hEventuallyMono] with ε hεInterval hεMono
      exact hεInterval.le.trans hεMono
    · let d : ℝ := min (r / 2) (gap / (2 * a))
      have haPos : 0 < a := by
        have haNonneg : 0 ≤ a := by
          dsimp [a]
          exact abs_nonneg _
        exact lt_of_le_of_ne haNonneg (Ne.symm haZero)
      have hdPos : 0 < d := by
        dsimp [d]
        have hrHalfPos : 0 < r / 2 := by positivity
        have hgapHalfPos : 0 < gap / (2 * a) := by
          have hTwoaPos : 0 < 2 * a := by positivity
          exact div_pos hGapPos hTwoaPos
        exact lt_min hrHalfPos hgapHalfPos
      have hdLeR : d ≤ r / 2 := by
        dsimp [d]
        exact min_le_left _ _
      have hErrorLt : a * d < gap := by
        have hdLe : d ≤ gap / (2 * a) := by
          dsimp [d]
          exact min_le_right _ _
        have hmulLe : a * d ≤ a * (gap / (2 * a)) := by
          exact mul_le_mul_of_nonneg_left hdLe (abs_nonneg _)
        have hhalf :
            a * (gap / (2 * a)) = gap / 2 := by
          field_simp [haZero]
        have hgapHalf : gap / 2 < gap := by linarith
        exact lt_of_le_of_lt (by simpa [hhalf] using hmulLe) hgapHalf
      have hyAtDReal :
          yr < -(continuousTimeSymmetricRandomWalkRateReal x + a * d) := by
        dsimp [gap] at hErrorLt
        linarith
      have hyAtD :
          y <
            -((continuousTimeSymmetricRandomWalkRateReal x + |Real.arsinh x| * d : ℝ) : EReal) := by
        rw [show |Real.arsinh x| = a by rfl, ← hyr]
        exact_mod_cast hyAtDReal
      have hIntervalSubset : Set.Ioo (x - d) (x + d) ⊆ U := by
        apply Set.Subset.trans ?_ hSubset
        intro z hz
        constructor <;> linarith [hz.1, hz.2, hdLeR]
      have hIntervalLiminf :
          y <
            Filter.liminf
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Ioo (x - d) (x + d)))
              positiveParameterFilter := by
        exact lt_of_lt_of_le hyAtD
          (continuousTimeSymmetricRandomWalk_centeredInterval_liminf_ge_affineError
            (μ := μ) (X := X) hX hdPos)
      have hEventuallyInterval :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            y <
              scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Ioo (x - d) (x + d)) ε := by
        exact Filter.eventually_lt_of_lt_liminf hIntervalLiminf
      have hEventuallyMono :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Ioo (x - d) (x + d)) ε ≤
              scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id U ε := by
        exact Filter.Eventually.of_forall fun ε ↦
          scaledLogMassAlong_mono_of_subset
            (μ := fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id hIntervalSubset ε
      filter_upwards [hEventuallyInterval, hEventuallyMono] with ε hεInterval hεMono
      exact hεInterval.le.trans hεMono
  · intro C hC
    by_cases hEmpty : C = ∅
    · have hEventually :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (∅ : Set ℝ) ε = ⊥ := by
        filter_upwards [Filter.Eventually.of_forall fun ε : PositiveParameter ↦ ε.2] with ε hε
        have hεE : (0 : EReal) < ((ε : ℝ) : EReal) := by
          exact_mod_cast hε
        rw [scaledLogMassAlong_def]
        simp [EReal.mul_bot_of_pos hεE]
      have hEmptyLimsup :
          Filter.limsup
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (∅ : Set ℝ))
              positiveParameterFilter ≤
            -sInf ((fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) ''
              (∅ : Set ℝ)) := by
        rw [Filter.limsup_congr hEventually]
        simp
      simpa [hEmpty] using hEmptyLimsup
    by_cases h0 : (0 : ℝ) ∈ C
    · have hEventually :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id C ε ≤ 0 := by
        exact Filter.Eventually.of_forall fun ε ↦
          scaledLogMassAlong_nonpos_of_probability
            (μ := fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            (ε := id) C ε
      have hLimsupNonpos :
          Filter.limsup
              (scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id C)
              positiveParameterFilter ≤
            0 :=
        Filter.limsup_le_of_le
          (hf := by
            simpa [Filter.IsCoboundedUnder] using
              (Filter.isCobounded_le_of_bot :
                (Filter.map
                  (scaledLogMassAlong
                    (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                    id C)
                  positiveParameterFilter).IsCobounded (· ≤ ·)))
          hEventually
      have hZeroMem :
          (0 : EReal) ∈
            ((fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) '' C) := by
        refine ⟨0, h0, ?_⟩
        simpa [continuousTimeSymmetricRandomWalkRateReal_zero] using
          (continuousTimeSymmetricRandomWalkRateFunction_coe_ereal 0)
      have hRateNonneg :
          ∀ z ∈
              ((fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) '' C),
            (0 : EReal) ≤ z := by
        rintro z ⟨x, hx, rfl⟩
        simpa [continuousTimeSymmetricRandomWalkRateFunction_coe_ereal] using
          (show (0 : EReal) ≤ ((continuousTimeSymmetricRandomWalkRateReal x : ℝ) : EReal) by
            exact_mod_cast continuousTimeSymmetricRandomWalkRateReal_nonneg x)
      have hsInfEq :
          sInf
              ((fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) '' C) =
            (0 : EReal) := by
        refine le_antisymm (sInf_le hZeroMem) (le_sInf hRateNonneg)
      simpa [hsInfEq] using hLimsupNonpos
    · have hCne : C.Nonempty := by
        by_contra hCne
        exact hEmpty (Set.not_nonempty_iff_eq_empty.mp hCne)
      rw [Filter.limsup_le_iff']
      intro y hy
      by_cases hyTop : y = ⊤
      · simp [hyTop]
      obtain ⟨z, hzLeft, hzRight⟩ := exists_between hy
      have hzBot : z ≠ ⊥ := ne_bot_of_gt hzLeft
      have hzTop : z ≠ ⊤ := ne_top_of_lt (hzRight.trans_le le_top)
      let yz : ℝ := z.toReal
      have hyz :
          ((yz : ℝ) : EReal) >
            -sInf
              ((fun x ↦ ((continuousTimeSymmetricRandomWalkRateFunction x : ENNReal) : EReal)) '' C) := by
        -- Proof comment: choose a finite real comparison level strictly between the target upper
        -- bound and the ambient test value `y`.
        rw [EReal.coe_toReal hzTop hzBot]
        exact hzLeft
      rcases
          continuousTimeSymmetricRandomWalk_exists_symmetricTailSubset_of_lt_rateInf_closed
            hC hCne h0 hyz with
        ⟨r, hr, hSubset, hTailRateLt⟩
      have hMonoEventually :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id C ε ≤
              scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Iic (-r) ∪ Set.Ici r) ε := by
        exact Filter.Eventually.of_forall fun ε ↦
          scaledLogMassAlong_mono_of_subset
            (μ := fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
            id hSubset ε
      have hTailEventually :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            scaledLogMassAlong
                (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                id (Set.Iic (-r) ∪ Set.Ici r) ε < z := by
        have hTailLimsupLt :
            Filter.limsup
                (scaledLogMassAlong
                  (fun ε ↦ (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε : Measure ℝ))
                  id (Set.Iic (-r) ∪ Set.Ici r))
                positiveParameterFilter < z := by
          rw [← EReal.coe_toReal hzTop hzBot]
          exact
            (continuousTimeSymmetricRandomWalk_symmetricTail_limsup_le_neg_rate
              (μ := μ) (X := X) hX hr).trans_lt hTailRateLt
        exact Filter.eventually_lt_of_limsup_lt hTailLimsupLt
      filter_upwards [hMonoEventually, hTailEventually] with ε hεMono hεTail
      exact hεMono.trans (hεTail.le.trans hzRight.le)

/-- Bridge form of Exercise 23.2.7: a Poisson right/left decomposition yields the intrinsic
continuous-time symmetric random-walk hypothesis, so the LDP follows from the source-facing owner
theorem. -/
theorem continuousTimeSymmetricRandomWalk_rescaled_satisfiesLDP_of_eq_poissonDifference
    (μ : Measure Ω)
    (X : NNReal → Ω → ℤ)
    {Nright Nleft : NNReal → Ω → ℕ}
    (hNright : IsPoissonProcess (1 / 2 : NNReal) μ Nright)
    (hNleft : IsPoissonProcess (1 / 2 : NNReal) μ Nleft)
    (hindep : IndepFun (fun ω t ↦ Nright t ω) (fun ω t ↦ Nleft t ω) μ)
    (hX : X = fun t ω ↦ (Nright t ω : ℤ) - Nleft t ω) :
    HasLargeDeviationsPrinciple
      (continuousTimeSymmetricRandomWalkRescaledLaw μ X
        (isContinuousTimeSymmetricRandomWalk_of_eq_poissonDifference
          μ X hNright hNleft hindep hX))
      continuousTimeSymmetricRandomWalkRateFunction := by
  exact continuousTimeSymmetricRandomWalk_rescaled_satisfiesLDP
    μ X
    (isContinuousTimeSymmetricRandomWalk_of_eq_poissonDifference
      μ X hNright hNleft hindep hX)

end ProbabilityTheory
