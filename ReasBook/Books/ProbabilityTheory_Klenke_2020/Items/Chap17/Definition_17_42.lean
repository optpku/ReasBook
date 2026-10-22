/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-!
### Definition 17.42

For a measure `μ` on `E`, the source-facing left action `μ p` is the measure action
`measureMatrixAction μ p = discreteMatrixKernel p ∘ₘ μ`. For a real-valued function `f`, the
source-facing right action `p f` is the rowwise series
`x ↦ ∑' y, (p x y).toReal * f y` under an explicit global convergence witness. The corresponding
kernel integral `x ↦ ∫ y, f y ∂ discreteMatrixKernel p x` is kept as an auxiliary bridge surface.
-/

section MeasureAction

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- The textbook left action `μ p`, implemented by composing the initial measure `μ` with the
canonical owner kernel `discreteMatrixKernel p`. -/
abbrev measureMatrixAction (μ : Measure E) (p : E → E → ℝ≥0∞) : Measure E :=
  discreteMatrixKernel p ∘ₘ μ

scoped[ProbabilityTheory] infixr:73 " ⋆ₘ " => measureMatrixAction

/-- Expanding `measureMatrixAction` recovers composition with the canonical discrete kernel. -/
@[simp] theorem measureMatrixAction_def (μ : Measure E) (p : E → E → ℝ≥0∞) :
    measureMatrixAction μ p = discreteMatrixKernel p ∘ₘ μ := rfl

/-- The source-facing specification of `measureMatrixAction` is composition with
`discreteMatrixKernel p`. -/
theorem measureMatrixAction_spec (μ : Measure E) (p : E → E → ℝ≥0∞) :
    measureMatrixAction μ p = discreteMatrixKernel p ∘ₘ μ := by
  -- Proof comment: this companion theorem is just the abbrev expanded once.
  rfl

/-- Expanding the left action `μ ⋆ₘ p` recovers composition with the canonical discrete kernel. -/
@[simp] theorem measureMatrixAction_eq_comp (μ : Measure E) (p : E → E → ℝ≥0∞) :
    μ ⋆ₘ p = discreteMatrixKernel p ∘ₘ μ := rfl

/-- Evaluating the canonical discrete matrix kernel on a singleton recovers the corresponding
matrix entry. -/
@[simp] theorem discreteMatrixKernel_apply_singleton
    (p : E → E → ℝ≥0∞) (x y : E) :
    discreteMatrixKernel p y ({x} : Set E) = p y x := by
  -- Reduce the row measure to the defining sum of weighted Dirac masses.
  rw [discreteMatrixKernel_apply]
  simp +contextual [tsum_eq_single x]

-- Proof sketch: expand the canonical discrete kernel `discreteMatrixKernel p`, rewrite the
-- measure-kernel composition `(μ ⋆ₘ p) {x}` by
-- `Measure.comp_eq_sum_of_countable` on the countable discrete state space, and then evaluate each
-- row measure on the singleton `{x}`.
/-- The textbook entrywise left action
`∑' y, μ {y} * p y x` is exactly the singleton mass at `x` of the source-facing action `μ ⋆ₘ p`
on a countable discrete state space. -/
theorem comp_discreteMatrixKernel_apply_singleton_eq_tsum
    [Countable E] (μ : Measure E) (p : E → E → ℝ≥0∞) (x : E) :
    (μ ⋆ₘ p) {x} = ∑' y : E, μ {y} * p y x := by
  -- Expand the measure action into the countable sum of row measures weighted by singleton masses.
  rw [measureMatrixAction_eq_comp, Measure.comp_eq_sum_of_countable]
  rw [Measure.sum_apply _ (measurableSet_singleton x)]
  -- Each summand is the singleton mass of the corresponding row of `discreteMatrixKernel p`.
  congr with y
  rw [Measure.smul_apply]
  simpa [mul_comm] using
    congrArg (fun t : ℝ≥0∞ ↦ μ {y} * t) (discreteMatrixKernel_apply_singleton p x y)

end MeasureAction

section FunctionAction

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- The row action `p f(x)` is defined at `x` when every weight in the row `y ↦ p x y` is finite
and the defining series converges. -/
def matrixFunctionActionConvergesAt (p : E → E → ℝ≥0∞) (f : E → ℝ) (x : E) : Prop :=
  (∀ y : E, p x y ≠ ∞) ∧ Summable (fun y : E ↦ (p x y).toReal * f y)

/-- The pointwise value of the textbook right action `p f(x)` under a witness that the defining
series converges at `x`. -/
def matrixFunctionActionAt
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (x : E)
    (_ : matrixFunctionActionConvergesAt p f x) : ℝ :=
  ∑' y : E, (p x y).toReal * f y

/-- The textbook right action `p f` exists when the defining row series converges at every
state. -/
def matrixFunctionActionExists (p : E → E → ℝ≥0∞) (f : E → ℝ) : Prop :=
  ∀ x : E, matrixFunctionActionConvergesAt p f x

-- Semantic recall: `IsHarmonic` in Definition 17.43 is phrased through kernel integrals, so this
-- file keeps both the source-facing series action and the auxiliary integral bridge.
/-- The source-facing right action `p f` is the witness-bearing rowwise series
`x ↦ ∑' y, (p x y).toReal * f y`, defined when the corresponding rows converge globally. -/
def matrixFunctionAction
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (hpf : matrixFunctionActionExists p f) : E → ℝ :=
  fun x ↦ matrixFunctionActionAt p f x (hpf x)

scoped[ProbabilityTheory] notation:73 p " ⋆ᶠ[" hpf "] " f => matrixFunctionAction p f hpf

/-- The auxiliary kernel-integral right action against `discreteMatrixKernel p`. -/
abbrev matrixFunctionIntegralAction
    (p : E → E → ℝ≥0∞) (f : E → ℝ) : E → ℝ :=
  fun x ↦ ∫ y, f y ∂ discreteMatrixKernel p x

/-- The auxiliary witness-bearing series action is an explicit synonym for the source-facing
right action `matrixFunctionAction`. -/
abbrev matrixFunctionSeriesAction
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (hpf : matrixFunctionActionExists p f) : E → ℝ :=
  matrixFunctionAction p f hpf

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- Expanding `matrixFunctionActionAt` recovers the defining rowwise series. -/
@[simp] theorem matrixFunctionActionAt_def
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (x : E)
    (hpf : matrixFunctionActionConvergesAt p f x) :
    matrixFunctionActionAt p f x hpf = ∑' y : E, (p x y).toReal * f y := rfl

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- The convergence witness for `p f(x)` records that the row weights are finite. -/
theorem matrixFunctionActionConvergesAt.neTop
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (x : E)
    (hpf : matrixFunctionActionConvergesAt p f x) :
    ∀ y : E, p x y ≠ ∞ :=
  hpf.1

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- The convergence witness for `p f(x)` records summability of the defining row series. -/
theorem matrixFunctionActionConvergesAt.summable
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (x : E)
    (hpf : matrixFunctionActionConvergesAt p f x) :
    Summable (fun y : E ↦ (p x y).toReal * f y) :=
  hpf.2

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- Expanding `matrixFunctionAction` recovers the witness-indexed pointwise rowwise
series action. -/
@[simp] theorem matrixFunctionAction_def
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (hpf : matrixFunctionActionExists p f) :
    matrixFunctionAction p f hpf = fun x ↦ matrixFunctionActionAt p f x (hpf x) := rfl

/-- Expanding `matrixFunctionIntegralAction` recovers the canonical row integral against
`discreteMatrixKernel p`. -/
@[simp] theorem matrixFunctionIntegralAction_def
    (p : E → E → ℝ≥0∞) (f : E → ℝ) :
    matrixFunctionIntegralAction p f = fun x ↦ ∫ y, f y ∂ discreteMatrixKernel p x := rfl

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- Expanding `matrixFunctionSeriesAction` recovers the witness-indexed pointwise series
action. -/
@[simp] theorem matrixFunctionSeriesAction_def
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (hpf : matrixFunctionActionExists p f) :
    matrixFunctionSeriesAction p f hpf = fun x ↦ matrixFunctionActionAt p f x (hpf x) := rfl

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- The source-facing specification of `matrixFunctionAction` is the defining rowwise series
owner. -/
theorem matrixFunctionAction_spec
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (hpf : matrixFunctionActionExists p f) (x : E) :
    matrixFunctionAction p f hpf x = matrixFunctionActionAt p f x (hpf x) := rfl

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- The auxiliary witness-bearing series surface expands to the defining pointwise row action. -/
theorem matrixFunctionSeriesAction_spec
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (hpf : matrixFunctionActionExists p f) (x : E) :
    matrixFunctionSeriesAction p f hpf x = matrixFunctionActionAt p f x (hpf x) := rfl

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- Evaluating the source-facing right action `p ⋆ᶠ[hpf] f` at `x` recovers the
defining series. -/
@[simp] theorem matrixFunctionAction_apply
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (hpf : matrixFunctionActionExists p f) (x : E) :
    matrixFunctionAction p f hpf x = ∑' y : E, (p x y).toReal * f y := rfl

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- Evaluating the auxiliary witness-bearing right action `matrixFunctionSeriesAction p f hpf`
at `x` recovers the defining series. -/
@[simp] theorem matrixFunctionSeriesAction_apply
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (hpf : matrixFunctionActionExists p f) (x : E) :
    matrixFunctionSeriesAction p f hpf x = ∑' y : E, (p x y).toReal * f y := rfl

/-- The helper `matrixFunctionIntegralAction` is the rowwise kernel integral formula. -/
theorem matrixFunctionIntegralAction_spec
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (x : E) :
    matrixFunctionIntegralAction p f x = ∫ y, f y ∂ discreteMatrixKernel p x := rfl

/-- Evaluating `matrixFunctionIntegralAction` at `x` recovers the canonical row integral. -/
@[simp] theorem matrixFunctionIntegralAction_apply
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (x : E) :
    matrixFunctionIntegralAction p f x = ∫ y, f y ∂ discreteMatrixKernel p x := rfl

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- Every entry of a stochastic matrix is finite because it is
dominated by the corresponding row sum `1`. -/
private theorem entry_neTop_of_isStochastic
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) :
    ∀ x y : E, p x y ≠ ∞ := by
  intro x y
  -- Compare one entry with the full stochastic row sum.
  have hle : p x y ≤ 1 := by
    calc
      p x y ≤ ∑' z : E, p x z := ENNReal.le_tsum y
      _ = 1 := hp x
  exact (lt_of_le_of_lt hle (by simp)).ne

/-- A stochastic row `y ↦ p x y` defines a probability mass function
whose associated measure is exactly the canonical row measure `discreteMatrixKernel p x`. -/
private theorem discreteMatrixKernelRow_eq_toMeasure
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (x : E) :
    let q : PMF E := ⟨fun y : E ↦ p x y, ENNReal.summable.hasSum_iff.2 (hp x)⟩
    discreteMatrixKernel p x = q.toMeasure := by
  let q : PMF E := ⟨fun y : E ↦ p x y, ENNReal.summable.hasSum_iff.2 (hp x)⟩
  ext s hs
  -- Compare both measures by evaluating them on an arbitrary measurable set.
  -- Route correction: first name the PMF row `q`, then rewrite both sides into the same
  -- indicator-sum normal form instead of rewriting the `toMeasure` side blindly.
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ hs]
  change ∑' i : E, (p x i • Measure.dirac i) s = q.toMeasure s
  calc
    ∑' i : E, (p x i • Measure.dirac i) s
        = ∑' i : E, s.indicator (fun y : E ↦ p x y) i := by
            refine tsum_congr fun i ↦ ?_
            by_cases hi : i ∈ s <;> simp [Measure.smul_apply, hi]
    _ = q.toMeasure s := by
        simpa [q] using (q.toMeasure_apply hs).symm

/-- Absolute summability of the row action gives Bochner
integrability of `f` against the row measure `discreteMatrixKernel p x`. -/
private theorem integrable_discreteMatrixKernelRow_of_summableNorm
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (f : E → ℝ) (x : E)
    (hpf : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖)) :
    Integrable f (discreteMatrixKernel p x) := by
  refine ⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩
  -- Compute the norm integral rowwise on the defining Dirac decomposition.
  rw [hasFiniteIntegral_iff_norm, discreteMatrixKernel_apply, lintegral_sum_measure]
  have hterm :
      (fun y : E ↦ ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂p x y • Measure.dirac y) =
        fun y : E ↦ ENNReal.ofReal ((p x y).toReal * ‖f y‖) := by
    funext y
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    have hentry :
        p x y = ENNReal.ofReal (p x y).toReal :=
      (ENNReal.ofReal_toReal (entry_neTop_of_isStochastic p hp x y)).symm
    calc
      p x y * ENNReal.ofReal ‖f y‖
          = ENNReal.ofReal (p x y).toReal * ENNReal.ofReal ‖f y‖ := by
            simpa using congrArg (fun t : ℝ≥0∞ ↦ t * ENNReal.ofReal ‖f y‖) hentry
      _ = ENNReal.ofReal ((p x y).toReal * ‖f y‖) := by
            exact
              (show
                  ENNReal.ofReal ((p x y).toReal * ‖f y‖) =
                    ENNReal.ofReal (p x y).toReal * ENNReal.ofReal ‖f y‖ from
                ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
  rw [hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun y ↦ by positivity) hpf]
  simp

/-- Absolute summability of the row action forces convergence of the textbook series at that
row. -/
private theorem matrixFunctionActionConvergesAt_of_summableNorm
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (f : E → ℝ) (x : E)
    (hpf : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖)) :
    matrixFunctionActionConvergesAt p f x := by
  refine ⟨entry_neTop_of_isStochastic p hp x, ?_⟩
  -- Proof comment: absolute convergence of the row implies convergence of the real-valued series.
  have hnorm : Summable (fun y : E ↦ ‖(p x y).toReal * f y‖) := by
    simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hpf
  exact summable_norm_iff.mp hnorm

-- Semantic recall: the canonical PMF bridge here is `PMF.toMeasure_apply`, and the row integral
-- expansion is `PMF.integral_eq_tsum`.
-- Proof sketch: expand `discreteMatrixKernel p x` as the row measure
-- `∑' y, p x y • δ_y`, use `hp` to ensure every row weight is finite, use the absolute
-- summability hypothesis to obtain Bochner integrability, and then evaluate the integral termwise
-- on the Dirac masses.
/-- Definition 17.42. For a stochastic transition matrix `p`, the row integral against the
canonical owner measure `discreteMatrixKernel p x` agrees with the explicit series
`∑' y, (p x y).toReal * f y` whenever the row action is absolutely summable. The stochastic
hypothesis is the source-faithful finiteness condition ensuring that `toReal` does not erase
infinite matrix entries. -/
theorem integral_discreteMatrixKernel_eq_tsum
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (f : E → ℝ) (x : E)
    (hpf : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖)) :
    ∫ y, f y ∂ discreteMatrixKernel p x = ∑' y : E, (p x y).toReal * f y := by
  let q : PMF E := ⟨fun y : E ↦ p x y, ENNReal.summable.hasSum_iff.2 (hp x)⟩
  have hrow : discreteMatrixKernel p x = q.toMeasure := by
    simpa [q] using discreteMatrixKernelRow_eq_toMeasure p hp x
  have hint : Integrable f q.toMeasure := by
    simpa [hrow] using integrable_discreteMatrixKernelRow_of_summableNorm p hp f x hpf
  -- Proof comment: rewrite the row kernel as the corresponding `PMF` measure and apply the
  -- standard discrete integral formula there.
  calc
    ∫ y, f y ∂ discreteMatrixKernel p x = ∫ y, f y ∂ q.toMeasure := by rw [hrow]
    _ = ∑' y : E, (q y).toReal • f y := PMF.integral_eq_tsum q f hint
    _ = ∑' y : E, (p x y).toReal * f y := by
          simp_rw [smul_eq_mul]
          rfl

/-- Under the same absolute-summability hypothesis, the Bochner integral recovers the
source-facing value of `p f(x)`. -/
theorem integral_discreteMatrixKernel_eq_matrixFunctionActionAt
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (f : E → ℝ) (x : E)
    (hpf : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖)) :
    ∫ y, f y ∂ discreteMatrixKernel p x =
      matrixFunctionActionAt p f x
        (matrixFunctionActionConvergesAt_of_summableNorm p hp f x hpf) :=
    by
  -- Proof comment: the source-facing action is definitionally the same rowwise series.
  simpa [matrixFunctionActionAt_def] using
    integral_discreteMatrixKernel_eq_tsum p hp f x hpf

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- The source-facing action `p ⋆ᶠ[hpf] f` is exactly the textbook rowwise series at `x`. -/
theorem matrixFunctionAction_eq_tsum
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (hpf : matrixFunctionActionExists p f) (x : E) :
    matrixFunctionAction p f hpf x = ∑' y : E, (p x y).toReal * f y := rfl

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- The source-facing action `p ⋆ᶠ[hpf] f` agrees with the auxiliary witness-bearing series
value at `x`. -/
theorem matrixFunctionAction_eq_matrixFunctionActionAt
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (hpf : matrixFunctionActionExists p f) (x : E) :
    matrixFunctionAction p f hpf x = matrixFunctionActionAt p f x (hpf x) := rfl

/-- Under the same absolute-summability hypothesis, the auxiliary kernel-integral action agrees
with the textbook rowwise series at `x`. -/
theorem matrixFunctionIntegralAction_eq_tsum
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (f : E → ℝ) (x : E)
    (hpf : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖)) :
    matrixFunctionIntegralAction p f x = ∑' y : E, (p x y).toReal * f y := by
  simpa [matrixFunctionIntegralAction_apply] using
    integral_discreteMatrixKernel_eq_tsum p hp f x hpf

/-- Under the same absolute-summability hypothesis, the auxiliary kernel-integral action agrees
with the source-facing value of `p f(x)`. -/
theorem matrixFunctionIntegralAction_eq_matrixFunctionActionAt
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (f : E → ℝ) (x : E)
    (hpf : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖)) :
    matrixFunctionIntegralAction p f x =
      matrixFunctionActionAt p f x
        (matrixFunctionActionConvergesAt_of_summableNorm p hp f x hpf) := by
  simpa [matrixFunctionIntegralAction_apply] using
    integral_discreteMatrixKernel_eq_matrixFunctionActionAt p hp f x hpf

end FunctionAction

end ProbabilityTheory
