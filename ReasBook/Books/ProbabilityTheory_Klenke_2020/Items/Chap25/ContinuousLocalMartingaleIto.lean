/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_76
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_17

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : Filtration NNReal mΩ}

/-- Pull back a real-valued continuous-time process along a map of sample spaces. -/
def pullbackProcess {Ω' : Type v} (π : Ω' → Ω) (X : Process) : NNReal → Ω' → ℝ :=
  fun t ω ↦ X t (π ω)

/-- Center a process at its initial value, i.e. replace `X` by `t ↦ X_t - X_0`. -/
def processCenteredAtZero (X : Process) : Process :=
  fun t ω ↦ X t ω - X 0 ω

section

omit mΩ

-- Proof sketch: unfold `pullbackProcess`; the pulled-back process is defined pointwise by
-- precomposing each time slice with `π`.
/-- Evaluating `pullbackProcess π X` at time `t` and sample point `ω` gives `X t (π ω)`. -/
@[simp] theorem pullbackProcess_apply
    {Ω' : Type v} (π : Ω' → Ω) (X : NNReal → Ω → ℝ) (t : NNReal) (ω : Ω') :
    pullbackProcess π X t ω = X t (π ω) :=
  rfl

end

/-- Data expressing that the canonical square-variation process `⟨M⟩` of a continuous local
martingale `M` is absolutely continuous with respect to Lebesgue measure, with nonnegative density
`a`. -/
structure HasAbsolutelyContinuousSquareVariation
    (M : Process) (hM : IsContinuousLocalMartingale ℱ μ M) where
  /-- The Lebesgue density `a_t` of the square variation `⟨M⟩`. -/
  density : NNReal → Ω → NNReal
  /-- The density is progressively measurable. -/
  density_progMeasurable : ProgMeasurable ℱ fun t ω ↦ (density t ω : ℝ)
  /-- The canonical square variation of `M` is obtained by integrating the density on `[0,t]`. -/
  squareVariation_eq :
    ∀ t : NNReal, ∀ ω : Ω,
      continuousSquareVariationProcess hM t ω =
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (density s.toNNReal ω : ℝ)

/-- The bracket-density integral `∫₀ᵗ H_s² d⟨M⟩_s`, written using a density for `⟨M⟩`. -/
def bracketDensityIntegralUpTo
    {M : Process} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) (H : Process) : Process :=
  fun t ω ↦
    ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
      (H s.toNNReal ω) ^ 2 * (hbr.density s.toNNReal ω : ℝ)

/-- The coefficient `sqrt (d⟨M⟩ / dt)` that realizes `M` as a Brownian local Itô integral on an
extension space. -/
def squareVariationDensityRoot
    {M : Process} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) : Process :=
  fun t ω ↦ Real.sqrt (hbr.density t ω : ℝ)

/-- On a Brownian representation of `M`, the Itô integral `∫ H dM` is represented by the Brownian
integrand `H * sqrt (d⟨M⟩ / dt)`. -/
def brownianRepresentationItoIntegrand
    {M : Process} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) (H : Process) : Process :=
  fun t ω ↦ H t ω * squareVariationDensityRoot hbr t ω

/-- The textbook norm `‖H‖_M` for an integrand against a continuous local martingale `M`, written
via the bracket density `d⟨M⟩ / dt`. -/
noncomputable def itoIntegrandNorm
    (M : Process) {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) (H : Process) : ℝ≥0∞ :=
  eLpNorm
    (MeasureTheory.processToTimeSpaceFun (brownianRepresentationItoIntegrand hbr H))
    2
    (MeasureTheory.processMeasure μ)

/-- The integrand `H` has finite textbook norm `‖H‖_M`. -/
def HasFiniteItoIntegrandNorm
    (M : Process) {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) (H : Process) : Prop :=
  itoIntegrandNorm M hbr H < ∞

/-- Convergence in the textbook norm `‖·‖_M`. -/
def TendstoInItoIntegrandNorm
    (M : Process) {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (Hs : ℕ → Process) (H : Process) : Prop :=
  Tendsto
    (fun n ↦ itoIntegrandNorm M hbr (fun t ω ↦ Hs n t ω - H t ω))
    atTop
    (𝓝 (0 : ℝ≥0∞))

/-- A localizing sequence for the stochastic integral against `M` is a stopping-time
approximation to `∞` along which the truncated integrands have finite textbook norm `‖·‖_M`. -/
def IsItoLocalizingSequence
    (M : Process) {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : Process) (τSeq : ℕ → Ω → NNReal) : Prop :=
  IsStoppingTimeApproximationUpTo ℱ μ
      (fun n ω ↦ (τSeq n ω : ENNReal)) (fun _ ↦ ∞) ∧
    ∀ n : ℕ,
      HasFiniteItoIntegrandNorm M hbr
        (processBeforeStoppingTime H fun ω ↦ (τSeq n ω : ENNReal))

/-- A family of predictable simple processes approximates `H` in the textbook norm `‖·‖_M` if
every stage has finite `M`-norm and the `M`-norm of the difference tends to `0`. -/
def IsPredictableSimpleItoApproximation
    (M : Process) {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : Process) (Hs : ℕ → PredictableSimpleProcess ℱ) : Prop :=
  (∀ m : ℕ, HasFiniteItoIntegrandNorm M hbr (Hs m : Process)) ∧
    TendstoInItoIntegrandNorm M hbr (fun m ↦ (Hs m : Process)) H

namespace IsPredictableSimpleItoApproximation

/-- Every stage of a predictable-simple Itô approximation has finite `M`-norm. -/
theorem hasFiniteItoIntegrandNorm
    {M : Process} {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    {H : Process} {Hs : ℕ → PredictableSimpleProcess ℱ}
    (hHs : IsPredictableSimpleItoApproximation M hbr H Hs) (m : ℕ) :
    HasFiniteItoIntegrandNorm M hbr (Hs m : Process) :=
  hHs.1 m

end IsPredictableSimpleItoApproximation

/-- A process `N` realizes the Itô integral `∫ H dM` if, after pulling back to a Brownian
representation of the centered martingale `M - M₀`, the pulled-back process `N` is the Brownian
local Itô integral of `H * sqrt (d⟨M⟩ / dt)` with respect to the same Brownian motion that
realizes `M - M₀` itself through the canonical Brownian-side owner
`IsBrownianLocalItoIntegral`. This keeps the stochastic integral tied to the actual driver `M`,
rather than only to its quadratic variation, without incorrectly forcing `M` itself to start from
`0`; Definition 25.16 remains internal as a bridge instead of exposing a chosen realization
operator. -/
def IsContinuousLocalMartingaleItoIntegral
    {M : Process} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) (H N : Process) : Prop :=
  ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (law : ProbabilityMeasure Ω') (lift : Ω' → Ω)
      (filtration : Filtration NNReal mΩ') (brownian : NNReal → Ω' → ℝ),
    MeasurePreserving lift (law : Measure Ω') μ ∧
      IsBrownianLocalItoIntegral filtration (law : Measure Ω') brownian
        (pullbackProcess lift (squareVariationDensityRoot hbr))
        (pullbackProcess lift (processCenteredAtZero M)) ∧
      IsBrownianLocalItoIntegral filtration (law : Measure Ω') brownian
        (pullbackProcess lift (brownianRepresentationItoIntegrand hbr H))
        (pullbackProcess lift N)

-- Proof sketch: pull back the centered driver `M - M 0` to a Brownian representation, use the
-- elementary Brownian Itô integral on the extension for the predictable simple integrand, and
-- descend the resulting process to the original space. Uniqueness follows from the canonical
-- extension-side elementary integral and the uniqueness of continuous local Itô realizations.
/-- A predictable simple integrand with finite `M`-norm admits a canonical Itô integral process
against the continuous local martingale `M`; this is the source-facing elementary integral
`I^M(H)`. -/
theorem exists_unique_predictableSimpleItoIntegral
    {M : Process} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : PredictableSimpleProcess ℱ)
    (hH : HasFiniteItoIntegrandNorm M hbr (H : Process)) :
    ∃! N : Process,
      IsContinuousLocalMartingaleItoIntegral hbr H N := sorry

/-- The canonical elementary Itô integral process `I^M(H)` of a predictable simple integrand `H`
against the continuous local martingale `M`. -/
noncomputable def continuousLocalMartingalePredictableSimpleItoIntegral
    {M : Process} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : PredictableSimpleProcess ℱ)
    (hH : HasFiniteItoIntegrandNorm M hbr (H : Process)) : Process :=
  Classical.choose
    ((exists_unique_predictableSimpleItoIntegral hM hbr H hH).exists)

namespace IsPredictableSimpleItoApproximation

/-- The canonical elementary Itô integrals attached to a predictable-simple approximation family.
-/
noncomputable def integralSequence
    {M : Process} {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    {H : Process} {Hs : ℕ → PredictableSimpleProcess ℱ}
    (hHs : IsPredictableSimpleItoApproximation M hbr H Hs) :
    ℕ → Process :=
  fun m ↦
    continuousLocalMartingalePredictableSimpleItoIntegral hM hbr
      (Hs m) (hHs.hasFiniteItoIntegrandNorm m)

end IsPredictableSimpleItoApproximation

end ProbabilityTheory
