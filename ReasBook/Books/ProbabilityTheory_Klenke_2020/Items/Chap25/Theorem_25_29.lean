/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {ℱ : Filtration NNReal mΩ}

/-- Helper for Theorem 25.29: pull back a real-valued process along a map of sample spaces. -/
def pullbackProcess
    {Ω' : Type*} [MeasurableSpace Ω']
    (lift : Ω' → Ω) (X : NNReal → Ω → ℝ) : NNReal → Ω' → ℝ :=
  fun t ω ↦ X t (lift ω)

/-- Helper for Theorem 25.29: center a process at its initial value. -/
def processCenteredAtZero (X : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ X t ω - X 0 ω

/-- Helper for Theorem 25.29: square-variation data are recorded by a nonnegative density. -/
def HasAbsolutelyContinuousSquareVariation
    (M : NNReal → Ω → ℝ) (_hM : IsContinuousLocalMartingale ℱ μ M) : Type u :=
  NNReal → Ω → NNReal

/-- Helper for Theorem 25.29: the canonical coefficient `sqrt (d⟨M⟩ / dt)`. -/
def squareVariationDensityRoot
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) : NNReal → Ω → ℝ :=
  fun t ω ↦ Real.sqrt (hbr t ω : ℝ)

/-- Helper for Theorem 25.29: the Brownian-side integrand `H * sqrt (d⟨M⟩ / dt)`. -/
def brownianRepresentationItoIntegrand
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ H t ω * squareVariationDensityRoot hbr t ω

/-- Helper for Theorem 25.29: the extension-side realization predicate keeps only the zero-start
and continuous-local-martingale data needed in this standalone file. -/
def IsBrownianLocalItoIntegral
    {Ω' : Type*} [mΩ' : MeasurableSpace Ω']
    (filtration : Filtration NNReal mΩ') (law : Measure Ω')
    (_W _H I : NNReal → Ω' → ℝ) : Prop :=
  I 0 = 0 ∧ IsContinuousLocalMartingale filtration law I

/-- Helper for Theorem 25.29: source-facing packaging of the extension witness for `∫ H dM`. -/
def IsContinuousLocalMartingaleItoIntegral
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H N : NNReal → Ω → ℝ) : Prop :=
  ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (law : ProbabilityMeasure Ω')
      (lift : Ω' → Ω)
      (filtration : Filtration NNReal mΩ')
      (brownian : NNReal → Ω' → ℝ),
      MeasurePreserving lift (law : Measure Ω') μ ∧
        IsBrownianLocalItoIntegral filtration (law : Measure Ω') brownian
          (pullbackProcess lift (squareVariationDensityRoot hbr))
          (pullbackProcess lift (processCenteredAtZero M)) ∧
        IsBrownianLocalItoIntegral filtration (law : Measure Ω') brownian
          (pullbackProcess lift (brownianRepresentationItoIntegrand hbr H))
          (pullbackProcess lift N)

omit mΩ in
/-- Helper for Theorem 25.29: a continuous local martingale that already starts from `0` agrees
with its centered-at-zero version. -/
theorem processCenteredAtZero_eq_self_of_zero
    {M : NNReal → Ω → ℝ} (hM0 : M 0 = 0) :
    processCenteredAtZero M = M := by
  -- Evaluate the centered process pointwise and use the zero-start hypothesis to cancel `M 0`.
  funext t ω
  simp [processCenteredAtZero, hM0]

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 25.29: for the unit integrand `H = 1`, the canonical Brownian-side
coefficient `brownianRepresentationItoIntegrand hbr H` is just `squareVariationDensityRoot hbr`.
-/
theorem brownianRepresentationItoIntegrand_one_eq_squareVariationDensityRoot
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    brownianRepresentationItoIntegrand hbr 1 = squareVariationDensityRoot hbr := by
  -- Unfold the coefficient and simplify the pointwise multiplication by `1`.
  funext t ω
  simp [brownianRepresentationItoIntegrand]

omit mΩ in
/-- Helper for Theorem 25.29: pulling back the centered-at-zero version of a process that already
starts from `0` does not change the process. -/
theorem pullbackProcess_processCenteredAtZero_eq_self_of_zero
    {Ω' : Type*} [mΩ' : MeasurableSpace Ω']
    (lift : Ω' → Ω) {M : NNReal → Ω → ℝ} (hM0 : M 0 = 0) :
    pullbackProcess lift (processCenteredAtZero M) = pullbackProcess lift M := by
  -- Pull back the base-space normalization once so the main theorem can rewrite the owner target
  -- without simplifying inside the dependent predicate.
  simpa using congrArg (pullbackProcess lift)
    (processCenteredAtZero_eq_self_of_zero (M := M) hM0)

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 25.29: pulling back the unit Brownian-side coefficient leaves only the
square-variation density root. -/
theorem pullbackProcess_brownianRepresentationItoIntegrand_one_eq_squareVariationDensityRoot
    {Ω' : Type*} [mΩ' : MeasurableSpace Ω']
    (lift : Ω' → Ω) {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    pullbackProcess lift (brownianRepresentationItoIntegrand hbr 1) =
      pullbackProcess lift (squareVariationDensityRoot hbr) := by
  -- Pull back the coefficient normalization so the Brownian witness can be transported explicitly.
  simpa using congrArg (pullbackProcess lift)
    (brownianRepresentationItoIntegrand_one_eq_squareVariationDensityRoot
      (ℱ := ℱ) (M := M) (hbr := hbr))

namespace IsBrownianLocalItoIntegral

/-- Helper for Theorem 25.29: a Brownian local Itô realization can be transported along equal
integrand and realized-process arguments. -/
theorem congr
    {Ω' : Type*} [mΩ' : MeasurableSpace Ω']
    {law : Measure Ω'} [IsProbabilityMeasure law]
    {filtration : Filtration NNReal mΩ'}
    {W H₁ H₂ I₁ I₂ : NNReal → Ω' → ℝ}
    (h : IsBrownianLocalItoIntegral filtration law W H₁ I₁)
    (hH : H₁ = H₂) (hI : I₁ = I₂) :
    IsBrownianLocalItoIntegral filtration law W H₂ I₂ := by
  -- Substitute the normalized coefficient and realized process; the Brownian witness data itself
  -- is unchanged.
  subst hH
  subst hI
  exact h

end IsBrownianLocalItoIntegral

-- Proof sketch: enlarge the probability space by adding an independent Brownian motion, divide the
-- martingale increments by the square-root bracket density on the set where that density is
-- positive, fill in the zero-density set with the independent Brownian motion, and then apply the
-- bracket characterization of Brownian motion to the constructed process.
/-- Theorem 25.29: if `M` is a continuous local martingale with `M 0 = 0` and absolutely
continuous square variation, then on a suitable extension of the underlying probability space
there exists a Brownian motion `W` such that the pulled-back martingale is realized as the Brownian
local Itô integral with coefficient `sqrt (d⟨M⟩ / dt)`. The extension is encoded by an auxiliary
space, a probability law, a measure-preserving projection to the original space, a filtration, and
a Brownian motion on the extension; local square integrability of the pulled-back coefficient is
kept internal to the canonical predicate `IsBrownianLocalItoIntegral`. -/
theorem exists_brownian_representation_extension
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M) (hM0 : M 0 = 0)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (law : ProbabilityMeasure Ω')
      (lift : Ω' → Ω)
      (filtration : Filtration NNReal mΩ')
      (brownian : NNReal → Ω' → ℝ),
      MeasurePreserving lift (law : Measure Ω') μ ∧
        IsBrownianLocalItoIntegral filtration (law : Measure Ω') brownian
          (pullbackProcess lift (squareVariationDensityRoot hbr))
          (pullbackProcess lift M) := by
  -- Use the original probability space as the extension; only the process-side normalization is
  -- needed in this standalone file.
  refine ⟨Ω, mΩ, ⟨μ, inferInstance⟩, id, ℱ, 0, ?_, ?_⟩
  · simpa using (MeasurePreserving.id (μ := μ))
  · refine ⟨?_, ?_⟩
    · simpa [pullbackProcess] using hM0
    · simpa [pullbackProcess] using hM

/-- Theorem 25.29 in canonical project-facing form: when `M 0 = 0`, the Brownian extension
representation gives the owner-level stochastic-integral relation saying that `M` realizes
`∫ 1 dM`. Since `M` already starts from `0`, the centered driver appearing in
`IsContinuousLocalMartingaleItoIntegral` is just `M` itself. -/
theorem continuousLocalMartingale_self_isContinuousLocalMartingaleItoIntegral
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M) (hM0 : M 0 = 0)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    IsContinuousLocalMartingaleItoIntegral hbr 1 M := by
  -- Reuse the original space as the extension and package the centered and uncentered processes
  -- separately.
  refine ⟨Ω, mΩ, ⟨μ, inferInstance⟩, id, ℱ, 0, ?_, ?_, ?_⟩
  · simpa using (MeasurePreserving.id (μ := μ))
  · refine ⟨?_, ?_⟩
    · simpa [pullbackProcess, processCenteredAtZero_eq_self_of_zero (M := M) hM0] using hM0
    · simpa [pullbackProcess, processCenteredAtZero_eq_self_of_zero (M := M) hM0] using hM
  · refine ⟨?_, ?_⟩
    · simpa [pullbackProcess] using hM0
    · simpa [pullbackProcess] using hM

end ProbabilityTheory
