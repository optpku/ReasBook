/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Exercise_26_2_1.WeakSolution

open MeasureTheory ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n : ℕ}

/-- The `n`-dimensional Euclidean state space used for the local martingale problem in
Theorem 26.25. -/
abbrev LMPState (n : ℕ) :=
  Fin n → ℝ

/-- The canonical continuous path space over `ℝ^n` used in Theorem 26.25. -/
abbrev LMPPathSpace (n : ℕ) :=
  EuclideanPathSpace n

/-- The diffusion-matrix coefficient type used in Theorem 26.25. -/
abbrev LMPDiffusionMatrixCoeff (n : ℕ) :=
  NNReal → LMPState n → Fin n → Fin n → ℝ

/-- The drift coefficient type used in Theorem 26.25. -/
abbrev LMPDriftCoeff (n : ℕ) :=
  NNReal → LMPState n → Fin n → ℝ

/-- The canonical coordinate process on the continuous path space over `ℝ^n`. -/
abbrev canonicalCoordinateProcess :
    NNReal → LMPPathSpace n → LMPState n :=
  fun t ↦ (ContinuousMap.evalCLM ℝ t : LMPPathSpace n → LMPState n)

/-- The canonical filtration on the continuous path space used in Theorem 26.25. -/
abbrev canonicalCoordinateFiltration :
    Filtration NNReal (inferInstance : MeasurableSpace (LMPPathSpace n)) :=
  let measurable_path_eval :
      ∀ t : NNReal, Measurable (fun γ : LMPPathSpace n ↦ γ t) := fun t ↦ by
        simpa using (continuous_eval_const t).measurable
  generatedFiltration canonicalCoordinateProcess measurable_path_eval

/-- Helper for Theorem 26.25: the local martingale problem coefficients are time-independent when
every time slice agrees with the time-zero slice. -/
def TimeIndependentLocalMartingaleProblemCoefficients
    (a : LMPDiffusionMatrixCoeff n) (b : LMPDriftCoeff n) : Prop :=
  (∀ t₁ t₂ x, a t₁ x = a t₂ x) ∧
    ∀ t₁ t₂ x, b t₁ x = b t₂ x

/-- Helper for Theorem 26.25: deterministic-time marginal uniqueness for Dirac-start local
martingale problem solutions. -/
def HasDeterministicTimeMarginalUniqueness
    (a : LMPDiffusionMatrixCoeff n) (b : LMPDriftCoeff n) : Prop :=
  ∀ (x : LMPState n)
    {Ω : Type u} [MeasurableSpace Ω]
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (X : Ω → LMPPathSpace n)
    {Ω' : Type v} [MeasurableSpace Ω']
    (ℱ' : Filtration NNReal (inferInstance : MeasurableSpace Ω'))
    (μ' : Measure Ω') (X' : Ω' → LMPPathSpace n),
    IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ μ X →
    IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ' μ' X' →
    ∀ T : NNReal,
      μ.map (fun ω ↦ X ω T) = μ'.map (fun ω ↦ X' ω T)

/-- Helper for Theorem 26.25: the deterministic-start part of `(26.21)` needed to normalize any
Dirac-start local-martingale-problem solution to the canonical path space without changing its
path law. -/
def HasDiracCanonicalPathNormalization
    (a : LMPDiffusionMatrixCoeff n) (b : LMPDriftCoeff n) : Prop :=
  ∀ (x : LMPState n)
    {Ω : Type u} [MeasurableSpace Ω]
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (X : Ω → LMPPathSpace n),
    IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ μ X →
      IsLocalMartingaleProblemSolution
        (Measure.dirac x) a b canonicalCoordinateFiltration (μ.map X) id

/-- Helper for Theorem 26.25: when `a = σσᵀ`, the deterministic-start part of `(26.21)`
identifies Dirac-start local martingale problem solutions with generalized weak SDE solutions
without changing the state-path law. -/
def HasDiracLawPreservingWeakSolutionBridge
    (a : LMPDiffusionMatrixCoeff n) (b : LMPDriftCoeff n) : Prop :=
  ∀ {m : ℕ} (σ : NNReal → LMPState n → Fin n → Fin m → ℝ),
    a = diffusionMatrixOfCoefficient σ →
      (∀ (x : LMPState n)
        {Ω : Type u} [MeasurableSpace Ω]
        (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
        (μ : Measure Ω) (X : Ω → LMPPathSpace n),
        IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ μ X →
          ∃ L : GeneralizedWeakSDESolution (Measure.dirac x) σ b,
            L.statePathLaw = μ.map X) ∧
        ∀ x : LMPState n,
          ∀ L : GeneralizedWeakSDESolution (Measure.dirac x) σ b,
            ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
              (P : ProbabilityMeasure Ω) (X : Ω → LMPPathSpace n),
              IsLocalMartingaleProblemSolution
                (Measure.dirac x) a b ℱ (P : Measure Ω) X ∧
                (P : Measure Ω).map X = L.statePathLaw

/-- Helper for Theorem 26.25: source assumption `(26.21)` packages the time-independent
coefficient hypothesis together with the canonical-path and weak-solution bridges used by the
uniqueness-in-the-martingale-problem theorem. -/
def Theorem26_21Hypothesis
    (a : LMPDiffusionMatrixCoeff n) (b : LMPDriftCoeff n) : Prop :=
  TimeIndependentLocalMartingaleProblemCoefficients a b ∧
    HasDiracCanonicalPathNormalization.{u} a b ∧
    HasDiracLawPreservingWeakSolutionBridge.{u} a b

end ProbabilityTheory
