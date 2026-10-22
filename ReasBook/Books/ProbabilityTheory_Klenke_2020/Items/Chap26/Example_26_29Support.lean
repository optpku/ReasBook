/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Exercise_26_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_6_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_27

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

local notation "State" => Fin 1 → ℝ

/-- Helper for Example 26.29: the state-path law of a generalized weak solution is the pushforward
of its ambient probability measure along the carried path map. -/
abbrev GeneralizedWeakSDESolution.statePathLaw
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {σ : NNReal → State → Fin 1 → Fin 1 → ℝ}
    {b : NNReal → State → Fin 1 → ℝ}
    (L : GeneralizedWeakSDESolution μ₀ σ b) :
    Measure (EuclideanPathSpace 1) := sorry

/-- Helper for Example 26.29: weak uniqueness means equality of state-path laws among all
generalized weak realizations with the same deterministic initial law. -/
def GeneralizedWeakSDESolution.IsWeaklyUnique
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {σ : NNReal → State → Fin 1 → Fin 1 → ℝ}
    {b : NNReal → State → Fin 1 → ℝ}
    (L : GeneralizedWeakSDESolution μ₀ σ b) : Prop := sorry

/-- The scalar diffusion coefficient of the Wright--Fisher SDE,
`𝟙_[0,1](x) * sqrt (γ x (1 - x))`. -/
def wrightFisherScalarDiffusionCoeff (γ : ℝ) : NNReal → ℝ → ℝ := sorry

/-- The polynomial duality function `H(x, n) = x^n`, written on the chapter's one-dimensional
state space `Fin 1 → ℝ` with the canonical complex codomain of `SatisfiesDualityAt`. -/
def wrightFisherDualityFunction : State → ℕ → ℂ := sorry

/-- Evaluating the Wright--Fisher duality function at the deterministic state `x` gives the usual
polynomial observable `x^n`. -/
theorem wrightFisherDualityFunction_oneDimensionalState (x : ℝ) (n : ℕ) :
    wrightFisherDualityFunction (oneDimensionalState x) n = (x : ℂ) ^ n := by
  sorry

/-- Helper for Example 26.29: the Wright--Fisher polynomial duality observable is jointly
measurable in the state and particle-number variables. -/
theorem measurable_wrightFisherDualityFunction_uncurry :
    Measurable (Function.uncurry wrightFisherDualityFunction) := by
  sorry

/-- Helper for Example 26.29: probability laws supported in `[0,1]` are determined by their
moments. -/
theorem identDistrib_of_forall_moment_eq_of_mem_unitInterval
    {Ω : Type _} [MeasurableSpace Ω] {Ω' : Type _} [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX_mem : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (hY_mem : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (hMoments : ∀ n : ℕ, moment X n μ = moment Y n ν) :
    IdentDistrib X Y μ ν := by
  sorry

/-- Helper for Example 26.29: every `Fin 1 → ℝ` state is the canonical one-dimensional state
built from its unique coordinate. -/
theorem state_eq_oneDimensionalState (x : State) :
    x = oneDimensionalState (x 0) := by
  sorry

/-- Helper for Example 26.29: outside the unit interval the Wright--Fisher diffusion coefficient
vanishes identically. -/
theorem wrightFisherScalarDiffusionCoeff_eq_zero_of_not_mem_unitInterval
    (γ : ℝ) {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) (t : NNReal) :
    wrightFisherScalarDiffusionCoeff γ t x = 0 := by
  sorry

/-- Helper for Example 26.29: the Wright--Fisher diffusion matrix coefficient can be written as
the autonomous truncated polynomial `γ * max x 0 * max (1 - x) 0` on the one-dimensional state
space. This is the continuous matrix field used by the Chapter 26.22 existence route. -/
def wrightFisherDiffusionMatrixCoeff (γ : ℝ) :
    NNReal → State → Fin 1 → Fin 1 → ℝ := sorry

/-- Helper for Example 26.29: for `γ ≥ 0`, the scalar Wright--Fisher diffusion coefficient
reconstructs the autonomous diffusion matrix field `γ * max x 0 * max (1 - x) 0`. -/
theorem wrightFisherDiffusionMatrixCoeff_eq_diffusionMatrixOfCoefficient
    (γ : ℝ) (hγ : 0 ≤ γ) :
    wrightFisherDiffusionMatrixCoeff γ =
      diffusionMatrixOfCoefficient
        (oneDimensionalDiffusion (wrightFisherScalarDiffusionCoeff γ)) := by
  sorry

/-- The pure-death Q-matrix on `ℕ` used as the Wright--Fisher moment dual. -/
def wrightFisherDualQMatrix (γ : ℝ) : ℕ → ℕ → ℝ := sorry

/-- For `γ ≥ 0`, the Wright--Fisher pure-death generator is a Q-matrix on `ℕ`. -/
theorem wrightFisherDualQMatrix_isQMatrix (γ : ℝ) (hγ : 0 ≤ γ) :
    IsQMatrix (wrightFisherDualQMatrix γ) := by
  sorry

/-- For `γ ≥ 0`, the Wright--Fisher dual pure-death chain exists as a continuous-time Markov
process on `ℕ` whose transition semigroup has generator matrix `wrightFisherDualQMatrix γ`. -/
theorem exists_wrightFisherDualProcess (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ κ : NNReal → Kernel ℕ ℕ,
      HasGeneratorMatrix κ (wrightFisherDualQMatrix γ) ∧
        ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (Q : ℕ → ProbabilityMeasure Ω')
          (Y : NNReal → Ω' → ℕ), IsMarkovProcessRealization κ Q Y := by
  sorry

section WrightFisher

variable {γ x : ℝ}

local notation "σWF" => oneDimensionalDiffusion (wrightFisherScalarDiffusionCoeff γ)
local notation "bWF" => oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))
local notation "WFSolution" =>
  GeneralizedWeakSDESolution
    (Measure.dirac (oneDimensionalState x))
    σWF bWF

/-- The `n`-th moment function `t ↦ E[X_t^n]` of a Wright--Fisher weak solution. -/
def wrightFisherMoment (L : WFSolution) (n : ℕ) (t : NNReal) : ℝ := sorry

/-- The source-facing Wright--Fisher duality of Example 26.29, expressed through the chapter's
fixed-start duality owner `SatisfiesDualityAt`. -/
theorem satisfiesDualityAt_wrightFisherDual
    (L : WFSolution) (hγ : 0 ≤ γ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hL_mem : ∀ ω : L.Ω, ∀ t : NNReal, L ω t 0 ∈ Set.Icc (0 : ℝ) 1)
    {Ω' : Type u} [MeasurableSpace Ω']
    {κ : NNReal → Kernel ℕ ℕ} {Q : ℕ → ProbabilityMeasure Ω'}
    {Y : NNReal → Ω' → ℕ}
    [IsMarkovProcessRealization κ Q Y]
    (hY_generator : HasGeneratorMatrix κ (wrightFisherDualQMatrix γ)) :
    SatisfiesDualityAt L.μ (pathProcess L.X) (oneDimensionalState x) Q (fun _ ↦ Y)
      wrightFisherDualityFunction := by
  sorry

/-- The Wright--Fisher moment duality identity of Example 26.29:
`E_x[X_t^n] = E_n[x^{Y_t}]`. -/
theorem wrightFisherMoment_eq_dualExpectation
    (L : WFSolution) (hγ : 0 ≤ γ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hL_mem : ∀ ω : L.Ω, ∀ t : NNReal, L ω t 0 ∈ Set.Icc (0 : ℝ) 1)
    {Ω' : Type u} [MeasurableSpace Ω']
    {κ : NNReal → Kernel ℕ ℕ} {Q : ℕ → ProbabilityMeasure Ω'}
    {Y : NNReal → Ω' → ℕ}
    [IsMarkovProcessRealization κ Q Y]
    (hY_generator : HasGeneratorMatrix κ (wrightFisherDualQMatrix γ))
    (n : ℕ) (t : NNReal) :
    wrightFisherMoment L n t = ∫ ω, x ^ (Y t ω) ∂(Q n) := by
  sorry

/-- The first moment of a Wright--Fisher weak solution stays equal to the initial state. -/
theorem wrightFisherMoment_one (L : WFSolution) :
    wrightFisherMoment L 1 = fun _ ↦ x := by
  sorry

/-- For `γ ≥ 0`, if a Wright--Fisher weak solution remains in `[0,1]`, then its moments satisfy
the recursive integral equations from formula `(26.28)`. -/
theorem wrightFisherMoment_recursion
    (L : WFSolution)
    (hγ : 0 ≤ γ)
    (hL_mem : ∀ ω : L.Ω, ∀ t : NNReal, L ω t 0 ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (hn : 2 ≤ n) (t : NNReal) :
    wrightFisherMoment L n t =
      x ^ n +
        γ * (Nat.choose n 2 : ℝ) *
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            (wrightFisherMoment L (n - 1) s.toNNReal - wrightFisherMoment L n s.toNNReal) := by
  sorry

/-- Any Wright--Fisher weak solution started outside `[0,1]` is constant. -/
theorem wrightFisherWeakSolution_constant_of_not_mem_unitInterval
    (hx : x ∉ Set.Icc (0 : ℝ) 1) (L : WFSolution) (ω : L.Ω) (t : NNReal) :
    L ω t = oneDimensionalState x := by
  sorry

end WrightFisher

section WrightFisherGlobal

variable {x : ℝ}

local notation "PathSpace" => EuclideanPathSpace 1
local notation "σWF(" gamma ")" => oneDimensionalDiffusion (wrightFisherScalarDiffusionCoeff gamma)
local notation "bWF" => oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))
local notation "CoordinateProcess" =>
  fun t ↦ (ContinuousMap.evalCLM ℝ t : PathSpace → State)

/-- Companion to Example 26.29: the Dirac-initial Wright--Fisher weak-solution family admits a
canonical time-homogeneous strong-Markov realization on path space already under the weaker
hypothesis `γ ≥ 0`. -/
theorem wrightFisher_existsStrongMarkovSolutionFamily_nonneg (gamma : ℝ) (hγ : 0 ≤ gamma) :
    ∃ (P : State → ProbabilityMeasure PathSpace)
      (pathKernel : Kernel State (NNReal → State)),
      (∀ x : State,
        ∃ L :
            GeneralizedWeakSDESolution
              (Measure.dirac x)
              (σWF(gamma)) bWF,
          L.IsWeaklyUnique ∧ L.statePathLaw = (P x : Measure PathSpace)) ∧
        IsTimeHomogeneousMarkovProcess CoordinateProcess P pathKernel ∧
        HasStrongMarkovProperty P CoordinateProcess pathKernel := by
  sorry

/-- Example 26.29: for `γ > 0`, the family of Dirac-initial Wright--Fisher weak solutions admits
a canonical time-homogeneous strong-Markov realization on path space. -/
theorem wrightFisher_existsStrongMarkovSolutionFamily (gamma : ℝ) (hγ : 0 < gamma) :
    ∃ (P : State → ProbabilityMeasure PathSpace)
      (pathKernel : Kernel State (NNReal → State)),
      (∀ x : State,
        ∃ L :
            GeneralizedWeakSDESolution
              (Measure.dirac x)
              (σWF(gamma)) bWF,
          L.IsWeaklyUnique ∧ L.statePathLaw = (P x : Measure PathSpace)) ∧
        IsTimeHomogeneousMarkovProcess CoordinateProcess P pathKernel ∧
        HasStrongMarkovProperty P CoordinateProcess pathKernel := by
  sorry

/-- Helper for Example 26.29: the Wright--Fisher diffusion matrix and drift are autonomous, so
varying only the deterministic time parameter leaves both coefficients unchanged. -/
theorem wrightFisherCoefficients_timeIndependent
    (gamma : ℝ) (t₁ t₂ : NNReal) (x : State) :
    diffusionMatrixOfCoefficient (σWF(gamma)) t₁ x =
      diffusionMatrixOfCoefficient (σWF(gamma)) t₂ x ∧
        bWF t₁ x = bWF t₂ x := by
  sorry

/-- Companion to Example 26.29: for every `γ ≥ 0`, the Wright--Fisher local martingale problem is
well-posed. The strong-Markov realization and weak-solution corollaries below are derived from
this owner-level statement. -/
theorem wrightFisherLocalMartingaleProblemWellPosed (gamma : ℝ) (hγ : 0 ≤ gamma) :
    LocalMartingaleProblemWellPosed (diffusionMatrixOfCoefficient (σWF(gamma))) bWF := by
  sorry

/-- A Wright--Fisher weak solution started from `x ∈ [0,1]` can be chosen to stay in `[0,1]` for
all times, and this realization is unique in law, already for `γ ≥ 0`. -/
theorem exists_wrightFisherWeakSolution_in_unitInterval
    (gamma x : ℝ) (hγ : 0 ≤ gamma) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ L :
        GeneralizedWeakSDESolution
          (Measure.dirac (oneDimensionalState x))
          (σWF(gamma)) bWF,
      L.IsWeaklyUnique ∧
        ∀ ω : L.Ω, ∀ t : NNReal, L ω t 0 ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- Corollary of Example 26.29: for every `γ ≥ 0` and every deterministic initial state
`x ∈ ℝ`, the Wright--Fisher SDE admits a weak solution, and this weak solution is unique in law.
-/
theorem exists_wrightFisherWeakSolution_isWeaklyUnique
    (gamma x : ℝ) (hγ : 0 ≤ gamma) :
    ∃ L :
        GeneralizedWeakSDESolution
          (Measure.dirac (oneDimensionalState x))
          (σWF(gamma)) bWF,
      L.IsWeaklyUnique := by
  sorry

end WrightFisherGlobal

end ProbabilityTheory
