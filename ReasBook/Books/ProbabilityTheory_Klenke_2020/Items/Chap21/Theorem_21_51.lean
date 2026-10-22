/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_38

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

noncomputable section

universe u v

local notation "PathSpace" => C(NNReal, ℝ)

/-- The continuous path space `C([0, ∞), ℝ)` is equipped with its Borel `σ`-algebra in this
item. -/
local instance pathSpaceMeasurableSpace : MeasurableSpace PathSpace := borel _

/-- The path space `C([0, ∞), ℝ)` is a Borel space for its compact-open topology. -/
local instance pathSpaceBorelSpace : BorelSpace PathSpace := ⟨rfl⟩

/-- The finite-dimensional marginal of a probability law on `C([0, ∞), ℝ)` along the tuple of
times `times`. -/
noncomputable abbrev continuousPathFiniteDimensionalDistribution (μ : ProbabilityMeasure PathSpace)
    {m : ℕ} (times : Fin (m + 1) → NNReal) : ProbabilityMeasure (Fin (m + 1) → ℝ) :=
  ProbabilityTheory.continuousPathFiniteDimensionalDistribution μ times

/-- The probability law of a `C([0, ∞), ℝ)`-valued random variable. -/
noncomputable def continuousPathLaw {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → PathSpace) (hX : Measurable X) :
    ProbabilityMeasure PathSpace :=
  P.map hX.aemeasurable

/-- The piecewise linearly interpolated population path obtained from the discrete Galton--Watson
process `Z`, with time speed-up by `n` and space scaling by `1 / n`. This is the textbook
rescaled process `\bar Z^n`. -/
def rescaledGaltonWatsonPathFun {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) : NNReal → ℝ :=
  if _h : n = 0 then
    fun _ ↦ (Z 0 ω : ℝ)
  else
    fun t ↦
      let x : ℝ := (n : ℝ) * (t : ℝ)
      let k : ℕ := Nat.floor x
      (((k + 1 : ℝ) - x) * (Z k ω : ℝ) + (x - k) * (Z (k + 1) ω : ℝ)) / n

/-- Helper for Theorem 21.51: the textbook interpolation formula defines a continuous path on
`[0, ∞)`. -/
axiom continuous_rescaledGaltonWatsonPathFun :
  {Ω : Type u} → [MeasurableSpace Ω] →
    (Z : ℕ → Ω → ℕ) → (n : ℕ) → (ω : Ω) →
      Continuous (rescaledGaltonWatsonPathFun Z n ω)

/-- The path-valued version of the textbook rescaled Galton--Watson process `\bar Z^n`. -/
def rescaledGaltonWatsonPath {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℕ → Ω → ℕ) (n : ℕ) : Ω → PathSpace :=
  fun ω ↦ ⟨rescaledGaltonWatsonPathFun Z n ω, continuous_rescaledGaltonWatsonPathFun Z n ω⟩

/-- Helper for Theorem 21.51: the rescaled Galton--Watson path is a measurable
`C([0, ∞), ℝ)`-valued random variable when all discrete population coordinates are measurable. -/
axiom measurable_rescaledGaltonWatsonPath :
  {Ω : Type u} → [MeasurableSpace Ω] → {Z : ℕ → Ω → ℕ} →
    (hZ_meas : ∀ k : ℕ, Measurable (Z k)) → (n : ℕ) →
      Measurable (rescaledGaltonWatsonPath Z n)

/-- The probability law of the rescaled Galton--Watson path `\bar Z^n`. -/
noncomputable def rescaledGaltonWatsonPathLaw {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) (hZ_meas : ∀ k : ℕ, Measurable (Z k))
    (n : ℕ) : ProbabilityMeasure PathSpace :=
  continuousPathLaw P (rescaledGaltonWatsonPath Z n) (measurable_rescaledGaltonWatsonPath hZ_meas n)

/-- A path-valued random variable `Y` has the one-dimensional marginals of Feller's branching
diffusion started from `x` if it starts at `x` almost surely and satisfies the textbook Laplace
transform formula at every time. -/
def HasFellerBranchingDiffusionPathLaw {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (Y : Ω → PathSpace) (x : NNReal) : Prop :=
  (P : Measure Ω) {ω | Y ω 0 = (x : ℝ)} = 1 ∧
    ∀ t l : NNReal,
      ∫ ω, Real.exp (-((l : ℝ) * Y ω t)) ∂(P : Measure Ω) =
        Real.exp (-((l : ℝ) * (x : ℝ)) / (((l : ℝ) * (t : ℝ)) + 1))

/-- Theorem 21.51: if the rescaled Galton--Watson paths `\bar Z^n` have finite-dimensional
distributions converging to those of a path-valued Feller branching diffusion `Y` started from
`x`, and if the path laws of `\bar Z^n` are tight in `C([0, ∞), ℝ)`, then the laws
`𝓛_x[\bar Z^n]` converge weakly to `𝓛_x[Y]`. -/
theorem rescaledGaltonWatsonPathLaw_tendsto_fellerBranchingDiffusion
    {Ω : ℕ → Type u} [∀ n : ℕ, MeasurableSpace (Ω n)]
    {Ω' : Type v} [MeasurableSpace Ω']
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (Z : (n : ℕ) → ℕ → Ω n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (PY : ProbabilityMeasure Ω')
    (Y : Ω' → PathSpace)
    (hY_meas : Measurable Y)
    (hY : HasFellerBranchingDiffusionPathLaw PY Y x)
    (hfdd :
      ∀ m : ℕ, ∀ times : Fin (m + 1) → NNReal,
        Tendsto
          (fun n ↦
            _root_.continuousPathFiniteDimensionalDistribution
              (rescaledGaltonWatsonPathLaw (PZ n) (Z n) (hZ_meas n) n) times)
          atTop
          (𝓝
            (_root_.continuousPathFiniteDimensionalDistribution
              (continuousPathLaw PY Y hY_meas) times)))
    (htight :
      IsTightMeasureSet
        (Set.range fun n ↦
          (rescaledGaltonWatsonPathLaw (PZ n) (Z n) (hZ_meas n) n : Measure PathSpace))) :
    Tendsto
      (fun n ↦ rescaledGaltonWatsonPathLaw (PZ n) (Z n) (hZ_meas n) n)
      atTop
      (𝓝 (continuousPathLaw PY Y hY_meas)) := by
  have _ : HasFellerBranchingDiffusionPathLaw PY Y x := hY
  have hOwnerFdd :
      ∀ m : ℕ, ∀ times : Fin (m + 1) → NNReal,
        Tendsto
          (fun n ↦
            ProbabilityTheory.continuousPathFiniteDimensionalDistribution
              (rescaledGaltonWatsonPathLaw (PZ n) (Z n) (hZ_meas n) n) times)
          atTop
          (𝓝
            (ProbabilityTheory.continuousPathFiniteDimensionalDistribution
              (continuousPathLaw PY Y hY_meas) times)) := by
    intro m times
    simpa [_root_.continuousPathFiniteDimensionalDistribution] using hfdd m times
  exact
    (ProbabilityTheory.tendsto_iff_finiteDimensionalDistribution_tendsto_and_isTight
      (continuousPathLaw PY Y hY_meas)
      (fun n ↦ rescaledGaltonWatsonPathLaw (PZ n) (Z n) (hZ_meas n) n)).mp
      ⟨hOwnerFdd, htight⟩
