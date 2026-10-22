/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Exercise_26_2_2

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

namespace ProbabilityTheory

universe u

variable {n : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionMatrixCoeff" => NNReal → State → Fin n → Fin n → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

/-- Helper for Theorem 26.22: the source-centered compensated `i`-th coordinate process attached
to a path-valued process `X`. Centering at time `0` matches the textbook formulation of the local
martingale problem and avoids imposing an unintended first-moment condition on the initial law. -/
def sourceLocalMartingaleProblemMartingalePart
    {Ω : Type u} [MeasurableSpace Ω]
    (b : DriftCoeff) (X : Ω → PathSpace) (i : Fin n) : NNReal → Ω → ℝ :=
  fun t ω ↦ X ω t i - X ω 0 i - ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (X ω s.toNNReal) i

/-- Helper for Theorem 26.22: the source-faithful local martingale problem owner uses the centered
compensated coordinates `X_t^i - X_0^i - ∫ b_i(s, X_s) ds`, together with the same prescribed
quadratic covariations and initial law as in Definition 26.20. -/
structure IsCenteredLocalMartingaleProblemSolution
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (a : DiffusionMatrixCoeff) (b : DriftCoeff)
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω)
    (X : Ω → PathSpace) : Prop where
  /-- The initial distribution of the solution is `μ₀`. -/
  initial_law : HasLaw (fun ω ↦ X ω 0) μ₀ μ
  /-- Each centered compensated coordinate is a continuous local martingale. -/
  martingalePart :
    letI : IsProbabilityMeasure μ := initial_law.isProbabilityMeasure
    ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (sourceLocalMartingaleProblemMartingalePart b X i)
  /-- The quadratic covariation of the centered compensated coordinates is still prescribed by the
  integral of `aᵢⱼ` along the path `X`. -/
  quadraticCovariation :
    letI : IsProbabilityMeasure μ := initial_law.isProbabilityMeasure
    ∀ i j : Fin n,
      HasContinuousQuadraticCovariation ℱ μ
        (sourceLocalMartingaleProblemMartingalePart b X i)
        (sourceLocalMartingaleProblemMartingalePart b X j)
        (localMartingaleProblemCovariation a X i j)

/-- Helper for Theorem 26.22: direct existence of a centered realization for bounded continuous
coefficients. -/
axiom existsCenteredRealization_of_continuousBoundedCoefficients
    (a : DiffusionMatrixCoeff) (b : DriftCoeff)
    (ha_symm : ∀ t : NNReal, ∀ x : State, ∀ i j : Fin n, a t x i j = a t x j i)
    (ha_psd : ∀ t : NNReal, ∀ x (v : State),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * a t x i j * v j)
    (ha_cont : Continuous fun p : NNReal × State ↦ a p.1 p.2)
    (ha_bdd : ∃ C : ℝ, ∀ p : NNReal × State, ‖a p.1 p.2‖ ≤ C)
    (hb_cont : Continuous fun p : NNReal × State ↦ b p.1 p.2)
    (hb_bdd : ∃ C : ℝ, ∀ p : NNReal × State, ‖b p.1 p.2‖ ≤ C)
    (μ₀ : Measure State) [IsProbabilityMeasure μ₀] :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
      (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
      IsCenteredLocalMartingaleProblemSolution μ₀ a b ℱ (P : Measure Ω) X

end ProbabilityTheory
