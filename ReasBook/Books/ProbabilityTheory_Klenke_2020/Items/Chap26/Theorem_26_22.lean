/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_22.Support

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

/-- Theorem 26.22: if the drift field `b` is continuous and bounded and the diffusion matrix field
`a` is continuous and bounded, with the pointwise symmetry and nonnegative-semidefiniteness
assumptions made explicit here as the diffusion-matrix side conditions, then every initial law
`μ₀` on `ℝ^n` admits a realization solving the centered local martingale problem `LMP(a, b, μ₀)`
on the source-faithful predicate `IsCenteredLocalMartingaleProblemSolution`. -/
theorem localMartingaleProblem_existsSolution_of_continuous_bounded_coefficients
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
      IsCenteredLocalMartingaleProblemSolution μ₀ a b ℱ (P : Measure Ω) X := by
  -- Proof comment: the target file now calls the direct realization-space owner from
  -- `Theorem_26_22/Support.lean`, so the only open frontier is the analytic weak-existence
  -- theorem on the dependency-closed support side.
  exact
    existsCenteredRealization_of_continuousBoundedCoefficients
      a b ha_symm ha_psd ha_cont ha_bdd hb_cont hb_bdd μ₀

end ProbabilityTheory
