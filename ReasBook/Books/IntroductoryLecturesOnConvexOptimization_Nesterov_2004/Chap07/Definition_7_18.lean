/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealSymmetricMatrixSpace

variable {p n : ℕ}

local notation "Eₚ" => EuclideanSpace ℝ (Fin p)
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/- Definition 7.18 lies in Chapter 7's symmetric-matrix spectral-radius domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, the chapter owner for real symmetric matrices;
- Chapter 7 Definition 7.21 `linearMatrixCombination`, the existing owner for coefficient-sum
  matrix maps;
- Chapter 7 Definition 7.17's direct use of `spectralRadius`, the canonical spectral-radius owner.

Best owner abstraction:
- source-facing: the spectral-radius objective `x ↦ ρ(∑ᵢ xᵢ Aᵢ)`;
- core/canonical: `𝕊^n`, `linearMatrixCombination`, and `spectralRadius`;
- bridge/view: the evaluation formula below rewriting the owner map to the textbook sum.

Primitive data:
- a family `coeffMatrices : Fin p → 𝕊^n` of symmetric coefficient matrices.

Derived API:
- the Chapter 7 coefficient-sum owner `linearMatrixCombination`;
- the real-valued spectral-radius expression obtained by applying `spectralRadius` to that sum.

This refinement removes the duplicate local subtype and local linear-map owner from this file and
reuses the established chapter owners directly. -/

/-- Definition 7.18: from symmetric coefficient matrices `A₁, …, Aₚ`, the induced objective maps
`x ∈ ℝᵖ` to the spectral radius of the linear matrix combination `∑ᵢ xᵢ Aᵢ`. -/
def spectralRadiusObjective (coeffMatrices : Fin p → SymmMat) : Eₚ → ℝ :=
  fun x ↦
    (spectralRadius ℝ
      ((linearMatrixCombination fun i ↦ (coeffMatrices i : Mₙ)) x)).toReal

/-- Evaluating `spectralRadiusObjective` recovers the spectral radius of `∑ᵢ xᵢ Aᵢ`. -/
-- Proof sketch: unfold `spectralRadiusObjective` and rewrite the coefficient-sum owner
-- `linearMatrixCombination` using its upstream evaluation formula.
theorem spectralRadiusObjective_apply
    (coeffMatrices : Fin p → SymmMat) (x : Eₚ) :
    spectralRadiusObjective coeffMatrices x =
      (spectralRadius ℝ (∑ i : Fin p, x i • (coeffMatrices i : Mₙ))).toReal := by
  simpa [spectralRadiusObjective] using
    congrArg (fun A : Mₙ ↦ (spectralRadius ℝ A).toReal)
      (linearMatrixCombination_apply (fun i ↦ (coeffMatrices i : Mₙ)) x)

end
