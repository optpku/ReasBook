/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Exercise_6_7

noncomputable section

section

variable {n : ℕ}

private abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

namespace TrustRegionSubproblem

/-- The Chapter 6 double-dogleg ratio
`γ = ‖g_k‖^4 / ((g_kᵀ B_k g_k) (g_kᵀ B_k⁻¹ g_k))`. Since
`s_k^N = -B_k⁻¹ g_k`, the second factor is `-g_kᵀ s_k^N`, so this uses the positive textbook
denominator in the positive-definite Hessian context where the double-dogleg Newton segment is
defined. -/
def doubleDoglegGamma
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) : ℝ :=
  let sN := P.newtonStep h_hessianApprox_isUnit
  (‖P.gradient‖ ^ (4 : ℕ)) / (P.gradientCurvature * (-dotProduct P.gradient sN))

/-- The intermediate Newton step `η s_k^N` on the second double-dogleg segment, in the
positive-definite Hessian setting of the double-dogleg method. -/
def doubleDoglegIntermediateNewtonStep
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (η : ℝ) :
    Point n :=
  η • P.newtonStep h_hessianApprox_isUnit

/-- The step-valued double-dogleg path starts at `0`, reaches `s_k^c` at `τ = 1`, reaches
`η s_k^N` at `τ = 2`, and reaches `s_k^N` at `τ = 3`, again in the positive-definite Hessian
context where the Newton segment is defined. -/
def doubleDoglegPath
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox)
    (η : ℝ) (τ : ℝ) : Point n :=
  let sN := P.newtonStep h_hessianApprox_isUnit
  let sη := η • sN
  if _ : τ ≤ 1 then
    τ • P.cauchyPoint
  else if _ : τ ≤ 2 then
    P.cauchyPoint + (τ - 1) • (sη - P.cauchyPoint)
  else
    sη + (τ - 2) • (sN - sη)

/-- On the first double-dogleg segment `τ ≤ 1`, the path is the ray from `0` to the Cauchy
point. -/
theorem doubleDoglegPath_eq_smul_cauchyPoint_of_le_one
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (η τ : ℝ)
    (hτ : τ ≤ 1) :
    P.doubleDoglegPath h_hessianApprox_isUnit η τ = τ • P.cauchyPoint := by
  simp [doubleDoglegPath, hτ]

/-- On the second double-dogleg segment `1 < τ ≤ 2`, the path is the segment from the Cauchy
point to the intermediate Newton step `η s_k^N`. -/
theorem doubleDoglegPath_eq_cauchyPoint_add_smul_of_one_lt_of_le_two
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (η τ : ℝ)
    (hτ₁ : 1 < τ) (hτ₂ : τ ≤ 2) :
    P.doubleDoglegPath h_hessianApprox_isUnit η τ =
      P.cauchyPoint + (τ - 1) •
        (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_isUnit η - P.cauchyPoint) := by
  simp [doubleDoglegPath, doubleDoglegIntermediateNewtonStep, hτ₂, not_le_of_gt hτ₁]

/-- On the third double-dogleg segment `2 < τ`, the path is the segment from `η s_k^N` to
`s_k^N`. -/
theorem doubleDoglegPath_eq_intermediateNewtonStep_add_smul_of_two_lt
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (η τ : ℝ)
    (hτ : 2 < τ) :
    P.doubleDoglegPath h_hessianApprox_isUnit η τ =
      P.doubleDoglegIntermediateNewtonStep h_hessianApprox_isUnit η +
        (τ - 2) •
          (P.newtonStep h_hessianApprox_isUnit -
            P.doubleDoglegIntermediateNewtonStep h_hessianApprox_isUnit η) := by
  have hτ₁ : 1 < τ := lt_trans one_lt_two hτ
  simp [doubleDoglegPath, doubleDoglegIntermediateNewtonStep, not_le_of_gt hτ, not_le_of_gt hτ₁]

/-- At `η = 1`, the double-dogleg path agrees with the dogleg path on the standard interval
`τ ∈ [0, 2]`. -/
theorem doubleDoglegPath_eq_doglegPath_of_le_two
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) {τ : ℝ}
    (hτ : τ ≤ 2) :
    P.doubleDoglegPath h_hessianApprox_isUnit 1 τ = P.doglegPath h_hessianApprox_isUnit τ := by
  by_cases hτ₁ : τ ≤ 1
  · simp [doubleDoglegPath, doglegPath, hτ₁]
  · simp [doubleDoglegPath, doglegPath, hτ₁, hτ]

@[simp] theorem doubleDoglegIntermediateNewtonStep_one
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) :
    P.doubleDoglegIntermediateNewtonStep h_hessianApprox_isUnit 1 =
      P.newtonStep h_hessianApprox_isUnit := by
  simp [doubleDoglegIntermediateNewtonStep]

@[simp] theorem doubleDoglegPath_zero
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (η : ℝ) :
    P.doubleDoglegPath h_hessianApprox_isUnit η 0 = 0 := by
  simpa using P.doubleDoglegPath_eq_smul_cauchyPoint_of_le_one h_hessianApprox_isUnit η 0
    zero_le_one

@[simp] theorem doubleDoglegPath_one
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (η : ℝ) :
    P.doubleDoglegPath h_hessianApprox_isUnit η 1 = P.cauchyPoint := by
  simpa using P.doubleDoglegPath_eq_smul_cauchyPoint_of_le_one h_hessianApprox_isUnit η 1
    le_rfl

@[simp] theorem doubleDoglegPath_two
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (η : ℝ) :
    P.doubleDoglegPath h_hessianApprox_isUnit η 2 =
      P.doubleDoglegIntermediateNewtonStep h_hessianApprox_isUnit η := by
  have hpath :
      P.cauchyPoint + ((2 : ℝ) - 1) •
          (η • P.newtonStep h_hessianApprox_isUnit - P.cauchyPoint) =
        P.doubleDoglegIntermediateNewtonStep h_hessianApprox_isUnit η := by
    calc
      P.cauchyPoint + ((2 : ℝ) - 1) •
          (η • P.newtonStep h_hessianApprox_isUnit - P.cauchyPoint)
          = P.cauchyPoint + (η • P.newtonStep h_hessianApprox_isUnit - P.cauchyPoint) := by
            norm_num
      _ = η • P.newtonStep h_hessianApprox_isUnit := by
        abel
      _ = P.doubleDoglegIntermediateNewtonStep h_hessianApprox_isUnit η := by
        simp [doubleDoglegIntermediateNewtonStep]
  simpa [doubleDoglegPath, doubleDoglegIntermediateNewtonStep, not_le_of_gt one_lt_two] using hpath

@[simp] theorem doubleDoglegPath_three
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (η : ℝ) :
    P.doubleDoglegPath h_hessianApprox_isUnit η 3 = P.newtonStep h_hessianApprox_isUnit := by
  have h23 : (2 : ℝ) < 3 := by
    norm_num
  have h13 : (1 : ℝ) < 3 := by
    norm_num
  have hpath :
      η • P.newtonStep h_hessianApprox_isUnit +
          ((3 : ℝ) - 2) •
            (P.newtonStep h_hessianApprox_isUnit - η • P.newtonStep h_hessianApprox_isUnit) =
        P.newtonStep h_hessianApprox_isUnit := by
    calc
      η • P.newtonStep h_hessianApprox_isUnit +
          ((3 : ℝ) - 2) •
            (P.newtonStep h_hessianApprox_isUnit - η • P.newtonStep h_hessianApprox_isUnit)
          =
        η • P.newtonStep h_hessianApprox_isUnit +
          (P.newtonStep h_hessianApprox_isUnit - η • P.newtonStep h_hessianApprox_isUnit) := by
            norm_num
      _ = P.newtonStep h_hessianApprox_isUnit := by
        abel
  simpa [doubleDoglegPath, not_le_of_gt h13, not_le_of_gt h23] using hpath

end TrustRegionSubproblem

end
