/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped HessianLocalNorm

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

-- Proof sketch: for a fixed interior point `x`, replace `h` by `-h`. The second directional
-- derivative and the Hessian local norm are even in `h`, while the third directional derivative
-- is odd, so the two displayed cone-membership conditions transform into one another.
/-- Theorem 5.4.6.1: for a map `ξ`, the cone-order bound
`D³ξ(x)[h,h,h] \preceq_K -3β D²ξ(x)[h,h] ‖h‖[F; x]` on `interior Q₁` is equivalent to the same
bound with `D³ξ(x)[h,h,h]` replaced by `-D³ξ(x)[h,h,h]`. The theorem is stated on the chapter's
owner surface for the vector-valued directional derivatives and the barrier Hessian local norm. -/
theorem betaCompatibility_sign_reversal_iff
    (Q₁ : Set E₁) (K : ConvexCone ℝ E₂) (F : E₁ → ℝ) (β : ℝ) (ξ : E₁ → E₂) :
    (∀ ⦃x : E₁⦄ (_ : x ∈ interior Q₁) (h : E₁),
      (3 * β * ‖h‖[F; x]) • (-vectorSecondDirectionalDerivative ξ x h) -
          vectorThirdDirectionalDerivative ξ x h ∈
        K) ↔
      ∀ ⦃x : E₁⦄ (_ : x ∈ interior Q₁) (h : E₁),
        (3 * β * ‖h‖[F; x]) • (-vectorSecondDirectionalDerivative ξ x h) +
            vectorThirdDirectionalDerivative ξ x h ∈
          K := by
  have h2 (x h : E₁) :
      vectorSecondDirectionalDerivative ξ x (-h) = vectorSecondDirectionalDerivative ξ x h := by
    calc
      vectorSecondDirectionalDerivative ξ x (-h)
          = (iteratedFDeriv ℝ 2 ξ x) (fun _ : Fin 2 ↦ (-1 : ℝ) • h) := by
              simp [vectorSecondDirectionalDerivative]
      _ = (∏ _ : Fin 2, (-1 : ℝ)) • (iteratedFDeriv ℝ 2 ξ x) (fun _ : Fin 2 ↦ h) := by
            rw [(iteratedFDeriv ℝ 2 ξ x).map_smul_univ (fun _ : Fin 2 ↦ (-1 : ℝ))
              (fun _ : Fin 2 ↦ h)]
      _ = vectorSecondDirectionalDerivative ξ x h := by
            norm_num [vectorSecondDirectionalDerivative]
  have h3 (x h : E₁) :
      vectorThirdDirectionalDerivative ξ x (-h) = -vectorThirdDirectionalDerivative ξ x h := by
    calc
      vectorThirdDirectionalDerivative ξ x (-h)
          = (iteratedFDeriv ℝ 3 ξ x) (fun _ : Fin 3 ↦ (-1 : ℝ) • h) := by
              simp [vectorThirdDirectionalDerivative]
      _ = (∏ _ : Fin 3, (-1 : ℝ)) • (iteratedFDeriv ℝ 3 ξ x) (fun _ : Fin 3 ↦ h) := by
            rw [(iteratedFDeriv ℝ 3 ξ x).map_smul_univ (fun _ : Fin 3 ↦ (-1 : ℝ))
              (fun _ : Fin 3 ↦ h)]
      _ = -vectorThirdDirectionalDerivative ξ x h := by
            norm_num [vectorThirdDirectionalDerivative]
  constructor <;> intro hbound x hx h
  · simpa [sub_eq_add_neg, h2, h3, hessianLocalNorm_neg] using hbound hx (-h)
  · simpa [sub_eq_add_neg, h2, h3, hessianLocalNorm_neg] using hbound hx (-h)

namespace IsBetaCompatibleWith

/-- A `β`-compatible map satisfies the sign-reversed pointwise cone-order bound from Theorem
5.4.6.1. -/
theorem compatibility_bound_sign_reversal
    {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {β : NNReal} {ξ : E₁ → E₂}
    (hξ : IsBetaCompatibleWith Q₁ K F β ξ) {x : E₁} (hx : x ∈ interior Q₁) (h : E₁) :
    (3 * (β : ℝ) * ‖h‖[F; x]) • (-vectorSecondDirectionalDerivative ξ x h) +
        vectorThirdDirectionalDerivative ξ x h ∈ K := by
  exact
    (betaCompatibility_sign_reversal_iff Q₁ K F (β : ℝ) ξ).mp
      (fun {_} hx' h' ↦ hξ.compatibility_bound hx' h') hx h

end IsBetaCompatibleWith
