/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Example_5_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ScaledProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section GammaZero

variable (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal)

-- Proof sketch: combine the pointwise envelope identity from Proposition 12.26 with the firm
-- nonexpansiveness of the residual map from Proposition 12.28 to identify the first-order term
-- with `γ⁻¹ • (x - Prox_{γ f} x)`.
/-- Proposition 12.30: for `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, the `γ`-Moreau envelope, viewed as the
real-valued function `x ↦ ({}^γ f x).toReal`, is Fréchet differentiable at every point with
gradient `γ⁻¹ • (x - Prox_{γ f} x)`. -/
theorem moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
    (hf : f ∈ Γ₀(H))
    (x : H) :
    HasGradientAt (fun y : H ↦ (({}^[γ] f) y).toReal)
      ((γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x)) x := sorry

-- Proof sketch: apply `gradient_eq` to the pointwise gradient formula from
-- `moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero`.
/-- The gradient of the real-valued `γ`-Moreau envelope is the scaled residual
`γ⁻¹ • (Id - Prox_{γ f})`. -/
theorem gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero
    (hf : f ∈ Γ₀(H))
    :
    ∇ (fun y : H ↦ (({}^[γ] f) y).toReal) =
      fun x ↦ (γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x) :=
  gradient_eq <| moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero f γ hf

-- Proof sketch: Proposition 12.28 makes the residual map `Id - Prox_{γ f}` firmly nonexpansive;
-- invoke the existing owner lemma `lipschitzWith_one_of_firmlyNonexpansive` and then scale by
-- `γ⁻¹`, using the gradient formula above to rewrite the result.
/-- The gradient field of the real-valued `γ`-Moreau envelope is `γ⁻¹`-Lipschitz. -/
theorem lipschitzWith_inv_of_gradient_moreauEnvelope_toReal_of_mem_gammaZero
    (hf : f ∈ Γ₀(H))
    :
    LipschitzWith (Real.toNNReal ((γ : ℝ)⁻¹))
      (∇ (fun y : H ↦ (({}^[γ] f) y).toReal)) := by
  rw [gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero
    f γ hf]
  have hres :
      LipschitzWith 1 (fun x : H ↦ x - Prox[γ, f, hf] x) := by
    simpa [scaledProximityOperator] using
      lipschitzWith_one_of_firmlyNonexpansive <|
        id_sub_proximityOperator_firmlyNonexpansive_of_mem_gammaZero
          (γ • f)
          (smul_mem_gammaZero f hf γ)
  have hscaled :
      LipschitzWith (‖(γ : ℝ)⁻¹‖₊ * 1)
        (fun x : H ↦ (γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x)) :=
    (lipschitzWith_smul ((γ : ℝ)⁻¹)).comp hres
  simpa [Real.toNNReal_eq_nnnorm_of_nonneg (inv_nonneg.mpr γ.2.le)] using hscaled

end GammaZero

end ERealFunction
