/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20_Core
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (γ : Set.Ioi (0 : ℝ))

-- Proof sketch: apply Proposition 13.28 to the infimum presentation of `γ q - f*`, use the
-- positive-scaling conjugation rule from Proposition 13.23, and simplify the resulting quadratic
-- terms to obtain formula (13.22).
/-- Proposition 13.29 (1): for an `]-∞,+∞]`-valued function `f` and `γ > 0`, the Fenchel
conjugate of `γ f - q` equals `γ (γ q - f*)* - q`, where `q(x) = ‖x‖² / 2`. -/
theorem conjugate_smul_sub_halfSquaredNorm_eq
    :
    (fun x : H ↦ ((γ : ℝ) : EReal) * f.asEReal x - halfSquaredNorm.asEReal x)∗ =
      fun u : H ↦
        ((γ : ℝ) : EReal) *
            ((fun v : H ↦
                ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗ u) -
          halfSquaredNorm.asEReal u := sorry

-- Proof sketch: rewrite `γ q - f*` as a positive multiple of the proper conjugate
-- `γ f - q` using Proposition 13.29 (1), then use Proposition 13.15 to package its conjugate as
-- an `]-∞,+∞]`-valued function.
theorem isProper_smul_halfSquaredNorm_sub_conjugate
    (hproper : IsProper f.asEReal)
    :
    IsProper
      (fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v) := sorry

/-- The canonical `]-∞,+∞]`-valued representative of the conjugate `(γ q - f*)*`, where
`q(x) = ‖x‖² / 2`. -/
noncomputable abbrev conjugateSmulHalfSquaredNormSubConjugate
    (hproper : IsProper f.asEReal) : H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗ u),
      bot_lt_iff_ne_bot.mpr
        (conjugate_ne_bot_of_isProper
          (isProper_smul_halfSquaredNorm_sub_conjugate f γ hproper) u)⟩

/-- Coercing `conjugateSmulHalfSquaredNormSubConjugate f γ hproper` back to `EReal` recovers the
canonical conjugate `(γ q - f*)*`. -/
@[simp] theorem conjugateSmulHalfSquaredNormSubConjugate_apply
    (hproper : IsProper f.asEReal) (u : H) :
    (conjugateSmulHalfSquaredNormSubConjugate f γ hproper u : EReal) =
      ((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗ u) :=
  rfl

-- Proof sketch: rewrite `(γ q - f*)*` as `γ⁻¹ q` plus the convex function
-- `γ⁻¹ (γ f - q)*` using Proposition 13.29 (1), then apply the Chapter 10 owner theorem
-- `StrongConvexOn.toStronglyConvex_effectiveDomain`.
/-- Proposition 13.29 (2): the conjugate `(γ q - f*)*`, viewed through its canonical
`]-∞,+∞]`-valued representative, is `γ⁻¹`-strongly convex, where `q(x) = ‖x‖² / 2`. -/
theorem stronglyConvex_conjugateSmulHalfSquaredNormSubConjugate
    (hproper : IsProper f.asEReal)
    :
    StronglyConvex
      (conjugateSmulHalfSquaredNormSubConjugate f γ hproper)
      ((γ : ℝ)⁻¹)
    := sorry

-- Proof sketch: apply the Chapter 10 bridge `StronglyConvex.toStrongConvexOn_effectiveDomain` to
-- the source-facing strong-convexity statement above.
/-- Proposition 13.29 (2), bridge form: the finite representative of `(γ q - f*)*` is
`γ⁻¹`-strongly convex on its effective domain. -/
theorem strongConvexOn_conjugateSmulHalfSquaredNormSubConjugate
    (hproper : IsProper f.asEReal) :
    StrongConvexOn
      (dom ((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗))
      ((γ : ℝ)⁻¹)
      (fun u ↦
        ((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗ u).toReal) := by
  have hstrong :
      StronglyConvex
        (conjugateSmulHalfSquaredNormSubConjugate f γ hproper)
        ((γ : ℝ)⁻¹) :=
    stronglyConvex_conjugateSmulHalfSquaredNormSubConjugate f γ hproper
  simpa [conjugateSmulHalfSquaredNormSubConjugate, effectiveDomain, dom] using
    hstrong.toStrongConvexOn_effectiveDomain

end

end ERealFunction
