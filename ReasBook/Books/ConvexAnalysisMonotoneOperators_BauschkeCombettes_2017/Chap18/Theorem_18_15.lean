/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Proposition_14_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Theorem_14_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace

universe u

namespace ERealFunction

section StrongerDifferentiabilityNotions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Differentiability together with `β`-Lipschitz continuity of the gradient. -/
def HasLipschitzGradient
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) : Prop :=
  Differentiable ℝ f ∧
    LipschitzWith (Real.toNNReal (β : ℝ)) (∇ f)

/-- Differentiability together with the quadratic upper bound on the gradient increment. -/
def HasGradientInnerQuadraticUpperBound
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) : Prop :=
  Differentiable ℝ f ∧
    ∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ (β : ℝ) * ‖x - y‖ ^ (2 : ℕ)

/-- Differentiability together with the quadratic descent estimate. -/
def HasQuadraticDescentEstimate
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) : Prop :=
  Differentiable ℝ f ∧
    ∀ x y : H,
      f y ≤
        f x + ⟪y - x, ∇ f x⟫_ℝ + ((β : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ)

/-- Differentiability together with the Fenchel-conjugate quadratic lower bound along the
gradient image. -/
def HasConjugateGradientQuadraticLowerBound
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) : Prop :=
  Differentiable ℝ f ∧
    ∀ x y : H,
      conjugate (fun z : H ↦ ((f z : ℝ) : EReal)) (∇ f y) ≥
        conjugate (fun z : H ↦ ((f z : ℝ) : EReal)) (∇ f x) +
          ((⟪x, ∇ f y - ∇ f x⟫_ℝ : ℝ) : EReal) +
            ((((1 / (2 * (β : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) : ℝ) : EReal))

/-- Differentiability together with `1 / β`-cocoercivity of the gradient on the whole space. -/
def HasCocoerciveGradient
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) : Prop :=
  Differentiable ℝ f ∧
    CocoerciveOn (1 / (β : ℝ)) (Set.univ : Set H) (fun x : (Set.univ : Set H) ↦ ∇ f x)

/-- Convexity of the shifted quadratic `β q - f`, with `q(x) = ‖x‖² / 2`. -/
def HasHalfSquaredNormSubConvexity
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) : Prop :=
  _root_.ConvexOn ℝ Set.univ (fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x)

/-- Convexity of the shifted conjugate `f* - β⁻¹ q` on its effective domain. -/
def HasShiftedConjugateConvexity
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) : Prop :=
  ConvexOn (conjugateSubInvHalfSquaredNorm f β)
    (effectiveDomain (conjugateSubInvHalfSquaredNorm f β))

/-- The Moreau-envelope representation attached to the shifted conjugate `f* - β⁻¹ q`. -/
structure HasMoreauEnvelopeRepresentation
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) : Prop where
  mem_gammaZero :
    conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H)
  primal_moreau_eq :
    f.toEReal.asEReal =
      {}^[(β⁻¹ : PosReal)]
        (gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) mem_gammaZero)
  dual_moreau_eq :
    f.toEReal.asEReal =
      (moreauQuadraticKernel (β⁻¹ : PosReal)).asEReal -
        {}^[β] (conjugateSubInvHalfSquaredNorm f β) ∘ ((β : ℝ) • ·)

/-- The proximal-operator formulas for the gradient attached to the shifted conjugate
`f* - β⁻¹ q`. -/
structure HasProximalGradientRepresentation
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) : Prop where
  mem_gammaZero :
    conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H)
  gradient_eq_scaledProximityOperator :
    ∇ f =
      fun x : H ↦
            Prox[β, conjugateSubInvHalfSquaredNorm f β, mem_gammaZero] ((β : ℝ) • x)
  gradient_eq_smul_sub_scaledProximityOperator_gammaZeroConjugate :
    ∇ f =
      fun x : H ↦
        (β : ℝ) •
          (x -
            Prox[(β⁻¹ : PosReal),
              gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) mem_gammaZero,
              gammaZeroConjugate_mem_gammaZero mem_gammaZero] x)

-- Proof sketch: specialize Corollary 18.14 to the case `p = 1` to obtain the equivalence of
-- clauses `(i)` through `(v)`. Then use Proposition 4.4 and Proposition 17.7 to identify
-- cocoercivity with convexity of `β q - f`, Proposition 14.2 for `(vi) ↔ (vii)`, Corollary 13.38
-- together with Proposition 14.1 and Theorem 14.3 for `(vii) → (viii) → (ix)`, and finally
-- Proposition 12.30 to recover clause `(i)` from `(ix)`.
/-- Theorem 18.15: for a continuous convex function `f : H → ℝ`, a positive parameter `β`, and
`h = f* - β⁻¹ q` with `q(x) = ‖x‖² / 2`, the standard smoothness, descent, cocoercivity,
convexity, and proximal formulations of `β`-Lipschitz differentiability are equivalent. -/
theorem frechetDifferentiable_tfae_lipschitz_gradient
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ)) :
    List.TFAE
      [ HasLipschitzGradient f β,
        HasGradientInnerQuadraticUpperBound f β,
        HasQuadraticDescentEstimate f β,
        HasConjugateGradientQuadraticLowerBound f β,
        HasCocoerciveGradient f β,
        HasHalfSquaredNormSubConvexity f β,
        HasShiftedConjugateConvexity f β,
        HasMoreauEnvelopeRepresentation f β,
        HasProximalGradientRepresentation f β ] :=
  sorry

end StrongerDifferentiabilityNotions

end ERealFunction
