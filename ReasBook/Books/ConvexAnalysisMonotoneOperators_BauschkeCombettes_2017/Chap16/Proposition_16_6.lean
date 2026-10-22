/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u v

namespace ContinuousLinearMap

section SetValuedOperatorCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The set-valued operator `L^* ∘ B ∘ L`, sending `x` to the adjoint image of `B (L x)`. -/
def adjointImage
    (L : H →L[ℝ] K) (B : SetValuedOperator K K) : SetValuedOperator H H :=
  fun x ↦ L.adjoint '' (B (L x))

/-- Evaluating `ContinuousLinearMap.adjointImage L B` gives the adjoint image of `B (L x)`. -/
@[simp] theorem adjointImage_apply
    (L : H →L[ℝ] K) (B : SetValuedOperator K K) (x : H) :
    L.adjointImage B x = L.adjoint '' (B (L x)) :=
  rfl

end SetValuedOperatorCalculus

end ContinuousLinearMap

namespace ERealFunction

section SubdifferentialBasicProperties

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: unfold membership in both subdifferentials and rewrite the affine-minorant
-- inequality for the canonical positive-real scalar action on `]-∞,+∞]`-valued functions;
-- dividing by the positive scalar identifies witnesses on the two sides.
/-- Proposition 16.6 (1): the subdifferential of a positive scalar multiple is the corresponding
positive scalar multiple of the subdifferential. -/
theorem subdifferential_posReal_smul_eq_smul
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) :
    ∂ ((γ • f : H → Set.Ioi (⊥ : EReal))) = (γ : ℝ) • (∂ f : SetValuedOperator H H) := sorry

end SubdifferentialBasicProperties

namespace ContinuousLinearMap

section SubdifferentialCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The set-valued operator `L^* ∘ (∂ g) ∘ L`, sending `x` to the adjoint image of the
subdifferential of `g` at `L x`. This is the specialization of
`ContinuousLinearMap.adjointImage` to the subdifferential of `g`. -/
abbrev adjointImageSubdifferential
    (L : H →L[ℝ] K) (g : K → Set.Ioi (⊥ : EReal)) : SetValuedOperator H H :=
  L.adjointImage (∂ g)

/-- Evaluating `ContinuousLinearMap.adjointImageSubdifferential L g` gives the adjoint image of
the subdifferential of `g` at `L x`. -/
@[simp] theorem adjointImageSubdifferential_apply
    (L : H →L[ℝ] K) (g : K → Set.Ioi (⊥ : EReal)) (x : H) :
    ContinuousLinearMap.adjointImageSubdifferential L g x = L.adjoint '' ((∂ g) (L x)) :=
  _root_.ContinuousLinearMap.adjointImage_apply L (∂ g) x

end SubdifferentialCalculus

end ContinuousLinearMap

section SubdifferentialBasicProperties

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: if `u ∈ (∂ f) x` and `v ∈ (∂ g) (L x)`, combine the two subgradient inequalities;
-- rewrite the second one with the adjoint identity
-- `⟪L y - L x, v⟫ = ⟪y - x, L.adjoint v⟫` to obtain the defining inequality for
-- `u + L.adjoint v ∈ ∂ (f + g ∘ L) x`.
/-- Proposition 16.6 (2): if the effective domain of `g` meets the image under `L` of the
effective domain of `f`, then every sum of a subgradient of `f` at `x` and the adjoint image of a
subgradient of `g` at `L x` is a subgradient of `f + g ∘ L` at `x`. -/
theorem subdifferential_add_adjoint_image_subset_subdifferential_add_comp
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (x : H) :
    (∂ f) x + ContinuousLinearMap.adjointImageSubdifferential L g x ⊆
      (∂ (f + g ∘ L)) x := sorry

end SubdifferentialBasicProperties

end ERealFunction
