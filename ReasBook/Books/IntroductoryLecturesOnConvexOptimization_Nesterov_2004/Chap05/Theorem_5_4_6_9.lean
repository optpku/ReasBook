/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_8

-- Declarations for this item will be appended below by the statement pipeline.

open ProperCone
open scoped Gradient HessianLocalNorm

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- Theorem 5.4.6.9 lies in the subsection's cone-ordered third-derivative / barrier-composition
pairing domain.

Sampled owner declarations:
* `IsBetaCompatibleWith.compatibility_bound_sign_reversal` from `Theorem_5_4_6_1`, the owner-level
  sign-reversed compatibility bound on `D³ξ`;
* `compositionPotentialSigmaTwo` from `Theorem_5_4_6_5`, the source-facing owner for the
  `∇ᵧ Φ` pairing with `D²ξ`;
* `sigmaThree` from `Definition_5_4_6_8`, the source-facing name for the squared Hessian local
  norm;
* mathlib `ProperCone.innerDual` and `ProperCone.mem_innerDual`, the canonical owner abstraction
  for dual-cone membership in this cone-pairing domain;
* `barrier_yGradient_pairing_nonpos` from `Definition_5_4_6_4`, the barrier-owner bridge that
  supplies the dual-cone membership bridge in the barrier specialization.

Source/core/bridge triage:
* source-facing: the textbook upper bound for
  `⟪∇ᵧ Φ(ξ(x), z), D³ξ(x)[h, h, h]⟫`;
* core/canonical: `IsBetaCompatibleWith`, `vectorThirdDirectionalDerivative`, and the Hessian
  local norm `‖h‖[F; x]`;
* bridge/view: the source-facing scalars `compositionPotentialSigmaTwo` and `sigmaThree`, plus the
  barrier specialization `barrier_yGradient_pairing_nonpos`.

Primitive data:
* the compatibility owner `hξ`, the point `x ∈ interior Q₁`, the direction `h`, and the fixed
  parameter `z`;
* the dual-cone membership hypothesis
  `-∇ᵧ Φ(ξ(x), z) ∈ innerDual (K : Set E₂)`.

Derived API:
* the sign-reversed compatibility cone element;
* `compositionPotentialSigmaTwo Φ ξ x z h`;
* `sigmaThree F x h = ‖h‖[F; x]^2`.

The theorem therefore stays a bridge theorem over the compatibility owner and the subsection
source-facing scalar names, and it should live on the same complete-Hilbert-space owner layer as
those reused declarations rather than on an unnecessary finite-dimensional specialization. -/

/-- Theorem 5.4.6.9: if `ξ` is `β`-compatible with the barrier `F` on `Q₁`, if `x` lies in
`interior Q₁`, and if `-∇ᵧ Φ(ξ(x), z)` belongs to the dual cone `innerDual (K : Set E₂)`, then
`⟪∇ᵧ Φ(ξ(x), z), D³ξ(x)[h, h, h]⟫ ≤ 3 β σ₂ σ₃^{1/2}`, where
`σ₂ = compositionPotentialSigmaTwo Φ ξ x z h` and `σ₃ = sigmaThree F x h`. -/
theorem yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility
    {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ}
    {β : NNReal} {ξ : E₁ → E₂} {x h : E₁} {z : E₃}
    (hξ : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂)) :
    inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
        (vectorThirdDirectionalDerivative ξ x h) ≤
      3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z h *
        Real.sqrt (sigmaThree F x h) := by
  let g : E₂ := ∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x)
  let s : E₂ :=
    (3 * (β : ℝ) * ‖h‖[F; x]) • (-vectorSecondDirectionalDerivative ξ x h) +
      vectorThirdDirectionalDerivative ξ x h
  have hs : s ∈ K := by
    simpa [s] using hξ.compatibility_bound_sign_reversal hx h
  rw [mem_innerDual] at hneg_yGradient_mem_innerDual
  have hpair : inner ℝ g s ≤ 0 :=
    by simpa [g, real_inner_comm] using hneg_yGradient_mem_innerDual hs
  dsimp [g, s] at hpair ⊢
  rw [inner_add_right, inner_smul_right, inner_neg_right] at hpair
  rw [compositionPotentialSigmaTwo_def]
  rw [sqrt_sigmaThree]
  linarith

section Barrier

variable [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

noncomputable local instance instLocalChap05_Theorem_5_4_6_91 : SeminormedAddCommGroup (E₂ × E₃) :=
  WithLp.seminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_92 : NormedAddCommGroup (E₂ × E₃) :=
  WithLp.normedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_93 : NormedSpace ℝ (E₂ × E₃) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_6_91 : InnerProductSpace ℝ (E₂ × E₃) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E₂ E₃ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instLocalChap05_Theorem_5_4_6_94 : CompleteSpace (E₂ × E₃) := inferInstance

-- Proof sketch: use `barrier_yGradient_pairing_nonpos` from Definition 5.4.6.4 to prove the
-- canonical dual-cone membership `-∇ᵧ Φ(ξ(x), z) ∈ innerDual K` via `mem_innerDual`, then apply
-- Theorem 5.4.6.9 with that owner-level hypothesis.
/-- Under the barrier and recession hypotheses from Definition 5.4.6.4, the cone-pairing
assumption in Theorem 5.4.6.9 is automatic, equivalently
`-∇ᵧ Φ(ξ(x), z) ∈ innerDual (K : Set E₂)`. -/
theorem yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility_of_barrier
    {Q₁ : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
    {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {β : NNReal}
    {ξ : E₁ → E₂} {x h : E₁} {z : E₃}
    (hξ : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hQ₂_convex : Convex ℝ Q₂)
    (hΦ : ∃ μ : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_ : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_ : p ∈ Q₂) (τ : ℝ) (_ : 0 ≤ τ), p + τ • (s, (0 : E₃)) ∈ Q₂)
    (hyz : (ξ x, z) ∈ interior Q₂) :
    inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
        (vectorThirdDirectionalDerivative ξ x h) ≤
      3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z h *
        Real.sqrt (sigmaThree F x h) := by
  have hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂) := by
    rw [mem_innerDual]
    intro s hs
    simpa [real_inner_comm] using
      barrier_yGradient_pairing_nonpos hQ₂_convex K hΦ hK_recession hyz hs
  exact
    yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility hξ hx
      hneg_yGradient_mem_innerDual

end Barrier

end
