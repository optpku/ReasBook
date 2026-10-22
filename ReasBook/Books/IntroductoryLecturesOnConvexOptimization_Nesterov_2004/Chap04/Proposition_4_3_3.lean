/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped Gradient CubicNewtonStepNotation LinearMap.BilinForm.BInducedNorm

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/- Proposition 4.3.3 lies in the finite-dimensional symmetric bilinear-form-induced cubic-Newton
first-order optimality domain.

Sampled owner declarations:
* `LinearMap.BilinForm.primalSeminorm` in `Definition_4_3_4`, the chapter owner for the
  `B`-induced norm `‖·‖[B]`;
* `LinearMap.BilinForm.IsSymm` in `Definition_4_2_5`, the canonical symmetry owner needed to
  expose the cubic derivative as the explicit covector `B (T_M(x) - x)`;
* `LinearMap.BilinForm.toDual` in mathlib, the finite-dimensional bridge identifying the
  bilinear-form covector `B (T_M(x) - x)` with a continuous dual functional;
* `LinearMap.BilinForm.PrimalSpace` in `Definition_4_2_9`, the intrinsic owner for the
  `B`-geometry carried by Chapter 4.3;
* `cubicNewtonModel` in `Definition_4_3_6`, the source cubic model minimized by `T_M(x)`;
* `CubicNewtonStep.firstOrderOptimalityCondition` in `Definition_4_3_6`, the core owner-level
  stationarity theorem `fderiv ℝ (cubicNewtonModel B f M x) (T_M x) = 0`;
* `hessian_isSelfAdjoint_of_contDiffAt` in `Text_4_2_3`, the chapter bridge turning a `C²`
  hypothesis into the self-adjointness needed to rewrite the Hessian derivative term.

Best owner abstraction:
* source-facing: the explicit first-order optimality equation `(4.3.12)` for `T_M(x)`;
* core/canonical: `CubicNewtonStep B f M` together with
  `CubicNewtonStep.firstOrderOptimalityCondition`;
* bridge/view: the dual-valued expansion of that derivative-zero statement, where the quadratic
  term is written with `hessian f x` only after a self-adjointness bridge, and the cubic term is
  written as `((M / 2) * r_M(x)) • B (T_M(x) - x)` only after a symmetry bridge for `B`.

Primitive data:
* the bilinear form `B`;
* the objective `f`;
* the regularization parameter `M`;
* the chosen cubic Newton step `step : CubicNewtonStep B f M`;
* the symmetry hypothesis `B.IsSymm`;
* the self-adjointness hypothesis `IsSelfAdjoint (hessian f x)`.

Derived API:
* the residual `r[step](x) = ‖step x - x‖[B]`;
* the owner derivative-zero statement for the cubic Newton model;
* the source-facing optimality equation below, obtained by expanding that owner theorem;
* the `C²` companion theorem obtained by the canonical bridge
  `hessian_isSelfAdjoint_of_contDiffAt`.

This proposition is therefore a source-facing bridge theorem on the existing Chapter 4.3 owner
`CubicNewtonStep`; it must not be collapsed to the ambient-norm Chapter 4.2 owner
`CubicRegularizationMapping`. -/

namespace CubicNewtonStep

variable {B : BilinForm ℝ E} [Fact B.toQuadraticMap.PosDef] {f : E → ℝ} {M : ℝ}

omit [FiniteDimensional ℝ E] in
/-- Helper for the Chapter 4.3 first-order optimality statement: the quadratic Taylor-model part
of the cubic Newton model has
the expected dual-valued derivative once the Hessian is self-adjoint. -/
lemma secondOrderTaylorModel_sub_hasFDerivAt_of_isSelfAdjoint
    {x y : E} (hH : IsSelfAdjoint (hessian f x)) :
    HasFDerivAt (fun T : E ↦ secondOrderTaylorModelAt f x T - f x)
      (InnerProductSpace.toDual ℝ E (∇ f x + hessian f x (y - x))) y := by
  -- Reuse the Chapter 4.2 Taylor-model derivative without reopening that calculus proof here.
  simpa using
    (_root_.secondOrderTaylorModel_sub_hasFDerivAt_of_isSelfAdjoint
      (f := f) (x := x) (y := y) hH)

omit [CompleteSpace E] [Fact B.toQuadraticMap.PosDef] in
/-- Helper for the Chapter 4.3 first-order optimality statement: the symmetric bilinear-form
quadratic displacement
`T ↦ B (T - x) (T - x)` has derivative `2 • B (y - x)` at `y`. -/
lemma b_displacement_quadratic_hasFDerivAt_of_isSymm
    {x y : E} (hSymm : B.IsSymm) :
    HasFDerivAt (fun T : E ↦ B (T - x) (T - x))
      ((2 : ℝ) • LinearMap.toContinuousLinearMap (B (y - x))) y := by
  -- Differentiate the two displacement factors through the bounded bilinear map `B`.
  let BcontLinear : E →ₗ[ℝ] E →L[ℝ] ℝ :=
    { toFun := fun z ↦ LinearMap.toContinuousLinearMap (B z)
      map_add' := by
        intro z₁ z₂
        ext w
        simp
      map_smul' := by
        intro c z
        ext w
        simp }
  let Bcont : E →L[ℝ] E →L[ℝ] ℝ :=
    ⟨BcontLinear, BcontLinear.continuous_of_finiteDimensional⟩
  have hsub : HasFDerivAt (fun T : E ↦ T - x) (ContinuousLinearMap.id ℝ E) y := by
    simpa using (hasFDerivAt_id y).sub_const x
  -- Symmetry collapses the two bilinear cross terms into `2 • B (y - x)`.
  convert Bcont.hasFDerivAt_of_bilinear hsub hsub using 1
  ext v
  simp [Bcont, BcontLinear, hSymm.eq]
  ring

omit [CompleteSpace E] in
/-- Helper for the Chapter 4.3 first-order optimality statement: the cubic `B`-penalty has
derivative
`((M / 2) * ‖y - x‖[B]) • B (y - x)` at `y`. -/
lemma cubic_b_penalty_hasFDerivAt_of_isSymm
    {x y : E} (hSymm : B.IsSymm) :
    HasFDerivAt (fun T : E ↦ (M / 6 : ℝ) * ‖T - x‖[B] ^ (3 : ℕ))
      ((((M / 2 : ℝ) * ‖y - x‖[B]) : ℝ) •
        LinearMap.toContinuousLinearMap (B (y - x))) y := by
  -- Rewrite the cubic `B`-penalty as the `(3 / 2)`-power of the quadratic displacement.
  have hquad :=
    b_displacement_quadratic_hasFDerivAt_of_isSymm (B := B) (x := x) (y := y) hSymm
  have hrpow :
      HasFDerivAt (fun T : E ↦ (B (T - x) (T - x)) ^ ((3 : ℝ) / 2))
        ((((3 : ℝ) / 2) * (B (y - x) (y - x)) ^ (((3 : ℝ) / 2) - 1)) •
          ((2 : ℝ) • LinearMap.toContinuousLinearMap (B (y - x)))) y := by
    exact hquad.rpow_const (p := (3 : ℝ) / 2) (by right; norm_num)
  have hscaled : HasFDerivAt
      (fun T : E ↦ (M / 6 : ℝ) * (B (T - x) (T - x)) ^ ((3 : ℝ) / 2))
      ((M / 6 : ℝ) •
        ((((3 : ℝ) / 2) * (B (y - x) (y - x)) ^ (((3 : ℝ) / 2) - 1)) •
          ((2 : ℝ) • LinearMap.toContinuousLinearMap (B (y - x))))) y := by
    simpa [smul_eq_mul] using hrpow.const_mul (M / 6 : ℝ)
  -- Normalize the scalar coefficient back to `((M / 2) * ‖y - x‖[B]) • B (y - x)`.
  convert hscaled using 1
  · funext T
    -- Normalize the cubic norm to the `(3 / 2)`-power of the quadratic form.
    rw [LinearMap.BilinForm.primalSeminorm_apply]
    have hPos : B.toQuadraticMap.PosDef := Fact.out
    have hnonneg : 0 ≤ B (T - x) (T - x) := by
      simpa using hPos.nonneg (T - x)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hnonneg]
    norm_num
  · ext v
    -- The derivative coefficient simplifies to the textbook factor `((M / 2) * ‖y - x‖[B])`.
    rw [LinearMap.BilinForm.primalSeminorm_apply]
    rw [Real.sqrt_eq_rpow]
    have hexp : ((3 : ℝ) / 2 - 1) = (1 / 2 : ℝ) := by
      norm_num
    rw [hexp]
    simp [ContinuousLinearMap.smul_apply]
    ring

/-- Helper for the Chapter 4.3 first-order optimality statement: the full cubic Newton model
derivative splits into the Taylor covector and the explicit symmetric-`B` cubic penalty covector. -/
lemma cubicNewtonModel_hasFDerivAt_of_isSelfAdjoint
    {x y : E} (hSymm : B.IsSymm) (hH : IsSelfAdjoint (hessian f x)) :
    HasFDerivAt (cubicNewtonModel B f M x)
      (InnerProductSpace.toDual ℝ E (∇ f x + hessian f x (y - x)) +
        ((M / 2 : ℝ) * ‖y - x‖[B]) • LinearMap.toContinuousLinearMap (B (y - x))) y := by
  -- The cubic Newton model is the Taylor part plus the cubic `B`-penalty.
  have hTaylor :=
    secondOrderTaylorModel_sub_hasFDerivAt_of_isSelfAdjoint (f := f) (x := x) (y := y) hH
  have hPenalty :=
    cubic_b_penalty_hasFDerivAt_of_isSymm (B := B) (M := M) (x := x) (y := y) hSymm
  convert hTaylor.add hPenalty using 1

/-- Primitive bridge form of the Chapter 4.3 first-order optimality statement: if `B` is
symmetric and `hessian f x` is self-adjoint, then the cubic Newton point `T_M(x)` satisfies the
source first-order optimality condition `(4.3.12)`, written as an equality of linear functionals
so the explicit Chapter 4.3 covector `B (T_M(x) - x)` remains visible. -/
theorem firstOrderOptimalityCondition_toDual_of_isSelfAdjoint
    (step : CubicNewtonStep B f M) (x : E)
    (hSymm : B.IsSymm) (hH : IsSelfAdjoint (hessian f x)) :
    InnerProductSpace.toDual ℝ E (∇ f x + hessian f x (step x - x)) +
        ((M / 2 : ℝ) * r[step](x)) •
          LinearMap.toContinuousLinearMap (B (step x - x)) = 0 := by
  -- Compare the explicit derivative formula with the owner theorem `fderiv = 0` at `step x`.
  have hderiv :=
    cubicNewtonModel_hasFDerivAt_of_isSelfAdjoint
      (B := B) (f := f) (M := M) (x := x) (y := step x) hSymm hH
  have hzero := step.firstOrderOptimalityCondition x
  rw [hderiv.fderiv] at hzero
  simpa [CubicNewtonStep.residual_apply] using hzero

/-- Proposition 4.3.3: if `f` is `C²` at `x` and `B` is symmetric, then the cubic Newton point
`T_M(x)` satisfies the source first-order optimality condition `(4.3.12)`. This is the Chapter
4.3 `C²` bridge obtained from
`firstOrderOptimalityCondition_toDual_of_isSelfAdjoint` via
`hessian_isSelfAdjoint_of_contDiffAt`. -/
theorem firstOrderOptimalityCondition_toDual
    (step : CubicNewtonStep B f M) (x : E)
    (hSymm : B.IsSymm) (hf : ContDiffAt ℝ 2 f x) :
    InnerProductSpace.toDual ℝ E (∇ f x + hessian f x (step x - x)) +
        ((M / 2 : ℝ) * r[step](x)) •
          LinearMap.toContinuousLinearMap (B (step x - x)) = 0 := by
  -- Supply the canonical `C²` bridge from differentiability to Hessian self-adjointness.
  exact firstOrderOptimalityCondition_toDual_of_isSelfAdjoint
    (B := B) (f := f) (M := M) step x hSymm (hessian_isSelfAdjoint_of_contDiffAt f x hf)

end CubicNewtonStep
