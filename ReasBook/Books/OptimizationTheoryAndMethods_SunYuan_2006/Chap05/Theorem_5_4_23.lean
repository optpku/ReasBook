/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_6_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_6_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_2_2
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open Filter
open scoped Matrix.Norms.L2Operator

section Chapter05Theorem5423

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Semantic recall: `lean_leansearch` surfaced the asymptotic `=o` API. Nearby Chapter 5 files
-- already use the canonical matrix action `Matrix.toEuclideanLin`, so this item keeps the
-- source-faithful restricted-Broyden data on that same surface.

/-- The Hessian-side restricted-Broyden correction vector
`w = (sᵀ B s)^(1 / 2) • ((sᵀ y)⁻¹ • y - (sᵀ B s)⁻¹ • B s)`. -/
def restrictedBroydenHessianDirection (B : MatrixN) (s y : Point) : Point :=
  Real.sqrt (dotProduct s (B.mulVec s)) •
    ((dotProduct s y)⁻¹ • y -
      (dotProduct s (B.mulVec s))⁻¹ • Matrix.toEuclideanLin B s)

/-- The defining formula for `restrictedBroydenHessianDirection`. -/
theorem restrictedBroydenHessianDirection_eq (B : MatrixN) (s y : Point) :
    restrictedBroydenHessianDirection B s y =
      Real.sqrt (dotProduct s (B.mulVec s)) •
        ((dotProduct s y)⁻¹ • y -
          (dotProduct s (B.mulVec s))⁻¹ • Matrix.toEuclideanLin B s) :=
  rfl

/-- The restricted-Broyden Hessian update
`B + (sᵀ y)⁻¹ • y yᵀ - (sᵀ B s)⁻¹ • (B s) (B s)ᵀ + θ • w wᵀ`. -/
def restrictedBroydenHessianUpdate (B : MatrixN) (s y : Point) (θ : ℝ) : MatrixN :=
  B
    + (dotProduct s y)⁻¹ • Matrix.vecMulVec y y
    - (dotProduct s (B.mulVec s))⁻¹ • Matrix.vecMulVec (B.mulVec s) (B.mulVec s)
    + θ •
        Matrix.vecMulVec
          (restrictedBroydenHessianDirection B s y)
          (restrictedBroydenHessianDirection B s y)

/-- The defining formula for `restrictedBroydenHessianUpdate`. -/
theorem restrictedBroydenHessianUpdate_eq (B : MatrixN) (s y : Point) (θ : ℝ) :
    restrictedBroydenHessianUpdate B s y θ =
      B
        + (dotProduct s y)⁻¹ • Matrix.vecMulVec y y
        - (dotProduct s (B.mulVec s))⁻¹ • Matrix.vecMulVec (B.mulVec s) (B.mulVec s)
        + θ •
            Matrix.vecMulVec
              (restrictedBroydenHessianDirection B s y)
              (restrictedBroydenHessianDirection B s y) :=
  rfl

/-- A `C²` objective on a convex domain has the local superlinear-convergence assumptions for the
restricted Broyden class when `xStar` is a local minimizer, the Hessian field is represented by
an explicit matrix field `hessian`, the quadratic form `u ↦ uᵀ (hessian x) u` is bounded below
uniformly by `m * ‖u‖²` on `D`, and the Hessian field is Lipschitz on a ball about `xStar`. -/
structure HasRestrictedBroydenLocalSuperlinearAssumptions
    (D : Set Point) (f : Point → ℝ) where
  convex_domain : Convex ℝ D
  contDiffOn : ContDiffOn ℝ 2 f D
  xStar : Point
  xStar_mem : xStar ∈ D
  isLocalMin : IsLocalMin f xStar
  hessian : Point → MatrixN
  hessian_hasFDerivAt :
    ∀ x ∈ D,
      HasFDerivAt (gradient f)
        (((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (hessian x)))
        x
  m : ℝ
  m_pos : 0 < m
  uniform_convex :
    ∀ x ∈ D, ∀ u : Point,
      m * ‖u‖ ^ (2 : ℕ) ≤ dotProduct u (Matrix.toEuclideanLin (hessian x) u)
  ε : ℝ
  ε_pos : 0 < ε
  ball_subset_domain : Metric.ball xStar ε ⊆ D
  γ : ℝ
  hessian_lipschitz :
    ∀ x xBar,
      x ∈ Metric.ball xStar ε →
      xBar ∈ Metric.ball xStar ε →
      ‖hessian xBar - hessian x‖ ≤ γ * ‖xBar - x‖

/-- Membership in `HasRestrictedBroydenLocalSuperlinearAssumptions D f` is membership in the
ambient domain `D`. -/
instance instMembershipPointHasRestrictedBroydenLocalSuperlinearAssumptions
    {D : Set Point} {f : Point → ℝ} :
    Membership Point (HasRestrictedBroydenLocalSuperlinearAssumptions D f) where
  mem _ x := x ∈ D

namespace HasRestrictedBroydenLocalSuperlinearAssumptions

@[simp] theorem mem_iff
    {D : Set Point} {f : Point → ℝ}
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f) (x : Point) :
    x ∈ h ↔ x ∈ D :=
  Iff.rfl

@[simp] theorem mem_xStar
    {D : Set Point} {f : Point → ℝ}
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f) :
    h.xStar ∈ h :=
  h.xStar_mem

/-- The distinguished local minimizer `xStar` from the restricted-Broyden assumption package,
viewed as a point of `D`. -/
def xStarInDomain
    {D : Set Point} {f : Point → ℝ}
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f) : D :=
  ⟨h.xStar, h.xStar_mem⟩

@[simp] theorem coe_xStarInDomain
    {D : Set Point} {f : Point → ℝ}
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f) :
    ((xStarInDomain h : D) : Point) = h.xStar :=
  rfl

@[simp] theorem xStarInDomain_mem
    {D : Set Point} {f : Point → ℝ}
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f) :
    (xStarInDomain h : Point) ∈ D :=
  h.xStar_mem

/-- Source-semantic expansion of
`HasRestrictedBroydenLocalSuperlinearAssumptions D f`. -/
theorem spec
    {D : Set Point} {f : Point → ℝ}
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f) :
    Convex ℝ D ∧
      ContDiffOn ℝ 2 f D ∧
      h.xStar ∈ D ∧
      IsLocalMin f h.xStar ∧
      (∀ x ∈ D,
        HasFDerivAt (gradient f)
          (((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (h.hessian x)))
          x) ∧
      0 < h.m ∧
      (∀ x ∈ D, ∀ u : Point,
        h.m * ‖u‖ ^ (2 : ℕ) ≤ dotProduct u (Matrix.toEuclideanLin (h.hessian x) u)) ∧
      0 < h.ε ∧
      Metric.ball h.xStar h.ε ⊆ D ∧
      ∀ x xBar,
        x ∈ Metric.ball h.xStar h.ε →
        xBar ∈ Metric.ball h.xStar h.ε →
        ‖h.hessian xBar - h.hessian x‖ ≤ h.γ * ‖xBar - x‖ := by
  exact ⟨h.convex_domain, h.contDiffOn, h.xStar_mem, h.isLocalMin, h.hessian_hasFDerivAt,
    h.m_pos, h.uniform_convex, h.ε_pos, h.ball_subset_domain, h.hessian_lipschitz⟩

end HasRestrictedBroydenLocalSuperlinearAssumptions

/-- A restricted-Broyden run on `D` for `f` consists of iterates `x k`, Hessian approximations
`B k`, explicit gradients `g k`, search directions `d k`, step sizes `α k`, a fixed
Broyden-class parameter `θ ∈ (0, 1)`, and the Hessian-side Broyden update together with the
secant positivity conditions used throughout the local convergence analysis. -/
structure RestrictedBroydenRun
    (D : Set Point) (f : Point → ℝ) where
  B0 : MatrixN
  x : ℕ → Point
  B : ℕ → MatrixN
  g : ℕ → Point
  d : ℕ → Point
  α : ℕ → ℝ
  θ : ℝ
  iterates_mem : ∀ k : ℕ, x k ∈ D
  B_zero : B 0 = B0
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)
  direction_eq : ∀ k : ℕ, d k = -Matrix.toEuclideanLin ((B k)⁻¹) (g k)
  stepSize_pos : ∀ k : ℕ, 0 < α k
  update : ∀ k : ℕ, x (k + 1) = x k + α k • d k
  theta_mem : θ ∈ Set.Ioo (0 : ℝ) 1
  secant_curvature_pos :
    ∀ k : ℕ, 0 < dotProduct (x (k + 1) - x k) (g (k + 1) - g k)
  step_quadratic_pos :
    ∀ k : ℕ,
      0 < dotProduct
        (x (k + 1) - x k) (Matrix.toEuclideanLin (B k) (x (k + 1) - x k))
  broyden_update :
    ∀ k : ℕ,
      B (k + 1) =
        restrictedBroydenHessianUpdate (B k) (x (k + 1) - x k) (g (k + 1) - g k) θ

/-- Source-semantic expansion of `RestrictedBroydenRun D f`. This exposes the iterates,
gradient model, fixed restricted-Broyden parameter condition `θ ∈ (0, 1)`, and the secant and
update data bundled into the run object. -/
theorem RestrictedBroydenRun.spec
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenRun D f) :
    (∀ k : ℕ, A.x k ∈ D) ∧
      A.B 0 = A.B0 ∧
      (∀ k : ℕ, HasGradientAt f (A.g k) (A.x k)) ∧
      (∀ k : ℕ, A.d k = -Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k)) ∧
      (∀ k : ℕ, 0 < A.α k) ∧
      (∀ k : ℕ, A.x (k + 1) = A.x k + A.α k • A.d k) ∧
      A.θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (∀ k : ℕ, 0 < dotProduct (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k)) ∧
      (∀ k : ℕ,
        0 < dotProduct
          (A.x (k + 1) - A.x k) (Matrix.toEuclideanLin (A.B k) (A.x (k + 1) - A.x k))) ∧
      ∀ k : ℕ,
        A.B (k + 1) =
          restrictedBroydenHessianUpdate
            (A.B k) (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) A.θ := by
  exact ⟨A.iterates_mem, A.B_zero, A.hasGradientAt, A.direction_eq, A.stepSize_pos, A.update,
    A.theta_mem, A.secant_curvature_pos, A.step_quadratic_pos, A.broyden_update⟩

/-- A restricted-Broyden run can be used as its iterate sequence `x`. -/
instance instCoeFunRestrictedBroydenRun
    {D : Set Point} {f : Point → ℝ} :
    CoeFun (RestrictedBroydenRun D f) (fun _ ↦ ℕ → Point) where
  coe A := A.x

namespace RestrictedBroydenRun

@[simp] theorem coe_apply
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenRun D f) (k : ℕ) :
    A k = A.x k :=
  rfl

/-- The inverse-form quasi-Newton view of a restricted-Broyden run with zero stopping tolerance.
The concrete iterate, gradient, direction, and step-size data are unchanged; only the
operator-valued inverse approximation `H k = Matrix.toEuclideanLin ((A.B k)⁻¹)` is exposed
through the canonical Chapter 5 owner `GeneralQuasiNewtonMethod` once the Hessian
approximations are known to stay positive definite. -/
theorem hessian_quasiNewtonEquation
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenRun D f) (k : ℕ) :
    satisfiesQuasiNewtonEquationHessianForm
      (Matrix.toEuclideanLin (A.B (k + 1)))
      (A.x (k + 1) - A.x k)
      (A.g (k + 1) - A.g k) := by
  let s : Point := A.x (k + 1) - A.x k
  let y : Point := A.g (k + 1) - A.g k
  have hsy : dotProduct s y ≠ 0 := ne_of_gt (A.secant_curvature_pos k)
  have hsBs_pos : 0 < dotProduct s (Matrix.toEuclideanLin (A.B k) s) := by
    simpa [s] using A.step_quadratic_pos k
  have hsBs_ne : dotProduct s ((A.B k).mulVec s) ≠ 0 := ne_of_gt hsBs_pos
  rw [satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff]
  -- Route correction: rewrite the local update to the canonical Hessian-form Broyden update,
  -- then use its built-in secant equation.
  rw [A.broyden_update k]
  have hCanonical :
      (broydenClassHessianUpdate (A.B k) s y A.θ).mulVec s = y :=
    broydenClassHessianUpdate_mulVec (A.B k) s y A.θ hsy hsBs_ne
  have hExplicit :
      broydenClassHessianUpdate (A.B k) s y A.θ =
        restrictedBroydenHessianUpdate (A.B k) s y A.θ := by
    rw [broydenClassHessianUpdate_eq_explicitUpdate (A.B k) s y A.θ hsy hsBs_pos]
    rfl
  simpa [s, y, hExplicit] using hCanonical

/-- Helper for Chapter05 Theorem 5.4.23: a positive-definite restricted-Broyden stage converts
the Hessian-form secant equation to the inverse-form one. -/
theorem quasiNewtonEquation_of_posDef
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenRun D f) (k : ℕ)
    (hPos : (A.B (k + 1)).PosDef) :
    satisfiesQuasiNewtonEquation
      (Matrix.toEuclideanLin ((A.B (k + 1))⁻¹))
      (A.g (k + 1) - A.g k)
      (A.x (k + 1) - A.x k) := by
  let _ := hPos.isUnit.invertible
  have hMul :
      Matrix.toEuclideanLin ((A.B (k + 1))⁻¹) *
          Matrix.toEuclideanLin (A.B (k + 1)) =
        1 := by
    ext x i
    simp [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  -- Positive definiteness supplies invertibility, so the canonical inverse conversion applies.
  exact satisfiesQuasiNewtonEquation_of_mul_eq_one hMul (A.hessian_quasiNewtonEquation k)

/-- The inverse-form quasi-Newton view of a restricted-Broyden run with zero stopping tolerance.
The concrete iterate, gradient, direction, and step-size data are unchanged; only the
operator-valued inverse approximation `H k = Matrix.toEuclideanLin ((A.B k)⁻¹)` is exposed
through the canonical Chapter 5 owner `GeneralQuasiNewtonMethod`. -/
abbrev toGeneralQuasiNewtonMethod
    {D : Set Point} {f : Point → ℝ} (A : RestrictedBroydenRun D f)
    (hB_posDef : ∀ k : ℕ, (A.B k).PosDef) :
    GeneralQuasiNewtonMethod f :=
  { ε := 0
    x := A.x
    H := fun k ↦ Matrix.toEuclideanLin ((A.B k)⁻¹)
    g := A.g
    d := A.d
    α := A.α
    epsilon_nonneg := le_rfl
    hasGradientAt := A.hasGradientAt
    direction_eq := fun k _ ↦ by
      simpa using A.direction_eq k
    stepSize_pos := fun k _ ↦ A.stepSize_pos k
    update := fun k _ ↦ by
      simpa using A.update k
    stationaryContinuation := fun k hk ↦ by
      have hg_norm : ‖A.g k‖ = 0 := le_antisymm hk (norm_nonneg _)
      have hg : A.g k = 0 := norm_eq_zero.mp hg_norm
      -- Once the recorded gradient vanishes, the frozen-tail convention keeps the iterate fixed.
      calc
        A.x (k + 1) = A.x k + A.α k • A.d k := A.update k
        _ = A.x k + A.α k • (-Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k)) := by
          rw [A.direction_eq k]
        _ = A.x k := by simp [hg]
    quasiNewtonEquation := fun _ _ ↦ by
      simpa using A.quasiNewtonEquation_of_posDef _ (hB_posDef _) }

@[simp] theorem toGeneralQuasiNewtonMethod_coe_apply
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenRun D f) (hB_posDef : ∀ k : ℕ, (A.B k).PosDef) (k : ℕ) :
    A.toGeneralQuasiNewtonMethod hB_posDef k = A k :=
  rfl

@[simp] theorem toGeneralQuasiNewtonMethod_g
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenRun D f) (hB_posDef : ∀ k : ℕ, (A.B k).PosDef) (k : ℕ) :
    (A.toGeneralQuasiNewtonMethod hB_posDef).g k = A.g k :=
  rfl

@[simp] theorem toGeneralQuasiNewtonMethod_d
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenRun D f) (hB_posDef : ∀ k : ℕ, (A.B k).PosDef) (k : ℕ) :
    (A.toGeneralQuasiNewtonMethod hB_posDef).d k = A.d k :=
  rfl

@[simp] theorem toGeneralQuasiNewtonMethod_α
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenRun D f) (hB_posDef : ∀ k : ℕ, (A.B k).PosDef) (k : ℕ) :
    (A.toGeneralQuasiNewtonMethod hB_posDef).α k = A.α k :=
  rfl

/-- Exact line search on the canonical inverse-form bridge
`A.toGeneralQuasiNewtonMethod` gives the same stagewise minimization statement for the
source-facing restricted-Broyden run `A`. -/
theorem exactLineSearch_isMinOn
    {D : Set Point} {f : Point → ℝ} {A : RestrictedBroydenRun D f}
    (hB_posDef : ∀ k : ℕ, (A.B k).PosDef)
    (hA : (A.toGeneralQuasiNewtonMethod hB_posDef).HasExactLineSearchOnNonnegativeRay) (k : ℕ) :
    IsMinOn (lineSearchObjective f (A k) (A.d k)) (Set.Ici 0) (A.α k) := by
  change IsMinOn (fun a : ℝ ↦ f (A k + a • A.d k)) (Set.Ici 0) (A.α k)
  simpa using hA.isMinOn k

/-- Every stage of a restricted-Broyden run with exact line search on the canonical
inverse-form bridge carries the line-search minimization property together with the standard
restricted-Broyden step data. -/
theorem exactLineSearch_stepSpec
    {D : Set Point} {f : Point → ℝ} {A : RestrictedBroydenRun D f}
    (hB_posDef : ∀ k : ℕ, (A.B k).PosDef)
    (hA : (A.toGeneralQuasiNewtonMethod hB_posDef).HasExactLineSearchOnNonnegativeRay)
    (k : ℕ) :
    IsMinOn (lineSearchObjective f (A k) (A.d k)) (Set.Ici 0) (A.α k) ∧
      A.d k = -Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k) ∧
      0 < A.α k ∧
      A.x (k + 1) = A.x k + A.α k • A.d k ∧
      A.θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      0 < dotProduct (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) ∧
      0 < dotProduct
        (A.x (k + 1) - A.x k) (Matrix.toEuclideanLin (A.B k) (A.x (k + 1) - A.x k)) ∧
      A.B (k + 1) =
        restrictedBroydenHessianUpdate
          (A.B k) (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) A.θ := by
  exact ⟨exactLineSearch_isMinOn hB_posDef hA k, A.direction_eq k, A.stepSize_pos k, A.update k,
    A.theta_mem, A.secant_curvature_pos k, A.step_quadratic_pos k, A.broyden_update k⟩

/-- A restricted-Broyden run converges `Q`-superlinearly to `xStar` when its iterates tend to
`xStar` and the next-step error is little-`o` of the current error. -/
class ConvergesQSuperlinearlyTo
    {D : Set Point} {f : Point → ℝ}
    (xStar : Point) (A : RestrictedBroydenRun D f) : Prop where
  tendsto : Tendsto A atTop (nhds xStar)
  superlinear :
    ((fun k ↦ ‖A (k + 1) - xStar‖) =o[atTop] fun k ↦ ‖A k - xStar‖)

/-- Every restricted-Broyden stage carries the search-direction, step-update, fixed
restricted-Broyden parameter, secant positivity, and Broyden-update data recorded in
`RestrictedBroydenRun D f`. -/
theorem stepSpec
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenRun D f) (k : ℕ) :
    A.d k = -Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k) ∧
      0 < A.α k ∧
      A.x (k + 1) = A.x k + A.α k • A.d k ∧
      A.θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      0 < dotProduct (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) ∧
      0 < dotProduct
        (A.x (k + 1) - A.x k) (Matrix.toEuclideanLin (A.B k) (A.x (k + 1) - A.x k)) ∧
      A.B (k + 1) =
        restrictedBroydenHessianUpdate
          (A.B k) (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) A.θ := by
  exact ⟨A.direction_eq k, A.stepSize_pos k, A.update k, A.theta_mem, A.secant_curvature_pos k,
    A.step_quadratic_pos k, A.broyden_update k⟩

end RestrictedBroydenRun

/-- A restricted-Broyden method on `D` for `f` is a restricted-Broyden run equipped with
Wolfe-Powell parameters and the corresponding line-search inequalities at every stage. -/
structure RestrictedBroydenMethod
    (D : Set Point) (f : Point → ℝ)
    extends RestrictedBroydenRun D f where
  rho : ℝ
  sigma : ℝ
  wolfeParameters : WolfePowellParameters rho sigma
  armijo :
    ∀ k : ℕ,
      f (x (k + 1)) ≤ f (x k) + rho * α k * dotProduct (g k) (d k)
  curvature :
    ∀ k : ℕ,
      sigma * dotProduct (g k) (d k) ≤ dotProduct (g (k + 1)) (d k)

/-- Source-semantic expansion of `RestrictedBroydenMethod D f`. This exposes the iterates,
gradient model, fixed restricted-Broyden parameter condition `θ ∈ (0, 1)`, and the
Wolfe-Powell parameter owner bundled into the run object. -/
theorem RestrictedBroydenMethod.spec
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) :
    (∀ k : ℕ, A.x k ∈ D) ∧
      A.B 0 = A.B0 ∧
      (∀ k : ℕ, HasGradientAt f (A.g k) (A.x k)) ∧
      (∀ k : ℕ, A.d k = -Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k)) ∧
      (∀ k : ℕ, 0 < A.α k) ∧
      (∀ k : ℕ, A.x (k + 1) = A.x k + A.α k • A.d k) ∧
      A.θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (∀ k : ℕ, 0 < dotProduct (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k)) ∧
      (∀ k : ℕ,
        0 < dotProduct
          (A.x (k + 1) - A.x k) (Matrix.toEuclideanLin (A.B k) (A.x (k + 1) - A.x k))) ∧
      (∀ k : ℕ,
        A.B (k + 1) =
          restrictedBroydenHessianUpdate
            (A.B k) (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) A.θ) ∧
      WolfePowellParameters A.rho A.sigma ∧
      (∀ k : ℕ,
        f (A.x (k + 1)) ≤ f (A.x k) + A.rho * A.α k * dotProduct (A.g k) (A.d k)) ∧
      ∀ k : ℕ,
        A.sigma * dotProduct (A.g k) (A.d k) ≤ dotProduct (A.g (k + 1)) (A.d k) := by
  exact ⟨A.toRestrictedBroydenRun.iterates_mem, A.toRestrictedBroydenRun.B_zero,
    A.toRestrictedBroydenRun.hasGradientAt, A.toRestrictedBroydenRun.direction_eq,
    A.toRestrictedBroydenRun.stepSize_pos, A.toRestrictedBroydenRun.update,
    A.toRestrictedBroydenRun.theta_mem, A.toRestrictedBroydenRun.secant_curvature_pos,
    A.toRestrictedBroydenRun.step_quadratic_pos, A.toRestrictedBroydenRun.broyden_update,
    A.wolfeParameters, A.armijo, A.curvature⟩

/-- A restricted-Broyden method can be viewed as its underlying restricted-Broyden run. -/
instance instCoeRestrictedBroydenMethodRestrictedBroydenRun
    {D : Set Point} {f : Point → ℝ} :
    Coe (RestrictedBroydenMethod D f) (RestrictedBroydenRun D f) where
  coe A := A.toRestrictedBroydenRun

/-- The Wolfe-Powell parameter owner carried by a restricted-Broyden method is available to
typeclass search. -/
instance instWolfePowellParametersRestrictedBroydenMethod
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) :
    WolfePowellParameters A.rho A.sigma :=
  A.wolfeParameters

/-- A restricted-Broyden method can be used as its iterate sequence `x`. -/
instance instCoeFunRestrictedBroydenMethod
    {D : Set Point} {f : Point → ℝ} :
    CoeFun (RestrictedBroydenMethod D f) (fun _ ↦ ℕ → Point) where
  coe A := A.x

namespace RestrictedBroydenMethod

@[simp] theorem coe_apply
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) (k : ℕ) :
    A k = A.x k :=
  rfl

/-- Every restricted-Broyden stage carries the search-direction, step-update, fixed
restricted-Broyden parameter, curvature, Broyden-update, and Wolfe-Powell data recorded in
`RestrictedBroydenMethod D f`. -/
theorem stepSpec
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) (k : ℕ) :
    A.d k = -Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k) ∧
      0 < A.α k ∧
      A.x (k + 1) = A.x k + A.α k • A.d k ∧
      A.θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      0 < dotProduct (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) ∧
      0 < dotProduct
        (A.x (k + 1) - A.x k) (Matrix.toEuclideanLin (A.B k) (A.x (k + 1) - A.x k)) ∧
      A.B (k + 1) =
        restrictedBroydenHessianUpdate
          (A.B k) (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) A.θ ∧
      WolfePowellParameters A.rho A.sigma ∧
      f (A.x (k + 1)) ≤ f (A.x k) + A.rho * A.α k * dotProduct (A.g k) (A.d k) ∧
      A.sigma * dotProduct (A.g k) (A.d k) ≤ dotProduct (A.g (k + 1)) (A.d k) := by
  exact ⟨A.toRestrictedBroydenRun.direction_eq k, A.toRestrictedBroydenRun.stepSize_pos k,
    A.toRestrictedBroydenRun.update k, A.toRestrictedBroydenRun.theta_mem,
    A.toRestrictedBroydenRun.secant_curvature_pos k,
    A.toRestrictedBroydenRun.step_quadratic_pos k, A.toRestrictedBroydenRun.broyden_update k,
    inferInstance, A.armijo k, A.curvature k⟩

end RestrictedBroydenMethod

/-- Helper for Chapter05 Theorem 5.4.23: the restricted-Broyden Hessian update is the
inverse-form Broyden convex-class update with the secant data swapped. This lets us reuse the
existing positive-definiteness theorem for the inverse-form class. -/
theorem restricted_broyden_hessian_update_posDef_of_posDef
    (B : MatrixN) (s y : Point) (θ : ℝ)
    (hB : B.PosDef)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hcurv : 0 < dotProduct s y)
    (hquad : 0 < dotProduct s (Matrix.toEuclideanLin B s)) :
    (restrictedBroydenHessianUpdate B s y θ).PosDef := by
  have hθ_nonneg : 0 ≤ θ := le_of_lt hθ.1
  have hBsymm : B.IsSymm := by
    simpa using hB.isHermitian
  have hExplicit :
      restrictedBroydenHessianUpdate B s y θ =
        broydenClassInverseUpdate B y s θ := by
    -- Route correction: identify the Hessian-side restricted-Broyden update with the already
    -- proved inverse-form Broyden convex class after swapping `(s, y)`.
    calc
      restrictedBroydenHessianUpdate B s y θ
          = broydenClassHessianUpdate B s y θ := by
              rw [broydenClassHessianUpdate_eq_explicitUpdate B s y θ (ne_of_gt hcurv) hquad]
              rfl
      _ = θ • bfgsInverseUpdate B y s + (1 - θ) • dfpInverseUpdate B y s := by
        -- Rewrite the two Hessian-side endpoints to the matching inverse-form owners.
        have hBfgs :
            bfgsHessianUpdate B s y = dfpInverseUpdate B y s := by
          simpa [bfgsHessianUpdate, dotProduct_comm] using
            (dfpInverseUpdate_eq_symmetricMatrixForm hBsymm y s).symm
        simp [broydenClassHessianUpdate, dfpDualHessianUpdate_eq_bfgsInverseUpdate, hBfgs]
      _ = broydenClassInverseUpdate B y s θ := by
        simp [broydenClassInverseUpdate, add_comm]
  have hPos :
      (broydenClassInverseUpdate B y s θ).PosDef := by
    -- The swapped update is inside the inverse Broyden convex class, so Theorem 5.2.2 applies.
    exact
      (broydenClassInverseUpdate_posDef_iff
        B hB y s θ hθ_nonneg (ne_of_gt (by simpa [dotProduct_comm] using hcurv))).2
        (by simpa [dotProduct_comm] using hcurv)
  simpa [hExplicit] using hPos

namespace RestrictedBroydenMethod

/-- Helper for Chapter05 Theorem 5.4.23: positive definiteness of the initial matrix propagates
through every restricted-Broyden Hessian update. -/
theorem matrices_posDef_of_initial_posDef
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) (hB0_posDef : A.B0.PosDef) :
    ∀ k : ℕ, (A.B k).PosDef := by
  intro k
  induction k with
  | zero =>
      simpa [A.toRestrictedBroydenRun.B_zero] using hB0_posDef
  | succ k hk =>
      rcases A.stepSpec k with
        ⟨_, _, _, hθ, hcurv, hquad, hupdate, _, _, _⟩
      -- Each update preserves positive definiteness because the restricted-Broyden step stays
      -- inside the convex Broyden class with positive curvature.
      simpa [hupdate] using
        restricted_broyden_hessian_update_posDef_of_posDef
          (A.B k)
          (A.x (k + 1) - A.x k)
          (A.g (k + 1) - A.g k)
          A.θ
          hk
          hθ
          hcurv
          hquad

/-- Helper for Chapter05 Theorem 5.4.23: the realized restricted-Broyden Newton step
`sₖ = xₖ₊₁ - xₖ`. -/
def step
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) : ℕ → Point :=
  fun k ↦ A.x (k + 1) - A.x k

/-- Helper for Chapter05 Theorem 5.4.23: the inexact-Newton residual
`rₖ = fderiv (gradient f) (xₖ) sₖ + gₖ` attached to the actual restricted-Broyden step. -/
def residual
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) : ℕ → Point :=
  fun k ↦ fderiv ℝ (gradient f) (A.x k) (step A k) + A.g k

/-- Helper for Chapter05 Theorem 5.4.23: the normalized residual ratio used as the forcing
sequence for the restricted-Broyden inexact-Newton package. -/
def forcing
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) : ℕ → ℝ :=
  fun k ↦ if A.g k = 0 then 0 else ‖residual A k‖ / ‖A.g k‖

/-- Helper for Chapter05 Theorem 5.4.23: a zero recorded gradient forces the realized
restricted-Broyden step to vanish. -/
lemma step_eq_zero_of_gradient_eq_zero
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) {k : ℕ}
    (hg : A.g k = 0) :
    step A k = 0 := by
  rcases A.stepSpec k with ⟨hd, _, hx, _, _, _, _, _, _, _⟩
  -- Once `gₖ = 0`, the search direction formula gives `dₖ = 0`, hence the step is zero.
  calc
    step A k = A.α k • A.d k := by
      simp [step, hx]
    _ = A.α k • (-Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k)) := by rw [hd]
    _ = 0 := by simp [hg]

/-- Helper for Chapter05 Theorem 5.4.23: every realized restricted-Broyden step is the stored
steplength times the stored search direction. -/
lemma step_eq_smul_direction
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) (k : ℕ) :
    step A k = A.α k • A.d k := by
  rcases A.stepSpec k with ⟨_, _, hx, _, _, _, _, _, _, _⟩
  -- The concrete step is just the iterate difference recorded by the update equation.
  simp [step, hx]

/-- Helper for Chapter05 Theorem 5.4.23: the concrete forcing sequence is pointwise
nonnegative because it is either zero or a norm ratio. -/
lemma forcing_nonneg
    {D : Set Point} {f : Point → ℝ}
    (A : RestrictedBroydenMethod D f) (k : ℕ) :
    0 ≤ forcing A k := by
  by_cases hg : A.g k = 0
  · -- At a stationary stage the forcing definition returns zero.
    simp [forcing, hg]
  · -- Otherwise the forcing term is the quotient of two nonnegative norms.
    rw [forcing, if_neg hg]
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Helper for Chapter05 Theorem 5.4.23: with the concrete step, residual, and forcing data,
the restricted-Broyden run is an inexact Newton sequence for `gradient f`. -/
theorem is_inexact_newton
    {D : Set Point} (f : Point → ℝ)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f)
    (A : RestrictedBroydenMethod D f) :
    IsInexactNewtonSequence (gradient f) A (step A) (residual A) (forcing A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    -- The assumption package already records the Fréchet derivative of `gradient f` at every
    -- iterate, so we only need to rewrite it to the canonical `fderiv` form.
    simpa [(h.hessian_hasFDerivAt (A.x k) (A.iterates_mem k)).fderiv] using
      h.hessian_hasFDerivAt (A.x k) (A.iterates_mem k)
  · intro k
    -- The residual definition is chosen so the inexact Newton linear system is tautological.
    have hg : gradient f (A.x k) = A.g k := by
      simpa using (A.hasGradientAt k).gradient
    rw [residual, hg]
    abel
  · intro k
    have hg : gradient f (A.x k) = A.g k := by
      simpa using (A.hasGradientAt k).gradient
    by_cases hgk : A.g k = 0
    · -- In the stationary case the direction formula gives a zero step, hence zero residual.
      have hstep : step A k = 0 :=
        step_eq_zero_of_gradient_eq_zero A hgk
      have hres : residual A k = 0 := by
        simp [residual, hstep, hgk]
      simp [forcing, hg, hgk, hres]
    · -- Otherwise the forcing term is the exact residual ratio.
      have hgnorm_ne : ‖A.g k‖ ≠ 0 := by
        exact norm_ne_zero_iff.mpr hgk
      rw [forcing, if_neg hgk, hg]
      have hratio :
          ‖residual A k‖ / ‖A.g k‖ * ‖A.g k‖ = ‖residual A k‖ := by
        field_simp [hgnorm_ne]
      exact le_of_eq hratio.symm
  · intro k
    -- The inexact-Newton state update uses the realized step `xₖ₊₁ - xₖ`.
    simp [step]

end RestrictedBroydenMethod

/-- Helper for Chapter05 Theorem 5.4.23: on the local ball from the source hypotheses,
the gradient map inherits the needed `C¹` regularity from the `C²` objective. -/
theorem restricted_broyden_gradient_contDiffOn_ball
    (f : Point → ℝ) (D : Set Point)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f) :
    ContDiffOn ℝ 1 (gradient f) (Metric.ball h.xStar h.ε) := by
  let U : Set Point := Metric.ball h.xStar h.ε
  have hU_open : IsOpen U := by
    simp [U]
  have hC2On_ball : ContDiffOn ℝ 2 f U := h.contDiffOn.mono h.ball_subset_domain
  have hC1fderiv : ContDiffOn ℝ 1 (fderiv ℝ f) U := by
    simpa using hC2On_ball.fderiv_of_isOpen hU_open (by norm_num)
  -- Rewrite the gradient as the Riesz representative of the Fréchet derivative.
  change ContDiffOn ℝ 1 (fun x ↦ (InnerProductSpace.toDual ℝ Point).symm (fderiv ℝ f x)) U
  exact (InnerProductSpace.toDual ℝ Point).symm.contDiff.comp_contDiffOn hC1fderiv

/-- Helper for Chapter05 Theorem 5.4.23: the uniform-convex lower bound forces the Hessian
quadratic form at `h.xStar` to be strictly positive on every nonzero direction. -/
theorem restricted_broyden_hessian_quadratic_pos_at_xStar
    (f : Point → ℝ) (D : Set Point)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f) :
    ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f h.xStar y := by
  intro y hy
  have hnorm_sq_pos : 0 < ‖y‖ ^ (2 : ℕ) := by
    exact pow_pos (norm_pos_iff.mpr hy) 2
  have huniform :
      h.m * ‖y‖ ^ (2 : ℕ) ≤
        dotProduct y (Matrix.toEuclideanLin (h.hessian h.xStar) y) :=
    h.uniform_convex h.xStar h.xStar_mem y
  have hquadratic :
      hessianQuadraticAt f h.xStar y =
        dotProduct y (Matrix.toEuclideanLin (h.hessian h.xStar) y) := by
    -- The bundled Hessian matrix is the Fréchet derivative of `gradient f` at `h.xStar`.
    calc
      hessianQuadraticAt f h.xStar y
          = inner ℝ y (((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
              (h.hessian h.xStar)) y) := by
              simp [hessianQuadraticAt, hessianAt,
                (h.hessian_hasFDerivAt h.xStar h.xStar_mem).fderiv]
      _ = dotProduct y (Matrix.toEuclideanLin (h.hessian h.xStar) y) := by
          simpa using Matrix.inner_toEuclideanCLM (h.hessian h.xStar) y y
  rw [hquadratic]
  exact lt_of_lt_of_le (mul_pos h.m_pos hnorm_sq_pos) huniform

/-- Helper for Chapter05 Theorem 5.4.23: the local `C¹` control of `gradient f` on the source
ball and the positive Hessian quadratic form at `h.xStar` package `gradient f` as a regular zero
of the Chapter 3 inexact-Newton owner. -/
theorem gradient_regular_zero_of_ball_contDiff_and_hessian_pos
    (f : Point → ℝ) (D : Set Point)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f) :
    IsRegularZero (gradient f) h.xStar := by
  let U : Set Point := Metric.ball h.xStar h.ε
  have hxStar_mem : h.xStar ∈ U := by
    simpa [U, Metric.mem_ball] using h.ε_pos
  have hU_open : IsOpen U := by
    simp [U]
  refine ⟨?_, ?_, ?_⟩
  · -- A local minimizer has vanishing gradient, so `h.xStar` is a zero of `gradient f`.
    rw [gradient, IsLocalMin.fderiv_eq_zero h.isLocalMin, map_zero]
  · -- The `C²` source hypothesis already gave the needed `C¹` germ of `gradient f` on the ball.
    exact
      ⟨U, IsOpen.mem_nhds hU_open hxStar_mem,
        restricted_broyden_gradient_contDiffOn_ball f D h⟩
  · let hessianLin : Point →ₗ[ℝ] Point := (hessianAt f h.xStar).toLinearMap
    have hker : LinearMap.ker hessianLin = ⊥ := by
      -- Positive definiteness rules out nonzero vectors in the Hessian kernel.
      refine LinearMap.ker_eq_bot'.2 ?_
      intro y hy
      by_contra hy_ne
      have hpositive :
          0 < hessianQuadraticAt f h.xStar y :=
        restricted_broyden_hessian_quadratic_pos_at_xStar f D h y hy_ne
      have hzero : hessianQuadraticAt f h.xStar y = 0 := by
        simpa [hessianQuadraticAt, hessianLin] using congrArg (fun v ↦ inner ℝ y v) hy
      linarith
    have hsurj : LinearMap.range hessianLin = ⊤ :=
      LinearMap.ker_eq_bot_iff_range_eq_top.1 hker
    -- In finite dimension, injectivity of the Hessian linear map upgrades to invertibility.
    exact ⟨ContinuousLinearEquiv.ofBijective (hessianAt f h.xStar) hker hsurj, rfl⟩

/-- Helper for Chapter05 Theorem 5.4.23: the source Hessian-Lipschitz hypothesis becomes the
exact `fderiv ℝ (gradient f)`-difference estimate needed by the Taylor remainder owner. -/
theorem restricted_broyden_fderiv_gradient_lipschitz_on_ball
    (f : Point → ℝ) (D : Set Point)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f) :
    ∀ x xBar,
      x ∈ Metric.ball h.xStar h.ε →
      xBar ∈ Metric.ball h.xStar h.ε →
      ‖fderiv ℝ (gradient f) xBar - fderiv ℝ (gradient f) x‖ ≤ h.γ * ‖xBar - x‖ := by
  intro x xBar hx hxBar
  -- Rewrite both derivatives to the concrete Hessian matrix field before using the source bound.
  calc
    ‖fderiv ℝ (gradient f) xBar - fderiv ℝ (gradient f) x‖
        = ‖((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (h.hessian xBar)) -
            ((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (h.hessian x))‖ := by
            rw [(h.hessian_hasFDerivAt xBar (h.ball_subset_domain hxBar)).fderiv,
              (h.hessian_hasFDerivAt x (h.ball_subset_domain hx)).fderiv]
    _ = ‖h.hessian xBar - h.hessian x‖ := by
          simpa using (Matrix.cstar_norm_def (h.hessian xBar - h.hessian x)).symm
    _ ≤ h.γ * ‖xBar - x‖ := h.hessian_lipschitz x xBar hx hxBar

/-- Helper for Chapter05 Theorem 5.4.23: once the restricted-Broyden iterates converge to
`xStar`, the realized steps `xₖ₊₁ - xₖ` converge to zero. -/
theorem restricted_broyden_step_tendsto_zero_of_tendsto
    {D : Set Point} {f : Point → ℝ}
    {xStar : Point} {A : RestrictedBroydenMethod D f}
    (hA : Tendsto A atTop (nhds xStar)) :
    Tendsto (RestrictedBroydenMethod.step A) atTop (nhds 0) := by
  have hShift : Tendsto (fun k : ℕ ↦ A (k + 1)) atTop (nhds xStar) := by
    exact hA.comp (tendsto_add_atTop_nat 1)
  -- Subtract the two tails of the convergent iterate sequence to obtain `sₖ → 0`.
  have hSub :
      Tendsto (fun k : ℕ ↦ A (k + 1) - A k) atTop (nhds (xStar - xStar)) :=
    hShift.sub hA
  -- Unfold the concrete step sequence back to the iterate difference `xₖ₊₁ - xₖ`.
  change Tendsto (fun k : ℕ ↦ A.x (k + 1) - A.x k) atTop (nhds 0)
  simpa using hSub

namespace RestrictedBroydenRun

/-- Helper for Chapter05 Theorem 5.4.23: the chapter-level superlinear convergence owner
packages directly into the source-facing restricted-Broyden convergence class. -/
theorem convergesQSuperlinearlyTo_of_hasSuperlinearConvergenceTo
    {D : Set Point} {f : Point → ℝ}
    {xStar : Point} {A : RestrictedBroydenRun D f}
    (hA : HasSuperlinearConvergenceTo A xStar) :
    ConvergesQSuperlinearlyTo xStar A := by
  -- The two owners record the same convergence data on the same iterate sequence.
  exact ⟨hA.tendsto, hA.isLittleO⟩

end RestrictedBroydenRun

namespace Chapter03.InexactNewtonCollisionFree

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Chapter05 Theorem 5.4.23: a collision-free local copy of the bounded-forcing
predicate needed from the Chapter 3.6 inexact-Newton endgame. -/
def HasInexactNewtonForcingBound (ηSeq : ℕ → ℝ) (η : ℝ) : Prop :=
  (∀ k : ℕ, 0 ≤ ηSeq k) ∧ ∀ k : ℕ, ηSeq k ≤ η

/-- Unfolding formula for the collision-free bounded-forcing predicate. -/
theorem hasInexactNewtonForcingBound_iff (ηSeq : ℕ → ℝ) (η : ℝ) :
    HasInexactNewtonForcingBound ηSeq η ↔
      (∀ k : ℕ, 0 ≤ ηSeq k) ∧ ∀ k : ℕ, ηSeq k ≤ η :=
  Iff.rfl

namespace HasInexactNewtonForcingBound

/-- A collision-free forcing bound records nonnegativity of each forcing term. -/
theorem nonneg {ηSeq : ℕ → ℝ} {η : ℝ}
    (h : HasInexactNewtonForcingBound ηSeq η) (k : ℕ) :
    0 ≤ ηSeq k :=
  h.1 k

/-- A collision-free forcing bound records the uniform upper bound `ηSeq k ≤ η`. -/
theorem le {ηSeq : ℕ → ℝ} {η : ℝ}
    (h : HasInexactNewtonForcingBound ηSeq η) (k : ℕ) :
    ηSeq k ≤ η :=
  h.2 k

end HasInexactNewtonForcingBound

/-- Helper for Chapter05 Theorem 5.4.23: collision-free owner for the bounded-forcing
eventual-linear inexact-Newton endgame from Chapter 3.6. -/
theorem inexactNewton_tendsto_root_and_eventually_linear_of_forcing_bounded
    (F : E → E) (xStar : E) (η : ℝ)
    (hRegular : IsRegularZero F xStar)
    (hη_lt_one : η < 1) :
    ∃ ε > 0, ∀ x s r : ℕ → E, ∀ ηSeq : ℕ → ℝ,
      ‖x 0 - xStar‖ < ε →
      IsInexactNewtonSequence F x s r ηSeq →
      HasInexactNewtonForcingBound ηSeq η →
      HasEventuallyLinearConvergenceTo x xStar := by
  -- Route correction: this owner must live on a collision-free Chapter 3.6 surface because
  -- importing the current `Theorem_3_6_6` duplicates `HasEventuallyLinearConvergenceTo.casesOn`.
  -- TODO: re-home the source proof of Theorem 3.6.6(1) here and keep its regular-zero +
  -- bounded-forcing route unchanged.
  sorry

/-- Helper for Chapter05 Theorem 5.4.23: collision-free owner for the residual-little-`o`
to superlinear-convergence equivalence from Chapter 3.6. -/
theorem inexactNewton_residual_isLittleO_iff_qSuperlinear
    (F : E → E) (xStar : E) (η : ℝ)
    (hRegular : IsRegularZero F xStar)
    (hη_lt_one : η < 1)
    (x s r : ℕ → E) (ηSeq : ℕ → ℝ)
    (hInexact : IsInexactNewtonSequence F x s r ηSeq)
    (hηBound : HasInexactNewtonForcingBound ηSeq η)
    (hx : Tendsto x atTop (nhds xStar)) :
    ((fun k ↦ ‖r k‖) =o[atTop] fun k ↦ ‖F (x k)‖) ↔
      HasSuperlinearConvergenceTo x xStar := by
  -- Route correction: this equivalence is the second Chapter 3.6 owner blocked by the same
  -- import collision, so the proof must be re-owned here instead of routing around it locally.
  -- TODO: transplant the source proof of Theorem 3.6.4 on this collision-free namespace.
  sorry

end

end Chapter03.InexactNewtonCollisionFree

/-- Helper for Chapter05 Theorem 5.4.23: the actual restricted-Broyden forcing sequence should
admit a uniform bound `η ∈ (0, 1)` once the Wolfe-Powell curvature inequality is combined with
the local Hessian-Lipschitz control. -/
theorem restricted_broyden_forcing_bound_of_wolfePowell
    (f : Point → ℝ) (D : Set Point)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f)
    (A : RestrictedBroydenMethod D f)
    (hB0_posDef : A.B0.PosDef) :
    ∃ η ∈ Set.Ioo (0 : ℝ) 1,
      Chapter03.InexactNewtonCollisionFree.HasInexactNewtonForcingBound
        (RestrictedBroydenMethod.forcing A) η := by
  have hB_posDef : ∀ k : ℕ, (A.B k).PosDef :=
    A.matrices_posDef_of_initial_posDef hB0_posDef
  -- Route correction: the source proof controls the concrete restricted-Broyden forcing ratio
  -- stagewise via the Wolfe-Powell curvature gap and the local Hessian-Lipschitz remainder; it
  -- should not be replaced by a different abstract forcing sequence.
  -- TODO: split on `A.g k = 0`; in the nonzero case combine the curvature lower bound,
  -- `hB_posDef`, and the Taylor remainder estimate on the source ball to prove
  -- `RestrictedBroydenMethod.forcing A k ≤ η` for one uniform `η < 1`.
  sorry

/-- Helper for Chapter05 Theorem 5.4.23: once the concrete restricted-Broyden forcing sequence is
uniformly bounded by some `η < 1`, the inexact-Newton package should supply eventual linear
convergence of the iterates to `h.xStar`. -/
theorem restricted_broyden_eventually_linear_of_forcing_bounded
    (f : Point → ℝ) (D : Set Point)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f)
    (A : RestrictedBroydenMethod D f)
    (hA0_local : A 0 ∈ Metric.ball h.xStar h.ε)
    (hηBound : ∃ η ∈ Set.Ioo (0 : ℝ) 1,
      Chapter03.InexactNewtonCollisionFree.HasInexactNewtonForcingBound
        (RestrictedBroydenMethod.forcing A) η) :
    HasEventuallyLinearConvergenceTo A h.xStar := by
  have hInexact :
      IsInexactNewtonSequence
        (gradient f)
        A
        (RestrictedBroydenMethod.step A)
        (RestrictedBroydenMethod.residual A)
        (RestrictedBroydenMethod.forcing A) := by
    simpa using RestrictedBroydenMethod.is_inexact_newton f h A
  have hRegular : IsRegularZero (gradient f) h.xStar :=
    gradient_regular_zero_of_ball_contDiff_and_hessian_pos f D h
  have hA0_norm : ‖A 0 - h.xStar‖ < h.ε := by
    -- Convert the source-ball hypothesis on the initial iterate to the norm inequality used by
    -- the Chapter 3.6 local-convergence surface.
    simpa [Metric.mem_ball, dist_eq_norm] using hA0_local
  rcases hηBound with ⟨η, hη_mem, hηBound'⟩
  -- Route correction: the remaining work is not another local quasi-Newton decomposition.
  -- The source route is to shrink the local ball if needed and then apply the collision-free
  -- bounded-forcing inexact-Newton theorem to the already-packaged run `A`.
  -- TODO: rebuild the source assumptions on a smaller ball containing `A 0` when necessary,
  -- apply `Chapter03.InexactNewtonCollisionFree
  --   .inexactNewton_tendsto_root_and_eventually_linear_of_forcing_bounded`
  -- to `F := gradient f`, and return the resulting eventual linear convergence owner.
  sorry

/-- Helper for Chapter05 Theorem 5.4.23: eventual linear convergence should upgrade the local
Taylor remainder estimate on `gradient f` to the residual little-`o` condition needed for the
Chapter 3.6 superlinear endgame. -/
theorem restricted_broyden_residual_isLittleO
    (f : Point → ℝ) (D : Set Point)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f)
    (A : RestrictedBroydenMethod D f)
    (hLinear : HasEventuallyLinearConvergenceTo A h.xStar) :
    ((fun k ↦ ‖RestrictedBroydenMethod.residual A k‖) =o[atTop]
      fun k ↦ ‖gradient f (A k)‖) := by
  have hA : Tendsto A atTop (nhds h.xStar) := hLinear.tendsto
  have hStepZero :
      Tendsto (RestrictedBroydenMethod.step A) atTop (nhds 0) :=
    restricted_broyden_step_tendsto_zero_of_tendsto hA
  have hFDerivLip :
      ∀ x xBar,
        x ∈ Metric.ball h.xStar h.ε →
        xBar ∈ Metric.ball h.xStar h.ε →
        ‖fderiv ℝ (gradient f) xBar - fderiv ℝ (gradient f) x‖ ≤
          h.γ * ‖xBar - x‖ :=
    restricted_broyden_fderiv_gradient_lipschitz_on_ball f D h
  -- Route correction: the book closes with a Taylor remainder estimate on the eventual ball,
  -- after converting eventual linear convergence into the step-vs-gradient asymptotic bridge.
  -- TODO: use `hLinear`, `hA`, `hStepZero`, and `hFDerivLip` to prove that the residuals are
  -- little-`o` of `‖gradient f (A k)‖`.
  sorry

/-- Helper for Chapter05 Theorem 5.4.23: once the concrete restricted-Broyden run has bounded
forcing, eventual linear convergence, and the residual little-`o` estimate, the collision-free
Chapter 3.6 residual/superlinear bridge yields the canonical superlinear owner. -/
theorem restricted_broyden_superlinear_of_eventually_linear_and_residual
    (f : Point → ℝ) (D : Set Point)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f)
    (A : RestrictedBroydenMethod D f)
    (hηBound : ∃ η ∈ Set.Ioo (0 : ℝ) 1,
      Chapter03.InexactNewtonCollisionFree.HasInexactNewtonForcingBound
        (RestrictedBroydenMethod.forcing A) η)
    (hLinear : HasEventuallyLinearConvergenceTo A h.xStar)
    (hResidualLittleO :
      ((fun k ↦ ‖RestrictedBroydenMethod.residual A k‖) =o[atTop]
        fun k ↦ ‖gradient f (A k)‖)) :
    HasSuperlinearConvergenceTo A h.xStar := by
  rcases hηBound with ⟨η, hη_mem, hηBound'⟩
  have hInexact :
      IsInexactNewtonSequence
        (gradient f)
        A
        (RestrictedBroydenMethod.step A)
        (RestrictedBroydenMethod.residual A)
        (RestrictedBroydenMethod.forcing A) := by
    simpa using RestrictedBroydenMethod.is_inexact_newton f h A
  have hRegular : IsRegularZero (gradient f) h.xStar :=
    gradient_regular_zero_of_ball_contDiff_and_hessian_pos f D h
  -- The collision-free Chapter 3.6 owner is exactly the missing bridge from the residual
  -- asymptotic estimate to superlinear convergence of the iterate sequence.
  exact
    (Chapter03.InexactNewtonCollisionFree.inexactNewton_residual_isLittleO_iff_qSuperlinear
      (F := gradient f)
      (xStar := h.xStar)
      (η := η)
      hRegular
      hη_mem.2
      A
      (RestrictedBroydenMethod.step A)
      (RestrictedBroydenMethod.residual A)
      (RestrictedBroydenMethod.forcing A)
      hInexact
      hηBound'
      hLinear.tendsto).mp hResidualLittleO

/-- Chapter05 Theorem 5.4.23: under the bundled hypotheses unpacked by
`HasRestrictedBroydenLocalSuperlinearAssumptions.spec` and `RestrictedBroydenMethod.spec`,
`D` is convex, `f : ℝ^n → ℝ` is `C²` on `D`, `h.xStar` belongs to `D` and is the intended local
minimizer/solution, `h.hessian` differentiates `gradient f` on `D`, the Hessian field satisfies
the uniform lower bound `h.m * ‖u‖² ≤ uᵀ ∇²f(x) u` on `D`, the Hessian is Lipschitz on a
neighborhood of `h.xStar`, and `A` is a restricted-Broyden run with a fixed `θ ∈ (0, 1)` and
Wolfe-Powell parameters `ρ`, `σ` satisfying `WolfePowellParameters ρ σ`, whose initial iterate
lies in the local ball `Metric.ball h.xStar h.ε`. Then a positive-definite initial matrix `A.B0`
implies that the generated sequence converges to `h.xStar` `Q`-superlinearly. -/
theorem restrictedBroyden_tendsto_and_qSuperlinear_of_uniformConvex_and_wolfePowell
    (f : Point → ℝ) (D : Set Point)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f)
    (A : RestrictedBroydenMethod D f)
    (hA0_local : A 0 ∈ Metric.ball h.xStar h.ε)
    (hB0_posDef : A.B0.PosDef) :
    RestrictedBroydenRun.ConvergesQSuperlinearlyTo h.xStar A.toRestrictedBroydenRun := by
  have hηBound :
      ∃ η ∈ Set.Ioo (0 : ℝ) 1,
        Chapter03.InexactNewtonCollisionFree.HasInexactNewtonForcingBound
          (RestrictedBroydenMethod.forcing A) η :=
    restricted_broyden_forcing_bound_of_wolfePowell f D h A hB0_posDef
  have hLinear : HasEventuallyLinearConvergenceTo A h.xStar :=
    restricted_broyden_eventually_linear_of_forcing_bounded
      f D h A hA0_local hηBound
  have hResidualLittleO :
      ((fun k ↦ ‖RestrictedBroydenMethod.residual A k‖) =o[atTop]
        fun k ↦ ‖gradient f (A k)‖) :=
    restricted_broyden_residual_isLittleO f D h A hLinear
  have hSuper : HasSuperlinearConvergenceTo A h.xStar :=
    restricted_broyden_superlinear_of_eventually_linear_and_residual
      f D h A hηBound hLinear hResidualLittleO
  -- The remaining repackaging is purely notational: the restricted-Broyden run owner stores the
  -- same iterate sequence and little-`o` rate as the Chapter 3 superlinear owner.
  exact RestrictedBroydenRun.convergesQSuperlinearlyTo_of_hasSuperlinearConvergenceTo hSuper

end Chapter05Theorem5423
