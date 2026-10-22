/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.HessianBFGSMethod
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_20

noncomputable section

section Chapter05Theorem5421

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * primary domain: local superlinear convergence for Hessian-side full-step BFGS runs;
-- * sampled owners in the minimal semantic closure:
--   `GeneralQuasiNewtonMethod.IsFullStepHessianBFGSOn` from
--   `Chapter05.HessianBFGSMethod`,
--   `DFPHessianRun` and `DFPSmallStartSuperlinearConvergence` from
--   `Chapter05.Theorem_5_4_20`,
--   and the canonical Chapter 3 rate owner `HasSuperlinearConvergenceTo`;
-- * source/core/bridge triage:
--   source-facing layer in this file: the theorem statement itself;
--   core/canonical owner: `GeneralQuasiNewtonMethod`;
--   bridge/view reused here: the already existing small-start DFP owner
--   `DFPSmallStartSuperlinearConvergence` together with the BFGS bridge
--   `GeneralQuasiNewtonMethod.IsFullStepHessianBFGSOn`;
-- * primitive data remain an existing Hessian-side run object, viewed either as
--   `DFPHessianRun D f` or as `GeneralQuasiNewtonMethod f` with the full-step Hessian-BFGS
--   bridge;
-- * derived API: the superlinear rate is the canonical Chapter 3 owner
--   `HasSuperlinearConvergenceTo`, so no additional theorem-local owner is introduced here.

namespace DFPHessianRun

@[simp] theorem toGeneralQuasiNewtonMethod_hessian
    {D : Set Point} {f : Point → ℝ} (A : DFPHessianRun D f) (k : ℕ) :
    A.toGeneralQuasiNewtonMethod.hessian k = A.B k := by
  let _ := (A.matrices_posDef k).isUnit.invertible
  simp [GeneralQuasiNewtonMethod.hessian]

@[simp] theorem toGeneralQuasiNewtonMethod_hessian0
    {D : Set Point} {f : Point → ℝ} (A : DFPHessianRun D f) :
    A.toGeneralQuasiNewtonMethod.hessian 0 = A.B0 := by
  simp

/-- A Hessian-side DFP run is the same mathematical data as a full-step Hessian-side BFGS run
on the canonical quasi-Newton owner, because the update in `Lemma_5_4_19` is already the
canonical `bfgsHessianUpdate`. -/
theorem isFullStepHessianBFGSOn_toGeneralQuasiNewtonMethod
    {D : Set Point} {f : Point → ℝ} (A : DFPHessianRun D f) :
    A.toGeneralQuasiNewtonMethod.IsFullStepHessianBFGSOn D where
  iterates_mem := A.iterates_mem
  hessian_posDef k := by
    simpa using A.toGeneralQuasiNewtonMethod_hessian k ▸ A.matrices_posDef k
  full_step k := by
    simpa using A.step_eq k
  secant_curvature_pos := A.secant_curvature_pos
  bfgs_update k := by
    simpa using A.dfp_update k

end DFPHessianRun

namespace GeneralQuasiNewtonMethod

/-- A full-step Hessian-side BFGS run on the canonical quasi-Newton owner can be viewed as the
Hessian-side run object already used in the Chapter 5 DFP local-convergence files. -/
def toDFPHessianRun
    {D : Set Point} {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f)
    (hA : A.IsFullStepHessianBFGSOn D) :
    DFPHessianRun D f :=
  { B0 := A.hessian 0
    x := A
    B := A.hessian
    g := A.g
    B_zero := rfl
    iterates_mem := hA.iterates_mem
    hasGradientAt := A.hasGradientAt
    matrices_posDef := hA.hessian_posDef
    step_eq := fun k ↦ by
      let _ := (hA.hessian_posDef k).isUnit.invertible
      have hMatrixPosDef : (A.matrix k).PosDef := by
        simpa [GeneralQuasiNewtonMethod.hessian] using (hA.hessian_posDef k).inv
      let _ := hMatrixPosDef.isUnit.invertible
      have hmatrix :
          Matrix.toEuclideanLin ((A.hessian k)⁻¹) = (A.matrix k).toEuclideanLin := by
        simp [GeneralQuasiNewtonMethod.hessian]
      rw [hmatrix]
      exact hA.full_step k
    secant_curvature_pos := hA.secant_curvature_pos
    dfp_update := fun k ↦ by
      let _ := (hA.hessian_posDef k).isUnit.invertible
      let _ := (hA.hessian_posDef (k + 1)).isUnit.invertible
      simpa [GeneralQuasiNewtonMethod.hessian] using hA.bfgs_update k }

@[simp] theorem toDFPHessianRun_coe_apply
    {D : Set Point} {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f)
    (hA : A.IsFullStepHessianBFGSOn D) (k : ℕ) :
    A.toDFPHessianRun hA k = A k :=
  rfl

@[simp] theorem toDFPHessianRun_x0
    {D : Set Point} {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f)
    (hA : A.IsFullStepHessianBFGSOn D) :
    (A.toDFPHessianRun hA).x0 = A.x0 :=
  rfl

@[simp] theorem toDFPHessianRun_B0
    {D : Set Point} {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f)
    (hA : A.IsFullStepHessianBFGSOn D) :
    (A.toDFPHessianRun hA).B0 = A.hessian 0 :=
  rfl

end GeneralQuasiNewtonMethod

/-- Chapter05 Theorem 5.4.21: under the assumptions of Chapter05 Theorem 5.4.15, there exist
`ε > 0` and `δ > 0` such that every Hessian-side BFGS run generated by `(5.4.79)` and the
BFGS update `(5.1.45)` from initial data `x0`, `B0` satisfying
`‖x0 - h.xStar‖ < ε` and
`dfpMatrixNorm (dfpReferenceHessian h) (B0 - dfpReferenceHessian h) < δ` converges to
`h.xStar` superlinearly. This file does not keep a second theorem-local small-start owner:
it reuses `DFPSmallStartSuperlinearConvergence` from the neighboring DFP theorem and translates
that source-facing package to the canonical Chapter 5 owner `GeneralQuasiNewtonMethod` with the
bridge `GeneralQuasiNewtonMethod.IsFullStepHessianBFGSOn`. The rate conclusion is expressed by
the canonical Chapter 3 owner `HasSuperlinearConvergenceTo`. -/
theorem bfgsMethod_tendsto_and_superlinear_of_small_initial_errors
    (D : Set Point) (f : Point → ℝ)
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f)
    (h_oneThird : dfpOneThirdConditionInNeighborhood h) :
    ∃ ε > 0, ∃ δ > 0, ∀ x0 B0,
      ‖x0 - h.xStar‖ < ε →
      dfpMatrixNorm (dfpReferenceHessian h) (B0 - dfpReferenceHessian h) < δ →
      (∃ A : GeneralQuasiNewtonMethod f,
        A.x0 = x0 ∧
        A.hessian 0 = B0 ∧
        A.IsFullStepHessianBFGSOn D) ∧
      ∀ A : GeneralQuasiNewtonMethod f,
        A.x0 = x0 →
        A.hessian 0 = B0 →
        A.IsFullStepHessianBFGSOn D →
        HasSuperlinearConvergenceTo A h.xStar := by
  rcases dfpMethod_tendsto_and_superlinear_of_small_initial_errors D f h h_oneThird with
    ⟨ε, hε, δ, hδ, hsmall⟩
  refine ⟨ε, hε, δ, hδ, ?_⟩
  intro x0 B0 hx0 hB0
  let hdfp := hsmall x0 B0 hx0 hB0
  refine ⟨?_, ?_⟩
  · rcases hdfp.exists_run with ⟨A, hxA, hBA, _⟩
    refine ⟨A.toGeneralQuasiNewtonMethod, ?_, ?_, A.isFullStepHessianBFGSOn_toGeneralQuasiNewtonMethod⟩
    · simpa using hxA
    · simpa [hBA] using A.toGeneralQuasiNewtonMethod_hessian0
  · intro A hxA hBA hA
    have hsuper :
        HasSuperlinearConvergenceTo (A.toDFPHessianRun hA) h.xStar :=
      hdfp.superlinear
        (A.toDFPHessianRun hA)
        (by simpa using hxA)
        (by simpa using hBA)
    refine ⟨?_, ?_⟩
    · simpa [GeneralQuasiNewtonMethod.toDFPHessianRun] using hsuper.tendsto
    · simpa [GeneralQuasiNewtonMethod.toDFPHessianRun] using hsuper.isLittleO

end Chapter05Theorem5421
