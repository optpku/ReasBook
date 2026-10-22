/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module LinearMap
open scoped BInducedNorm
open scoped InnerProduct
open scoped EllipsoidNotation
open scoped SeminormDualNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Lemma 3.20 lies in the chapter's centered-ellipsoid / support-value domain.

Sampled owner-style declarations:
- `affineEllipsoid` and `mem_affineEllipsoid_iff` in `Lemma_3_2_7`, the chapter owner/view for
  the textbook ellipsoid `E(H, x̄)`;
- `LinearMap.BilinForm.primalSeminorm` and `LinearMap.BilinForm.dualNorm_apply_strongDual` in
  `Chap04/Definition_4_2_6`, the project owners for the quadratic norm induced by a positive
  definite bilinear form and its dual support value;
- `Seminorm.inner_le_dualNorm_mul` in `Chap02/Definition_2_5`, the canonical duality inequality
  controlling `⟪c, x⟫` by the dual norm times the primal norm;
- downstream recall `Lemma_3_1_20`, which already treats this file's theorem as the owner result.

Best owner abstraction:
- source-facing: the maximum-attainment statement itself, expressed as `IsGreatest`;
- core/canonical: the chapter ellipsoid owner `affineEllipsoid` together with the bilinear-form
  induced seminorm owner attached to `A`;
- bridge/view: the dual-norm formula for the support value and the generic supremum consequence
  `hmax.csSup_eq`.

Primitive data:
- `A : Mat` with `hA : A.PosDef`;
- `c : E`.

Derived API:
- the centered ellipsoid `affineEllipsoid A⁻¹ 0`;
- the induced primal seminorm `x ↦ √⟪A x, x⟫`;
- the image of that ellipsoid under the linear functional `x ↦ ⟪c, x⟫`;
- the support value `√⟪c, A⁻¹ c⟫`.

Source/core/bridge triage:
- source-facing: the textbook claim that the linear functional attains its maximum on the
  centered ellipsoid, together with the maximizing value;
- core/canonical: `affineEllipsoid`, `LinearMap.BilinForm.primalSeminorm`, and
  `Seminorm.dualNorm`;
- bridge/view: the bilinear-form dual-norm formula and the companion supremum identity obtained
  generically from `IsGreatest`.

No earlier chapter/project theorem with this exact mathematical content was found, so this file
keeps the maximum-attainment theorem as the owner declaration rather than collapsing it to a
support-function equality and thereby losing the source-facing attainment data.
-/

private def matrixBilin (A : Mat) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp A.toEuclideanLin.toContinuousLinearMap).toBilinForm

private theorem matrixBilin_isSymm_of_posDef
    (A : Mat) (hA : A.PosDef) :
    (matrixBilin A).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  change inner ℝ (A.toEuclideanLin x) y = inner ℝ (A.toEuclideanLin y) x
  have hPosLin : A.toEuclideanLin.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hA.posSemidef
  simpa [real_inner_comm] using hPosLin.isSymmetric x y

private theorem matrixBilin_posDef_of_posDef
    (A : Mat) (hA : A.PosDef) :
    (matrixBilin A).toQuadraticMap.PosDef := by
  rw [QuadraticMap.posDef_iff_nonneg]
  refine ⟨?_, ?_⟩
  · intro x
    change 0 ≤ inner ℝ (A.toEuclideanLin x) x
    have hPosLin : A.toEuclideanLin.IsPositive :=
      Matrix.isPositive_toEuclideanLin_iff.mpr hA.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
  · intro x hx
    by_contra hx0
    have hx' : x.ofLp ≠ 0 := by
      intro h0
      apply hx0
      ext i
      exact congrArg (fun y : Fin n → ℝ ↦ y i) h0
    have hdot : 0 < dotProduct x.ofLp (A.mulVec x.ofLp) := by
      simpa using hA.dotProduct_mulVec_pos hx'
    have hdot_eq : inner ℝ (A.toEuclideanLin x) x = dotProduct x.ofLp (A.mulVec x.ofLp) := by
      have hinner := EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin x) x
      simp only [Matrix.ofLp_toLpLin] at hinner
      simpa [dotProduct_comm] using hinner
    have hx_inner : inner ℝ (A.toEuclideanLin x) x = 0 := by
      simpa [matrixBilin] using hx
    rw [hdot_eq] at hx_inner
    exact hdot.ne' hx_inner

private theorem inner_toEuclideanLin_pos_of_posDef
    (A : Mat) (hA : A.PosDef) {c : E} (hc : c ≠ 0) :
    0 < inner ℝ c (A.toEuclideanLin c) := by
  have hc' : c.ofLp ≠ 0 := by
    intro h0
    apply hc
    ext i
    exact congrArg (fun y : Fin n → ℝ ↦ y i) h0
  have hdot : 0 < dotProduct c.ofLp (A.mulVec c.ofLp) := by
    simpa using hA.dotProduct_mulVec_pos hc'
  have hdot_eq : inner ℝ c (A.toEuclideanLin c) = dotProduct c.ofLp (A.mulVec c.ofLp) := by
    have hinner := EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin c) c
    simp only [Matrix.ofLp_toLpLin] at hinner
    calc
      inner ℝ c (A.toEuclideanLin c) = inner ℝ (A.toEuclideanLin c) c := by
        rw [real_inner_comm]
      _ = dotProduct c.ofLp (A.mulVec c.ofLp) := by
        simpa using hinner
  rw [hdot_eq]
  exact hdot

/-- Lemma 3.20: for a symmetric positive-definite matrix `A`, the linear functional
`x ↦ ⟪c, x⟫` attains its maximum on the centered ellipsoid `affineEllipsoid A⁻¹ 0`, equivalently
on `{x | ⟪A x, x⟫ ≤ 1}`, and that maximum is `√⟪c, A⁻¹ c⟫`. -/
-- Proof sketch: use compactness of the closed ellipsoid and continuity of `x ↦ ⟪c, x⟫` to obtain
-- a maximizer. At an optimal point, the quadratic constraint is active; then apply the
-- first-order optimality condition for the Lagrangian to identify the maximizer with a scalar
-- multiple of `A⁻¹ c`, and solve for the multiplier using the boundary equation.
theorem isGreatest_inner_image_spdEllipsoid
    (A : Mat) (hA : A.PosDef) (c : E) :
    IsGreatest ((fun x : E ↦ inner ℝ c x) '' E(A⁻¹, (0 : E)))
      (Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c))) := by
  letI : Invertible A := hA.isUnit.invertible
  by_cases hc : c = 0
  · refine ⟨?_, ?_⟩
    · refine ⟨0, center_mem_affineEllipsoid A⁻¹ (0 : E), ?_⟩
      simp [hc]
    · rintro y ⟨x, hx, rfl⟩
      simp [hc]
  · let B : LinearMap.BilinForm ℝ E := matrixBilin A
    let hSymm : B.IsSymm := matrixBilin_isSymm_of_posDef A hA
    let hPos : B.toQuadraticMap.PosDef := matrixBilin_posDef_of_posDef A hA
    let p : Seminorm ℝ E := B.primalSeminorm hPos
    letI : Seminorm.IsNorm p := B.primalSeminorm_isNorm hPos
    have hdual :
        Seminorm.dualNorm p c = Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c)) := by
      have hpreimage :
          ((B.toDual (B.nondegenerate_of_posDef hPos)).symm
            (InnerProductSpace.toDual ℝ E c).toLinearMap : E) =
            (A⁻¹).toEuclideanLin c := by
        apply (B.toDual (B.nondegenerate_of_posDef hPos)).injective
        ext y
        change
          B
              (((B.toDual (B.nondegenerate_of_posDef hPos)).symm
                (InnerProductSpace.toDual ℝ E c).toLinearMap)) y =
            B ((A⁻¹).toEuclideanLin c) y
        rw [LinearMap.BilinForm.apply_toDual_symm_apply]
        change inner ℝ c y = inner ℝ (A.toEuclideanLin ((A⁻¹).toEuclideanLin c)) y
        rw [show A.toEuclideanLin ((A⁻¹).toEuclideanLin c) = c by
          ext i
          simp only [Matrix.ofLp_toLpLin]
          simp]
      calc
        Seminorm.dualNorm p c =
            B.dualNorm hPos (InnerProductSpace.toDual ℝ E c).toLinearMap := by
              rw [Seminorm.dualNorm_apply, B.dualNorm_eq_sSup_primalUnitBall_strongDual]
              simp [p, InnerProductSpace.toDual_apply_apply]
        _ = Real.sqrt
              ((InnerProductSpace.toDual ℝ E c)
                ((B.toDual (B.nondegenerate_of_posDef hPos)).symm
                  (InnerProductSpace.toDual ℝ E c).toLinearMap)) := by
              simpa using
                LinearMap.BilinForm.dualNorm_apply_strongDual B hSymm hPos
                  (InnerProductSpace.toDual ℝ E c)
        _ = Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c)) := by
              rw [hpreimage]
              rfl
    let q : ℝ := inner ℝ c ((A⁻¹).toEuclideanLin c)
    have hq : 0 < q := inner_toEuclideanLin_pos_of_posDef A⁻¹ hA.inv hc
    let x0 : E := (Real.sqrt q)⁻¹ • (A⁻¹).toEuclideanLin c
    refine ⟨?_, ?_⟩
    · refine ⟨x0, ?_, ?_⟩
      · rw [mem_affineEllipsoid_iff]
        have hsqrt : Real.sqrt q ≠ 0 := ne_of_gt <| Real.sqrt_pos.2 hq
        have hAinv : A.toEuclideanLin ((A⁻¹).toEuclideanLin c) = c := by
          ext i
          simp only [Matrix.ofLp_toLpLin]
          simp
        have hquad : inner ℝ (A.toEuclideanLin x0) x0 = 1 := by
          calc
            inner ℝ (A.toEuclideanLin x0) x0
                = inner ℝ ((Real.sqrt q)⁻¹ • c)
                    ((Real.sqrt q)⁻¹ • (A⁻¹).toEuclideanLin c) := by
                      simp [x0, hAinv]
            _ = ((Real.sqrt q)⁻¹) ^ (2 : ℕ) * q := by
                  rw [inner_smul_left, inner_smul_right]
                  simp [q, pow_two, mul_comm, mul_left_comm]
            _ = 1 := by
                  field_simp [hsqrt]
                  nlinarith [Real.sq_sqrt (le_of_lt hq)]
        simpa [sub_zero, Matrix.inv_inv_of_invertible] using hquad.le
      · calc
          inner ℝ c x0 = (Real.sqrt q)⁻¹ * q := by
            simpa [x0, q, mul_comm] using
              show
                inner ℝ c ((Real.sqrt q)⁻¹ • (A⁻¹).toEuclideanLin c) =
                  (Real.sqrt q)⁻¹ * inner ℝ c ((A⁻¹).toEuclideanLin c) by
                rw [inner_smul_right]
          _ = Real.sqrt q := by
            have hsqrt : Real.sqrt q ≠ 0 := ne_of_gt <| Real.sqrt_pos.2 hq
            field_simp [hsqrt]
            nlinarith [Real.sq_sqrt (le_of_lt hq)]
          _ = Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c)) := by
            simp [q]
    · rintro y ⟨x, hx, rfl⟩
      have hp_x : p x ≤ 1 := by
        rw [mem_affineEllipsoid_iff] at hx
        simpa [p, B, matrixBilin, LinearMap.BilinForm.primalSeminorm_apply] using hx
      calc
        inner ℝ c x ≤ Seminorm.dualNorm p c * p x :=
          Seminorm.inner_le_dualNorm_mul p x c
        _ ≤ Seminorm.dualNorm p c * 1 := by
              have hdual_nonneg : 0 ≤ Seminorm.dualNorm p c := by
                rw [hdual]
                exact Real.sqrt_nonneg _
              exact mul_le_mul_of_nonneg_left hp_x hdual_nonneg
        _ = Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c)) := by
              rw [hdual]
              simp
