/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_8_3
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped MatrixOrder MatrixPosDef

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Coord" => Fin n → ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ

/- Lemma 1.8.5 lies in finite-dimensional weighted Euclidean geometry.

Primary domain:
- equivalence of the identity-matrix norm and the weighted norm induced by a positive-definite
  matrix on `ℝⁿ`

Source/core/bridge triage:
- source-facing: the two-sided comparison between the identity owner norm and the weighted norm
  owner on the coordinate model `Coord`
- core/canonical: the two norm owners on `Coord`,
  `toNormedAddCommGroup (1 : Mat) PosDef.one` and `toNormedAddCommGroup A hA`
- bridge/view: `coordEquiv` together with
  `Matrix.PosDef.norm_coordEquiv_eq_sqrt_inner_toEuclideanLin`

Sampled owner-style declarations:
- `toNormedAddCommGroup`
- `Matrix.PosDef.norm_coordEquiv_eq_sqrt_inner_toEuclideanLin`
- `EuclideanSpace.equiv`
- `LinearMap.continuous_of_finiteDimensional`

Best owner abstraction:
- compare the weighted norm owner attached to `A` directly against the identity-matrix norm owner
  on `Coord`

Primitive data:
- `A : Mat`
- `hA : A.PosDef`

Derived API:
- the Euclidean bridge formula
  `‖coordEquiv x‖[⟨A, hA⟩] = Real.sqrt (inner ℝ (A.toEuclideanLin x) x)`
- the quadratic form `inner ℝ (A.toEuclideanLin x) x`

Accordingly, the main public statement stays at the source-facing owner layer on `Coord`, and the
Euclidean `Real.sqrt (inner ...)` formula is kept as a thin companion bridge rather than the main
entry.
-/

/-- Helper for Lemma 1.8.5: an invertible matrix acts by a bi-Lipschitz Euclidean linear map on
`ℝⁿ`. -/
private theorem isUnit_exists_euclidean_bounds (B : Mat) (hBunit : IsUnit B) :
    ∃ c₁ > 0, ∃ c₂ > 0,
      ∀ y : E, c₁ * ‖y‖ ≤ ‖B.toEuclideanLin y‖ ∧ ‖B.toEuclideanLin y‖ ≤ c₂ * ‖y‖ := by
  -- We bound the image from below by injectivity and from above by continuity.
  have hBinj : Function.Injective (B.toEuclideanLin : E → E) := by
    intro x y hxy
    have hcoords : B *ᵥ x.ofLp = B *ᵥ y.ofLp := by
      simpa only [Matrix.ofLp_toLpLin] using congrArg (fun z : E ↦ z.ofLp) hxy
    have hmulVec_inj : Function.Injective B.mulVec := (mulVec_injective_iff_isUnit).2 hBunit
    have hxofy : x.ofLp = y.ofLp := hmulVec_inj hcoords
    exact congrArg (WithLp.toLp 2) hxofy
  obtain ⟨K, hKpos, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz (B.toEuclideanLin : E →ₗ[ℝ] E)).mp hBinj
  let T : E →L[ℝ] E := (B.toEuclideanLin).toContinuousLinearMap
  obtain ⟨C, hCpos, hC⟩ := T.bound
  have hKpos' : 0 < (K : ℝ) := hKpos
  refine ⟨(K : ℝ)⁻¹, by positivity, C, hCpos, ?_⟩
  intro y
  constructor
  · -- Anti-Lipschitz control of `B` gives the lower comparison constant.
    have hle : ‖y‖ ≤ (K : ℝ) * ‖B.toEuclideanLin y‖ := by
      simpa [dist_eq_norm, map_zero] using hanti.le_mul_dist y 0
    exact (inv_mul_le_iff₀ hKpos').2 hle
  · -- Continuity supplies the upper comparison constant.
    simpa [T] using hC y

/-- Helper for Lemma 1.8.5: if `A = Bᵀ B`, then the `A`-weighted norm equals the Euclidean norm of
`Bx`. -/
private theorem sqrt_inner_eq_euclidean_image_norm
    (A B : Mat) (hAeq : A = Bᴴ * B) (x : E) :
    Real.sqrt (inner ℝ (A.toEuclideanLin x) x) = ‖B.toEuclideanLin x‖ := by
  -- Rewrite the quadratic form in coordinates and collapse it to the Euclidean square norm.
  have hquad : inner ℝ (A.toEuclideanLin x) x = ‖B.toEuclideanLin x‖ ^ 2 := by
    calc
      inner ℝ (A.toEuclideanLin x) x = dotProduct x.ofLp (A *ᵥ x.ofLp) := by
        simpa only [Matrix.ofLp_toLpLin] using
          (EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin x) x)
      _ = dotProduct x.ofLp ((Bᴴ * B) *ᵥ x.ofLp) := by rw [hAeq]
      _ = dotProduct (B *ᵥ x.ofLp) (B *ᵥ x.ofLp) := by
        rw [dotProduct_comm]
        rw [dotProduct_comm, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose]
        simp
      _ = ‖B.toEuclideanLin x‖ ^ 2 := by
        have hraw :=
          EuclideanSpace.inner_eq_star_dotProduct (B.toEuclideanLin x) (B.toEuclideanLin x)
        simp only [Matrix.ofLp_toLpLin] at hraw
        have hnorm : inner ℝ (B.toEuclideanLin x) (B.toEuclideanLin x) =
            ‖B.toEuclideanLin x‖ ^ 2 := by
          simp
        exact hraw.symm.trans hnorm
  rw [hquad, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Lemma 1.8.5: the weighted norm owner induced by a positive-definite real matrix is equivalent
to the identity-matrix norm owner on `ℝⁿ`. -/
-- Proof sketch: factor `A` as `Bᵀ B`, transport the coordinate owner norms to Euclidean space by
-- `coordEquiv.symm`, and apply the bi-Lipschitz bounds for the Euclidean operator `B`.
theorem posDef_exists_weightedNorm_bounds (A : {A : Mat // A.PosDef}) :
    ∃ c₁ > 0, ∃ c₂ > 0,
      ∀ x : Coord,
        c₁ * ‖x‖[⟨(1 : Mat), PosDef.one⟩] ≤ ‖x‖[A] ∧
        ‖x‖[A] ≤ c₂ * ‖x‖[⟨(1 : Mat), PosDef.one⟩] := by
  have hAstrict : IsStrictlyPositive A.1 := A.2.isStrictlyPositive
  obtain ⟨B, hBunit, hBself, hAeq_mul⟩ :=
    (CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self).mp
      hAstrict
  have hAeq : A.1 = Bᴴ * B := by
    have hBtranspose : Bᵀ = B := by
      simpa using hBself
    calc
      A.1 = B * B := hAeq_mul
      _ = Bᵀ * B := by
        congr 1
        simpa using hBtranspose.symm
  obtain ⟨c₁, hc₁, c₂, hc₂, hbounds⟩ := isUnit_exists_euclidean_bounds B hBunit
  refine ⟨c₁, hc₁, c₂, hc₂, ?_⟩
  intro x
  let y : E := (EuclideanSpace.equiv (Fin n) ℝ).symm x
  have hy_coord : coordEquiv y = x := by
    simpa [y] using (EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply x
  have hy_id : ‖x‖[⟨(1 : Mat), PosDef.one⟩] = ‖y‖ := by
    calc
      ‖x‖[⟨(1 : Mat), PosDef.one⟩] = ‖coordEquiv y‖[⟨(1 : Mat), PosDef.one⟩] := by
        rw [hy_coord]
      _ = ‖y‖ := Matrix.PosDef.one_norm_coordEquiv_eq y
  have hy_weight : ‖x‖[A] = ‖B.toEuclideanLin y‖ := by
    calc
      ‖x‖[A] = ‖coordEquiv y‖[A] := by
        rw [hy_coord]
      _ = Real.sqrt (inner ℝ (A.1.toEuclideanLin y) y) := by
        exact Matrix.PosDef.norm_coordEquiv_eq_sqrt_inner_toEuclideanLin A y
      _ = ‖B.toEuclideanLin y‖ := by
        exact sqrt_inner_eq_euclidean_image_norm A.1 B hAeq y
  obtain ⟨hlower, hupper⟩ := hbounds y
  constructor
  · calc
      c₁ * ‖x‖[⟨(1 : Mat), PosDef.one⟩] = c₁ * ‖y‖ := by
        rw [hy_id]
      _ ≤ ‖B.toEuclideanLin y‖ := hlower
      _ = ‖x‖[A] := hy_weight.symm
  · calc
      ‖x‖[A] = ‖B.toEuclideanLin y‖ := hy_weight
      _ ≤ c₂ * ‖y‖ := hupper
      _ = c₂ * ‖x‖[⟨(1 : Mat), PosDef.one⟩] := by
        rw [hy_id]

/-- Lemma 1.8.5 companion: transporting the weighted norm owner through `EuclideanSpace.equiv`
rewrites the owner comparison as the textbook bound
`c₁ ‖x‖ ≤ √⟪Ax, x⟫ ≤ c₂ ‖x‖`. -/
-- Proof sketch: apply the owner theorem to `coordEquiv x` and rewrite the weighted owner norm by
-- `Matrix.PosDef.norm_coordEquiv_eq_sqrt_inner_toEuclideanLin`.
theorem posDef_exists_sqrt_inner_bounds (A : Mat) (hA : A.PosDef) :
    ∃ c₁ > 0, ∃ c₂ > 0,
      ∀ x : E,
        c₁ * ‖x‖ ≤ Real.sqrt (inner ℝ (A.toEuclideanLin x) x) ∧
          Real.sqrt (inner ℝ (A.toEuclideanLin x) x) ≤ c₂ * ‖x‖ := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hcoord⟩ := posDef_exists_weightedNorm_bounds ⟨A, hA⟩
  refine ⟨c₁, hc₁, c₂, hc₂, ?_⟩
  intro x
  simpa [Matrix.PosDef.one_norm_coordEquiv_eq x,
    Matrix.PosDef.norm_coordEquiv_eq_sqrt_inner_toEuclideanLin ⟨A, hA⟩ x] using
    hcoord (coordEquiv x)

/-- Lemma 1.8.5 companion: equivalently, the weighted quadratic form `⟪Ax, x⟫` of a
positive-definite real matrix is bounded above and below by positive multiples of the Euclidean
square norm. -/
-- Proof sketch: apply `posDef_exists_sqrt_inner_bounds` and square the two inequalities.
theorem posDef_exists_quadraticForm_bounds (A : Mat) (hA : A.PosDef) :
    ∃ m > 0, ∃ M > 0,
      ∀ x : E,
        m * ‖x‖ ^ 2 ≤ inner ℝ (A.toEuclideanLin x) x ∧
          inner ℝ (A.toEuclideanLin x) x ≤ M * ‖x‖ ^ 2 := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hbounds⟩ := posDef_exists_sqrt_inner_bounds A hA
  refine ⟨c₁ ^ 2, by positivity, c₂ ^ 2, by positivity, ?_⟩
  intro x
  obtain ⟨hlower, hupper⟩ := hbounds x
  -- The quadratic form is nonnegative because `A` is positive semidefinite.
  have hq_nonneg : 0 ≤ inner ℝ (A.toEuclideanLin x) x := by
    have hcoords : 0 ≤ dotProduct x.ofLp (A *ᵥ x.ofLp) := by
      simpa [dotProduct_comm] using hA.posSemidef.dotProduct_mulVec_nonneg x.ofLp
    have hraw := EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin x) x
    simp only [Matrix.ofLp_toLpLin] at hraw
    simpa [hraw, dotProduct_comm] using hcoords
  have hleft_nonneg : 0 ≤ c₁ * ‖x‖ := by
    positivity
  have hright_nonneg : 0 ≤ c₂ * ‖x‖ := by
    positivity
  -- Squaring the lower norm bound produces the lower quadratic-form bound.
  have hlower_sq : (c₁ * ‖x‖) ^ 2 ≤ inner ℝ (A.toEuclideanLin x) x := by
    have habs : |c₁ * ‖x‖| ≤ |Real.sqrt (inner ℝ (A.toEuclideanLin x) x)| := by
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg (Real.sqrt_nonneg _)] using hlower
    have hsquare : (c₁ * ‖x‖) ^ 2 ≤ (Real.sqrt (inner ℝ (A.toEuclideanLin x) x)) ^ 2 :=
      (sq_le_sq).2 habs
    simpa [Real.sq_sqrt hq_nonneg] using hsquare
  -- Squaring the upper norm bound produces the upper quadratic-form bound.
  have hupper_sq : inner ℝ (A.toEuclideanLin x) x ≤ (c₂ * ‖x‖) ^ 2 := by
    have habs : |Real.sqrt (inner ℝ (A.toEuclideanLin x) x)| ≤ |c₂ * ‖x‖| := by
      simpa [abs_of_nonneg hright_nonneg, abs_of_nonneg (Real.sqrt_nonneg _)] using hupper
    have hsquare : (Real.sqrt (inner ℝ (A.toEuclideanLin x) x)) ^ 2 ≤ (c₂ * ‖x‖) ^ 2 :=
      (sq_le_sq).2 habs
    simpa [Real.sq_sqrt hq_nonneg] using hsquare
  constructor
  · simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hlower_sq
  · simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hupper_sq
