/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace StrictPositiveSemidefiniteCone
open scoped Matrix.Norms.Frobenius MatrixOrder RealSymmetricMatrixSpace

/- Lemma 5.4.4.1 lies in the strict positive-definite symmetric-matrix / log-determinant-barrier
domain.

Sampled owner-style declarations:
* `logDetBarrier` and `logDetBarrierAmbient` from `Definition_5_4_4_5`, the source-facing barrier
  and its ambient formula bridge;
* `logDetBarrier_eq_neg_sum_log_eigenvalues` from `Theorem_5_4_4_2`, which already states Chapter 5
  barrier facts on the intrinsic domain `𝕊^n₊₊`;
* `RealSymmetricMatrixSpace.frobeniusInner` from `Definition_5_4_4_2`, the symmetric-space owner
  for the Frobenius pairing on `𝕊^n`, together with the intrinsic bridges `sandwich` and `cube`;
* `StrictPositiveSemidefiniteCone.inv` and `StrictPositiveSemidefiniteCone.sqrtInv` from
  `Definition_5_4_4_5`, the strict-cone bridges returning `X⁻¹` and `X^{-1/2}` to `𝕊^n`;
* `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone` from
  `Theorem_5_4_4_3`, which differentiates the ambient extension on the symmetric ambient space.

Source/core/bridge triage:
* source-facing: the barrier `logDetBarrier n : 𝕊^n₊₊ → ℝ` together with the Chapter 5
  directional-derivative owners `lineDeriv`, `secondDirectionalDerivative`, and
  `thirdDirectionalDerivative` for its symmetric-space extension;
* core/canonical: differentiation of the symmetric-space extension `logDetBarrierAmbient n`;
* bridge/view: the ambient trace formula `Matrix.trace (Aᵀ * B)`.

Primitive data:
* `n : ℕ`.

Derived API:
* the Chapter 5 Frobenius owner `RealSymmetricMatrixSpace.frobeniusInner`;
* convexity and `C³` regularity from the upstream barrier owner
  `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone`;
* the directional-derivative formulas stated with the Chapter 5 owners
  `lineDeriv`, `secondDirectionalDerivative`, and `thirdDirectionalDerivative`.

This refinement removes the duplicate root-level Frobenius owner and keeps the public derivative
surface on the Chapter 5 directional owners rather than on raw `fderiv` / `iteratedFDeriv`.
The public statements are source-facing in the point `X : 𝕊^n₊₊` and direction `Δ : 𝕊^n`, using
the chapter owner `⟪·, ·⟫_F` on symmetric matrices and ambient trace formulas only as local bridge
syntax where the derivative formulas naturally live in the matrix algebra.
-/

section

variable (n : ℕ)

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n
local notation "logDetBarrierAmbientSymm" => logDetBarrierAmbient n

/-- Helper for Lemma 5.4.4.1: the ambient matrix trace viewed as a continuous linear map. -/
private def traceContinuousLinearMap : Mat →L[ℝ] ℝ :=
  ⟨Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ),
    (Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)).continuous_of_finiteDimensional⟩

@[simp] private theorem traceContinuousLinearMap_apply (M : Mat) :
    traceContinuousLinearMap (n := n) M = Matrix.trace M :=
  rfl

/-- Helper for Lemma 5.4.4.1: along an affine matrix path `B + s • H` based at an invertible
matrix `B`, the derivative of `s ↦ -log det (B + s • H)` at `0` is `-trace (B⁻¹ H)`. -/
private theorem hasDerivAt_negLogDet_affine
    (B H : Mat) (hB_det_ne : B.det ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ -Real.log ((B + s • H).det))
      (-Matrix.trace (B⁻¹ * H)) 0 := by
  let M : Mat := B⁻¹ * H
  letI := ((Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB_det_ne)).invertible
  have hmul : B * M = H := by
    simp [M]
  have hfactor : ∀ s : ℝ, (B + s • H).det = B.det * (1 + s • M).det := by
    intro s
    calc
      (B + s • H).det = (B * (1 + s • M)).det := by
        congr 1
        simp [Matrix.mul_add, hmul]
      _ = B.det * (1 + s • M).det := Matrix.det_mul _ _
  have hdet : HasDerivAt (fun s : ℝ ↦ (1 + s • M).det) (Matrix.trace M) 0 := by
    convert (Polynomial.hasDerivAt
      (p := Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)) (x := 0)) using 1
    · ext s
      simp [eval_det, ← smul_eq_mul_diagonal]
    · symm
      exact Matrix.derivative_det_one_add_X_smul M
  have hAffineDet : HasDerivAt (fun s : ℝ ↦ (B + s • H).det) (B.det * Matrix.trace M) 0 := by
    have hconst : HasDerivAt (fun s : ℝ ↦ B.det) 0 0 := hasDerivAt_const _ _
    simpa [hfactor] using hconst.mul hdet
  have hlog : HasDerivAt (fun s : ℝ ↦ Real.log ((B + s • H).det)) (Matrix.trace M) 0 := by
    have hdet0 : (fun s : ℝ ↦ (B + s • H).det) 0 ≠ 0 := by
      simpa using hB_det_ne
    simpa [hfactor, hB_det_ne] using hAffineDet.log hdet0
  simpa [M] using hlog.neg

/-- Helper for Lemma 5.4.4.1: the affine-path derivative formula for `-log det` centered at a
parameter `t` along the fixed direction `H`. -/
private theorem hasDerivAt_negLogDet_affine_at
    (A H : Mat) {t : ℝ} (ht : (A + t • H).det ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ -Real.log ((A + u • H).det))
      (-Matrix.trace (((A + t • H)⁻¹) * H)) t := by
  have hbase :
      HasDerivAt (fun s : ℝ ↦ -Real.log (((A + t • H) + s • H).det))
        (-Matrix.trace (((A + t • H)⁻¹) * H)) (t + -t) := by
    simpa using hasDerivAt_negLogDet_affine n (A + t • H) H ht
  convert hbase.comp t ((hasDerivAt_id t).add_const (-t)) using 1
  · ext u
    simp [Function.comp, add_assoc, add_smul]
  · simp

/-- Helper for Lemma 5.4.4.1: differentiating the inverse-trace slice
`s ↦ -trace ((B + s • H)⁻¹ H)` at `0` yields the quadratic trace
`trace ((B⁻¹ H)²)`. -/
private theorem hasDerivAt_invTrace_affine
    (B H : Mat) (hB_det_ne : B.det ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ -Matrix.trace ((Ring.inverse (B + s • H)) * H))
      (Matrix.trace ((B⁻¹ * H) * (B⁻¹ * H))) 0 := by
  letI : NormedAddCommGroup Mat := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
  letI : NormedRing Mat := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
  let hB_unit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB_det_ne)
  obtain ⟨u, rfl⟩ := hB_unit
  let Uinv : Mat := ↑u⁻¹
  have hpath : HasDerivAt (fun s : ℝ ↦ (u : Mat) + s • H) H 0 := by
    simpa [one_smul] using
      (((hasDerivAt_id (x := (0 : ℝ))).smul_const H).const_add (u : Mat))
  have hring :
      HasFDerivAt Ring.inverse
        (-ContinuousLinearMap.mulLeftRight ℝ Mat Uinv Uinv)
        ((u : Mat) + (0 : ℝ) • H) := by
    simpa [Uinv] using (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  have hinv :
      HasDerivAt (fun s : ℝ ↦ Ring.inverse ((u : Mat) + s • H))
        (-(Uinv * H * Uinv)) 0 := by
    simpa [ContinuousLinearMap.mulLeftRight_apply, Matrix.mul_assoc, Uinv] using
      hring.comp_hasDerivAt 0 hpath
  have hmul :
      HasDerivAt (fun s : ℝ ↦ Ring.inverse ((u : Mat) + s • H) * H)
        (-(Uinv * H * Uinv) * H) 0 := by
    simpa [Matrix.mul_assoc, Uinv] using hinv.mul_const H
  have htrace :
      HasDerivAt (fun s : ℝ ↦ Matrix.trace (Ring.inverse ((u : Mat) + s • H) * H))
        (Matrix.trace (-(Uinv * H * Uinv) * H)) 0 := by
    simpa [Function.comp, traceContinuousLinearMap_apply] using
      ((traceContinuousLinearMap (n := n)).hasFDerivAt).comp_hasDerivAt 0 hmul
  exact by simpa [Matrix.mul_assoc, Uinv] using htrace.neg

/-- Helper for Lemma 5.4.4.1: the inverse-trace derivative formula along `A + u • H`, recentered
at an arbitrary parameter `t`. -/
private theorem hasDerivAt_invTrace_affine_at
    (A H : Mat) {t : ℝ} (ht : (A + t • H).det ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ -Matrix.trace ((Ring.inverse (A + u • H)) * H))
      (Matrix.trace (((Ring.inverse (A + t • H)) * H) ^ (2 : ℕ))) t := by
  have hbase :
      HasDerivAt (fun s : ℝ ↦ -Matrix.trace ((Ring.inverse ((A + t • H) + s • H)) * H))
        (Matrix.trace ((((A + t • H)⁻¹ * H) ^ (2 : ℕ)))) (t + -t) := by
    simpa [pow_two, Matrix.mul_assoc] using hasDerivAt_invTrace_affine n (A + t • H) H ht
  convert hbase.comp t ((hasDerivAt_id t).add_const (-t)) using 1
  · ext u
    simp [Function.comp, add_assoc, add_smul]
  · simp [pow_two, Matrix.nonsing_inv_eq_ringInverse]

/-- Helper for Lemma 5.4.4.1: differentiating the quadratic inverse-trace slice
`s ↦ trace (((B + s • H)⁻¹ H)²)` at `0` yields `-2 trace ((B⁻¹ H)³)`. -/
private theorem hasDerivAt_invTraceSquare_affine
    (B H : Mat) (hB_det_ne : B.det ≠ 0) :
    HasDerivAt
      (fun s : ℝ ↦ Matrix.trace (((Ring.inverse (B + s • H)) * H) ^ (2 : ℕ)))
      (-2 * Matrix.trace ((B⁻¹ * H) ^ (3 : ℕ))) 0 := by
  letI : NormedAddCommGroup Mat := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
  letI : NormedRing Mat := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
  let hB_unit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB_det_ne)
  obtain ⟨u, rfl⟩ := hB_unit
  let Uinv : Mat := ↑u⁻¹
  have hpath : HasDerivAt (fun s : ℝ ↦ (u : Mat) + s • H) H 0 := by
    simpa [one_smul] using
      (((hasDerivAt_id (x := (0 : ℝ))).smul_const H).const_add (u : Mat))
  have hring :
      HasFDerivAt Ring.inverse
        (-ContinuousLinearMap.mulLeftRight ℝ Mat Uinv Uinv)
        ((u : Mat) + (0 : ℝ) • H) := by
    simpa [Uinv] using (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  have hinv :
      HasDerivAt (fun s : ℝ ↦ Ring.inverse ((u : Mat) + s • H))
        (-(Uinv * H * Uinv)) 0 := by
    simpa [ContinuousLinearMap.mulLeftRight_apply, Matrix.mul_assoc, Uinv] using
      hring.comp_hasDerivAt 0 hpath
  have hmul :
      HasDerivAt (fun s : ℝ ↦ Ring.inverse ((u : Mat) + s • H) * H)
        (-(Uinv * H * Uinv) * H) 0 := by
    simpa [Matrix.mul_assoc, Uinv] using hinv.mul_const H
  have hsquare :
      HasDerivAt
        (fun s : ℝ ↦ (Ring.inverse ((u : Mat) + s • H) * H) *
          (Ring.inverse ((u : Mat) + s • H) * H))
        ((-(Uinv * H * Uinv) * H) * (Uinv * H) + (Uinv * H) * (-(Uinv * H * Uinv) * H)) 0 := by
    simpa [Uinv] using hmul.mul hmul
  have htrace :
      HasDerivAt
        (fun s : ℝ ↦ Matrix.trace
          ((Ring.inverse ((u : Mat) + s • H) * H) * (Ring.inverse ((u : Mat) + s • H) * H)))
        (Matrix.trace
          (((-(Uinv * H * Uinv) * H) * (Uinv * H)) +
            (Uinv * H) * (-(Uinv * H * Uinv) * H)))
        0 := by
    simpa [Function.comp, traceContinuousLinearMap_apply] using
      ((traceContinuousLinearMap (n := n)).hasFDerivAt).comp_hasDerivAt 0 hsquare
  have hcyc :
      Matrix.trace (((Uinv * H) * (-(Uinv * H * Uinv) * H))) =
        Matrix.trace ((-(Uinv * H * Uinv) * H) * (Uinv * H)) := by
    rw [Matrix.trace_mul_comm]
  simpa [pow_two, pow_succ, Matrix.mul_assoc, hcyc, Uinv, two_mul] using htrace


/-- Helper for Lemma 5.4.4.1: the Frobenius self-pairing of a symmetric matrix is the trace of
its square. -/
private theorem frobeniusInner_self_eq_trace_sq
    (Q : SymmMat) :
    ⟪Q, Q⟫_F = Matrix.trace (((Q : Mat) ^ (2 : ℕ))) := by
  -- For symmetric matrices the transpose in the Frobenius formula drops out.
  rw [frobeniusInner_def]
  have hsymm : (((Q : Mat)ᵀ) : Mat) = (Q : Mat) := by
    simpa [Matrix.IsSymm] using (RealSymmetricMatrixSpace.isSymm Q).eq
  simp [pow_two, hsymm]

/-- Helper for Lemma 5.4.4.1: pairing the identity with a cube in Frobenius form is just the
ambient trace of that cube. -/
private theorem frobeniusInner_one_cube_eq_trace_cube
    (Q : SymmMat) :
    ⟪(1 : SymmMat), cube Q⟫_F = Matrix.trace (cube Q : Mat) := by
  -- Expand the Frobenius pairing and simplify the identity transpose/product.
  rw [frobeniusInner_def]
  simp

/-- Helper for Lemma 5.4.4.1: the intrinsic square of `X^{-1/2}` is `X^{-1}`. -/
private theorem sandwich_sqrtInv_one_eq_inv
    (X : 𝕊^n₊₊) :
    sandwich (sqrtInv X) (1 : SymmMat) = inv X := by
  have hinv_nonneg :
      0 ≤ ((((X : SymmMat) : Mat)⁻¹) : Mat) := by
    exact (Matrix.PosDef.inv (strictPositiveSemidefiniteCone_posDef X)).posSemidef.nonneg
  apply Subtype.ext
  -- Rewrite both symmetric-carrier terms into ambient matrices and use `√A * √A = A`.
  simp [RealSymmetricMatrixSpace.sandwich]
  simpa [pow_two] using
    (CFC.sqrt_mul_sqrt_self ((((X : SymmMat) : Mat)⁻¹)) (ha := hinv_nonneg))

/-- Helper for Lemma 5.4.4.1: the normalized Frobenius square agrees with the inverse sandwich
pairing after rewriting `sqrtInv X` squared as `inv X`. -/
private theorem frobeniusSelfSandwichSqrtInv_eq_invPairing
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    ⟪sandwich (sqrtInv X) Δ, sandwich (sqrtInv X) Δ⟫_F =
      ⟪sandwich (inv X) Δ, Δ⟫_F := by
  let S : Mat := (sqrtInv X : SymmMat)
  let Δm : Mat := Δ
  let XmInv : Mat := inv X
  have hΔsymm : Δmᵀ = Δm := by
    simpa [Δm, Matrix.IsSymm] using (RealSymmetricMatrixSpace.isSymm Δ).eq
  have hInvsymm : XmInvᵀ = XmInv := by
    simpa [XmInv, StrictPositiveSemidefiniteCone.coe_inv, Matrix.IsSymm] using
      (RealSymmetricMatrixSpace.isSymm (inv X)).eq
  have hInvAmbientSymm :
      ((((X : SymmMat) : Mat)⁻¹) : Mat)ᵀ = (((X : SymmMat) : Mat)⁻¹) := by
    simpa [StrictPositiveSemidefiniteCone.coe_inv] using hInvsymm
  have hSS : S * S = XmInv := by
    simpa
      [S, XmInv, StrictPositiveSemidefiniteCone.coe_inv, RealSymmetricMatrixSpace.sandwich] using
      congrArg (fun Z : SymmMat => ((Z : SymmMat) : Mat)) (sandwich_sqrtInv_one_eq_inv n X)
  calc
    ⟪sandwich (sqrtInv X) Δ, sandwich (sqrtInv X) Δ⟫_F
        = Matrix.trace (S * (Δm * (S * (S * (Δm * S))))) := by
            rw [frobeniusInner_self_eq_trace_sq]
            simp [S, Δm, pow_two, RealSymmetricMatrixSpace.sandwich, Matrix.mul_assoc]
    _ = Matrix.trace ((Δm * (S * (S * (Δm * S)))) * S) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (Δm * (XmInv * (Δm * XmInv))) := by
          rw [show Δm * (S * (S * (Δm * S))) * S = Δm * ((S * S) * (Δm * (S * S))) by
                simp [Matrix.mul_assoc]]
          simp [hSS]
    _ = Matrix.trace ((XmInv * (Δm * XmInv)) * Δm) := by
          rw [Matrix.trace_mul_comm]
    _ = ⟪sandwich (inv X) Δ, Δ⟫_F := by
          rw [frobeniusInner_def]
          simp [XmInv, Δm, RealSymmetricMatrixSpace.sandwich, hΔsymm, Matrix.mul_assoc,
            hInvAmbientSymm]

/-- Helper for Lemma 5.4.4.1: the trace of `(X⁻¹ Δ)³` matches the trace of the cube of the
normalized sandwich `X^{-1/2} Δ X^{-1/2}`. -/
private theorem trace_invMulCube_eq_trace_cube_sandwichSqrtInv
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    Matrix.trace ((((((X : SymmMat) : Mat)⁻¹) * (Δ : Mat)) ^ (3 : ℕ))) =
      Matrix.trace (cube (sandwich (sqrtInv X) Δ) : Mat) := by
  let S : Mat := (sqrtInv X : SymmMat)
  let H : Mat := (Δ : Mat)
  let U : Mat := (((X : SymmMat) : Mat)⁻¹)
  have hSS : S * S = U := by
    simpa [S, U, StrictPositiveSemidefiniteCone.coe_inv, RealSymmetricMatrixSpace.sandwich] using
      congrArg (fun Z : SymmMat => ((Z : SymmMat) : Mat)) (sandwich_sqrtInv_one_eq_inv n X)
  calc
    Matrix.trace ((((((X : SymmMat) : Mat)⁻¹) * (Δ : Mat)) ^ (3 : ℕ))) =
        Matrix.trace ((U * H) * ((U * H) * (U * H))) := by
          simp [U, H, pow_succ, Matrix.mul_assoc]
    _ = Matrix.trace (S * (S * (H * (S * (S * (H * (S * (S * H)))))))) := by
          have hrewrite :
              (U * H) * ((U * H) * (U * H)) =
                S * (S * (H * (S * (S * (H * (S * (S * H))))))) := by
            calc
              (U * H) * ((U * H) * (U * H))
                  = U * (H * (U * (H * (U * H)))) := by
                      simp [Matrix.mul_assoc]
              _
                  = (S * S) * (H * ((S * S) * (H * ((S * S) * H)))) := by
                      simp [hSS]
              _ = S * (S * (H * (S * (S * (H * (S * (S * H))))))) := by
                    simp [Matrix.mul_assoc]
          simp [hrewrite]
    _ = Matrix.trace ((S * (H * (S * (S * (H * (S * (S * H))))))) * S) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (((S * H * S) ^ (3 : ℕ))) := by
          simp [pow_succ, Matrix.mul_assoc]
    _ = Matrix.trace (cube (sandwich (sqrtInv X) Δ) : Mat) := by
          simp [S, H, RealSymmetricMatrixSpace.cube, RealSymmetricMatrixSpace.sandwich,
            pow_succ, Matrix.mul_assoc]

/-- Lemma 5.4.4.1 (1): at a strict-cone point, the first directional derivative of the
log-determinant barrier in a symmetric direction is the Frobenius pairing with `-X⁻¹`. -/
theorem logDetBarrier_lineDeriv_eq_frobeniusInner
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    lineDeriv ℝ logDetBarrierAmbientSymm X Δ =
      ⟪-inv X, Δ⟫_F := by
  let A : Mat := ((X : SymmMat) : Mat)
  let H : Mat := (Δ : Mat)
  have hA_det_ne : A.det ≠ 0 := by
    exact (strictPositiveSemidefiniteCone_posDef X).det_pos.ne'
  have hline : lineDeriv ℝ logDetBarrierAmbientSymm X Δ = -Matrix.trace (A⁻¹ * H) := by
    have hneg : HasDerivAt (fun s : ℝ ↦ -Real.log ((A + s • H).det))
        (-Matrix.trace (A⁻¹ * H)) 0 :=
      hasDerivAt_negLogDet_affine n A H hA_det_ne
    simpa [lineDeriv, directionalSlice, logDetBarrierAmbient, A, H] using hneg.deriv
  have hInvsymm : ((A⁻¹)ᵀ : Mat) = A⁻¹ := by
    simpa [A, StrictPositiveSemidefiniteCone.coe_inv, Matrix.IsSymm] using
      (RealSymmetricMatrixSpace.isSymm (inv X)).eq
  calc
    lineDeriv ℝ logDetBarrierAmbientSymm X Δ = -Matrix.trace (A⁻¹ * H) := hline
    _ = ⟪-inv X, Δ⟫_F := by
          rw [frobeniusInner_def]
          simp [A, H, StrictPositiveSemidefiniteCone.coe_inv, hInvsymm]

/-- Lemma 5.4.4.1 (3): the second directional derivative is the Frobenius pairing of `X⁻¹ Δ X⁻¹`
with `Δ`. -/
theorem logDetBarrier_secondDirectional_eq_frobeniusInner
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    secondDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      ⟪sandwich (inv X) Δ, Δ⟫_F := by
  let A : Mat := ((X : SymmMat) : Mat)
  let H : Mat := (Δ : Mat)
  have hA_det_ne : A.det ≠ 0 := by
    exact (strictPositiveSemidefiniteCone_posDef X).det_pos.ne'
  have hdet_nhds : {t : ℝ | (A + t • H).det ≠ 0} ∈ nhds (0 : ℝ) := by
    have hcont : Continuous fun t : ℝ ↦ (A + t • H).det := by
      fun_prop
    have hdet0 : ((A + (0 : ℝ) • H).det : ℝ) ∈ {y : ℝ | y ≠ 0} := by
      simpa using hA_det_ne
    simpa using hcont.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_ne hdet0)
  have hEq :
      (fun t : ℝ ↦ deriv (directionalSlice logDetBarrierAmbientSymm X Δ) t) =ᶠ[nhds 0]
        fun t : ℝ ↦ -Matrix.trace ((Ring.inverse (A + t • H)) * H) := by
    have hslice : directionalSlice logDetBarrierAmbientSymm X Δ =
        fun u : ℝ ↦ -Real.log ((A + u • H).det) := by
      ext u
      simp [directionalSlice, logDetBarrierAmbient, A, H]
    filter_upwards [hdet_nhds] with t ht
    calc
      deriv (directionalSlice logDetBarrierAmbientSymm X Δ) t
          = deriv (fun u : ℝ ↦ -Real.log ((A + u • H).det)) t := by rw [hslice]
      _ = -Matrix.trace (((A + t • H)⁻¹) * H) :=
            (hasDerivAt_negLogDet_affine_at n A H ht).deriv
      _ = -Matrix.trace ((Ring.inverse (A + t • H)) * H) := by
            simp [Matrix.nonsing_inv_eq_ringInverse]
  have hquad : HasDerivAt (fun t : ℝ ↦ -Matrix.trace ((Ring.inverse (A + t • H)) * H))
      (Matrix.trace ((A⁻¹ * H) * (A⁻¹ * H))) 0 :=
    hasDerivAt_invTrace_affine n A H hA_det_ne
  have hInvsymm : ((A⁻¹)ᵀ : Mat) = A⁻¹ := by
    simpa [A, StrictPositiveSemidefiniteCone.coe_inv, Matrix.IsSymm] using
      (RealSymmetricMatrixSpace.isSymm (inv X)).eq
  have hHsymm : (Hᵀ : Mat) = H := by
    simpa [H, Matrix.IsSymm] using (RealSymmetricMatrixSpace.isSymm Δ).eq
  calc
    secondDirectionalDerivative logDetBarrierAmbientSymm X Δ
        = deriv (deriv (directionalSlice logDetBarrierAmbientSymm X Δ)) 0 := by
            simp [secondDirectionalDerivative, iteratedDeriv_succ]
    _ = deriv (fun t : ℝ ↦ -Matrix.trace ((Ring.inverse (A + t • H)) * H)) 0 := by
          rw [Filter.EventuallyEq.deriv_eq hEq]
    _ = Matrix.trace ((A⁻¹ * H) * (A⁻¹ * H)) := by
          simpa [A] using hquad.deriv
    _ = ⟪sandwich (inv X) Δ, Δ⟫_F := by
          rw [frobeniusInner_def]
          simp [A, H, StrictPositiveSemidefiniteCone.coe_inv, RealSymmetricMatrixSpace.sandwich,
            hInvsymm, hHsymm, Matrix.mul_assoc]

/-- Lemma 5.4.4.1 (2): the second directional derivative is the Frobenius self-pairing of
`√(X⁻¹) Δ √(X⁻¹)`. -/
theorem logDetBarrier_secondDirectional_eq_frobeniusNormSq
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    secondDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      ⟪sandwich (sqrtInv X) Δ, sandwich (sqrtInv X) Δ⟫_F := by
  -- Route correction: use the stabilized `sqrtInv² = inv` bridge instead of recomputing the
  -- second derivative in normalized coordinates.
  rw [logDetBarrier_secondDirectional_eq_frobeniusInner]
  exact (frobeniusSelfSandwichSqrtInv_eq_invPairing n X Δ).symm

/-- Lemma 5.4.4.1 (4): the second directional derivative is the trace of
`(√(X⁻¹) Δ √(X⁻¹))²`. -/
theorem logDetBarrier_secondDirectional_eq_trace_sq
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    secondDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      Matrix.trace (((sandwich (sqrtInv X) Δ : Mat) ^ (2 : ℕ))) := by
  -- Convert the Frobenius self-pairing from the normalized sandwich form to an ambient trace.
  rw [logDetBarrier_secondDirectional_eq_frobeniusNormSq]
  exact frobeniusInner_self_eq_trace_sq n (sandwich (sqrtInv X) Δ)

/-- Lemma 5.4.4.1 (5): the third directional derivative is `-2` times the Frobenius pairing of the
identity with `(√(X⁻¹) Δ √(X⁻¹))³`. -/
theorem logDetBarrier_thirdDirectional_eq_frobeniusInner
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    thirdDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      -2 *
        ⟪(1 : SymmMat), cube (sandwich (sqrtInv X) Δ)⟫_F := by
  let A : Mat := ((X : SymmMat) : Mat)
  let H : Mat := (Δ : Mat)
  have hA_det_ne : A.det ≠ 0 := by
    exact (strictPositiveSemidefiniteCone_posDef X).det_pos.ne'
  have hdet_nhds : {t : ℝ | (A + t • H).det ≠ 0} ∈ nhds (0 : ℝ) := by
    have hcont : Continuous fun t : ℝ ↦ (A + t • H).det := by
      fun_prop
    have hdet0 : ((A + (0 : ℝ) • H).det : ℝ) ∈ {y : ℝ | y ≠ 0} := by
      simpa using hA_det_ne
    simpa using hcont.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_ne hdet0)
  have hEq₁ :
      (fun t : ℝ ↦ deriv (directionalSlice logDetBarrierAmbientSymm X Δ) t) =ᶠ[nhds 0]
        fun t : ℝ ↦ -Matrix.trace ((Ring.inverse (A + t • H)) * H) := by
    have hslice : directionalSlice logDetBarrierAmbientSymm X Δ =
        fun u : ℝ ↦ -Real.log ((A + u • H).det) := by
      ext u
      simp [directionalSlice, logDetBarrierAmbient, A, H]
    filter_upwards [hdet_nhds] with t ht
    calc
      deriv (directionalSlice logDetBarrierAmbientSymm X Δ) t
          = deriv (fun u : ℝ ↦ -Real.log ((A + u • H).det)) t := by rw [hslice]
      _ = -Matrix.trace (((A + t • H)⁻¹) * H) :=
            (hasDerivAt_negLogDet_affine_at n A H ht).deriv
      _ = -Matrix.trace ((Ring.inverse (A + t • H)) * H) := by
            simp [Matrix.nonsing_inv_eq_ringInverse]
  have hEq₁' :
      (fun t : ℝ ↦ deriv (deriv (directionalSlice logDetBarrierAmbientSymm X Δ)) t) =ᶠ[nhds 0]
        fun t : ℝ ↦ deriv (fun u : ℝ ↦ -Matrix.trace ((Ring.inverse (A + u • H)) * H)) t := by
    filter_upwards [hdet_nhds] with t ht
    have hlocalDet : {u : ℝ | (A + u • H).det ≠ 0} ∈ nhds t := by
      have hcont : Continuous fun u : ℝ ↦ (A + u • H).det := by
        fun_prop
      have hmem : ((A + t • H).det : ℝ) ∈ {y : ℝ | y ≠ 0} := ht
      simpa using hcont.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_ne hmem)
    have hslice : directionalSlice logDetBarrierAmbientSymm X Δ =
        fun u : ℝ ↦ -Real.log ((A + u • H).det) := by
      ext u
      simp [directionalSlice, logDetBarrierAmbient, A, H]
    have hlocal :
        (fun u : ℝ ↦ deriv (directionalSlice logDetBarrierAmbientSymm X Δ) u) =ᶠ[nhds t]
          fun u : ℝ ↦ -Matrix.trace ((Ring.inverse (A + u • H)) * H) := by
      filter_upwards [hlocalDet] with u hu
      calc
        deriv (directionalSlice logDetBarrierAmbientSymm X Δ) u
            = deriv (fun s : ℝ ↦ -Real.log ((A + s • H).det)) u := by rw [hslice]
        _ = -Matrix.trace (((A + u • H)⁻¹) * H) :=
              (hasDerivAt_negLogDet_affine_at n A H hu).deriv
        _ = -Matrix.trace ((Ring.inverse (A + u • H)) * H) := by
              simp [Matrix.nonsing_inv_eq_ringInverse]
    exact Filter.EventuallyEq.deriv_eq hlocal
  have hEq₂ :
      (fun t : ℝ ↦ deriv (fun u : ℝ ↦ -Matrix.trace ((Ring.inverse (A + u • H)) * H)) t) =ᶠ[nhds 0]
        fun t : ℝ ↦ Matrix.trace (((Ring.inverse (A + t • H)) * H) ^ (2 : ℕ)) := by
    filter_upwards [hdet_nhds] with t ht
    simpa using (hasDerivAt_invTrace_affine_at n A H ht).deriv
  have hcube :
      HasDerivAt
        (fun t : ℝ ↦ Matrix.trace (((Ring.inverse (A + t • H)) * H) ^ (2 : ℕ)))
        (-2 * Matrix.trace ((A⁻¹ * H) ^ (3 : ℕ)))
        0 :=
    hasDerivAt_invTraceSquare_affine n A H hA_det_ne
  calc
    thirdDirectionalDerivative logDetBarrierAmbientSymm X Δ
        = deriv (deriv (deriv (directionalSlice logDetBarrierAmbientSymm X Δ))) 0 := by
            simp [thirdDirectionalDerivative, iteratedDeriv_succ']
    _ = deriv (fun t : ℝ ↦ deriv (fun u : ℝ ↦ -Matrix.trace ((Ring.inverse (A + u • H)) * H)) t)
          0 := by
            rw [Filter.EventuallyEq.deriv_eq hEq₁']
    _ = deriv (fun t : ℝ ↦ Matrix.trace (((Ring.inverse (A + t • H)) * H) ^ (2 : ℕ))) 0 := by
          rw [Filter.EventuallyEq.deriv_eq hEq₂]
    _ = -2 * Matrix.trace ((A⁻¹ * H) ^ (3 : ℕ)) := by
          simpa [A] using hcube.deriv
    _ = -2 * Matrix.trace (cube (sandwich (sqrtInv X) Δ) : Mat) := by
          congr 1
          simpa [A, H] using trace_invMulCube_eq_trace_cube_sandwichSqrtInv n X Δ
    _ = -2 * ⟪(1 : SymmMat), cube (sandwich (sqrtInv X) Δ)⟫_F := by
          congr 1
          symm
          exact frobeniusInner_one_cube_eq_trace_cube n (sandwich (sqrtInv X) Δ)

/-- Lemma 5.4.4.1 (6): the third directional derivative is `-2` times the trace of
`(√(X⁻¹) Δ √(X⁻¹))³`. -/
theorem logDetBarrier_thirdDirectional_eq_trace_cube
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    thirdDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      -2 * Matrix.trace (cube (sandwich (sqrtInv X) Δ) : Mat) := by
  -- Convert the Frobenius pairing against the identity into the ambient trace of the cube.
  rw [logDetBarrier_thirdDirectional_eq_frobeniusInner]
  congr 1
  exact frobeniusInner_one_cube_eq_trace_cube n (sandwich (sqrtInv X) Δ)

end

end
