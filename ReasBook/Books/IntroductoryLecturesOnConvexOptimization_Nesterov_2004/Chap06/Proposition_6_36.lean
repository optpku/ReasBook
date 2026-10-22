/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open NormedSpace
open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace
open scoped RightActions

/- Proposition 6.36 lies in Chapter 6's symmetric-matrix spectral smoothing domain.

Sampled owner-style declarations:
- `𝕊^n`, `RealSymmetricMatrixSpace.isHermitian`, and `RealSymmetricMatrixSpace.eigenvalues` in
  `Chap05/Definition_5_4_4_1` and `Chap05/Definition_5_4_4_2`, the chapter owners for real
  symmetric matrices and their intrinsic spectral data;
- `Matrix.leastEigenvalue` and the notation `λ_min(H)` in `Chap04/Definition_4_1_6`, showing the
  project style for extremal spectral scalars: the ambient-spectrum owner is primitive, and any
  coordinate/eigenvalue-list formula is a bridge theorem;
- `Matrix.greatestEigenvalue` and the notation `λ_max(H)` in `Chap04/Definition_4_1_6`, the
  project owner for largest real spectral values;
- `entropySmoothing` in `Chap06/Proposition_6_35`, the unscaled spectral log-sum-exp owner;
- `logSumExpMaxEigenvalueSmoothing` in `Chap06/Definition_6_47`, the positive-parameter owner
  for the smoothed maximal eigenvalue on `𝕊^n`;
- mathlib `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`,
  `Matrix.IsSymm.exp`, and `Matrix.IsHermitian.trace_eq_sum_eigenvalues`, the canonical ambient
  spectral and exponential bridges.

Best owner abstraction:
- source-facing: Proposition 6.36's approximation and derivative formulas for the smoothed maximal
  eigenvalue;
- core/canonical: `𝕊^n`, `λ_max((X : Matrix (Fin n) (Fin n) ℝ))`, and
  `logSumExpMaxEigenvalueSmoothing`;
- bridge/view: the top-ordered-eigenvalue formula for `0 < n`, the matrix-exponential trace
  formula, and the normalized exponential matrix realizing the derivative.

Primitive data:
- `n : ℕ`;
- a positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- a symmetric matrix `X : 𝕊^n`.

Derived API:
- the intrinsic maximal-eigenvalue owner `λ_max((X : Matrix (Fin n) (Fin n) ℝ))`;
- the bridge
  `λ_max((X : Matrix (Fin n) (Fin n) ℝ)) = eigenvalues X ⟨0, hn⟩` for `n > 0`;
- `RealSymmetricMatrixSpace.exponentialGradient`;
- the trace-form bridge for `logSumExpMaxEigenvalueSmoothing`;
- Proposition 6.36's approximation and differentiability statements.

This refinement removes the local ambient-matrix wrappers
`realSymmetricMatrix_isHermitian`, `symmetricMatrixEigenvalues`,
`symmetricMatrixMaxEigenvalue`, and `matrixExponentialSmoothing`, rewrites the file onto the
existing symmetric-matrix owner surface used elsewhere in the chapter, and keeps the ordered
eigenvalue formula only as a bridge from the intrinsic `λ_max` owner.
-/

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Proposition 6.36: use the Frobenius normed-group structure on ambient matrices
when differentiating matrix-valued maps. -/
local instance proposition636AmbientMatrixNormedAddCommGroup : NormedAddCommGroup Mat :=
  Matrix.frobeniusNormedAddCommGroup

/-- Helper for Proposition 6.36: scalar multiplication on ambient matrices is measured with the
Frobenius norm during the local calculus arguments. -/
local instance proposition636AmbientMatrixNormedSpace : NormedSpace ℝ Mat :=
  Matrix.frobeniusNormedSpace

/-- Helper for Proposition 6.36: the ambient matrix ring carries the Frobenius-compatible normed
ring structure used by the matrix-exponential calculus API. -/
local instance proposition636AmbientMatrixNormedRing : NormedRing Mat :=
  Matrix.frobeniusNormedRing

/-- Helper for Proposition 6.36: the ambient matrix algebra over `ℝ` carries the Frobenius
normed-algebra structure used in the local analytic arguments. -/
local instance proposition636AmbientMatrixNormedAlgebra : NormedAlgebra ℝ Mat :=
  Matrix.frobeniusNormedAlgebra

attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedSpace
attribute [local instance 1001] RealSymmetricMatrixSpace.symmetricMatrixInnerProductSpace
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace

namespace RealSymmetricMatrixSpace

/-- For `0 < n`, the supremum of the real spectrum of a symmetric matrix is its top ordered
eigenvalue. -/
theorem greatestEigenvalue_eq_eigenvalues_zero
    (hn : 0 < n) (X : SymmMat) :
    λ_max((X : Mat)) =
      (RealSymmetricMatrixSpace.isHermitian X).eigenvalues₀
        ⟨0, by simpa using hn⟩ := by
  let hX := RealSymmetricMatrixSpace.isHermitian X
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (by simp)
  let i0 : Fin (Fintype.card (Fin n)) := ⟨0, by simpa using hn⟩
  -- The canonical `eigenvalues₀` list is ordered, while `spectrum_real_eq_range_eigenvalues`
  -- is stated for the reindexed `eigenvalues`; compare through that reindexing.
  have hgreatest :
      IsGreatest (Set.range hX.eigenvalues) (hX.eigenvalues₀ i0) := by
    refine ⟨?_, ?_⟩
    · refine ⟨e i0, ?_⟩
      simp [e, i0, Matrix.IsHermitian.eigenvalues]
    intro y hy
    rcases hy with ⟨i, rfl⟩
    simpa [Matrix.IsHermitian.eigenvalues] using
      hX.eigenvalues₀_antitone
        (by simp [Fin.le_iff_val_le_val, i0])
  simpa [Matrix.greatestEigenvalue, hX.spectrum_real_eq_range_eigenvalues] using hgreatest.csSup_eq

/-- The normalized matrix exponential appearing in the derivative formula for the smoothed maximal
eigenvalue, packaged directly in the symmetric-matrix owner `𝕊^n`. -/
def exponentialGradient
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) : 𝕊^n :=
  ⟨(Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ))))⁻¹ •
      exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ)), by
    have h_scaled : (((μ : ℝ)⁻¹) • (X : Matrix (Fin n) (Fin n) ℝ)).IsSymm :=
      (isSymm X).smul ((μ : ℝ)⁻¹)
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    simpa using
      (h_scaled.exp.smul
        ((Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ))))⁻¹))⟩

/-- Expanding `exponentialGradient μ X` gives the normalized exponential matrix
`Trace (exp (X / μ))⁻¹ exp (X / μ)`. -/
@[simp] theorem coe_exponentialGradient
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) :
    ((exponentialGradient μ X : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ) =
      (Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ))))⁻¹ •
        exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ)) :=
  rfl

end RealSymmetricMatrixSpace

open RealSymmetricMatrixSpace

-- Proof sketch: rewrite `exp ((μ⁻¹) • X)` as the real continuous functional calculus of
-- `t ↦ exp (μ⁻¹ t)` applied to `X`, then evaluate that functional calculus by the Hermitian
-- spectral theorem and take the trace of the resulting diagonal form.
/-- Helper for Proposition 6.36: the trace of the scaled matrix exponential is the sum of the
exponentials of the ordered eigenvalues. -/
theorem trace_exp_scaled_eq_sum_exp_eigenvalues
    (μ : {μ : ℝ // 0 < μ}) (X : SymmMat) :
    Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Mat))) =
      ∑ i : Fin n, Real.exp (eigenvalues X i / (μ : ℝ)) := by
  let hX := RealSymmetricMatrixSpace.isHermitian X
  letI : NormedRing Mat := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
  have hscaled : IsSelfAdjoint (((μ : ℝ)⁻¹) • (X : Mat)) := by
    simpa [Matrix.IsSelfAdjoint, Matrix.IsHermitian] using
      hX.smul (show IsSelfAdjoint (((μ : ℝ)⁻¹) : ℝ) by simp [IsSelfAdjoint])
  -- Rewrite the exponential via the real functional calculus, then evaluate it on the diagonal
  -- spectral model of `X`.
  conv_lhs =>
    rw [← CFC.real_exp_eq_normedSpace_exp
      (a := ((μ : ℝ)⁻¹ • (X : Mat))) hscaled]
    rw [← cfc_comp_smul (R := ℝ) ((μ : ℝ)⁻¹) Real.exp (X : Mat)]
    rw [hX.cfc_eq (fun t : ℝ ↦ Real.exp ((μ : ℝ)⁻¹ • t)), Matrix.IsHermitian.cfc,
      Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
      Matrix.trace_diagonal]
  simp [div_eq_mul_inv, mul_comm]

-- Proof sketch: diagonalize `X`, use the spectral mapping theorem for the matrix exponential, and
-- rewrite the trace of `exp (X / μ)` as the sum of the exponentials of the ordered eigenvalues.
/-- Helper for Proposition 6.36: the Chapter 6 smoothing owner agrees with the textbook
matrix-exponential trace formula
`μ log (Trace (exp (X / μ)))`. -/
theorem logSumExpMaxEigenvalueSmoothing_eq_matrixExponentialTrace
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) :
    logSumExpMaxEigenvalueSmoothing μ X =
      (μ : ℝ) * Real.log
        (Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Matrix (Fin n) (Fin n) ℝ)))) := by
  -- Rewrite the smoothing owner through the explicit eigenvalue log-sum-exp formula.
  rw [logSumExpMaxEigenvalueSmoothing_eq]
  -- Replace the eigenvalue sum by the trace of the scaled matrix exponential.
  rw [trace_exp_scaled_eq_sum_exp_eigenvalues]

-- Proof sketch: expand the Frobenius pairing by definition, use symmetry of
-- `exponentialGradient μ X` to remove the transpose, and cycle the trace factors.
/-- Helper for Proposition 6.36: pairing against the exponential gradient in Frobenius form is the
same as the ambient trace pairing. -/
theorem frobeniusInner_exponentialGradient_eq_trace_mul
    (μ : {μ : ℝ // 0 < μ}) (X H : SymmMat) :
    ⟪exponentialGradient μ X, H⟫_F =
      Matrix.trace ((H : Mat) * (exponentialGradient μ X : Mat)) := by
  -- Rewrite the Frobenius pairing into the ambient matrix trace formula.
  rw [RealSymmetricMatrixSpace.frobeniusInner_def]
  -- Symmetry of `exponentialGradient μ X` removes the transpose on the left factor.
  rw [(RealSymmetricMatrixSpace.isSymm (exponentialGradient μ X)).eq]
  -- Cyclicity then puts the direction matrix `H` in the source-textbook position.
  simpa using
    (Matrix.trace_mul_comm
      (exponentialGradient μ X : Mat)
      (H : Mat))

-- Proof sketch: compare the finite sum `∑ i, exp (λᵢ(X) / μ)` with its largest summand and with
-- `n` times that largest summand, then identify that largest ordered eigenvalue with the
-- supremum of the real spectrum.
/-- Approximation bound for Proposition 6.36: for a positive smoothing parameter `μ`,
the smoothed maximal eigenvalue approximates the maximal eigenvalue of `X`,
expressed intrinsically as the supremum of the real spectrum,
within the additive error `μ log n`. -/
theorem greatestEigenvalue_le_logSumExpMaxEigenvalueSmoothing_le
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) :
    λ_max((X : Mat)) ≤ logSumExpMaxEigenvalueSmoothing μ X ∧
      logSumExpMaxEigenvalueSmoothing μ X ≤
        λ_max((X : Mat)) + (μ : ℝ) * Real.log (n : ℝ) := by
  by_cases hzero : n = 0
  · subst hzero
    -- In the empty-dimensional case, both the spectrum and the smoothing value collapse to `0`.
    simp [Matrix.greatestEigenvalue, logSumExpMaxEigenvalueSmoothing]
  · let i0 : Fin n := ⟨0, Nat.pos_iff_ne_zero.mpr hzero⟩
    let hX := RealSymmetricMatrixSpace.isHermitian X
    let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (by simp)
    let i00 : Fin (Fintype.card (Fin n)) := ⟨0, by simpa using Nat.pos_iff_ne_zero.mpr hzero⟩
    let imax : Fin n := e i00
    let lambda0 : ℝ := hX.eigenvalues₀ i00
    let s : ℝ := ∑ i : Fin n, Real.exp (eigenvalues X i / (μ : ℝ))
    have hs_pos : 0 < s := by
      have hexp_pos : 0 < Real.exp (eigenvalues X imax / (μ : ℝ)) := Real.exp_pos _
      refine lt_of_lt_of_le hexp_pos ?_
      simpa [s] using
        (Finset.single_le_sum
          (fun j _ ↦ (Real.exp_pos (eigenvalues X j / (μ : ℝ))).le)
          (Finset.mem_univ imax))
    have himax : eigenvalues X imax = lambda0 := by
      simp [e, i00, imax, lambda0, Matrix.IsHermitian.eigenvalues]
    have hsingle_le : Real.exp (lambda0 / (μ : ℝ)) ≤ s := by
      simpa [s, himax] using
        (Finset.single_le_sum
          (fun j _ ↦ (Real.exp_pos (eigenvalues X j / (μ : ℝ))).le)
          (Finset.mem_univ imax))
    have hmax (i : Fin n) : eigenvalues X i ≤ lambda0 := by
      simpa [e, lambda0, Matrix.IsHermitian.eigenvalues] using
        hX.eigenvalues₀_antitone
          (by simp [Fin.le_iff_val_le_val, i00])
    have hsum_le :
        s ≤ (n : ℝ) * Real.exp (lambda0 / (μ : ℝ)) := by
      calc
        s = ∑ i : Fin n, Real.exp (eigenvalues X i / (μ : ℝ)) := rfl
        _ ≤ ∑ _i : Fin n, Real.exp (lambda0 / (μ : ℝ)) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          apply Real.exp_le_exp.mpr
          exact div_le_div_of_nonneg_right (hmax i) μ.2.le
        _ = (n : ℝ) * Real.exp (lambda0 / (μ : ℝ)) := by
          simp [nsmul_eq_mul]
    have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt μ.2
    have hlower_log :
        lambda0 / (μ : ℝ) ≤ Real.log s := by
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hsingle_le
    have hupper_log :
        Real.log s ≤ Real.log (n : ℝ) + lambda0 / (μ : ℝ) := by
      have hlog := Real.log_le_log hs_pos hsum_le
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast hzero
      simpa [Real.log_mul hn_ne (Real.exp_ne_zero _), Real.log_exp] using hlog
    have hlower_scaled :
        lambda0 ≤ (μ : ℝ) * Real.log s := by
      have hscaled := mul_le_mul_of_nonneg_left hlower_log μ.2.le
      simpa [s, div_eq_mul_inv, hμ_ne, mul_assoc, mul_left_comm, mul_comm] using hscaled
    have hupper_scaled :
        (μ : ℝ) * Real.log s ≤ lambda0 + (μ : ℝ) * Real.log (n : ℝ) := by
      have hscaled := mul_le_mul_of_nonneg_left hupper_log μ.2.le
      have hrewrite :
          (μ : ℝ) * (Real.log (n : ℝ) + lambda0 / (μ : ℝ)) =
            lambda0 + (μ : ℝ) * Real.log (n : ℝ) := by
        rw [mul_add]
        field_simp [hμ_ne]
        ring
      exact hscaled.trans_eq hrewrite
    constructor
    · -- The largest eigenvalue is controlled by the logarithm of the sum through the largest term.
      rw [greatestEigenvalue_eq_eigenvalues_zero (Nat.pos_iff_ne_zero.mpr hzero)]
      simpa [logSumExpMaxEigenvalueSmoothing_eq, s] using hlower_scaled
    · -- The whole sum is at most `n` copies of the largest exponential term.
      rw [greatestEigenvalue_eq_eigenvalues_zero (Nat.pos_iff_ne_zero.mpr hzero)]
      simpa [logSumExpMaxEigenvalueSmoothing_eq, s, add_comm, add_left_comm, add_assoc] using
        hupper_scaled

-- Proof sketch: cyclicity of the trace lets every insertion term in the noncommutative derivative
-- of `A^(m+1)` collapse to the same ambient trace `Trace (H A^m)`, so the whole insertion sum is
-- just `(m + 1)` copies of that common value.
/-- Helper for Proposition 6.36: after collapsing the insertion terms in the derivative of a power
under the trace, the whole sum becomes `(m + 1) * Trace (H A^m)`. -/
theorem trace_sum_insertions_eq_nsmul_trace_mul_pow
    (A H : Mat) (m : ℕ) :
    Matrix.trace ((Finset.range (m + 1)).sum fun i ↦ A ^ (m - i) * H * A ^ i) =
      (m + 1 : ℝ) * Matrix.trace (H * A ^ m) := by
  -- Move the trace through the finite sum and show every summand has the same cyclic trace.
  rw [Matrix.trace_sum]
  have hsum :
      (Finset.range (m + 1)).sum (fun i ↦ Matrix.trace (A ^ (m - i) * H * A ^ i)) =
        (Finset.range (m + 1)).sum (fun _ ↦ Matrix.trace (H * A ^ m)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    calc
      Matrix.trace (A ^ (m - i) * H * A ^ i)
        = Matrix.trace ((A ^ i * A ^ (m - i)) * H) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle (A ^ (m - i)) H (A ^ i)
      _ = Matrix.trace (H * (A ^ i * A ^ (m - i))) := by
            simpa using Matrix.trace_mul_comm (A ^ i * A ^ (m - i)) H
      _ = Matrix.trace (H * A ^ m) := by
            have hpow : A ^ i * A ^ (m - i) = A ^ m := by
              simpa [Nat.add_sub_of_le hi_le] using (pow_add A i (m - i)).symm
            simp [hpow]
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

-- Proof sketch: once the trace of the scaled exponential is rewritten as a finite sum of positive
-- exponentials of eigenvalues, one positive summand gives strict positivity of the whole sum when
-- `n > 0`.
/-- Helper for Proposition 6.36: in positive dimension, the trace of the scaled matrix exponential
is strictly positive. -/
theorem trace_exp_scaled_pos
    (hn : 0 < n) (μ : {μ : ℝ // 0 < μ}) (X : SymmMat) :
    0 < Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Mat))) := by
  -- Rewrite the trace as the eigenvalue exponential sum and keep one positive summand.
  rw [trace_exp_scaled_eq_sum_exp_eigenvalues]
  let i0 : Fin n := ⟨0, hn⟩
  have hterm : 0 < Real.exp (eigenvalues X i0 / (μ : ℝ)) := Real.exp_pos _
  refine lt_of_lt_of_le hterm ?_
  simpa using
    (Finset.single_le_sum
      (fun i _ ↦ (Real.exp_pos (eigenvalues X i / (μ : ℝ))).le)
      (Finset.mem_univ i0))

/-- Helper for Proposition 6.36: the matrix trace packaged as a continuous linear map on the
ambient matrix space. -/
def traceContinuousLinearMap : Mat →L[ℝ] ℝ :=
  { toLinearMap := Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)
    cont := (Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)).continuous_of_finiteDimensional }

/-- Helper for Proposition 6.36: evaluating the packaged trace continuous linear map recovers the
ordinary matrix trace. -/
@[simp] theorem traceContinuousLinearMap_apply
    (M : Mat) :
    traceContinuousLinearMap (n := n) M = Matrix.trace M :=
  rfl

/-- Helper for Proposition 6.36: the scaled subtype inclusion `Y ↦ (1 / μ) • (Y : Mat)` is a
continuous linear map from `𝕊^n` to the ambient matrix space. -/
def scaledSymmetricInclusion
    (μ : {μ : ℝ // 0 < μ}) : SymmMat →L[ℝ] Mat :=
  ((μ : ℝ)⁻¹) • (Submodule.subtypeₗᵢ (𝕊^n : Submodule ℝ Mat)).toContinuousLinearMap

/-- Helper for Proposition 6.36: expanding the scaled subtype inclusion gives the expected ambient
matrix formula. -/
@[simp] theorem scaledSymmetricInclusion_apply
    (μ : {μ : ℝ // 0 < μ}) (Y : SymmMat) :
    scaledSymmetricInclusion (n := n) μ Y = ((μ : ℝ)⁻¹) • (Y : Mat) :=
  rfl

-- Proof sketch: package the scaled ambient matrix exponential as the composition of the fixed
-- scaling map, the analytic Banach-algebra exponential, and the continuous linear trace map, then
-- restrict that ambient `C²` surface along the symmetric-matrix inclusion.
/-- Helper for Proposition 6.36: the scaled trace-exponential core is `C²` on `𝕊^n`. -/
theorem traceExpScaled_contDiffTwo
    (μ : {μ : ℝ // 0 < μ}) :
    ContDiff ℝ 2
      (fun Y : SymmMat ↦
        Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))) := by
  have hexpAnalytic : AnalyticOnNhd ℝ (exp : Mat → Mat) Set.univ := by
    intro A hA
    exact NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := Mat) A
  have hexpContDiff : ContDiff ℝ 2 (exp : Mat → Mat) := hexpAnalytic.contDiff
  have hscaled : ContDiff ℝ 2 (scaledSymmetricInclusion (n := n) μ : SymmMat → Mat) := by
    -- The scaled symmetric inclusion is a continuous linear map on the same owner surface.
    simpa using (scaledSymmetricInclusion (n := n) μ).contDiff
  -- Compose the ambient matrix exponential with the scaled inclusion and the packaged trace map.
  simpa [Function.comp, scaledSymmetricInclusion_apply, traceContinuousLinearMap_apply] using
    ((traceContinuousLinearMap (n := n)).contDiff.comp (hexpContDiff.comp hscaled))

/-- Helper for Proposition 6.36: on any real normed space, an affine line has derivative equal
to its direction. -/
private lemma affineLineHasDerivAt_generic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul, add_comm] using ((hasDerivAt_id t).smul_const d).const_add x

-- Proof sketch: differentiate each power-series term of
-- `t ↦ Trace ((A + t • B)^(m + 1)) / (m + 1)!` in the ambient matrix algebra, then collapse the
-- insertion sum under the trace using cyclicity.
/-- Helper for Proposition 6.36: each affine-slice power-series term of the trace exponential has
the expected scalar derivative. -/
theorem traceExpAffineSliceTerm_hasDerivAt
    (A B : Mat) (m : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        Matrix.trace ((A + s • B) ^ (m + 1)) / ((Nat.factorial (m + 1)) : ℝ))
      (Matrix.trace (B * (A + t • B) ^ m) / ((Nat.factorial m) : ℝ))
      t := by
  let line : ℝ → Mat := fun s : ℝ ↦ A + s • B
  have hpow :
      HasFDerivAt
        (fun M : Mat ↦ M ^ (m + 1))
        (∑ i ∈ Finset.range (m + 1),
          (line t) ^ ((m + 1).pred - i) •> ContinuousLinearMap.id ℝ Mat <• (line t) ^ i)
        (line t) := by
    -- Differentiate the ambient power map at the affine-slice base point.
    simpa [line] using (hasFDerivAt_pow' (𝕜 := ℝ) (n := m + 1) (x := line t))
  have hpowLine :
      HasDerivAt
        (fun s : ℝ ↦ line s ^ (m + 1))
        ((Finset.range (m + 1)).sum fun i ↦ (line t) ^ (m - i) * B * (line t) ^ i)
        t := by
    have hline : HasDerivAt line B t := by
      -- The affine line `s ↦ A + s • B` has derivative equal to its direction `B`.
      simpa [line, one_smul, add_comm] using ((hasDerivAt_id t).smul_const B).const_add A
    -- Compose the ambient power derivative with the affine slice.
    simpa [line, ContinuousLinearMap.sum_apply, Matrix.mul_assoc] using
      hpow.comp_hasDerivAt t hline
  have htrace :
      HasDerivAt
        (fun s : ℝ ↦ Matrix.trace (line s ^ (m + 1)))
        ((Finset.range (m + 1)).sum fun i ↦ Matrix.trace ((line t) ^ (m - i) * B * (line t) ^ i))
        t := by
    -- Apply the bundled trace map to the differentiated power slice.
    simpa [traceContinuousLinearMap_apply] using
      (traceContinuousLinearMap (n := n)).hasFDerivAt.comp_hasDerivAt t hpowLine
  have hcollapse :
      ((Finset.range (m + 1)).sum fun i ↦ Matrix.trace ((line t) ^ (m - i) * B * (line t) ^ i)) =
        (m + 1 : ℝ) * Matrix.trace (B * (line t) ^ m) := by
    -- Cyclicity of trace collapses the insertion sum to `(m + 1)` copies of one term.
    simpa [line] using
      trace_sum_insertions_eq_nsmul_trace_mul_pow (A := line t) (H := B) m
  have hscaled :
      HasDerivAt
        (fun s : ℝ ↦ (((Nat.factorial (m + 1) : ℕ) : ℝ)⁻¹) * Matrix.trace (line s ^ (m + 1)))
        ((((Nat.factorial (m + 1) : ℕ) : ℝ)⁻¹) *
          ((Finset.range (m + 1)).sum fun i ↦ Matrix.trace ((line t) ^ (m - i) * B * (line t) ^ i)))
        t := by
    -- Scale the derivative by the reciprocal factorial from the power-series coefficient.
    simpa [line, mul_comm, mul_assoc] using
      htrace.const_mul ((((Nat.factorial (m + 1) : ℕ) : ℝ)⁻¹))
  -- Rewrite the scaled derivative into the source-facing factorial denominator.
  convert hscaled using 1
  · ext s
    simp [line, div_eq_mul_inv, mul_comm]
  · simp [div_eq_mul_inv, hcollapse]
    field_simp
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- Helper for Proposition 6.36: at `t = 0`, the scaled affine slice collapses to the scaled base
matrix. -/
private lemma scaledAffineSlice_zero
    (μ : {μ : ℝ // 0 < μ}) (X H : SymmMat) :
    ((μ : ℝ)⁻¹) • (((X + (0 : ℝ) • H : SymmMat) : Mat)) = ((μ : ℝ)⁻¹) • (X : Mat) := by
  -- The affine line at `0` is the base point, so the ambient scaled matrix is unchanged.
  simp

-- Proof sketch: bound the derivative terms uniformly on `t ∈ (-1, 1)` by comparing
-- `‖A + t • B‖` with a fixed radius and using the operator norm of the trace functional.
/-- Helper for Proposition 6.36: the raw affine-slice trace term is controlled by the operator
norm of the trace map, the direction norm, the ambient unit norm, and the fixed radius
`‖A‖ + ‖B‖`. -/
theorem traceExpAffineSliceTraceNormMajorant
    (A B : Mat) (m : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖Matrix.trace (B * (A + t • B) ^ m)‖ ≤
      ‖traceContinuousLinearMap (n := n)‖ * ‖B‖ * ‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ m := by
  have ht_abs : |t| ≤ 1 := by
    exact (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩).le
  have hsmul_norm : ‖t • B‖ ≤ ‖B‖ := by
    rw [norm_smul]
    calc
      |t| * ‖B‖ ≤ 1 * ‖B‖ := by
        exact mul_le_mul_of_nonneg_right ht_abs (norm_nonneg _)
      _ = ‖B‖ := by ring
  have hline_norm : ‖A + t • B‖ ≤ ‖A‖ + ‖B‖ := by
    calc
      ‖A + t • B‖ ≤ ‖A‖ + ‖t • B‖ := norm_add_le _ _
      _ ≤ ‖A‖ + ‖B‖ := by gcongr
  have hradius_nonneg : 0 ≤ ‖A‖ + ‖B‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpow_bound : ‖(A + t • B) ^ m‖ ≤ ‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ m := by
    induction m with
    | zero =>
        simp
    | succ k ih =>
        calc
          ‖(A + t • B) ^ (k + 1)‖ = ‖(A + t • B) ^ k * (A + t • B)‖ := by
              rw [pow_succ]
          _ ≤ ‖(A + t • B) ^ k‖ * ‖A + t • B‖ := norm_mul_le _ _
          _ ≤ (‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ k) * ‖A + t • B‖ := by
              exact mul_le_mul_of_nonneg_right ih (norm_nonneg _)
          _ ≤ (‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ k) * (‖A‖ + ‖B‖) := by
              exact mul_le_mul_of_nonneg_left hline_norm
                (mul_nonneg (norm_nonneg _) (pow_nonneg hradius_nonneg _))
          _ = ‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ (k + 1) := by
              rw [pow_succ]
              ring
  -- First control the trace term by the operator norm of the packaged trace functional.
  calc
    ‖Matrix.trace (B * (A + t • B) ^ m)‖
      ≤ ‖traceContinuousLinearMap (n := n)‖ * ‖B * (A + t • B) ^ m‖ := by
          simpa [traceContinuousLinearMap_apply] using
            (ContinuousLinearMap.le_opNorm
              (traceContinuousLinearMap (n := n))
              (B * (A + t • B) ^ m))
    _ ≤ ‖traceContinuousLinearMap (n := n)‖ * (‖B‖ * ‖(A + t • B) ^ m‖) := by
          gcongr
          exact norm_mul_le _ _
    _ ≤ ‖traceContinuousLinearMap (n := n)‖ * (‖B‖ * (‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ m)) := by
          gcongr
    _ = ‖traceContinuousLinearMap (n := n)‖ * ‖B‖ * ‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ m := by ring

/-- Helper for Proposition 6.36: the differentiated affine-slice series admits a summable
uniform majorant on `(-1, 1)`. -/
theorem traceExpAffineSliceDerivBound
    (A B : Mat) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ m t, t ∈ Set.Ioo (-1 : ℝ) 1 →
        ‖Matrix.trace (B * (A + t • B) ^ m) / ((Nat.factorial m) : ℝ)‖ ≤ u m := by
  let C : ℝ := ‖traceContinuousLinearMap (n := n)‖ * ‖B‖ * ‖(1 : Mat)‖
  let u : ℕ → ℝ := fun m ↦ C * ((‖A‖ + ‖B‖) ^ m / ((Nat.factorial m) : ℝ))
  refine ⟨u, ?_, ?_⟩
  · have hpow :
        Summable (fun m : ℕ ↦ (‖A‖ + ‖B‖) ^ m / ((Nat.factorial m) : ℝ)) :=
      Real.summable_pow_div_factorial (‖A‖ + ‖B‖)
    -- The factorial-decaying scalar series remains summable after multiplying by the fixed
    -- trace/direction constant.
    simpa [u, C, mul_assoc] using hpow.mul_left C
  · intro m t ht
    have hfactorial_pos : 0 < ((Nat.factorial m) : ℝ) := by
      exact Nat.cast_pos.mpr (Nat.factorial_pos m)
    have hmajorant :=
      traceExpAffineSliceTraceNormMajorant (n := n) (A := A) (B := B) (m := m) ht
    -- Divide the raw norm estimate by the positive factorial coefficient only at the end.
    have hdiv :
        ‖Matrix.trace (B * (A + t • B) ^ m)‖ / ((Nat.factorial m) : ℝ) ≤
          C * ((‖A‖ + ‖B‖) ^ m / ((Nat.factorial m) : ℝ)) := by
      calc
      ‖Matrix.trace (B * (A + t • B) ^ m)‖ / ((Nat.factorial m) : ℝ)
        ≤ (‖traceContinuousLinearMap (n := n)‖ * ‖B‖ * ‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ m) /
            ((Nat.factorial m) : ℝ) := by
              exact div_le_div_of_nonneg_right hmajorant hfactorial_pos.le
      _ = C * ((‖A‖ + ‖B‖) ^ m / ((Nat.factorial m) : ℝ)) := by
            field_simp [C, hfactorial_pos.ne']
            ring
    simpa [u, norm_div, Real.norm_natCast] using hdiv

-- Proof sketch: rewrite the matrix exponential as its power series and separate the `k = 0`
-- term so the remaining series starts at exponent `m + 1`.
/-- Helper for Proposition 6.36: the trace of the affine-slice exponential has the stable normal
form `Trace 1 + ∑' m, Trace ((A + t • B)^(m + 1)) / (m + 1)!`. -/
theorem traceExpAffineSlice_eq_traceOne_add_tsum
    (A B : Mat) (t : ℝ) :
    Matrix.trace (exp (A + t • B)) =
      Matrix.trace (1 : Mat) +
        ∑' m : ℕ,
          Matrix.trace ((A + t • B) ^ (m + 1)) / ((Nat.factorial (m + 1)) : ℝ) := by
  letI : CompleteSpace Mat := FiniteDimensional.complete ℝ Mat
  let X : Mat := A + t • B
  have hsum :
      Summable
        (fun m : ℕ ↦ Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • X ^ m)) := by
    -- The ambient exponential series stays summable after applying the continuous trace map.
    simpa [traceContinuousLinearMap_apply] using
      (expSeries_summable' (𝕂 := ℝ) X).mapL (traceContinuousLinearMap (n := n))
  have hexp :
      exp X = ∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • X ^ m := by
    simpa using
      (congrArg (fun f : Mat → Mat ↦ f X) (exp_eq_tsum (𝕂 := ℝ) (𝔸 := Mat)))
  -- Rewrite `trace (exp X)` as the trace of the exponential power series.
  calc
    Matrix.trace (exp (A + t • B))
      = Matrix.trace (exp X) := by
          simp [X]
    _ = Matrix.trace (∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • X ^ m) := by
          rw [hexp]
    _
      = ∑' m : ℕ, Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • X ^ m) := by
          simpa [traceContinuousLinearMap_apply] using
            (traceContinuousLinearMap (n := n)).map_tsum (expSeries_summable' (𝕂 := ℝ) X)
    _ = Matrix.trace (1 : Mat) +
          ∑' m : ℕ, Matrix.trace (X ^ (m + 1)) / ((Nat.factorial (m + 1)) : ℝ) := by
          simpa [div_eq_mul_inv, Matrix.trace_smul, mul_comm, mul_left_comm, mul_assoc] using
            (hsum.sum_add_tsum_nat_add 1).symm

-- Proof sketch: evaluate the derivative series at `t = 0`, rewrite it back to
-- `Trace (B * exp A)`, and combine it with the termwise derivative result.
/-- Helper for Proposition 6.36: the affine slice
`t ↦ Trace (exp (A + t • B))` has derivative `Trace (B * exp A)` at `0`. -/
theorem hasDerivAt_traceExpAffineSlice_zero
    (A B : Mat) :
    HasDerivAt (fun t : ℝ ↦ Matrix.trace (exp (A + t • B))) (Matrix.trace (B * exp A)) 0 := by
  let g : ℕ → ℝ → ℝ := fun m t ↦
    Matrix.trace ((A + t • B) ^ (m + 1)) / ((Nat.factorial (m + 1)) : ℝ)
  let g' : ℕ → ℝ → ℝ := fun m t ↦
    Matrix.trace (B * (A + t • B) ^ m) / ((Nat.factorial m) : ℝ)
  have hg :
      ∀ m t, t ∈ Set.Ioo (-1 : ℝ) 1 → HasDerivAt (g m) (g' m t) t := by
    intro m t ht
    simpa [g, g'] using
      traceExpAffineSliceTerm_hasDerivAt (n := n) (A := A) (B := B) m t
  rcases traceExpAffineSliceDerivBound (n := n) A B with ⟨u, hu, hu_bound⟩
  have hg_bound :
      ∀ m t, t ∈ Set.Ioo (-1 : ℝ) 1 → ‖g' m t‖ ≤ u m := by
    intro m t ht
    simpa [g'] using hu_bound m t ht
  have hg0 :
      Summable (fun m : ℕ => g m 0) := by
    have hsum :
        Summable
          (fun m : ℕ ↦ Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • A ^ m)) := by
      simpa [traceContinuousLinearMap_apply] using
        (expSeries_summable' (𝕂 := ℝ) A).mapL (traceContinuousLinearMap (n := n))
    simpa [g, div_eq_mul_inv, Matrix.trace_smul, mul_assoc, mul_comm, mul_left_comm] using
      hsum.comp_injective Nat.succ_injective
  have htsum :
      HasDerivAt (fun t : ℝ ↦ ∑' m : ℕ, g m t) (∑' m : ℕ, g' m 0) 0 := by
    refine hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg_bound ?_ hg0 ?_
    · norm_num
    · norm_num
  let leftMul : Mat →L[ℝ] Mat :=
    ⟨LinearMap.mulLeft ℝ B, (LinearMap.mulLeft ℝ B).continuous_of_finiteDimensional⟩
  have hleftSummable :
      Summable (fun m : ℕ ↦ (((Nat.factorial m : ℕ) : ℝ)⁻¹) • (B * A ^ m)) := by
    simpa [leftMul, Matrix.mul_smul] using
      (expSeries_summable' (𝕂 := ℝ) A).mapL leftMul
  have hexpA :
      exp A = ∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • A ^ m := by
    simpa using
      (congrArg (fun f : Mat → Mat ↦ f A) (exp_eq_tsum (𝕂 := ℝ) (𝔸 := Mat)))
  have hleftTsum :
      ∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • (B * A ^ m) = B * exp A := by
    calc
      ∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • (B * A ^ m)
        = ∑' m : ℕ, B * ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • A ^ m) := by
            apply tsum_congr
            intro m
            rw [Matrix.mul_smul]
      _ = B * ∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • A ^ m := by
            symm
            simpa [leftMul] using leftMul.map_tsum (expSeries_summable' (𝕂 := ℝ) A)
      _ = B * exp A := by rw [hexpA]
  have hderiv_sum :
      (∑' m : ℕ, g' m 0) = Matrix.trace (B * exp A) := by
    calc
      (∑' m : ℕ, g' m 0)
        = ∑' m : ℕ, Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • (B * A ^ m)) := by
            apply tsum_congr
            intro m
            simp [g', div_eq_mul_inv, Matrix.trace_smul, mul_comm]
      _ = Matrix.trace (∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • (B * A ^ m)) := by
            symm
            simpa [traceContinuousLinearMap_apply] using
              (traceContinuousLinearMap (n := n)).map_tsum hleftSummable
      _ = Matrix.trace (B * exp A) := by rw [hleftTsum]
  have hseries :
      HasDerivAt
        (fun t : ℝ ↦ Matrix.trace (1 : Mat) + ∑' m : ℕ, g m t)
        (Matrix.trace (B * exp A))
        0 := by
    convert htsum.const_add (Matrix.trace (1 : Mat)) using 1
    exact hderiv_sum.symm
  convert hseries using 1
  ext t
  simpa [g] using traceExpAffineSlice_eq_traceOne_add_tsum (n := n) (A := A) (B := B) t

/-- Helper for Proposition 6.36: the ambient affine-slice derivative specializes cleanly to the
scaled intrinsic line `t ↦ X + t • H` in `𝕊^n`. -/
theorem traceExpScaledLine_hasDerivAt
    (μ : {μ : ℝ // 0 < μ}) (X H : SymmMat) :
    HasDerivAt
      (fun t : ℝ ↦
        Matrix.trace (exp ((μ : ℝ)⁻¹ • (((X + t • H : SymmMat) : Mat)))))
      (((μ : ℝ)⁻¹) *
        Matrix.trace ((H : Mat) * exp ((μ : ℝ)⁻¹ • (X : Mat))))
      0 := by
  -- Apply the ambient affine-slice derivative theorem to the scaled line
  -- `A := (1 / μ) • X`, `B := (1 / μ) • H`.
  simpa [smul_add, smul_smul, smul_mul_assoc, Matrix.trace_smul, mul_comm, mul_left_comm,
    mul_assoc] using
    (hasDerivAt_traceExpAffineSlice_zero (n := n)
      (((μ : ℝ)⁻¹) • (X : Mat))
      (((μ : ℝ)⁻¹) • (H : Mat)))

-- Route correction: isolate the source-faithful analytic core
-- `Y ↦ Trace (exp ((1 / μ) • Y))` and build the final `Real.log` / Frobenius rewrite on top of
-- that, instead of trying to close the whole proposition with one opaque derivative step.
/-- Helper for Proposition 6.36: the analytic core for the smoothing derivative is the Fréchet
derivative of the scalar trace-exponential map on `𝕊^n`. -/
theorem differentiableAt_trace_exp_scaled_and_fderiv_eq
    (μ : {μ : ℝ // 0 < μ}) (X : SymmMat) :
    DifferentiableAt ℝ
      (fun Y : SymmMat =>
        Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))) X ∧
      ∀ H : SymmMat,
        fderiv ℝ
          (fun Y : SymmMat =>
            Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))) X H =
          ((μ : ℝ)⁻¹) *
            Matrix.trace ((H : Mat) * exp ((μ : ℝ)⁻¹ • (X : Mat))) := by
  let g : SymmMat → ℝ := fun Y : SymmMat ↦
    Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))
  have hdiff : DifferentiableAt ℝ g X := by
    -- The `C²` scaled trace-exponential core is differentiable at every symmetric matrix.
    exact (traceExpScaled_contDiffTwo (n := n) μ).contDiffAt.differentiableAt (by norm_num)
  constructor
  · simpa [g] using hdiff
  · intro H
    have hline :
        deriv (fun t : ℝ ↦ g (X + t • H)) 0 =
          ((μ : ℝ)⁻¹) *
            Matrix.trace ((H : Mat) * exp ((μ : ℝ)⁻¹ • (X : Mat))) := by
      -- The affine scalar slice already has the explicit source-facing derivative formula.
      simpa [g] using (traceExpScaledLine_hasDerivAt (n := n) μ X H).deriv
    -- Rewrite the line derivative back to the Fréchet derivative on the same owner surface.
    rw [← hdiff.lineDeriv_eq_fderiv (v := H), lineDeriv_eq_deriv_directionalSlice]
    simpa [directionalSlice] using hline

/-- Helper for Proposition 6.36: package the trace-form rewrite as an equality of functions so the
positive-dimensional chain-rule proof can work on a stable target surface. -/
theorem logSumExpMaxEigenvalueSmoothing_eq_matrixExponentialTrace_fun
    (μ : {μ : ℝ // 0 < μ}) :
    (logSumExpMaxEigenvalueSmoothing μ : SymmMat → ℝ) =
      fun Y : SymmMat ↦
        (μ : ℝ) * Real.log
          (Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))) := by
  funext Y
  exact logSumExpMaxEigenvalueSmoothing_eq_matrixExponentialTrace μ Y

/-- Helper for Proposition 6.36: package the analytic trace-exponential core as the
`HasFDerivAt` input needed by the later scalar chain rules. -/
theorem hasFDerivAt_trace_exp_scaled
    (μ : {μ : ℝ // 0 < μ}) (X : SymmMat) :
    HasFDerivAt
      (fun Y : SymmMat ↦
        Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat))))
      (fderiv ℝ
        (fun Y : SymmMat ↦
          Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))) X)
      X := by
  -- Repackage the existing differentiability result as the precise Fréchet derivative theorem.
  exact (differentiableAt_trace_exp_scaled_and_fderiv_eq μ X).1.hasFDerivAt

/-- Helper for Proposition 6.36: evaluating the scalar chain-rule functional from
`μ log (Trace (exp (X / μ)))` on a direction `H` gives the Frobenius pairing with the normalized
matrix exponential. -/
theorem trace_exp_scaled_fderiv_riesz_eq_exponentialGradient
    (μ : {μ : ℝ // 0 < μ}) (X : SymmMat) :
    ∀ H : SymmMat,
      ((((μ : ℝ) * (Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Mat))))⁻¹) •
          fderiv ℝ
            (fun Y : SymmMat ↦
              Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))) X) H) =
        ⟪exponentialGradient μ X, H⟫_F := by
  have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt μ.2
  intro H
  -- Evaluate the continuous linear functional on `H` and simplify the scalar prefactor first.
  rw [ContinuousLinearMap.smul_apply]
  rw [(differentiableAt_trace_exp_scaled_and_fderiv_eq μ X).2 H]
  calc
    ((μ : ℝ) * (Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Mat))))⁻¹) *
        (((μ : ℝ)⁻¹) * Matrix.trace ((H : Mat) * exp ((μ : ℝ)⁻¹ • (X : Mat))))
      =
        (Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Mat))))⁻¹ *
          Matrix.trace ((H : Mat) * exp ((μ : ℝ)⁻¹ • (X : Mat))) := by
            field_simp [hμ_ne]
    _ =
        Matrix.trace
          ((H : Mat) *
            ((Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Mat))))⁻¹ •
              exp ((μ : ℝ)⁻¹ • (X : Mat)))) := by
            rw [Matrix.mul_smul, Matrix.trace_smul]
            simp [smul_eq_mul]
    _ = Matrix.trace ((H : Mat) * (exponentialGradient μ X : Mat)) := by
          rw [coe_exponentialGradient]
    _ = ⟪exponentialGradient μ X, H⟫_F := by
          rw [frobeniusInner_exponentialGradient_eq_trace_mul]

-- Proof sketch: keep the scalar chain rule in the owner that `HasFDerivAt.log` and
-- `HasFDerivAt.const_mul` naturally produce, namely the continuous linear map
-- `(((μ : ℝ) * g(X)⁻¹) • fderiv g X)`.
/-- Helper for Proposition 6.36: in positive dimension, the trace-form map
`Y ↦ μ log (Trace (exp ((1 / μ) • Y)))` has the Fréchet derivative dictated by the scalar chain
rule before any Riesz/Frobenius repackaging. -/
theorem hasFDerivAt_matrixExponentialTrace_log_pos
    (hn : 0 < n) (μ : {μ : ℝ // 0 < μ}) (X : SymmMat) :
    HasFDerivAt
      (fun Y : SymmMat ↦
        (μ : ℝ) * Real.log
          (Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))))
      ((((μ : ℝ) * (Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Mat))))⁻¹) •
          fderiv ℝ
            (fun Y : SymmMat ↦
              Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))) X) :
        StrongDual ℝ SymmMat)
      X := by
  let g : SymmMat → ℝ := fun Y : SymmMat ↦
    Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))
  have hcore : HasFDerivAt g (fderiv ℝ g X) X := by
    -- Reuse the packaged Fréchet derivative of the trace-exponential core.
    simpa [g] using (hasFDerivAt_trace_exp_scaled (n := n) μ X)
  have hpos : 0 < g X := by
    -- Positive dimension keeps the logarithm on its positive branch.
    simpa [g] using trace_exp_scaled_pos (n := n) hn μ X
  have hlog :
      HasFDerivAt
        (fun Y : SymmMat ↦ Real.log (g Y))
        ((g X)⁻¹ • fderiv ℝ g X)
        X := by
    -- Apply the scalar `log` chain rule directly on the same owner surface.
    simpa using hcore.log hpos.ne'
  -- Multiplying by the fixed scalar `μ` yields the trace-form smoothing derivative owner.
  simpa [g, smul_smul, mul_assoc, mul_left_comm, mul_comm] using hlog.const_mul (μ : ℝ)
/-- Helper for Proposition 6.36: in dimension `0`, the smoothing owner is the constant zero
function. -/
theorem logSumExpMaxEigenvalueSmoothing_eq_zero_dim
    (μ : {μ : ℝ // 0 < μ}) :
    @logSumExpMaxEigenvalueSmoothing 0 μ = fun _ : 𝕊^0 => (0 : ℝ) := by
  funext Y
  simp [logSumExpMaxEigenvalueSmoothing]

-- Proof sketch: differentiate the trace-form expression
-- `μ log (Trace (exp (X / μ)))`, use cyclicity of the trace to rewrite the Fréchet derivative as
-- the Frobenius pairing with the normalized exponential, and keep the derivative on the intrinsic
-- carrier `𝕊^n` so no separate symmetry side condition is needed.
/-- Proposition 6.36 (2): for `μ > 0`, the smoothed maximal eigenvalue is differentiable on
`𝕊^n`, and its Fréchet derivative in direction `H` is the Frobenius pairing with the normalized
matrix exponential. -/
theorem differentiableAt_logSumExpMaxEigenvalueSmoothing_and_fderiv_eq_frobeniusInner
    (μ : {μ : ℝ // 0 < μ}) (X : SymmMat) :
    DifferentiableAt ℝ (logSumExpMaxEigenvalueSmoothing μ) X ∧
      ∀ H : SymmMat,
        fderiv ℝ (logSumExpMaxEigenvalueSmoothing μ) X H =
          ⟪exponentialGradient μ X, H⟫_F := by
  by_cases hzero : n = 0
  · subst hzero
    constructor
    · -- In dimension `0`, the smoothing owner is the constant zero map.
      rw [logSumExpMaxEigenvalueSmoothing_eq_zero_dim (μ := μ)]
      simp
    · intro H
      -- The Fréchet derivative of a constant map and the Frobenius pairing on `𝕊^0` both vanish.
      rw [logSumExpMaxEigenvalueSmoothing_eq_zero_dim (μ := μ)]
      have hX : X = 0 := Subsingleton.elim _ _
      have hH : H = 0 := Subsingleton.elim _ _
      subst hX
      subst hH
      rw [RealSymmetricMatrixSpace.frobeniusInner_def]
      simp
  · have hn : 0 < n := Nat.pos_iff_ne_zero.mpr hzero
    have hderiv_trace :
        HasFDerivAt
          (logSumExpMaxEigenvalueSmoothing μ)
          ((((μ : ℝ) * (Matrix.trace (exp ((μ : ℝ)⁻¹ • (X : Mat))))⁻¹) •
              fderiv ℝ
                (fun Y : SymmMat ↦
                  Matrix.trace (exp ((μ : ℝ)⁻¹ • (Y : Mat)))) X) :
            StrongDual ℝ SymmMat)
          X := by
      -- Rewrite the smoothing owner into the stable trace/log presentation before using the
      -- already-packaged positive-branch derivative theorem.
      simpa [logSumExpMaxEigenvalueSmoothing_eq_matrixExponentialTrace_fun (n := n) μ] using
        (hasFDerivAt_matrixExponentialTrace_log_pos (n := n) hn μ X)
    constructor
    · -- The packaged gradient witness already certifies differentiability.
      exact hderiv_trace.differentiableAt
    · intro H
      -- Evaluate the Fréchet derivative and then rewrite it into the Frobenius pairing formula.
      rw [hderiv_trace.fderiv]
      exact trace_exp_scaled_fderiv_riesz_eq_exponentialGradient (n := n) μ X H

/-- Helper for Proposition 6.36: expanding the Chapter 5 Frobenius pairing in the
derivative formula recovers the textbook trace pairing with the normalized matrix exponential. -/
theorem differentiableAt_logSumExpMaxEigenvalueSmoothing_and_fderiv_eq_trace
    (μ : {μ : ℝ // 0 < μ}) (X : SymmMat) :
    DifferentiableAt ℝ (logSumExpMaxEigenvalueSmoothing μ) X ∧
      ∀ H : SymmMat,
        fderiv ℝ (logSumExpMaxEigenvalueSmoothing μ) X H =
          Matrix.trace ((H : Mat) * (exponentialGradient μ X : Mat)) := by
  rcases
      differentiableAt_logSumExpMaxEigenvalueSmoothing_and_fderiv_eq_frobeniusInner
        (n := n) μ X with
    ⟨hdiff, hderiv⟩
  constructor
  · exact hdiff
  · intro H
    -- Rewrite the intrinsic Frobenius pairing into the ambient trace formula from the textbook.
    rw [hderiv H, frobeniusInner_exponentialGradient_eq_trace_mul]

end
