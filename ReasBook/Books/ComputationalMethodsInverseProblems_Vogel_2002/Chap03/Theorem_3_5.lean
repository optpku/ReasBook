/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_1_1.Iterates
import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3
import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_4.ConditionNumber
import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Theorem_3_5.Error
import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_1.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Extr

noncomputable section

open scoped Matrix.Energy
open QuadraticOptimization

namespace Matrix.IsHermitian

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Helper for Theorem 3.5: every eigenvalue of a Hermitian real matrix lies in the
closed interval between `λ_min(A)` and `λ_max(A)`. -/
theorem eigenvalue_mem_Icc_lambdaMin_lambdaMax [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    λ_min(A) ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ λ_max(A) := by
  have hspectrum_bddBelow : BddBelow (spectrum ℝ A) := by
    simpa [hA.spectrum_real_eq_range_eigenvalues] using
      (Set.finite_range hA.eigenvalues).bddBelow
  have hspectrum_bddAbove : BddAbove (spectrum ℝ A) := by
    simpa [hA.spectrum_real_eq_range_eigenvalues] using
      (Set.finite_range hA.eigenvalues).bddAbove
  have hmem : hA.eigenvalues i ∈ spectrum ℝ A := hA.eigenvalues_mem_spectrum_real i
  constructor
  · -- The spectral infimum is a lower bound for every eigenvalue.
    simpa [Matrix.lambdaMin_eq_sInf_spectrum] using csInf_le hspectrum_bddBelow hmem
  · -- The spectral supremum is an upper bound for every eigenvalue.
    simpa [Matrix.lambdaMax_eq_sSup_spectrum] using le_csSup hspectrum_bddAbove hmem

/-- Helper for Theorem 3.5: in the orthonormal eigenbasis of a Hermitian matrix,
applying `A` multiplies the `i`-th coordinate by the `i`-th eigenvalue. -/
theorem repr_toEuclideanLin_eq_eigenvalue_mul_repr
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ n) (i : n) :
    (hA.eigenvectorBasis.repr (A.toEuclideanLin x)) i =
      hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) := by
  have hsymm : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have heig :
      A.toEuclideanLin (hA.eigenvectorBasis i) =
        hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext j
    simpa [Matrix.toEuclideanLin_apply] using congrFun (hA.mulVec_eigenvectorBasis i) j
  -- Move `A` onto the eigenvector basis element, then use the eigenvector equation.
  calc
    (hA.eigenvectorBasis.repr (A.toEuclideanLin x)) i
        = inner ℝ (hA.eigenvectorBasis i) (A.toEuclideanLin x) := by
            rw [OrthonormalBasis.repr_apply_apply]
    _ = inner ℝ (A.toEuclideanLin (hA.eigenvectorBasis i)) x := by
          symm
          exact hsymm (hA.eigenvectorBasis i) x
    _ = inner ℝ (hA.eigenvalues i • hA.eigenvectorBasis i) x := by rw [heig]
    _ = hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) := by
          rw [OrthonormalBasis.repr_apply_apply, real_inner_smul_left]

/-- Helper for Theorem 3.5: the quadratic form of a Hermitian real matrix is the
eigenvalue-weighted sum of squared coordinates in an orthonormal eigenbasis. -/
theorem inner_toEuclideanLin_eq_sum_eigenvalues_mul_sq_repr
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ n) :
    inner ℝ (A.toEuclideanLin x) x =
      ∑ i, hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) ^ 2 := by
  -- Expand the inner product in the orthonormal eigenbasis and collapse cross terms.
  calc
    inner ℝ (A.toEuclideanLin x) x =
        ∑ i,
          inner ℝ (A.toEuclideanLin x) (hA.eigenvectorBasis i) *
            inner ℝ (hA.eigenvectorBasis i) x := by
          symm
          simpa using hA.eigenvectorBasis.sum_inner_mul_inner (A.toEuclideanLin x) x
    _ =
        ∑ i,
          (hA.eigenvalues i * (hA.eigenvectorBasis.repr x i)) *
            (hA.eigenvectorBasis.repr x i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hcoord :
              inner ℝ (hA.eigenvectorBasis i) (A.toEuclideanLin x) =
                hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) := by
            calc
              inner ℝ (hA.eigenvectorBasis i) (A.toEuclideanLin x)
                  = (hA.eigenvectorBasis.repr (A.toEuclideanLin x)) i := by
                      rw [OrthonormalBasis.repr_apply_apply]
              _ = hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) :=
                    hA.repr_toEuclideanLin_eq_eigenvalue_mul_repr x i
          rw [real_inner_comm, hcoord, OrthonormalBasis.repr_apply_apply]
    _ = ∑ i, hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring

end Matrix.IsHermitian

namespace SteepestDescent

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Helper for Theorem 3.5: a steepest-descent update is exactly the affine step
`f + τ • direction J f`. -/
theorem update_eq_add_smul_direction
    (J : EuclideanSpace ℝ n → ℝ) (τ : ℝ) (f : EuclideanSpace ℝ n) :
    update J τ f = f + τ • direction J f := by
  -- Route correction: in the non-`module` file form, reuse the owner equation theorem directly.
  simpa using SteepestDescent.update.eq_1 J τ f

/-- Helper for Theorem 3.5: evaluating the line-search profile along the steepest-descent
direction is the same as evaluating the objective after the steepest-descent update. -/
theorem profileDirection_apply_eq_update
    (J : EuclideanSpace ℝ n → ℝ) (f : EuclideanSpace ℝ n) (τ : ℝ) :
    LineSearch.profile J f (direction J f) τ = J (update J τ f) := by
  -- Route correction: normalize both sides to the shared affine-step spelling once.
  simp [LineSearch.profile_apply, SteepestDescent.update_eq_add_smul_direction]

/-- Helper for Theorem 3.5: the quadratic gradient is the matrix image of the
error from the minimizer. -/
theorem gradient_eq_errorImage
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    gradient (quadraticFunctional c b A) f =
      A.toEuclideanLin (QuadraticOptimization.error A b f) := by
  -- Rewrite the gradient using the explicit quadratic formula.
  rw [QuadraticOptimization.gradient_quadraticFunctional c b A]
  · -- Then translate the affine term using the minimizer equation `A f⋆ = -b`.
    rw [QuadraticOptimization.error_eq_sub, LinearMap.map_sub]
    have hcrit :
        A.toEuclideanLin (quadraticFunctionalMinimizer b A) = -b := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_comm] using
        QuadraticOptimization.quadraticFunctionalMinimizer_isCriticalPoint b A hA
    simp [hcrit, sub_eq_add_neg, add_comm]
  · simpa using hA.isHermitian

/-- Helper for Theorem 3.5: the quadratic objective gap equals half the square
of the `A`-energy error. -/
theorem quadraticGap_eq_half_energyNormError_sq
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    quadraticFunctional c b A f =
      quadraticFunctional c b A (quadraticFunctionalMinimizer b A) +
        (1 / 2 : ℝ) * (energyNormError A b hA f) ^ 2 := by
  -- Express `f` as the minimizer plus the current error vector.
  have hf :
      f = quadraticFunctionalMinimizer b A + QuadraticOptimization.error A b f := by
    rw [QuadraticOptimization.error_eq_sub]
    abel
  have hinner_nonneg :
      0 ≤
        inner ℝ
          (A.toEuclideanLin (QuadraticOptimization.error A b f))
          (QuadraticOptimization.error A b f) :=
    Matrix.inner_toEuclideanLin_nonneg_of_posSemidef _ hA.posSemidef _
  have hsq :
      (energyNormError A b hA f) ^ 2 =
        inner ℝ
          (A.toEuclideanLin (QuadraticOptimization.error A b f))
          (QuadraticOptimization.error A b f) := by
    -- Rewrite the square of the energy norm as the quadratic form defined by `A`.
    rw [QuadraticOptimization.energyNormError_eq, Matrix.energyNorm_eq_sqrt_energyInner,
      Matrix.energyInner_eq, Real.sq_sqrt hinner_nonneg]
  -- Now apply the quadratic-translation identity at the critical point.
  calc
    quadraticFunctional c b A f =
        quadraticFunctional c b A
          (quadraticFunctionalMinimizer b A + QuadraticOptimization.error A b f) := by
          simpa using congrArg (quadraticFunctional c b A) hf
    _ =
        quadraticFunctional c b A (quadraticFunctionalMinimizer b A) +
          (1 / 2 : ℝ) *
            inner ℝ
              (A.toEuclideanLin (QuadraticOptimization.error A b f))
              (QuadraticOptimization.error A b f) := by
          simpa using
            QuadraticOptimization.quadraticFunctional_translate_eq_base_add_half_inner
              c b A (by simpa using hA.isHermitian)
              (f0 := quadraticFunctionalMinimizer b A)
              (h := QuadraticOptimization.error A b f)
              (QuadraticOptimization.quadraticFunctionalMinimizer_isCriticalPoint b A hA)
    _ =
        quadraticFunctional c b A (quadraticFunctionalMinimizer b A) +
          (1 / 2 : ℝ) * (energyNormError A b hA f) ^ 2 := by
          rw [hsq]

/-- Helper for Theorem 3.5: the Euclidean error is controlled by the reciprocal
square root of the smallest spectral value times the `A`-energy error. -/
theorem normError_le_invSqrtSpectralInf_mul_energyNormError
    (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) [Nonempty n] (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    ‖QuadraticOptimization.error A b f‖ ≤
      (Real.sqrt (sInf (spectrum ℝ A)))⁻¹ * energyNormError A b hA f := by
  have hsinf_pos : 0 < sInf (spectrum ℝ A) := by
    simpa [Matrix.lambdaMin_eq_sInf_spectrum] using Matrix.lambdaMin_pos_of_posDef A hA
  have hsqrt_pos : 0 < Real.sqrt (sInf (spectrum ℝ A)) :=
    Real.sqrt_pos.mpr hsinf_pos
  -- Divide the standard lower energy-norm bound by `sqrt (λ_min(A))`.
  rw [QuadraticOptimization.energyNormError_eq]
  exact (le_inv_mul_iff₀ hsqrt_pos).2 <|
    Matrix.energyNorm_lowerBound A hA (QuadraticOptimization.error A b f)

/-- Helper for Theorem 3.5: the closed-form exact step drops the squared
`A`-energy error by the expected quartic-over-cubic quotient. -/
theorem candidateExactStep_energyNormSq_eq_drop
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    let g := b + A.toEuclideanLin f
    let αStar := ‖g‖ ^ 2 / inner ℝ (A.toEuclideanLin g) g
    (energyNormError A b hA (update (quadraticFunctional c b A) αStar f)) ^ 2 =
      (energyNormError A b hA f) ^ 2 - ‖g‖ ^ 4 / inner ℝ (A.toEuclideanLin g) g := by
  -- Route correction: the fixed-step proof was replaced by a direct exact-step identity.
  -- Split off the zero-gradient branch so that all division terms collapse definitionally.
  dsimp
  set g : EuclideanSpace ℝ n := b + A.toEuclideanLin f
  set αStar : ℝ := ‖g‖ ^ 2 / inner ℝ (A.toEuclideanLin g) g
  by_cases hg : g = 0
  · -- When `g = 0`, the candidate step is `0` and the update is the identity.
    have hgrad_zero : gradient (quadraticFunctional c b A) f = 0 := by
      simpa [g] using
        (QuadraticOptimization.gradient_quadraticFunctional c b A
          (by simpa using hA.isHermitian) f).trans hg
    rw [SteepestDescent.update_eq_sub_smul_gradient, hgrad_zero]
    simp [g, αStar, hg]
  · -- In the nonzero branch, evaluate the profile at `αStar` and compare quadratic gaps.
    have hden_pos : 0 < inner ℝ (A.toEuclideanLin g) g := by
      -- Positive definiteness makes the cubic denominator strictly positive.
      simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply] using
        hA.dotProduct_mulVec_pos (x := g.ofLp) (by simpa using hg)
    have hden_ne : inner ℝ (A.toEuclideanLin g) g ≠ 0 := hden_pos.ne'
    have hprofile_eval :
        quadraticFunctional c b A (update (quadraticFunctional c b A) αStar f) =
          quadraticFunctional c b A f - αStar * ‖g‖ ^ 2 +
            (1 / 2 : ℝ) * αStar ^ 2 * inner ℝ (A.toEuclideanLin g) g := by
      -- Rewrite the update as the line-search profile along the negative gradient.
      calc
        quadraticFunctional c b A (update (quadraticFunctional c b A) αStar f) =
            LineSearch.profile (quadraticFunctional c b A) f (-g) αStar := by
              rw [LineSearch.profile_apply, SteepestDescent.update_eq_sub_smul_gradient,
                QuadraticOptimization.gradient_quadraticFunctional c b A
                  (by simpa using hA.isHermitian) f]
              simp [g, sub_eq_add_neg]
        _ = quadraticFunctional c b A f - αStar * ‖g‖ ^ 2 +
              (1 / 2 : ℝ) * αStar ^ 2 * inner ℝ (A.toEuclideanLin g) g := by
              simpa [g, αStar] using
                congrArg (fun φ : ℝ → ℝ => φ αStar)
                  (QuadraticOptimization.profile_quadraticFunctional_negGradient c b A
                    (by simpa using hA.isHermitian) f)
    have hprofile_drop :
        quadraticFunctional c b A (update (quadraticFunctional c b A) αStar f) =
          quadraticFunctional c b A f -
            (1 / 2 : ℝ) * (‖g‖ ^ 4 / inner ℝ (A.toEuclideanLin g) g) := by
      -- Substitute the explicit candidate step and simplify the resulting rational expression.
      simp [αStar] at hprofile_eval ⊢
      field_simp [hden_ne, pow_two] at hprofile_eval ⊢
      nlinarith
    have hgap_update :=
      quadraticGap_eq_half_energyNormError_sq c b A hA
        (update (quadraticFunctional c b A) αStar f)
    have hgap_f := quadraticGap_eq_half_energyNormError_sq c b A hA f
    -- The gap identity at `f` and at the updated point gives the claimed energy drop formula.
    nlinarith [hgap_update, hgap_f, hprofile_drop]

/-- Helper for Theorem 3.5: applying `A⁻¹` to the error image recovers the
original error, so the inverse-side quadratic form is exactly the squared
`A`-energy error. -/
theorem invErrorImageInner_eq_energyNormSq
    (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    inner ℝ
      ((A⁻¹).toEuclideanLin (A.toEuclideanLin (QuadraticOptimization.error A b f)))
      (A.toEuclideanLin (QuadraticOptimization.error A b f)) =
      (energyNormError A b hA f) ^ 2 := by
  let e : EuclideanSpace ℝ n := QuadraticOptimization.error A b f
  have hA_det : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hinv :
      (A⁻¹).toEuclideanLin (A.toEuclideanLin e) = e := by
    -- Reduce the inverse action to the matrix identity `A⁻¹ * A = 1`.
    calc
      (A⁻¹).toEuclideanLin (A.toEuclideanLin e)
          = ((A⁻¹ * A).toEuclideanLin e) := by
              simp [e, Matrix.toEuclideanLin, Matrix.mulVec_mulVec]
      _ = (1 : Matrix n n ℝ).toEuclideanLin e := by rw [Matrix.nonsing_inv_mul A hA_det]
      _ = e := by simp [e, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have hinner_nonneg :
      0 ≤ inner ℝ (A.toEuclideanLin e) e :=
    Matrix.inner_toEuclideanLin_nonneg_of_posSemidef _ hA.posSemidef _
  have hsq :
      (energyNormError A b hA f) ^ 2 =
        inner ℝ (A.toEuclideanLin e) e := by
    -- Rewrite the energy norm square as the `A`-quadratic form on the error.
    rw [QuadraticOptimization.energyNormError_eq, Matrix.energyNorm_eq_sqrt_energyInner,
      Matrix.energyInner_eq, Real.sq_sqrt hinner_nonneg]
  -- Commute the real inner product after cancelling `A⁻¹A`.
  calc
    inner ℝ ((A⁻¹).toEuclideanLin (A.toEuclideanLin e)) (A.toEuclideanLin e)
        = inner ℝ e (A.toEuclideanLin e) := by rw [hinv]
    _ = inner ℝ (A.toEuclideanLin e) e := by rw [real_inner_comm]
    _ = (energyNormError A b hA f) ^ 2 := hsq.symm

/-- Helper for Theorem 3.5: in the Hermitian eigenbasis, the fixed comparison
step scales each error coordinate by `1 - β * λᵢ`. -/
theorem comparisonStepErrorCoord
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) [Nonempty n] (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) (i : n) :
    let β : ℝ := (2 : ℝ) / (Matrix.lambdaMin A + Matrix.lambdaMax A)
    (hA.isHermitian.eigenvectorBasis.repr
      (QuadraticOptimization.error A b
        (update (quadraticFunctional c b A) β f))) i =
      (1 - β * hA.isHermitian.eigenvalues i) *
        (hA.isHermitian.eigenvectorBasis.repr (QuadraticOptimization.error A b f) i) := by
  let β : ℝ := (2 : ℝ) / (Matrix.lambdaMin A + Matrix.lambdaMax A)
  let e : EuclideanSpace ℝ n := QuadraticOptimization.error A b f
  have herror_update :
      QuadraticOptimization.error A b (update (quadraticFunctional c b A) β f) =
        e - β • A.toEuclideanLin e := by
    -- Rewrite the updated error through the gradient-image identity.
    rw [QuadraticOptimization.error_eq_sub, SteepestDescent.update_eq_sub_smul_gradient,
      gradient_eq_errorImage c b A hA f]
    simpa [e, QuadraticOptimization.error_eq_sub, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]
  -- Apply the eigenbasis coordinate map to the affine error update.
  calc
    (hA.isHermitian.eigenvectorBasis.repr
      (QuadraticOptimization.error A b (update (quadraticFunctional c b A) β f))) i
        = ((hA.isHermitian.eigenvectorBasis.repr e) i) -
            β * ((hA.isHermitian.eigenvectorBasis.repr (A.toEuclideanLin e)) i) := by
            rw [herror_update]
            simp
    _ = ((hA.isHermitian.eigenvectorBasis.repr e) i) -
          β * (hA.isHermitian.eigenvalues i *
            ((hA.isHermitian.eigenvectorBasis.repr e) i)) := by
          rw [hA.isHermitian.repr_toEuclideanLin_eq_eigenvalue_mul_repr]
    _ = (1 - β * hA.isHermitian.eigenvalues i) *
          (hA.isHermitian.eigenvectorBasis.repr e i) := by
          ring

/-- Helper for Theorem 3.5: every spectral factor of the comparison step is
bounded by the sharp interval ratio. -/
theorem comparisonFactor_sq_le_of_mem_interval
    (A : Matrix n n ℝ) [Nonempty n] (hA : A.PosDef) {lam : ℝ}
    (hlam_min : Matrix.lambdaMin A ≤ lam) (hlam_max : lam ≤ Matrix.lambdaMax A) :
    let β : ℝ := (2 : ℝ) / (Matrix.lambdaMin A + Matrix.lambdaMax A)
    (1 - β * lam) ^ 2 ≤
      (((Matrix.lambdaMax A - Matrix.lambdaMin A) /
        (Matrix.lambdaMax A + Matrix.lambdaMin A)) ^ 2) := by
  let m : ℝ := Matrix.lambdaMin A
  let M : ℝ := Matrix.lambdaMax A
  let β : ℝ := (2 : ℝ) / (m + M)
  have hm_pos : 0 < m := by
    simpa [m] using Matrix.lambdaMin_pos_of_posDef A hA
  have hM_pos : 0 < M := by
    simpa [M] using Matrix.lambdaMax_pos_of_posDef A hA
  have hden_pos : 0 < m + M := add_pos hm_pos hM_pos
  have hnum_sq :
      (m + M - 2 * lam) ^ 2 ≤ (M - m) ^ 2 := by
    nlinarith
  have hdiv :
      (m + M - 2 * lam) ^ 2 / (m + M) ^ 2 ≤
        (M - m) ^ 2 / (m + M) ^ 2 := by
    exact div_le_div_of_nonneg_right hnum_sq (sq_nonneg (m + M))
  have hleft :
      (1 - β * lam) ^ 2 = (m + M - 2 * lam) ^ 2 / (m + M) ^ 2 := by
    have hbase : 1 - β * lam = (m + M - 2 * lam) / (m + M) := by
      dsimp [β]
      field_simp [hden_pos.ne']
    rw [hbase, div_pow]
  have hright :
      (((Matrix.lambdaMax A - Matrix.lambdaMin A) /
          (Matrix.lambdaMax A + Matrix.lambdaMin A)) ^ 2) =
        (M - m) ^ 2 / (m + M) ^ 2 := by
    simp [m, M, add_comm, div_pow]
  -- Normalize both sides to the same denominator and apply the interval inequality.
  have htarget :
      (1 - β * lam) ^ 2 ≤
        (((Matrix.lambdaMax A - Matrix.lambdaMin A) /
          (Matrix.lambdaMax A + Matrix.lambdaMin A)) ^ 2) := by
    rw [hleft, hright]
    exact hdiv
  simpa [β] using htarget

/-- Helper for Theorem 3.5: the fixed step `β = 2 / (λ_min(A) + λ_max(A))`
contracts the squared `A`-energy error by the sharp spectral factor
`((λ_max(A) - λ_min(A)) / (λ_max(A) + λ_min(A))) ^ 2`. -/
theorem comparisonStep_energyNormSq_le_spectralRatioSq
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) [Nonempty n] (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    (energyNormError A b hA
        (update (quadraticFunctional c b A)
          ((2 : ℝ) / (Matrix.lambdaMin A + Matrix.lambdaMax A)) f)) ^ 2 ≤
      ((((Matrix.lambdaMax A - Matrix.lambdaMin A) /
          (Matrix.lambdaMax A + Matrix.lambdaMin A)) ^ 2)) *
        (energyNormError A b hA f) ^ 2 := by
  let β : ℝ := (2 : ℝ) / (Matrix.lambdaMin A + Matrix.lambdaMax A)
  let ρ : ℝ :=
    (Matrix.lambdaMax A - Matrix.lambdaMin A) /
      (Matrix.lambdaMax A + Matrix.lambdaMin A)
  let e : EuclideanSpace ℝ n := QuadraticOptimization.error A b f
  let e' : EuclideanSpace ℝ n :=
    QuadraticOptimization.error A b (update (quadraticFunctional c b A) β f)
  have hold_nonneg :
      0 ≤ inner ℝ (A.toEuclideanLin e) e :=
    Matrix.inner_toEuclideanLin_nonneg_of_posSemidef _ hA.posSemidef _
  have hnew_nonneg :
      0 ≤ inner ℝ (A.toEuclideanLin e') e' :=
    Matrix.inner_toEuclideanLin_nonneg_of_posSemidef _ hA.posSemidef _
  have hsq_old :
      (energyNormError A b hA f) ^ 2 = inner ℝ (A.toEuclideanLin e) e := by
    -- Rewrite the old squared energy norm as the quadratic form of the error vector.
    simpa [e] using
      (by
        rw [QuadraticOptimization.energyNormError_eq, Matrix.energyNorm_eq_sqrt_energyInner,
          Matrix.energyInner_eq, Real.sq_sqrt hold_nonneg] :
          (energyNormError A b hA f) ^ 2 =
            inner ℝ
              (A.toEuclideanLin (QuadraticOptimization.error A b f))
              (QuadraticOptimization.error A b f))
  have hsq_new :
      (energyNormError A b hA (update (quadraticFunctional c b A) β f)) ^ 2 =
        inner ℝ (A.toEuclideanLin e') e' := by
    -- Rewrite the updated squared energy norm through the same quadratic form.
    simpa [e'] using
      (by
        rw [QuadraticOptimization.energyNormError_eq, Matrix.energyNorm_eq_sqrt_energyInner,
          Matrix.energyInner_eq, Real.sq_sqrt hnew_nonneg] :
          (energyNormError A b hA (update (quadraticFunctional c b A) β f)) ^ 2 =
            inner ℝ
              (A.toEuclideanLin
                (QuadraticOptimization.error A b
                  (update (quadraticFunctional c b A) β f)))
              (QuadraticOptimization.error A b
                (update (quadraticFunctional c b A) β f)))
  -- Compare the eigenbasis expansion termwise using the sharp scalar interval bound.
  calc
    (energyNormError A b hA (update (quadraticFunctional c b A) β f)) ^ 2
        = inner ℝ (A.toEuclideanLin e') e' := hsq_new
    _ = ∑ i, hA.isHermitian.eigenvalues i *
          (hA.isHermitian.eigenvectorBasis.repr e' i) ^ 2 := by
          rw [hA.isHermitian.inner_toEuclideanLin_eq_sum_eigenvalues_mul_sq_repr]
    _ = ∑ i, hA.isHermitian.eigenvalues i *
          (((1 - β * hA.isHermitian.eigenvalues i) *
              (hA.isHermitian.eigenvectorBasis.repr e i)) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [comparisonStepErrorCoord c b A hA f i]
    _ ≤ ∑ i, ρ ^ 2 *
          (hA.isHermitian.eigenvalues i *
            (hA.isHermitian.eigenvectorBasis.repr e i) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hi_bounds :=
            Matrix.IsHermitian.eigenvalue_mem_Icc_lambdaMin_lambdaMax hA.isHermitian i
          have hi_nonneg :
              0 ≤ hA.isHermitian.eigenvalues i *
                (hA.isHermitian.eigenvectorBasis.repr e i) ^ 2 := by
            have heig_nonneg :
                0 ≤ hA.isHermitian.eigenvalues i := by
              exact le_trans (le_of_lt (Matrix.lambdaMin_pos_of_posDef A hA)) hi_bounds.1
            exact mul_nonneg heig_nonneg (sq_nonneg _)
          have hfactor :
              (1 - β * hA.isHermitian.eigenvalues i) ^ 2 ≤ ρ ^ 2 := by
            simpa [β, ρ] using
              comparisonFactor_sq_le_of_mem_interval A hA hi_bounds.1 hi_bounds.2
          nlinarith [hfactor, hi_nonneg]
    _ = ρ ^ 2 *
          ∑ i, hA.isHermitian.eigenvalues i *
            (hA.isHermitian.eigenvectorBasis.repr e i) ^ 2 := by
          rw [← Finset.mul_sum]
    _ = ρ ^ 2 * inner ℝ (A.toEuclideanLin e) e := by
          rw [← hA.isHermitian.inner_toEuclideanLin_eq_sum_eigenvalues_mul_sq_repr]
    _ = ρ ^ 2 * (energyNormError A b hA f) ^ 2 := by
          rw [hsq_old]
    _ = ((((Matrix.lambdaMax A - Matrix.lambdaMin A) /
            (Matrix.lambdaMax A + Matrix.lambdaMin A)) ^ 2)) *
          (energyNormError A b hA f) ^ 2 := by
          simp [ρ]

/-- Helper for Theorem 3.5: the closed-form exact step satisfies the sharp
condition-number bound at the squared energy level. -/
theorem candidateExactStep_energyNormSq_le_conditionRatioSq
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) [Nonempty n] (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    let g := b + A.toEuclideanLin f
    let αStar := ‖g‖ ^ 2 / inner ℝ (A.toEuclideanLin g) g
    (energyNormError A b hA (update (quadraticFunctional c b A) αStar f)) ^ 2 ≤
      ((((A.posDefConditionNumber hA) - 1) / ((A.posDefConditionNumber hA) + 1)) ^ 2) *
        (energyNormError A b hA f) ^ 2 := by
  let g : EuclideanSpace ℝ n := b + A.toEuclideanLin f
  let αStar : ℝ := ‖g‖ ^ 2 / inner ℝ (A.toEuclideanLin g) g
  let β : ℝ := (2 : ℝ) / (Matrix.lambdaMin A + Matrix.lambdaMax A)
  let ρ : ℝ :=
    (Matrix.lambdaMax A - Matrix.lambdaMin A) /
      (Matrix.lambdaMax A + Matrix.lambdaMin A)
  by_cases hg : g = 0
  · -- If the gradient vanishes, the current iterate is already the minimizer.
    have hgrad_zero : gradient (quadraticFunctional c b A) f = 0 := by
      simpa [g] using
        (QuadraticOptimization.gradient_quadraticFunctional c b A
          (by simpa using hA.isHermitian) f).trans hg
    have herrorImage_zero :
        A.toEuclideanLin (QuadraticOptimization.error A b f) = 0 := by
      rw [← gradient_eq_errorImage c b A hA f]
      exact hgrad_zero
    have henergy_sq_zero : (energyNormError A b hA f) ^ 2 = 0 := by
      have hbridge := invErrorImageInner_eq_energyNormSq b A hA f
      simpa [herrorImage_zero] using hbridge.symm
    have henergy_zero : energyNormError A b hA f = 0 := sq_eq_zero_iff.mp henergy_sq_zero
    -- Unfold the theorem-local lets and collapse the zero-gradient update.
    simpa [g, αStar, hg, henergy_zero, SteepestDescent.update_eq_sub_smul_gradient, hgrad_zero]
  · -- Otherwise the exact profile minimizer beats the positive comparison step `β`.
    have hupdate_eq (τ : ℝ) :
        update (quadraticFunctional c b A) τ f = f + τ • (-g) := by
      -- Expose the update using the explicit negative-gradient direction `-g`.
      rw [SteepestDescent.update_eq_sub_smul_gradient,
        QuadraticOptimization.gradient_quadraticFunctional c b A
          (by simpa using hA.isHermitian) f]
      simp [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hden_pos : 0 < inner ℝ (A.toEuclideanLin g) g := by
      -- Positive definiteness makes the exact-step denominator strictly positive.
      simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply] using
        hA.dotProduct_mulVec_pos (x := g.ofLp) (by simpa using hg)
    have hαStar_pos : 0 < αStar := by
      -- The exact candidate step is positive because both numerator and denominator are.
      have hnum_pos : 0 < ‖g‖ ^ 2 := by
        have hnorm_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg
        nlinarith
      exact div_pos hnum_pos hden_pos
    have hβ_pos : 0 < β := by
      -- The comparison step uses the positive spectral denominator `λ_min(A) + λ_max(A)`.
      have hm_pos : 0 < Matrix.lambdaMin A := Matrix.lambdaMin_pos_of_posDef A hA
      have hM_pos : 0 < Matrix.lambdaMax A := Matrix.lambdaMax_pos_of_posDef A hA
      exact div_pos zero_lt_two (add_pos hm_pos hM_pos)
    have hαStar_min :
        IsMinOn
          (LineSearch.profile (quadraticFunctional c b A) f (-g))
          (Set.Ioi (0 : ℝ))
          αStar := by
      -- Reuse the closed-form exact line-search minimizer for the quadratic profile.
      simpa [g, αStar] using
        QuadraticOptimization.exactLineSearchStep_quadraticFunctional c b A hA f
    have hobjective_compare :
        quadraticFunctional c b A (update (quadraticFunctional c b A) αStar f) ≤
          quadraticFunctional c b A (update (quadraticFunctional c b A) β f) := by
      -- Evaluate the exact minimizer property at the positive comparison step `β`.
      rw [isMinOn_iff] at hαStar_min
      have hprofile_compare := hαStar_min β hβ_pos
      simpa [LineSearch.profile_apply, hupdate_eq αStar, hupdate_eq β] using hprofile_compare
    have hgap_αStar :=
      quadraticGap_eq_half_energyNormError_sq c b A hA
        (update (quadraticFunctional c b A) αStar f)
    have hgap_β :=
      quadraticGap_eq_half_energyNormError_sq c b A hA
        (update (quadraticFunctional c b A) β f)
    have hsq_compare :
        (energyNormError A b hA (update (quadraticFunctional c b A) αStar f)) ^ 2 ≤
          (energyNormError A b hA (update (quadraticFunctional c b A) β f)) ^ 2 := by
      -- Convert the objective comparison into a squared energy comparison.
      linarith [hobjective_compare, hgap_αStar, hgap_β]
    have hsq_beta :
        (energyNormError A b hA (update (quadraticFunctional c b A) β f)) ^ 2 ≤
          (ρ ^ 2) * (energyNormError A b hA f) ^ 2 := by
      -- Apply the fixed-step spectral contraction at the comparison step `β`.
      simpa [β, ρ] using
        comparisonStep_energyNormSq_le_spectralRatioSq c b A hA f
    have hκ_eq :
        A.posDefConditionNumber hA = Matrix.lambdaMax A / Matrix.lambdaMin A := by
      rw [Matrix.posDefConditionNumber_eq_spectralExtrema, Matrix.lambdaMax_eq_sSup_spectrum,
        Matrix.lambdaMin_eq_sInf_spectrum]
    have hm_pos : 0 < Matrix.lambdaMin A := Matrix.lambdaMin_pos_of_posDef A hA
    have hratio_base :
        ρ =
          ((A.posDefConditionNumber hA) - 1) / ((A.posDefConditionNumber hA) + 1) := by
      rw [hκ_eq]
      field_simp [ρ, hm_pos.ne']
      ring
    -- Combine exact-step optimality with the fixed-step contraction and rewrite the factor.
    calc
      (energyNormError A b hA (update (quadraticFunctional c b A) αStar f)) ^ 2
          ≤ (energyNormError A b hA (update (quadraticFunctional c b A) β f)) ^ 2 :=
            hsq_compare
      _ ≤ (ρ ^ 2) * (energyNormError A b hA f) ^ 2 := hsq_beta
      _ =
          ((((A.posDefConditionNumber hA) - 1) / ((A.posDefConditionNumber hA) + 1)) ^ 2) *
            (energyNormError A b hA f) ^ 2 := by
            rw [hratio_base]

theorem exactLineSearch_oneStep_energyNormError_le
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) [Nonempty n] (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) (α : ℝ)
    (hα : IsMinOn
      (LineSearch.profile
        (quadraticFunctional c b A)
        f
        (direction (quadraticFunctional c b A) f))
      (Set.Ioi (0 : ℝ))
      α) :
    energyNormError A b hA (update (quadraticFunctional c b A) α f) ≤
      (((A.posDefConditionNumber hA) - 1) / ((A.posDefConditionNumber hA) + 1)) *
        energyNormError A b hA f := by
  -- Route correction: compare the exact line-search profile directly at `αStar`,
  -- then rewrite the profile values through the update bridge.
  let g : EuclideanSpace ℝ n := b + A.toEuclideanLin f
  let q : ℝ := ((A.posDefConditionNumber hA - 1) / ((A.posDefConditionNumber hA) + 1))
  by_cases hg : g = 0
  · -- When the gradient vanishes, the iterate is already the minimizer and the update is trivial.
    have hgrad_zero : gradient (quadraticFunctional c b A) f = 0 := by
      simpa [g] using
        (QuadraticOptimization.gradient_quadraticFunctional c b A
          (by simpa using hA.isHermitian) f).trans hg
    have herrorImage_zero :
        A.toEuclideanLin (QuadraticOptimization.error A b f) = 0 := by
      rw [← gradient_eq_errorImage c b A hA f]
      exact hgrad_zero
    have henergy_sq_zero : (energyNormError A b hA f) ^ 2 = 0 := by
      have hbridge := invErrorImageInner_eq_energyNormSq b A hA f
      simpa [herrorImage_zero] using hbridge.symm
    have henergy_zero : energyNormError A b hA f = 0 := sq_eq_zero_iff.mp henergy_sq_zero
    rw [SteepestDescent.update_eq_sub_smul_gradient, hgrad_zero]
    simp [henergy_zero]
  · -- In the nonzero branch, compare the exact line search with the explicit quadratic minimizer.
    let αStar : ℝ := ‖g‖ ^ 2 / inner ℝ (A.toEuclideanLin g) g
    have hden_pos : 0 < inner ℝ (A.toEuclideanLin g) g := by
      -- Positive definiteness keeps the cubic denominator strictly positive away from `g = 0`.
      simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply] using
        hA.dotProduct_mulVec_pos (x := g.ofLp) (by simpa using hg)
    have hαStar_pos : 0 < αStar := by
      -- The explicit candidate step is positive because both numerator and denominator are.
      have hnum_pos : 0 < ‖g‖ ^ 2 := by
        have hnorm_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg
        nlinarith
      exact div_pos hnum_pos hden_pos
    have hobjective_compare :
        quadraticFunctional c b A (update (quadraticFunctional c b A) α f) ≤
          quadraticFunctional c b A (update (quadraticFunctional c b A) αStar f) := by
      -- Evaluate the exact-line-search hypothesis directly at the positive candidate `αStar`.
      rw [isMinOn_iff] at hα
      have hprofile_compare := hα αStar hαStar_pos
      simpa [SteepestDescent.profileDirection_apply_eq_update] using hprofile_compare
    have hgap_α :=
      quadraticGap_eq_half_energyNormError_sq c b A hA
        (update (quadraticFunctional c b A) α f)
    have hgap_αStar :=
      quadraticGap_eq_half_energyNormError_sq c b A hA
        (update (quadraticFunctional c b A) αStar f)
    have hsq_compare :
        (energyNormError A b hA (update (quadraticFunctional c b A) α f)) ^ 2 ≤
          (energyNormError A b hA (update (quadraticFunctional c b A) αStar f)) ^ 2 := by
      -- Subtract the common minimum objective value and clear the factor `1/2`.
      linarith [hobjective_compare, hgap_α, hgap_αStar]
    have hsq_candidate :
        (energyNormError A b hA (update (quadraticFunctional c b A) αStar f)) ^ 2 ≤
          (q ^ 2) * (energyNormError A b hA f) ^ 2 := by
      -- Invoke the sharp squared contraction already proved for the explicit candidate step.
      simpa [g, q, αStar] using
        candidateExactStep_energyNormSq_le_conditionRatioSq c b A hA f
    have hsinf_pos : 0 < sInf (spectrum ℝ A) := by
      simpa [Matrix.lambdaMin_eq_sInf_spectrum] using Matrix.lambdaMin_pos_of_posDef A hA
    have hsup_pos : 0 < sSup (spectrum ℝ A) := by
      simpa [Matrix.lambdaMax_eq_sSup_spectrum] using Matrix.lambdaMax_pos_of_posDef A hA
    have hspectrum_nonempty : (spectrum ℝ A).Nonempty := by
      simpa using Matrix.realSpectrum_nonempty A hA.isHermitian
    have hspectrum_bddBelow : BddBelow (spectrum ℝ A) := by
      simpa [hA.isHermitian.spectrum_real_eq_range_eigenvalues] using
        (Set.finite_range hA.isHermitian.eigenvalues).bddBelow
    have hspectrum_bddAbove : BddAbove (spectrum ℝ A) := by
      simpa [hA.isHermitian.spectrum_real_eq_range_eigenvalues] using
        (Set.finite_range hA.isHermitian.eigenvalues).bddAbove
    have hsinf_le_hsup : sInf (spectrum ℝ A) ≤ sSup (spectrum ℝ A) :=
      csInf_le_csSup hspectrum_nonempty hspectrum_bddBelow hspectrum_bddAbove
    have hκ_eq :
        A.posDefConditionNumber hA = sSup (spectrum ℝ A) / sInf (spectrum ℝ A) := by
      simpa using Matrix.posDefConditionNumber_eq_spectralExtrema A hA
    have hκ_ge_one : 1 ≤ A.posDefConditionNumber hA := by
      rw [hκ_eq]
      exact (one_le_div hsinf_pos).2 hsinf_le_hsup
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      have hden_pos : 0 < A.posDefConditionNumber hA + 1 := by
        have hκ_pos : 0 < A.posDefConditionNumber hA := by
          rw [hκ_eq]
          exact div_pos hsup_pos hsinf_pos
        linarith
      exact div_nonneg (sub_nonneg.mpr hκ_ge_one) hden_pos.le
    have hsq_target :
        (energyNormError A b hA (update (quadraticFunctional c b A) α f)) ^ 2 ≤
          (q * energyNormError A b hA f) ^ 2 := by
      -- Combine the squared comparison with the candidate-step contraction, then regroup.
      calc
        (energyNormError A b hA (update (quadraticFunctional c b A) α f)) ^ 2
            ≤ (q ^ 2) * (energyNormError A b hA f) ^ 2 :=
              le_trans hsq_compare hsq_candidate
        _ = (q * energyNormError A b hA f) ^ 2 := by ring
    have hleft_nonneg :
        0 ≤ energyNormError A b hA (update (quadraticFunctional c b A) α f) :=
      by
        rw [QuadraticOptimization.energyNormError_eq, Matrix.energyNorm_eq_sqrt_energyInner]
        exact Real.sqrt_nonneg _
    have hright_nonneg : 0 ≤ q * energyNormError A b hA f :=
      by
        rw [QuadraticOptimization.energyNormError_eq, Matrix.energyNorm_eq_sqrt_energyInner]
        exact mul_nonneg hq_nonneg (Real.sqrt_nonneg _)
    -- Unsquare the comparison once, using nonnegativity of both energy norms.
    exact (sq_le_sq₀ hleft_nonneg hright_nonneg).mp hsq_target

/-- Helper for Theorem 3.5: the condition-number contraction factor is
nonnegative and strictly less than `1`. -/
theorem conditionRatio_nonneg_lt_one
    (A : Matrix n n ℝ) [Nonempty n] (hA : A.PosDef) :
    0 ≤ ((A.posDefConditionNumber hA - 1) / (A.posDefConditionNumber hA + 1)) ∧
      ((A.posDefConditionNumber hA - 1) / (A.posDefConditionNumber hA + 1)) < 1 := by
  let κ := A.posDefConditionNumber hA
  have hspectrum_nonempty : (spectrum ℝ A).Nonempty := by
    simpa using Matrix.realSpectrum_nonempty A hA.isHermitian
  have hsinf_pos : 0 < sInf (spectrum ℝ A) := by
    simpa [Matrix.lambdaMin_eq_sInf_spectrum] using Matrix.lambdaMin_pos_of_posDef A hA
  have hsup_pos : 0 < sSup (spectrum ℝ A) := by
    simpa [Matrix.lambdaMax_eq_sSup_spectrum] using Matrix.lambdaMax_pos_of_posDef A hA
  have hspectrum_bddBelow : BddBelow (spectrum ℝ A) := by
    simpa [hA.isHermitian.spectrum_real_eq_range_eigenvalues] using
      (Set.finite_range hA.isHermitian.eigenvalues).bddBelow
  have hspectrum_bddAbove : BddAbove (spectrum ℝ A) := by
    simpa [hA.isHermitian.spectrum_real_eq_range_eigenvalues] using
      (Set.finite_range hA.isHermitian.eigenvalues).bddAbove
  have hsinf_le_hsup : sInf (spectrum ℝ A) ≤ sSup (spectrum ℝ A) :=
    csInf_le_csSup hspectrum_nonempty hspectrum_bddBelow hspectrum_bddAbove
  have hκ_eq :
      κ = sSup (spectrum ℝ A) / sInf (spectrum ℝ A) := by
    simpa [κ] using Matrix.posDefConditionNumber_eq_spectralExtrema A hA
  have hκ_pos : 0 < κ := by
    rw [hκ_eq]
    exact div_pos hsup_pos hsinf_pos
  have hκ_ge_one : 1 ≤ κ := by
    rw [hκ_eq]
    field_simp [hsinf_pos.ne']
    linarith
  have hden_pos : 0 < κ + 1 := by
    linarith
  constructor
  · -- The numerator is nonnegative because the condition number is at least `1`.
    exact div_nonneg (sub_nonneg.mpr hκ_ge_one) hden_pos.le
  · -- The numerator is strictly smaller than the denominator because `1 > 0`.
    exact (div_lt_one hden_pos).2 (by linarith)

/-- Theorem 3.5. If `τ` is an exact line search for the steepest-descent iterates
of the positive quadratic functional `quadraticFunctional c b A`,
then the `A`-energy-norm error decays at the linear rate
`((A.posDefConditionNumber hA - 1) / (A.posDefConditionNumber hA + 1)) ^ v`. -/
theorem energyNorm_error_bound
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) [Nonempty n] (hA : A.PosDef)
    (τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ n)
    (hτ : IsExactLineSearch (quadraticFunctional c b A) τ f0)
    (v : ℕ) :
    energyNormError A b hA (iterates (quadraticFunctional c b A) τ f0 v) ≤
      (((A.posDefConditionNumber hA) - 1) / ((A.posDefConditionNumber hA) + 1)) ^ v *
        energyNormError A b hA f0 := by
  let q : ℝ := ((A.posDefConditionNumber hA - 1) / (A.posDefConditionNumber hA + 1))
  have hq_nonneg : 0 ≤ q := (conditionRatio_nonneg_lt_one A hA).1
  have hτ_exact :
      ∀ v,
        LineSearch.IsExactStep
          (quadraticFunctional c b A)
          (iterates (quadraticFunctional c b A) τ f0 v)
          (direction (quadraticFunctional c b A) (iterates (quadraticFunctional c b A) τ f0 v))
          (τ v) :=
    (SteepestDescent.isExactLineSearch_iff (quadraticFunctional c b A) τ f0).mp hτ
  have hτ_min :
      ∀ v,
        IsMinOn
          (LineSearch.profile
            (quadraticFunctional c b A)
            (iterates (quadraticFunctional c b A) τ f0 v)
            (direction (quadraticFunctional c b A) (iterates (quadraticFunctional c b A) τ f0 v)))
          (Set.Ioi (0 : ℝ))
          (τ v) :=
    fun v ↦ (hτ_exact v).isMinOn
  -- Iterate the one-step contraction produced by exact line search.
  induction v with
  | zero =>
      simp
  | succ v hv =>
      have hstep :=
        exactLineSearch_oneStep_energyNormError_le c b A hA
          (iterates (quadraticFunctional c b A) τ f0 v)
          (τ v)
          (hτ_min v)
      calc
        energyNormError A b hA (iterates (quadraticFunctional c b A) τ f0 (v + 1))
            = energyNormError A b hA
                (update (quadraticFunctional c b A) (τ v)
                  (iterates (quadraticFunctional c b A) τ f0 v)) := by
                simp [SteepestDescent.iterates]
        _ ≤ q * energyNormError A b hA (iterates (quadraticFunctional c b A) τ f0 v) := by
              simpa [q] using hstep
        _ ≤ q * (q ^ v * energyNormError A b hA f0) := by
              exact mul_le_mul_of_nonneg_left hv hq_nonneg
        _ = q ^ (v + 1) * energyNormError A b hA f0 := by
              simp [pow_succ, mul_assoc, mul_comm]

/-- Exact-line-search steepest descent for a positive quadratic functional
converges to the minimizer `quadraticFunctionalMinimizer b A`. -/
theorem tendsto_minimizer
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hA : A.PosDef)
    (τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ n)
    (hτ : IsExactLineSearch (quadraticFunctional c b A) τ f0) :
    Filter.Tendsto (iterates (quadraticFunctional c b A) τ f0) Filter.atTop
      (nhds (quadraticFunctionalMinimizer b A)) := by
  classical
  obtain hempty | hnonempty := isEmpty_or_nonempty n
  · -- Local instance justification (proof-local temporary data): the empty-index
    -- branch makes `EuclideanSpace ℝ n` a subsingleton, so every iterate equals
    -- the minimizer and the sequence is constant.
    letI : IsEmpty n := hempty
    have hconst :
        iterates (quadraticFunctional c b A) τ f0 =
          fun _ : ℕ ↦ quadraticFunctionalMinimizer b A := by
      funext v
      exact Subsingleton.elim _ _
    simpa [hconst] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ ↦ quadraticFunctionalMinimizer b A)
        Filter.atTop
        (nhds (quadraticFunctionalMinimizer b A)))
  · letI : Nonempty n := hnonempty
    let q : ℝ := ((A.posDefConditionNumber hA - 1) / (A.posDefConditionNumber hA + 1))
    let C : ℝ := (Real.sqrt (sInf (spectrum ℝ A)))⁻¹
    have hq_nonneg : 0 ≤ q := (conditionRatio_nonneg_lt_one A hA).1
    have hq_lt_one : q < 1 := (conditionRatio_nonneg_lt_one A hA).2
    have hC_nonneg : 0 ≤ C := by
      simp [C]
    have hpow_tendsto :
        Filter.Tendsto (fun v : ℕ ↦ q ^ v * energyNormError A b hA f0)
          Filter.atTop (nhds 0) := by
      -- The geometric factor tends to zero because the contraction ratio lies in `[0, 1)`.
      simpa [q] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one).mul_const
          (energyNormError A b hA f0)
    have hbound_tendsto :
        Filter.Tendsto
          (fun v : ℕ ↦ C * (q ^ v * energyNormError A b hA f0))
          Filter.atTop
          (nhds 0) := by
      simpa [C] using (tendsto_const_nhds.mul hpow_tendsto)
    have herror_norm_tendsto :
        Filter.Tendsto
          (fun v : ℕ ↦ ‖QuadraticOptimization.error A b
            (iterates (quadraticFunctional c b A) τ f0 v)‖)
          Filter.atTop
          (nhds 0) := by
      refine squeeze_zero (fun v ↦ norm_nonneg _) ?_ hbound_tendsto
      intro v
      calc
        ‖QuadraticOptimization.error A b (iterates (quadraticFunctional c b A) τ f0 v)‖
            ≤ C * energyNormError A b hA (iterates (quadraticFunctional c b A) τ f0 v) := by
              simpa [C] using
                normError_le_invSqrtSpectralInf_mul_energyNormError b A hA
                  (iterates (quadraticFunctional c b A) τ f0 v)
        _ ≤ C * (q ^ v * energyNormError A b hA f0) := by
              exact mul_le_mul_of_nonneg_left
                (energyNorm_error_bound c b A hA τ f0 hτ v)
                hC_nonneg
    -- Convert the norm convergence of the error sequence into convergence to the minimizer.
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [QuadraticOptimization.error_eq_sub] using herror_norm_tendsto

end SteepestDescent
