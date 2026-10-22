/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_10
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_12
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Matrix.Norms.L2Operator MatrixOrder

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Corollary 5.13 is a `bridge/view` specialization of the Chapter 5 real-valued smoothness owner
predicate `is_l_smooth_on`, specialized to `Set.univ`, with Theorem 5.12 as its
`core/canonical` Hessian characterization. The source-facing content here is the Euclidean
coordinate realization in terms of the Hessian matrix of `bilinearIteratedFDerivTwo ℝ f x` and its
largest eigenvalue. -/

/-- The Hessian of a twice differentiable function on `ℝ^n`, written as a matrix in the standard
Euclidean basis. -/
def hessian_matrix (f : E → ℝ) (x : E) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix₂ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis) (bilinearIteratedFDerivTwo ℝ f x)

-- Proof sketch: `ContDiff ℝ 2 f` implies that the second derivative of `f` at every point is
-- symmetric via `ContDiffAt.isSymmSndFDerivAt`. Translating the resulting symmetric bilinear form
-- to the standard basis identifies `hessian_matrix f x` as a Hermitian real matrix.
/-- The Hessian matrix of a `C²` real-valued function on `ℝ^n` is Hermitian. -/
theorem hessian_matrix_isHermitian (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x : E) :
    (hessian_matrix f x).IsHermitian := by
  have hsymm : (bilinearIteratedFDerivTwo ℝ f x).IsSymm := by
    refine ⟨fun v w ↦ ?_⟩
    simpa [bilinearIteratedFDerivTwo] using
      (hf.contDiffAt.isSymmSndFDerivAt (by simp : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))).eq v w
  exact
    (LinearMap.isSymm_iff_isHermitian_toMatrix ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)).mp
      hsymm

/-- Helper for Corollary 5.13: the second derivative of the centered line pullback at the midpoint
is four times the Hessian quadratic form in the direction `v`. -/
lemma midpointPullbackSecondDeriv_eq_fourHessianQuadratic
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) :
    iteratedDeriv 2 (fun t : ℝ ↦ f (AffineMap.lineMap (x - v) (x + v) t)) (1 / 2 : ℝ) =
      4 * bilinearIteratedFDerivTwo ℝ f x v v := by
  have hmid :
      (1 / 2 : ℝ) ∈ Set.uIoo (0 : ℝ) 1 := by
    simpa [Set.uIoo_of_lt zero_lt_one] using
      (show (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by norm_num)
  have hsegment :
      segment ℝ (x - v) (x + v) ⊆ (Set.univ : Set E) := by
    intro z hz
    simp
  have hdir : (x + v) - (x - v) = (2 : ℝ) • v := by
    calc
      (x + v) - (x - v) = v + v := by abel_nf
      _ = (2 : ℝ) • v := by simp [two_smul]
  have hmidpoint : AffineMap.lineMap (x - v) (x + v) (1 / 2 : ℝ) = x := by
    rw [AffineMap.lineMap_apply_module', hdir]
    calc
      (1 / 2 : ℝ) • ((2 : ℝ) • v) + (x - v) = v + (x - v) := by simp
      _ = x := by abel_nf
  -- Isolate the only affine normalization needed for the centered pullback.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ f (AffineMap.lineMap (x - v) (x + v) t)) (1 / 2 : ℝ)
        =
          bilinearIteratedFDerivTwo ℝ f
            (AffineMap.lineMap (x - v) (x + v) (1 / 2 : ℝ))
            ((x + v) - (x - v)) ((x + v) - (x - v)) := by
              simpa using
                segmentPullbackIteratedDerivTwo (U := Set.univ) (f := f)
                  (x := x - v) (y := x + v) isOpen_univ hf.contDiffOn hsegment hmid
    _ = bilinearIteratedFDerivTwo ℝ f x ((2 : ℝ) • v) ((2 : ℝ) • v) := by
          rw [hmidpoint, hdir]
    _ = 4 * bilinearIteratedFDerivTwo ℝ f x v v := by
          calc
            bilinearIteratedFDerivTwo ℝ f x ((2 : ℝ) • v) ((2 : ℝ) • v)
                = (2 : ℝ) * ((2 : ℝ) * bilinearIteratedFDerivTwo ℝ f x v v) := by
                    simp
            _ = 4 * bilinearIteratedFDerivTwo ℝ f x v v := by
                    ring

/-- Helper for Corollary 5.13: convexity makes the Hessian bilinear form nonnegative in every
direction. -/
lemma hessianBilinear_isPosSemidef
    {f : E → ℝ} (hconvex : ConvexOn ℝ Set.univ f) (hf : ContDiff ℝ 2 f) (x : E) :
    (bilinearIteratedFDerivTwo ℝ f x).IsPosSemidef := by
  have hsymm : (bilinearIteratedFDerivTwo ℝ f x).IsSymm := by
    refine ⟨fun v w ↦ ?_⟩
    simpa [bilinearIteratedFDerivTwo] using
      (hf.contDiffAt.isSymmSndFDerivAt (by simp : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))).eq v w
  refine ⟨hsymm, ?_⟩
  refine ⟨fun v ↦ ?_⟩
  let φ : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap (x - v) (x + v) t)
  have hφ : ContDiff ℝ 2 φ := by
    simpa [φ, AffineMap.lineMap_apply_module'] using
      (show ContDiff ℝ 2 (fun t : ℝ ↦ f (t • ((x + v) - (x - v)) + (x - v))) from by
        fun_prop)
  have hconvexφ : ConvexOn ℝ Set.univ φ := by
    simpa [φ] using hconvex.comp_affineMap (AffineMap.lineMap (x - v) (x + v))
  have hmono : Monotone (deriv φ) := by
    simpa using
      (hconvexφ.monotoneOn_deriv fun t ht ↦ (hφ.differentiable (by norm_num)) t)
  have hsecondNonneg : 0 ≤ iteratedDeriv 2 φ (1 / 2 : ℝ) := by
    have hderivNonneg : 0 ≤ deriv (deriv φ) (1 / 2 : ℝ) := by
      exact ((hφ.differentiable_deriv_two (1 / 2 : ℝ)).hasDerivAt).nonneg_of_monotone hmono
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using hderivNonneg
  have hscaled :
      0 ≤ 4 * bilinearIteratedFDerivTwo ℝ f x v v := by
    rw [← midpointPullbackSecondDeriv_eq_fourHessianQuadratic (hf := hf) x v]
    simpa [φ] using hsecondNonneg
  nlinarith

/-- Helper for Corollary 5.13: convexity upgrades the Hessian matrix to positive semidefinite. -/
lemma hessianMatrix_posSemidef
    {f : E → ℝ} (hconvex : ConvexOn ℝ Set.univ f) (hf : ContDiff ℝ 2 f) (x : E) :
    (hessian_matrix f x).PosSemidef := by
  -- Transport positivity of the Hessian bilinear form to its standard-basis matrix.
  simpa [hessian_matrix] using
    (LinearMap.isPosSemidef_iff_posSemidef_toMatrix ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)).1
      (hessianBilinear_isPosSemidef hconvex hf x)

/-- Helper for Corollary 5.13: the Euclidean operator induced by the Hessian matrix is the Riesz
representation of the second derivative. -/
lemma hessianMatrix_toEuclideanCLM_eq_continuousLinearMapOfHessian
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (hessian_matrix f x) =
      InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ f) x) := by
  have hsymm : (bilinearIteratedFDerivTwo ℝ f x).IsSymm := by
    refine ⟨fun v w ↦ ?_⟩
    simpa [bilinearIteratedFDerivTwo] using
      (hf.contDiffAt.isSymmSndFDerivAt (by simp : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))).eq v w
  apply ContinuousLinearMap.ext
  intro v
  refine
    (InnerProductSpace.unique_continuousLinearMapOfBilin
      (B := fderiv ℝ (fderiv ℝ f) x)
      (v := v)
      (f := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (hessian_matrix f x) v)
      (fun w ↦ ?_))
  calc
    inner ℝ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (hessian_matrix f x) v) w
        = inner ℝ w (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (hessian_matrix f x) v) := by
            rw [real_inner_comm]
    _ = bilinearIteratedFDerivTwo ℝ f x w v := by
          rw [Matrix.inner_toEuclideanCLM]
          simpa [hessian_matrix] using
            (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec
              ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis) (bilinearIteratedFDerivTwo ℝ f x)
              w v).symm
    _ = bilinearIteratedFDerivTwo ℝ f x v w := by
          simpa using hsymm.eq w v
    _ = fderiv ℝ (fderiv ℝ f) x v w := by
          simp [bilinearIteratedFDerivTwo]

/-- Helper for Corollary 5.13: the Hessian operator norm from Theorem 5.12 equals the Euclidean
operator norm of the Hessian matrix. -/
lemma hessianOperatorNNNorm_eq_hessianMatrixNNNorm
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖₊ = ‖hessian_matrix f x‖₊ := by
  by_cases hzero : n = 0
  · subst hzero
    have hmatrixZero : hessian_matrix f x = 0 := by
      ext i j
      exact Fin.elim0 i
    simp [hmatrixZero]
  · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_iff_ne_zero.mpr hzero⟩⟩
    haveI : Nontrivial E := inferInstance
    apply NNReal.coe_injective
    calc
      ‖fderiv ℝ (fderiv ℝ f) x‖
          = ‖InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ f) x)‖ := by
              symm
              simpa [InnerProductSpace.continuousLinearMapOfBilin] using
                (LinearIsometry.norm_toContinuousLinearMap_comp
                  (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
                  (g := fderiv ℝ (fderiv ℝ f) x))
      _ = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (hessian_matrix f x)‖ := by
            rw [← hessianMatrix_toEuclideanCLM_eq_continuousLinearMapOfHessian (hf := hf) x]
      _ = ‖hessian_matrix f x‖ := by
            rw [← Matrix.cstar_norm_def]

/-- Helper for Corollary 5.13: for a positive semidefinite real Hessian matrix, an operator-norm
bound is equivalent to bounding the top ordered eigenvalue. -/
lemma hessianMatrix_nnnorm_le_iff_topEigenvalue_le
    {A : Matrix (Fin n) (Fin n) ℝ} {L : NNReal} (hn : 0 < n) (hAherm : A.IsHermitian)
    (hApos : A.PosSemidef) :
    ‖A‖₊ ≤ L ↔ hAherm.eigenvalues₀ ⟨0, by simpa using hn⟩ ≤ (L : ℝ) := by
  let i0 : Fin (Fintype.card (Fin n)) := ⟨0, by simpa using hn⟩
  have hnormEq : ‖A‖ = hAherm.eigenvalues₀ i0 := by
    have hpositive : A.toEuclideanLin.IsPositive := (Matrix.isPositive_toEuclideanLin_iff).2 hApos
    have hk : 0 < Fintype.card (Fin n) := by
      simpa [finrank_euclideanSpace] using hn
    have hi0Eq : (⟨0, hk⟩ : Fin (Fintype.card (Fin n))) = i0 := by
      ext
      rfl
    have hsymmEq :
        hpositive.isSymmetric = Matrix.isSymmetric_toEuclideanLin_iff.mpr hAherm := by
      apply Subsingleton.elim
    calc
      ‖A‖ = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ := by
        rw [Matrix.cstar_norm_def]
      _ = ‖A.toEuclideanLin.toContinuousLinearMap‖ := by
        rfl
      _ = hpositive.isSymmetric.eigenvalues finrank_euclideanSpace ⟨0, hk⟩ := by
        exact
          @positive_operator_norm_eq_top_eigenvalue_real E inferInstance inferInstance
            inferInstance A.toEuclideanLin (Fintype.card (Fin n)) finrank_euclideanSpace hk
              hpositive
      _ = hAherm.eigenvalues₀ i0 := by
        rw [hi0Eq, Matrix.IsHermitian.eigenvalues₀, hsymmEq]
  constructor
  · intro hnorm
    rw [← hnormEq]
    exact NNReal.coe_le_coe.mp hnorm
  · intro htop
    exact NNReal.coe_le_coe.mpr (hnormEq.trans_le htop)

-- Proof sketch: combine the owner theorem `is_l_smooth_iff_hessian_operator_norm_le`
-- with the fact that convexity makes each Hessian matrix positive semidefinite. For a Hermitian
-- positive semidefinite matrix, the operator norm equals its largest eigenvalue, so the Hessian
-- operator-norm bound is equivalent to the displayed maximal-eigenvalue bound.
/-- Corollary 5.13: a twice continuously differentiable convex function on `ℝ^n` is globally
`L`-smooth with respect to the Euclidean norm if and only if, at every point, the largest
eigenvalue of its Hessian matrix is at most `L`. -/
theorem convex_is_l_smooth_iff_hessian_max_eigenvalue_le
    {f : E → ℝ} {L : NNReal} (hn : 0 < n) (hconvex : ConvexOn ℝ Set.univ f)
    (hf : ContDiff ℝ 2 f) :
    is_l_smooth_on f Set.univ L ↔
      ∀ x : E, (hessian_matrix_isHermitian f hf x).eigenvalues₀ ⟨0, by simpa using hn⟩ ≤
        (L : ℝ) := by
  rw [is_l_smooth_iff_hessian_operator_nnnorm_le hf]
  constructor
  · intro hs x
    have hpsd : (hessian_matrix f x).PosSemidef := hessianMatrix_posSemidef hconvex hf x
    -- Translate the Hessian operator bound from Theorem 5.12 to the matrix spectrum bound.
    have hmatrixNorm : ‖hessian_matrix f x‖₊ ≤ L := by
      simpa [hessianOperatorNNNorm_eq_hessianMatrixNNNorm hf x] using hs x
    exact
      (hessianMatrix_nnnorm_le_iff_topEigenvalue_le (hn := hn)
        (hAherm := hessian_matrix_isHermitian f hf x) (hApos := hpsd)).1 hmatrixNorm
  · intro hs x
    have hpsd : (hessian_matrix f x).PosSemidef := hessianMatrix_posSemidef hconvex hf x
    -- Convert the top-eigenvalue bound back to the operator norm bound required by Theorem 5.12.
    have hmatrixNorm : ‖hessian_matrix f x‖₊ ≤ L := by
      exact
        (hessianMatrix_nnnorm_le_iff_topEigenvalue_le (hn := hn)
          (hAherm := hessian_matrix_isHermitian f hf x) (hApos := hpsd)).2 (hs x)
    simpa [hessianOperatorNNNorm_eq_hessianMatrixNNNorm hf x] using hmatrixNorm

end
