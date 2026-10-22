/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Algorithm_7_3_9
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_1

noncomputable section

open Filter Matrix NormedSpace

-- Domain sampling for this item:
-- * primary domain: finite-dimensional least-squares Gauss-Newton and Levenberg-Marquardt
--   directions at a fixed iterate;
-- * sampled owner-family declarations:
--   `solvesLevenbergMarquardtNormalEquation`,
--   `levenbergMarquardtStep_norm_strictAntiOn`,
--   `Algorithm_7_3_9.trustRegionLevenbergMarquardtGradient`,
--   `Matrix.toEuclideanLin`,
--   `NormedSpace.normalize`
-- * source-facing layer here: the asymptotic statements for the fixed-iterate directions;
-- * core/canonical owners reused here: `solvesLevenbergMarquardtNormalEquation` for the damped
--   normal-equation semantics, `trustRegionLevenbergMarquardtGradient` for the least-squares
--   gradient, and `NormedSpace.normalize` for normalized directions
-- * primitive data reused from upstream: a step family solving the regularized normal equations
--   for nonnegative damping parameters and the least-squares gradient
-- * derived API: no local normalization wrapper is kept, since mathlib already owns it.

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Residual" => EuclideanSpace ℝ (Fin m)
local notation "Jacobian" => Matrix (Fin m) (Fin n) ℝ
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Chapter07 Exercise 7.6: injectivity of `Matrix.toEuclideanLin J` is exactly the
full-column-rank hypothesis needed for the concrete matrix action `J.mulVec`. -/
lemma mulVec_injective_of_toEuclideanLin_injective
    (J : Jacobian) (hfullRank : Function.Injective (Matrix.toEuclideanLin J)) :
    Function.Injective J.mulVec := by
  intro x y hxy
  -- Move the matrix equality into Euclidean space, where the theorem hypothesis applies directly.
  apply WithLp.toLp_injective 2
  apply hfullRank
  simp [Matrix.toLpLin_toLp, hxy]

/-- Helper for Chapter07 Exercise 7.6: full column rank makes the Gauss-Newton normal matrix
`Jᵀ * J` positive definite. -/
lemma gauss_newton_normal_matrix_posDef
    (J : Jacobian) (hfullRank : Function.Injective (Matrix.toEuclideanLin J)) :
    (Jᵀ * J).PosDef := by
  -- The Gram matrix is positive definite once the Jacobian action is injective.
  exact Matrix.PosDef.conjTranspose_mul_self J
    (mulVec_injective_of_toEuclideanLin_injective J hfullRank)

/-- Helper for Chapter07 Exercise 7.6: an invertible linear system `A s = -g` has the textbook
inverse representation `s = -A⁻¹ g`. -/
lemma step_eq_neg_inv_toEuclideanLin_of_isUnit
    (A : MatrixN) (g step : Point) (hA : IsUnit A)
    (hstep : A.mulVec step = -g) :
    step = -Matrix.toEuclideanLin A⁻¹ g := by
  letI : Invertible A := hA.invertible
  -- Solve the system on underlying coordinates, then transport back to Euclidean space.
  have hinv : A⁻¹.mulVec (-g) = step :=
    Matrix.inv_mulVec_eq_vec (A := A) hstep.symm
  apply WithLp.ofLp_injective 2
  simpa [Matrix.ofLp_toLpLin, Matrix.mulVec_neg] using hinv.symm

/-- Helper for Chapter07 Exercise 7.6: every nonnegative-damping LM step coincides with the
inverse-based formula, with the `μ = 0` branch closed by full rank. -/
lemma levenberg_marquardt_step_eq_neg_inv_toEuclideanLin_of_nonneg
    (J : Jacobian) (r : Residual) (step : Point)
    (hfullRank : Function.Injective (Matrix.toEuclideanLin J))
    {μ : ℝ} (hμ : 0 ≤ μ)
    (hstep :
      solvesLevenbergMarquardtNormalEquation
        J (trustRegionLevenbergMarquardtGradient J r) μ step) :
    step = -Matrix.toEuclideanLin ((Jᵀ * J + μ • (1 : MatrixN))⁻¹)
      (trustRegionLevenbergMarquardtGradient J r) := by
  let A : MatrixN := Jᵀ * J + μ • (1 : MatrixN)
  have hA : IsUnit A := by
    -- The undamped matrix uses full rank; positive damping uses the imported regularization lemma.
    rcases eq_or_lt_of_le hμ with rfl | hμ'
    · simpa [A] using (gauss_newton_normal_matrix_posDef J hfullRank).isUnit
    · simpa [A] using (regularized_normal_matrix_posDef J hμ').isUnit
  -- Once `A` is invertible, the normal equation gives the inverse formula immediately.
  apply step_eq_neg_inv_toEuclideanLin_of_isUnit A
    (trustRegionLevenbergMarquardtGradient J r) step hA
  simpa [A, solvesLevenbergMarquardtNormalEquation] using hstep

/-- Helper for Chapter07 Exercise 7.6: after multiplying the LM equation by `μ`, the scaled step
`μ • s` solves the unit-damped system `(μ⁻¹(JᵀJ) + I)(μs) = -g`. -/
lemma scaled_levenberg_marquardt_step_eq_neg_inv_toEuclideanLin
    (J : Jacobian) (r : Residual) (step : Point) {μ : ℝ} (hμ : 0 < μ)
    (hstep :
      solvesLevenbergMarquardtNormalEquation
        J (trustRegionLevenbergMarquardtGradient J r) μ step) :
    μ • step =
      -Matrix.toEuclideanLin
        ((μ⁻¹ • (Jᵀ * J) + (1 : MatrixN))⁻¹)
        (trustRegionLevenbergMarquardtGradient J r) := by
  let B : MatrixN := μ⁻¹ • (Jᵀ * J) + (1 : MatrixN)
  have hB : IsUnit B := by
    -- Scale the positive-definite regularized normal matrix by the positive scalar `μ⁻¹`.
    have hreg : (Jᵀ * J + μ • (1 : MatrixN)).PosDef :=
      regularized_normal_matrix_posDef J hμ
    have hscaled :
        (μ⁻¹ • (Jᵀ * J + μ • (1 : MatrixN)) : MatrixN).PosDef := by
      simpa using Matrix.PosDef.smul hreg (inv_pos.mpr hμ)
    simpa [B, smul_add, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul] using hscaled.isUnit
  have hsolve : B.mulVec (μ • step) = -trustRegionLevenbergMarquardtGradient J r := by
    -- This is the source scaling identity behind the large-damping asymptotics.
    have hstep' :
        (Jᵀ * J).mulVec step + μ • step =
          -trustRegionLevenbergMarquardtGradient J r := by
      simpa [solvesLevenbergMarquardtNormalEquation, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec] using hstep
    calc
      B.mulVec (μ • step)
          = (μ⁻¹ • (Jᵀ * J)).mulVec (μ • step) + (1 : MatrixN).mulVec (μ • step) := by
              simp [B, Matrix.add_mulVec]
      _ = μ⁻¹ • (Jᵀ * J).mulVec (μ • step) + μ • step := by
            rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = μ⁻¹ • (μ • (Jᵀ * J).mulVec step) + μ • step := by
            rw [Matrix.mulVec_smul]
      _ = (μ⁻¹ * μ) • (Jᵀ * J).mulVec step + μ • step := by
            rw [smul_smul]
      _ = (Jᵀ * J).mulVec step + μ • step := by
            simp [hμ.ne']
      _ = -trustRegionLevenbergMarquardtGradient J r := hstep'
  exact step_eq_neg_inv_toEuclideanLin_of_isUnit B
    (trustRegionLevenbergMarquardtGradient J r) (μ • step) hB hsolve

/-- Helper for Chapter07 Exercise 7.6: normalization is continuous at every nonzero vector. -/
lemma tendsto_normalize_of_tendsto_nonzero
    {α : Type*} {F : Filter α} {u : α → Point} {v : Point}
    (hu : Tendsto u F (nhds v)) (hv : v ≠ 0) :
    Tendsto (fun x ↦ normalize (u x)) F (nhds (normalize v)) := by
  -- Rewrite `normalize` as `‖u x‖⁻¹ • u x` and use continuity of inversion away from zero.
  have hInv : Tendsto (fun x ↦ ‖u x‖⁻¹) F (nhds ‖v‖⁻¹) := by
    exact hu.norm.inv₀ (by simpa [norm_eq_zero] using hv)
  simpa [NormedSpace.normalize] using hInv.smul hu

/-- Chapter07 Exercise 7.6 (1): fixing a Jacobian `J` of full column rank and a residual vector
`r` at one least-squares iterate, if `s μ` solves the regularized normal equation for every
nonnegative damping parameter `μ`, then the Levenberg-Marquardt direction `s μ` tends to the
Gauss-Newton direction `s 0` as the damping parameter tends to `0` through positive values. -/
theorem levenbergMarquardtDirection_tendsto_gaussNewtonDirection
    (J : Jacobian) (r : Residual) (s : ℝ → Point)
    (hfullRank : Function.Injective (Matrix.toEuclideanLin J))
    (h_step :
      ∀ ⦃μ : ℝ⦄, 0 ≤ μ →
        solvesLevenbergMarquardtNormalEquation
          J (trustRegionLevenbergMarquardtGradient J r) μ (s μ)) :
    Filter.Tendsto s
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (s 0)) := by
  let A : ℝ → MatrixN := fun μ ↦ Jᵀ * J + μ • (1 : MatrixN)
  have hs0 :
      s 0 =
        -Matrix.toEuclideanLin ((A 0)⁻¹)
          (trustRegionLevenbergMarquardtGradient J r) :=
    levenberg_marquardt_step_eq_neg_inv_toEuclideanLin_of_nonneg J r (s 0)
      hfullRank (show 0 ≤ (0 : ℝ) by simp) (h_step (show 0 ≤ (0 : ℝ) by simp))
  have hA_cont : Continuous A := by
    -- The regularized normal matrix depends affinely on `μ`.
    continuity
  have hAinv_cont : ContinuousAt (fun μ ↦ (A μ)⁻¹) 0 := by
    -- Inversion is continuous at the undamped positive-definite normal matrix.
    have hdet_ne : (A 0).det ≠ 0 := by
      exact ((A 0).isUnit_iff_isUnit_det.mp
        (by simpa [A] using (gauss_newton_normal_matrix_posDef J hfullRank).isUnit)).ne_zero
    refine (continuousAt_matrix_inv (A 0) ?_).comp hA_cont.continuousAt
    simpa [Ring.inverse] using (continuousAt_inv₀ (x := (A 0).det) hdet_ne)
  have hcoord_cont :
      ContinuousAt
        (fun μ ↦ -(((A μ)⁻¹).mulVec
          (trustRegionLevenbergMarquardtGradient J r))
        )
        0 := by
    -- After the inverse family is continuous, matrix-vector evaluation is continuous as well.
    have hmul :
        Continuous
          (fun M : MatrixN ↦
            -(M.mulVec (trustRegionLevenbergMarquardtGradient J r))) := by
      exact (Continuous.matrix_mulVec continuous_id continuous_const).neg
    exact hmul.continuousAt.comp hAinv_cont
  have hexplicit :
      Tendsto
        (fun μ ↦
          -Matrix.toEuclideanLin ((A μ)⁻¹)
            (trustRegionLevenbergMarquardtGradient J r))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds
          (-Matrix.toEuclideanLin ((A 0)⁻¹)
            (trustRegionLevenbergMarquardtGradient J r))) := by
    -- Transfer the coordinatewise limit back to Euclidean space through `toLp`.
    have hcoord :
        Tendsto
          (fun μ ↦
            -((A μ)⁻¹).mulVec
              (trustRegionLevenbergMarquardtGradient J r))
          (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
          (nhds
            (-((A 0)⁻¹).mulVec
              (trustRegionLevenbergMarquardtGradient J r))) :=
      hcoord_cont.tendsto.mono_left nhdsWithin_le_nhds
    have htolp :
        Tendsto
          (fun μ ↦
            WithLp.toLp 2
              (-(((A μ)⁻¹).mulVec
                (trustRegionLevenbergMarquardtGradient J r))))
          (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
          (nhds
            (WithLp.toLp 2
              (-(((A 0)⁻¹).mulVec
                (trustRegionLevenbergMarquardtGradient J r))))) :=
      ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n ↦ ℝ)).tendsto _).comp hcoord
    change
      Tendsto
        (fun μ ↦
          WithLp.toLp 2
            (-(((A μ)⁻¹).mulVec
              (trustRegionLevenbergMarquardtGradient J r))))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds
          (WithLp.toLp 2
            (-(((A 0)⁻¹).mulVec
              (trustRegionLevenbergMarquardtGradient J r)))))
    simpa [Matrix.toLpLin_apply] using htolp
  have hEq :
      (fun μ ↦ s μ) =ᶠ[nhdsWithin 0 (Set.Ioi (0 : ℝ))]
        fun μ ↦
          -Matrix.toEuclideanLin ((A μ)⁻¹)
            (trustRegionLevenbergMarquardtGradient J r) := by
    -- On the right-neighborhood filter, every parameter is positive, so the explicit formula holds.
    filter_upwards [eventually_mem_nhdsWithin] with μ hμ
    exact levenberg_marquardt_step_eq_neg_inv_toEuclideanLin_of_nonneg J r (s μ)
      hfullRank (le_of_lt hμ) (h_step (le_of_lt hμ))
  -- The eventual explicit formula and the continuous inverse family close the limit.
  simpa [hs0] using Tendsto.congr' hEq.symm hexplicit

/-- Chapter07 Exercise 7.6 (2): fixing a Jacobian `J` and a residual vector `r` at one
least-squares iterate, if `s μ` solves the regularized normal equation for every positive damping
parameter `μ`, then the normalized Levenberg-Marquardt directions converge to the normalized
steepest-descent direction as the damping parameter tends to `+∞`. -/
theorem normalizedLevenbergMarquardtDirection_tendsto_steepestDescentDirection
    (J : Jacobian) (r : Residual) (s : ℝ → Point)
    (h_step :
      ∀ ⦃μ : ℝ⦄, 0 < μ →
        solvesLevenbergMarquardtNormalEquation
          J (trustRegionLevenbergMarquardtGradient J r) μ (s μ)) :
    Filter.Tendsto (fun μ : ℝ ↦ normalize (s μ))
      Filter.atTop
      (nhds (normalize (-trustRegionLevenbergMarquardtGradient J r))) := by
  let B : ℝ → MatrixN := fun t ↦ t • (Jᵀ * J) + (1 : MatrixN)
  let g := trustRegionLevenbergMarquardtGradient J r
  by_cases hg : g = 0
  · have hs_zero : ∀ ⦃μ : ℝ⦄, 0 < μ → s μ = 0 := by
      intro μ hμ
      -- When the gradient is zero, every positive-damping LM step is the zero vector.
      have hformula :
          s μ =
            -Matrix.toEuclideanLin ((Jᵀ * J + μ • (1 : MatrixN))⁻¹) g := by
        have hA : IsUnit (Jᵀ * J + μ • (1 : MatrixN) : MatrixN) :=
          (regularized_normal_matrix_posDef J hμ).isUnit
        apply step_eq_neg_inv_toEuclideanLin_of_isUnit
          (Jᵀ * J + μ • (1 : MatrixN)) g (s μ) hA
        simpa [solvesLevenbergMarquardtNormalEquation] using h_step hμ
      simpa [g, hg] using hformula
    have hEq :
        (fun μ : ℝ ↦ normalize (s μ)) =ᶠ[atTop] fun _ ↦ 0 := by
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with μ hμ
      simp [hs_zero hμ]
    -- Both the steps and the target steepest-descent direction normalize to zero.
    simpa [g, hg] using
      Tendsto.congr' hEq.symm
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : Point)) atTop (nhds 0))
  · have hB_cont : Continuous B := by
      -- The scaled matrix family `t • (JᵀJ) + I` is affine in `t`.
      continuity
    have hBinv_cont : ContinuousAt (fun t ↦ (B t)⁻¹) 0 := by
      -- Inversion is continuous at the identity matrix, the `t = 0` endpoint of the scaled family.
      have hdet_ne : (B 0).det ≠ 0 := by
        simp [B]
      refine (continuousAt_matrix_inv (B 0) ?_).comp hB_cont.continuousAt
      simpa [Ring.inverse] using (continuousAt_inv₀ (x := (B 0).det) hdet_ne)
    have hscaledExplicit :
        Tendsto
          (fun μ : ℝ ↦
            -Matrix.toEuclideanLin ((B μ⁻¹)⁻¹) g)
          atTop
          (nhds (-g)) := by
      -- The scaled explicit formula converges because `μ⁻¹ → 0` and `B 0 = I`.
      have hcoordCont :
          ContinuousAt (fun t ↦ -(((B t)⁻¹).mulVec g)) 0 := by
        have hmul :
            Continuous (fun M : MatrixN ↦ -(M.mulVec g)) := by
          exact (Continuous.matrix_mulVec continuous_id continuous_const).neg
        exact hmul.continuousAt.comp hBinv_cont
      have hcoord :
          Tendsto (fun μ : ℝ ↦ -(((B μ⁻¹)⁻¹).mulVec g)) atTop (nhds (-g)) := by
        have hbase :
            Tendsto (fun t ↦ -(((B t)⁻¹).mulVec g)) (nhds 0) (nhds (-g)) := by
          simpa [B] using hcoordCont.tendsto
        exact hbase.comp
          (tendsto_inv_atTop_zero : Tendsto (fun μ : ℝ ↦ μ⁻¹) atTop (nhds 0))
      have htolp :
        Tendsto
            (fun μ : ℝ ↦ WithLp.toLp 2 (-(((B μ⁻¹)⁻¹).mulVec g)))
            atTop
            (nhds (WithLp.toLp 2 (-g))) :=
        ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n ↦ ℝ)).tendsto _).comp hcoord
      change
        Tendsto
          (fun μ : ℝ ↦ WithLp.toLp 2 (-(((B μ⁻¹)⁻¹).mulVec g)))
          atTop
          (nhds (WithLp.toLp 2 (-g)))
      simpa [Matrix.toLpLin_apply] using htolp
    have hscaledEq :
        (fun μ : ℝ ↦ μ • s μ) =ᶠ[atTop]
          fun μ : ℝ ↦ -Matrix.toEuclideanLin ((B μ⁻¹)⁻¹) g := by
      -- Eventually `μ > 0`, so the scaled-step inverse formula applies verbatim.
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with μ hμ
      simpa [B] using
        scaled_levenberg_marquardt_step_eq_neg_inv_toEuclideanLin J r (s μ) hμ (h_step hμ)
    have hscaled :
        Tendsto (fun μ : ℝ ↦ μ • s μ) atTop (nhds (-g)) :=
      Tendsto.congr' hscaledEq.symm hscaledExplicit
    have hnormalizeScaled :
        Tendsto (fun μ : ℝ ↦ normalize (μ • s μ))
          atTop (nhds (normalize (-g))) :=
      tendsto_normalize_of_tendsto_nonzero hscaled (by simpa using neg_ne_zero.mpr hg)
    have hnormalizeEq :
        (fun μ : ℝ ↦ normalize (s μ)) =ᶠ[atTop]
          fun μ : ℝ ↦ normalize (μ • s μ) := by
      -- Positive scalar multiplication does not change a normalized direction.
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with μ hμ
      simpa [eq_comm] using (NormedSpace.normalize_smul_of_pos hμ (s μ))
    -- Replace `normalize (s μ)` by the normalized scaled step and close at the nonzero limit.
    exact Tendsto.congr' hnormalizeEq.symm hnormalizeScaled

end
