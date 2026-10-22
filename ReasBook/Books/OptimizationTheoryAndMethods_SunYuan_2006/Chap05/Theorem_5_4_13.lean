/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Corollary_5_4_11
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Lemma_5_4_17
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_13.Transport
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_13.Iteration

noncomputable section
open Filter
open scoped Matrix.Norms.L2Operator

section Chapter05Theorem5413

variable {n : ℕ}

/-- Helper for Chapter05 Theorem 5.4.13: applying `matrixToOperator M` agrees with the standard
Euclidean matrix action `Matrix.toEuclideanLin M`. -/
@[simp] theorem matrixToOperator_apply
    (M : BroydenMatrix n) (z : BroydenPoint n) :
    matrixToOperator M z = Matrix.toEuclideanLin M z := by
  exact congrArg (fun T : BroydenPoint n →ₗ[ℝ] BroydenPoint n ↦ T z)
    (show matrixToOperator M = Matrix.toEuclideanLin M by
      simpa [matrixToOperator] using Matrix.coe_toEuclideanCLM_eq_toEuclideanLin M)

/-- Helper for Chapter05 Theorem 5.4.13: transporting a matrix difference through
`matrixToOperator` preserves the `ℓ₂` operator norm. -/
theorem matrixToOperator_sub_norm_eq
    (M N : BroydenMatrix n) :
    ‖matrixToOperator M - matrixToOperator N‖ = ‖M - N‖ := by
  rw [← map_sub]
  simpa [matrixToOperator] using Matrix.l2_opNorm_toEuclideanCLM (M - N)

/-- Helper for Chapter05 Theorem 5.4.13: a source-generated Broyden rank-one run coincides
stagewise with any Jacobian-side run for the singleton update rule with the same initial data. -/
lemma generated_eq_jacobianBroydenIteration
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    {domU : Set (BroydenPoint n × BroydenOperator n)}
    {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    {x : ℕ → BroydenPoint n} {B : ℕ → BroydenMatrix n}
    (A : JacobianQuasiNewtonIteration D F domU (broydenRankOneUpdateFunction F)
      x0 (matrixToOperator B0))
    (hgen : IsGeneratedBroydenRankOneIteration F x0 B0 x B) :
    ∀ k : ℕ, x k = A.x k ∧ matrixToOperator (B k) = A.B k := by
  intro k
  induction k with
  | zero =>
      -- Both recursions start from the same initial point and Jacobian approximation.
      constructor
      · simp [hgen.x_zero, A.x_zero]
      · simp [hgen.B_zero, A.B_zero]
  | succ k ih =>
      rcases ih with ⟨hxk, hBk⟩
      have hxNext :
          x (k + 1) = A.x (k + 1) := by
        -- The next iterate is uniquely determined by the current state.
        calc
          x (k + 1) = quasiNewtonNextIterate F (x k) (matrixToOperator (B k)) := by
            simpa [broydenNextIterate] using hgen.step_eq k
          _ = quasiNewtonNextIterate F (A.x k) (A.B k) := by
            simp [hxk, hBk]
          _ = A.x (k + 1) := by
            simpa using (A.step_eq k).symm
      have hBkMatrix : operatorToMatrix (A.B k) = B k := by
        simpa using (congrArg operatorToMatrix hBk).symm
      have hAupdate :
          A.B (k + 1) =
            matrixToOperator
              (broydenRankOneUpdate
                (operatorToMatrix (A.B k))
                (quasiNewtonNextIterate F (A.x k) (A.B k) - A.x k)
                (F (quasiNewtonNextIterate F (A.x k) (A.B k)) - F (A.x k))) := by
        exact
          (mem_broydenRankOneUpdateFunction_iff F (A.x k) (A.B k) (A.B (k + 1))).1
            (A.update_mem k)
      constructor
      · exact hxNext
      · -- The singleton-valued update rule then forces the matrix recursion to agree as well.
        calc
          matrixToOperator (B (k + 1))
              =
                matrixToOperator
                  (broydenRankOneUpdate
                    (B k)
                    (x (k + 1) - x k)
                    (F (x (k + 1)) - F (x k))) := by
                      rw [hgen.update_eq k]
          _ =
              matrixToOperator
                (broydenRankOneUpdate
                  (operatorToMatrix (A.B k))
                  (quasiNewtonNextIterate F (A.x k) (A.B k) - A.x k)
                  (F (quasiNewtonNextIterate F (A.x k) (A.B k)) - F (A.x k))) := by
                    rw [show x (k + 1) = quasiNewtonNextIterate F (x k) (matrixToOperator (B k)) by
                      simpa [broydenNextIterate] using hgen.step_eq k]
                    simp [hxk, hBk, hBkMatrix]
          _ = A.B (k + 1) := hAupdate.symm

/-- Helper for Chapter05 Theorem 5.4.13: the abstract small-start convergence package from
Theorem 5.4.9 transports back to source-facing Broyden well-definedness and linear convergence. -/
lemma wellDefinedAndLinear_of_smallStartConvergence
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (BroydenPoint n × BroydenOperator n)}
    {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    {x : ℕ → BroydenPoint n} {B : ℕ → BroydenMatrix n}
    (hsmall :
      JacobianQuasiNewtonSmallStartConvergence D F domU
        (broydenRankOneUpdateFunction F) hF.xStar x0 (matrixToOperator B0))
    (hgen : IsGeneratedBroydenRankOneIteration F x0 B0 x B) :
    IsWellDefinedBroydenRankOneIteration D F x0 B0 x B ∧
      LinearlyConvergesTo x hF.xStar := by
  rcases hsmall.exists_iteration with ⟨A, hlinearA⟩
  have hmatch := generated_eq_jacobianBroydenIteration A hgen
  have hwell :
      IsWellDefinedBroydenRankOneIteration D F x0 B0 x B := by
    -- Transport domain membership and invertibility from the abstract Jacobian run.
    refine
      { generated := hgen
        iterates_mem := ?_
        matrices_invertible := ?_ }
    · intro k
      simpa [(hmatch k).1] using A.iterates_mem k
    · intro k
      simpa [(hmatch k).2] using A.matrices_invertible k
  have hlinear :
      LinearlyConvergesTo x hF.xStar := by
    -- The geometric convergence rate is invariant under the stagewise identification `x = A.x`.
    rcases hlinearA with ⟨C, q, hC, hq, hbound⟩
    refine ⟨C, q, hC, hq, ?_⟩
    intro k
    simpa [(hmatch k).1] using hbound k
  exact ⟨hwell, hlinear⟩

/-- Helper for Chapter05 Theorem 5.4.13: the operator associated to the rank-one projector
complement acts by subtracting the component of `z` along `s`. -/
lemma broydenProjectorComplement_apply
    (s z : BroydenPoint n) :
    matrixToOperator
        ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s) z =
      z - ((dotProduct s z) / (dotProduct s s)) • s := by
  ext i
  simp [matrixToOperator, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.vecMulVec_mulVec, sub_eq_add_neg]
  ring

/-- Helper for Chapter05 Theorem 5.4.13: the orthogonal-projector complement from `(5.4.65)`
does not increase Euclidean norms. -/
lemma broydenProjectorComplement_apply_norm_le
    (s z : BroydenPoint n) :
    ‖matrixToOperator
        ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s) z‖ ≤
      ‖z‖ := by
  by_cases hs : s = 0
  · subst hs
    simp
  · set c : ℝ := (dotProduct s z) / (dotProduct s s)
    have hss : dotProduct s s ≠ 0 := by
      intro hzero
      exact hs <| by
        simpa using congrArg (WithLp.toLp 2) ((dotProduct_self_eq_zero).1 hzero)
    rw [broydenProjectorComplement_apply]
    have hc : c * dotProduct s s = dotProduct s z := by
      dsimp [c]
      field_simp [hss]
    have horthDot : dotProduct (z - c • s) (c • s) = 0 := by
      calc
        dotProduct (z - c • s) (c • s)
            = c * (dotProduct z s - c * dotProduct s s) := by
                simp [dotProduct_smul]
        _ = c * (dotProduct z s - dotProduct s z) := by rw [hc]
        _ = 0 := by simp [dotProduct_comm]
    have hsq : ‖z‖ ^ 2 = ‖z - c • s‖ ^ 2 + ‖c • s‖ ^ 2 := by
      calc
        ‖z‖ ^ 2 = ‖(z - c • s) + c • s‖ ^ 2 := by
          congr 1
          abel
        _ = ‖z - c • s‖ ^ 2 + 2 * inner ℝ (z - c • s) (c • s) + ‖c • s‖ ^ 2 := by
          rw [norm_add_sq_real]
        _ = ‖z - c • s‖ ^ 2 + 2 * dotProduct (z - c • s) (c • s) + ‖c • s‖ ^ 2 := by
          simp [PiLp.inner_apply, dotProduct, mul_comm]
        _ = ‖z - c • s‖ ^ 2 + ‖c • s‖ ^ 2 := by
          rw [horthDot]
          ring
    have hnonneg : 0 ≤ ‖c • s‖ ^ 2 := by positivity
    have hsquare_le : ‖z - c • s‖ ^ 2 ≤ ‖z‖ ^ 2 := by
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsquare_le

/-- Helper for Chapter05 Theorem 5.4.13: the projector complement in the Broyden error update has
operator norm at most `1`. -/
lemma broydenProjectorComplement_norm_le_one
    (s : BroydenPoint n) :
    ‖((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s)‖ ≤ 1 := by
  -- Bound the operator norm through the pointwise orthogonal-projection estimate.
  have hbound :
      ‖matrixToOperator
          ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
    intro z
    calc
      ‖matrixToOperator
          ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s) z‖
          ≤ ‖z‖ := broydenProjectorComplement_apply_norm_le s z
      _ = 1 * ‖z‖ := by ring
  simpa [matrixToOperator] using
    (Matrix.l2_opNorm_toEuclideanCLM
      ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s)).symm.trans_le hbound

/-- Helper for Chapter05 Theorem 5.4.13: the normalized rank-one correction
`((sᵀ s)⁻¹) u sᵀ` has operator norm at most `‖u‖ / ‖s‖`. -/
lemma broydenNormalizedRankOneCorrection_norm_le
    (u s : BroydenPoint n) :
    ‖matrixToOperator ((((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec u s : BroydenMatrix n))‖ ≤
      ‖u‖ / ‖s‖ := by
  by_cases hs : s = 0
  · -- The degenerate secant branch collapses because the rank-one factor vanishes.
    subst hs
    simp
  · have hss : dotProduct s s ≠ 0 := by
      intro hzero
      exact hs <| by
        simpa using congrArg (WithLp.toLp 2) ((dotProduct_self_eq_zero).1 hzero)
    have hdot : dotProduct s s = ‖s‖ ^ (2 : ℕ) := by
      simpa [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq s).symm
    have hs_norm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs
    have hbound :
        ‖matrixToOperator
            ((((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec u s : BroydenMatrix n))‖ ≤
          ‖u‖ / ‖s‖ := by
      -- Compute the action on a test vector and bound the scalar factor by Cauchy-Schwarz.
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
      intro z
      have happly :
          matrixToOperator
              ((((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec u s : BroydenMatrix n)) z =
            (((dotProduct s z) / (dotProduct s s)) : ℝ) • u := by
        ext i
        simp [matrixToOperator, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
          Matrix.vecMulVec_mulVec, div_eq_mul_inv]
        ring
      have hinner :
          |dotProduct s z| ≤ ‖s‖ * ‖z‖ := by
        simpa [PiLp.inner_apply, dotProduct, Real.norm_eq_abs, mul_comm] using
          norm_inner_le_norm (𝕜 := ℝ) s z
      have hden_abs : |dotProduct s s| = ‖s‖ ^ (2 : ℕ) := by
        rw [abs_of_nonneg (by rw [hdot]; positivity), hdot]
      have hs_sq_pos : 0 < ‖s‖ ^ (2 : ℕ) := by
        positivity
      calc
        ‖matrixToOperator
            ((((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec u s : BroydenMatrix n)) z‖
            = ‖(((dotProduct s z) / (dotProduct s s)) : ℝ) • u‖ := by
                rw [happly]
        _ = |(dotProduct s z) / (dotProduct s s)| * ‖u‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ = (|dotProduct s z| * ‖u‖) / ‖s‖ ^ (2 : ℕ) := by
              rw [abs_div, hden_abs]
              field_simp [hs_norm_pos.ne']
        _ ≤ ((‖s‖ * ‖z‖) * ‖u‖) / ‖s‖ ^ (2 : ℕ) := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hinner (norm_nonneg _)) hs_sq_pos.le
        _ = (‖u‖ / ‖s‖) * ‖z‖ := by
              field_simp [hs_norm_pos.ne']
    exact hbound

/-- Helper for Chapter05 Theorem 5.4.13: subtracting `F'(x*)` from the rank-one Broyden update
produces the projector-plus-remainder decomposition `(5.4.65)`. -/
lemma broydenRankOneUpdate_sub_fderivMatrix_eq
    (F : BroydenPoint n → BroydenPoint n)
    (xStar : BroydenPoint n)
    (B : BroydenMatrix n) (s y : BroydenPoint n) :
    broydenRankOneUpdate B s y - fderivMatrix F xStar =
      (B - fderivMatrix F xStar) *
          ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s) +
        (dotProduct s s)⁻¹ •
          Matrix.vecMulVec (y - Matrix.toEuclideanLin (fderivMatrix F xStar) s) s := by
  let DF : BroydenMatrix n := fderivMatrix F xStar
  let E : BroydenMatrix n := B - DF
  calc
    broydenRankOneUpdate B s y - DF
        = E + (dotProduct s s)⁻¹ • Matrix.vecMulVec (y - Matrix.toEuclideanLin B s) s := by
            simp [broydenRankOneUpdate_eq, DF, E, sub_eq_add_neg, add_assoc, add_left_comm,
              add_comm]
    _ = E + (dotProduct s s)⁻¹ •
          Matrix.vecMulVec ((y - Matrix.toEuclideanLin DF s) - Matrix.toEuclideanLin E s) s := by
            congr 2
            ext i
            simp [DF, E, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = (E * ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s)) +
          (dotProduct s s)⁻¹ • Matrix.vecMulVec (y - Matrix.toEuclideanLin DF s) s := by
            rw [right_mul_rank_one_projector_eq]
            ext i j
            simp [Matrix.vecMulVec_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
              sub_eq_add_neg]
            ring
    _ = (B - DF) * ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s) +
          (dotProduct s s)⁻¹ • Matrix.vecMulVec (y - Matrix.toEuclideanLin DF s) s := by
            simp [E]

/-- Helper for Chapter05 Theorem 5.4.13: once the source-facing Broyden run is known to be
well-defined, linearly convergent, and to have vanishing secant-error ratio, Theorem 5.4.3
upgrades the run to `Q`-superlinear convergence. -/
lemma qSuperlinear_of_wellDefinedLinearAndSecantErrorRatio
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    {x : ℕ → BroydenPoint n} {B : ℕ → BroydenMatrix n}
    (hwell : IsWellDefinedBroydenRankOneIteration D F x0 B0 x B)
    (hlinear : LinearlyConvergesTo x hF.xStar)
    (hsecant :
      Tendsto
        (quasiNewtonSecantErrorRatio F hF.xStar (fun k ↦ matrixToOperator (B k)) x)
        atTop
        (nhds 0)) :
    HasQSuperlinearConvergenceTo x hF.xStar := by
  have hx_tendsto :
      Tendsto x atTop (nhds hF.xStar) :=
    (linearlyConvergesTo_tendsto_and_summableErrorNorm hlinear).1
  have hstep :
      ∀ k : ℕ,
        x (k + 1) = x k - (matrixToOperator (B k)).inverse (F (x k)) := by
    -- Normalize the Broyden step equation to the canonical quasi-Newton form from Theorem 5.4.3.
    intro k
    simpa [broydenNextIterate, quasiNewtonNextIterate] using hwell.generated.step_eq k
  -- Feed the secant-ratio limit into the canonical Chapter 5 superlinear criterion.
  exact
    (quasiNewton_superlinear_iff_secantErrorRatio_tendsto_zero F hF
      (fun k ↦ matrixToOperator (B k)) x hwell.matrices_invertible hstep hwell.iterates_mem
      hx_tendsto).2 hsecant

/-- Helper for Chapter05 Theorem 5.4.13: sufficiently small operator-norm perturbations of the
reference Jacobian remain invertible. -/
lemma broydenOperator_isInvertible_near_reference
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    ∃ ρ > 0, ∀ ⦃B : BroydenOperator n⦄,
      ‖B - fderiv ℝ F hF.xStar‖ < ρ → B.IsInvertible := by
  let DFstar : BroydenOperator n := fderiv ℝ F hF.xStar
  have hRange :
      Set.range (fun e : BroydenPoint n ≃L[ℝ] BroydenPoint n ↦ (e : BroydenOperator n)) ∈
        nhds DFstar := by
    -- Rewrite the reference Jacobian as a continuous linear equivalence and use its standard
    -- neighborhood inside the ambient operator space.
    rcases hF.fderiv_isInvertible with ⟨e, he⟩
    simpa [DFstar, he] using e.nhds
  rcases Metric.mem_nhds_iff.mp hRange with ⟨ρ, hρ_pos, hρsub⟩
  refine ⟨ρ, hρ_pos, ?_⟩
  intro B hB
  have hBall : B ∈ Metric.ball DFstar ρ := by
    simpa [Metric.mem_ball, dist_eq_norm, DFstar] using hB
  rcases hρsub hBall with ⟨e, he⟩
  -- Membership in the nearby equivalence range witnesses invertibility.
  simpa [he] using (ContinuousLinearMap.isInvertible_equiv (f := e))

/-- Helper for Chapter05 Theorem 5.4.13: admissible Broyden states whose iterate stays in `D`,
remains within the fixed radius `ε` of `xStar`, and whose combined Jacobian/iterate error is
controlled by `2 * δ`. -/
def broydenLyapunovDom
    (D : Set (BroydenPoint n)) (xStar : BroydenPoint n) (DFstar : BroydenOperator n)
    (γ ε δ : ℝ) : Set (BroydenPoint n × BroydenOperator n) :=
  {p |
    p.1 ∈ D ∧
      ‖p.1 - xStar‖ ≤ ε ∧
        ‖p.2 - DFstar‖ + 6 * γ * ‖p.1 - xStar‖ ≤ 2 * δ}

/-- Helper for Chapter05 Theorem 5.4.13: a uniform Jacobian-error bound and a uniform inverse
bound contract one Broyden step by a factor `1 / 2` relative to the current iterate error. -/
lemma halfCurrentNextError_of_uniformBounds
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {x : BroydenPoint n} {B : BroydenOperator n} {ξ ε δ : ℝ}
    (hx : x ∈ D)
    (hB : B.IsInvertible)
    (hinv : ‖B.inverse‖ ≤ ξ)
    (hBclose : ‖B - fderiv ℝ F hF.xStar‖ ≤ 2 * δ)
    (hxerr : ‖x - hF.xStar‖ ≤ ε)
    (hcontract : ξ * (max hF.gamma 0 * ε + 2 * δ) ≤ 1 / 2) :
    ‖quasiNewtonNextIterate F x B - hF.xStar‖ ≤ (1 / 2 : ℝ) * ‖x - hF.xStar‖ := by
  have hξ_nonneg : 0 ≤ ξ := le_trans (norm_nonneg _) hinv
  have hδ_nonneg : 0 ≤ δ := by
    nlinarith [norm_nonneg (B - fderiv ℝ F hF.xStar), hBclose]
  have hγ_nonneg : 0 ≤ max hF.gamma 0 := by
    simp
  have hinner :
      (max hF.gamma 0 * ‖x - hF.xStar‖ + ‖B - fderiv ℝ F hF.xStar‖) * ‖x - hF.xStar‖ ≤
        (max hF.gamma 0 * ε + 2 * δ) * ‖x - hF.xStar‖ := by
    have hcoeff :
        max hF.gamma 0 * ‖x - hF.xStar‖ + ‖B - fderiv ℝ F hF.xStar‖ ≤
          max hF.gamma 0 * ε + 2 * δ := by
      nlinarith
    exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
  -- Route correction: prove the one-step contraction directly from the current error instead of
  -- forcing the generic dyadic owner from Theorem 5.4.9 into this local support estimate.
  calc
    ‖quasiNewtonNextIterate F x B - hF.xStar‖
        ≤ ‖B.inverse‖ *
            ((max hF.gamma 0 * ‖x - hF.xStar‖ + ‖B - fderiv ℝ F hF.xStar‖) *
              ‖x - hF.xStar‖) := quasiNewtonNextError_le hF hx hB
    _ ≤ ξ * ((max hF.gamma 0 * ε + 2 * δ) * ‖x - hF.xStar‖) := by
          exact mul_le_mul hinv hinner (by positivity) hξ_nonneg
    _ = (ξ * (max hF.gamma 0 * ε + 2 * δ)) * ‖x - hF.xStar‖ := by
          ring
    _ ≤ (1 / 2 : ℝ) * ‖x - hF.xStar‖ := by
          exact mul_le_mul_of_nonneg_right hcontract (norm_nonneg _)

/-- Helper for Chapter05 Theorem 5.4.13: the rank-one Broyden update satisfies the source
additive Jacobian-error estimate on the matrix surface. -/
lemma broydenRankOneUpdateMatrixAdditiveBound
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {x : BroydenPoint n} {B Bnext : BroydenOperator n}
    (hx : x ∈ D)
    (hxnext : quasiNewtonNextIterate F x B ∈ D)
    (hBnext : Bnext ∈ broydenRankOneUpdateFunction F x B) :
    ‖operatorToMatrix Bnext - fderivMatrix F hF.xStar‖ ≤
      ‖operatorToMatrix B - fderivMatrix F hF.xStar‖ +
        max hF.gamma 0 *
          (‖quasiNewtonNextIterate F x B - hF.xStar‖ + 2 * ‖x - hF.xStar‖) := by
  let xNext : BroydenPoint n := quasiNewtonNextIterate F x B
  let s : BroydenPoint n := xNext - x
  let y : BroydenPoint n := F xNext - F x
  let DF : BroydenMatrix n := fderivMatrix F hF.xStar
  let correction : BroydenMatrix n :=
    (dotProduct s s)⁻¹ • Matrix.vecMulVec (y - Matrix.toEuclideanLin DF s) s
  have hupdate :
      Bnext =
        matrixToOperator
          (broydenRankOneUpdate (operatorToMatrix B) s y) := by
    simpa [xNext, s, y] using
      (mem_broydenRankOneUpdateFunction_iff F x B Bnext).1 hBnext
  have hrem :
      ‖y - Matrix.toEuclideanLin DF s‖ ≤
        max hF.gamma 0 *
          (‖xNext - hF.xStar‖ + 2 * ‖x - hF.xStar‖) * ‖s‖ := by
    have hDFapply :
        Matrix.toEuclideanLin DF s = (fderiv ℝ F hF.xStar) s := by
      simpa [DF, fderivMatrix, s] using
        (matrixToOperator_apply (fderivMatrix F hF.xStar) s).symm
    -- Rewrite the linearization remainder exactly on the Broyden secant step `s = xNext - x`.
    simpa [xNext, s, y, DF, hDFapply] using
      linearizationRemainder_le_errorControl F hF hxnext hx
  have hcorr :
      ‖correction‖ ≤
        max hF.gamma 0 *
          (‖xNext - hF.xStar‖ + 2 * ‖x - hF.xStar‖) := by
    have hrank :
        ‖correction‖ ≤ ‖y - Matrix.toEuclideanLin DF s‖ / ‖s‖ := by
      have hrankOp :
          ‖matrixToOperator correction‖ ≤ ‖y - Matrix.toEuclideanLin DF s‖ / ‖s‖ := by
        simpa [correction] using
          broydenNormalizedRankOneCorrection_norm_le
            (y - Matrix.toEuclideanLin DF s) s
      have hcorrNorm : ‖matrixToOperator correction‖ = ‖correction‖ := by
        simpa using (matrixToOperator_sub_norm_eq correction (0 : BroydenMatrix n))
      rw [hcorrNorm] at hrankOp
      exact hrankOp
    by_cases hs : s = 0
    · have hzero :
        y - Matrix.toEuclideanLin DF s = 0 := by
          have : ‖y - Matrix.toEuclideanLin DF s‖ ≤ 0 := by
            simpa [hs] using hrem
          exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
      -- On a zero step, the rank-one correction collapses because its numerator is zero.
      have hnonneg :
          0 ≤
            max hF.gamma 0 *
              (‖xNext - hF.xStar‖ + 2 * ‖x - hF.xStar‖) := by
        positivity
      simpa [correction, hs, hzero] using hnonneg
    · have hs_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs
      refine hrank.trans ?_
      refine (div_le_iff₀ hs_pos).2 ?_
      simpa using hrem
  -- Decompose the update as the projector term plus the normalized correction and bound each
  -- contribution separately.
  calc
    ‖operatorToMatrix Bnext - fderivMatrix F hF.xStar‖
        = ‖(operatorToMatrix B - DF) *
              ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s) +
            correction‖ := by
              rw [hupdate, operatorToMatrix_matrixToOperator]
              simpa [DF, correction] using
                congrArg norm
                  (broydenRankOneUpdate_sub_fderivMatrix_eq F hF.xStar (operatorToMatrix B) s y)
    _ ≤
        ‖(operatorToMatrix B - DF) *
            ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s)‖ +
          ‖correction‖ := norm_add_le _ _
    _ ≤
        ‖operatorToMatrix B - DF‖ *
            ‖(1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s‖ +
          ‖correction‖ := by
            exact add_le_add (norm_mul_le _ _) le_rfl
    _ ≤ ‖operatorToMatrix B - DF‖ * 1 + ‖correction‖ := by
          gcongr
          exact broydenProjectorComplement_norm_le_one s
    _ = ‖operatorToMatrix B - fderivMatrix F hF.xStar‖ + ‖correction‖ := by
          simp [DF]
    _ ≤
        ‖operatorToMatrix B - fderivMatrix F hF.xStar‖ +
          max hF.gamma 0 *
            (‖quasiNewtonNextIterate F x B - hF.xStar‖ + 2 * ‖x - hF.xStar‖) := by
              gcongr

/-- Helper for Chapter05 Theorem 5.4.13: the matrix-side Broyden additive estimate transports
back to the operator-norm surface used by Theorem 5.4.9. -/
lemma broydenRankOneUpdateOperatorAdditiveBound
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {x : BroydenPoint n} {B Bnext : BroydenOperator n}
    (hx : x ∈ D)
    (hxnext : quasiNewtonNextIterate F x B ∈ D)
    (hBnext : Bnext ∈ broydenRankOneUpdateFunction F x B) :
    ‖Bnext - fderiv ℝ F hF.xStar‖ ≤
      ‖B - fderiv ℝ F hF.xStar‖ +
        max hF.gamma 0 *
          (‖quasiNewtonNextIterate F x B - hF.xStar‖ + 2 * ‖x - hF.xStar‖) := by
  have hnextEq :
      ‖Bnext - fderiv ℝ F hF.xStar‖ =
        ‖operatorToMatrix Bnext - fderivMatrix F hF.xStar‖ := by
    simpa [fderivMatrix] using
      (matrixToOperator_sub_norm_eq (operatorToMatrix Bnext) (fderivMatrix F hF.xStar))
  have hcurrEq :
      ‖B - fderiv ℝ F hF.xStar‖ =
        ‖operatorToMatrix B - fderivMatrix F hF.xStar‖ := by
    simpa [fderivMatrix] using
      (matrixToOperator_sub_norm_eq (operatorToMatrix B) (fderivMatrix F hF.xStar))
  -- Rewrite both operator-norm errors on the matrix surface exactly once.
  calc
    ‖Bnext - fderiv ℝ F hF.xStar‖
        = ‖operatorToMatrix Bnext - fderivMatrix F hF.xStar‖ := hnextEq
    _ ≤ ‖operatorToMatrix B - fderivMatrix F hF.xStar‖ +
          max hF.gamma 0 *
            (‖quasiNewtonNextIterate F x B - hF.xStar‖ + 2 * ‖x - hF.xStar‖) :=
          broydenRankOneUpdateMatrixAdditiveBound hF hx hxnext hBnext
    _ = ‖B - fderiv ℝ F hF.xStar‖ +
          max hF.gamma 0 *
            (‖quasiNewtonNextIterate F x B - hF.xStar‖ + 2 * ‖x - hF.xStar‖) := by
          rw [← hcurrEq]

/-- Helper for Chapter05 Theorem 5.4.13: explicit radii make the concrete Lyapunov owner
`broydenLyapunovDom` support well-defined singleton Broyden rank-one iterations. -/
lemma broydenLyapunovSupport_of_smallRadii
    (D : Set (BroydenPoint n)) (F : BroydenPoint n → BroydenPoint n)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    ∃ ε > 0, ∃ δ > 0,
      SupportsLocalWellDefinedJacobianIteration
        (broydenRankOneUpdateFunction F) F hF.xStar (fderiv ℝ F hF.xStar)
        (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) ε δ) := by
  let γF0 : ℝ := max hF.gamma 0
  have hγF0_nonneg : 0 ≤ γF0 := by
    simp [γF0]
  have hDnhds : D ∈ nhds hF.xStar := hF.open_domain.mem_nhds hF.xStar_mem
  rcases Metric.mem_nhds_iff.mp hDnhds with ⟨ρD, hρD_pos, hball⟩
  rcases broydenOperator_isInvertible_near_reference hF with ⟨ρInv, hρInv_pos, hInvNear⟩
  rcases inverseNormBoundNearReferenceJacobian hF with
    ⟨ρNorm, hρNorm_pos, ξ, hξ_pos, hInverseBound⟩
  let ρ : ℝ := min ρInv ρNorm
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρInv_pos hρNorm_pos
  have hρ_le_inv : ρ ≤ ρInv := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_norm : ρ ≤ ρNorm := by
    dsimp [ρ]
    exact min_le_right _ _
  let δ : ℝ := min (ρ / 4) (1 / (8 * ξ))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min ?_ ?_
    · nlinarith
    · positivity
  have hδ_le_rho_quarter : δ ≤ ρ / 4 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_inv : δ ≤ 1 / (8 * ξ) := by
    dsimp [δ]
    exact min_le_right _ _
  have hδ_lt_ρ : δ < ρ := by
    have hquarter_lt : ρ / 4 < ρ := by
      nlinarith
    exact lt_of_le_of_lt hδ_le_rho_quarter hquarter_lt
  have h2δ_lt_ρ : 2 * δ < ρ := by
    nlinarith
  let ε : ℝ := min (ρD / 2) (min (δ / (6 * γF0 + 1)) (1 / (4 * ξ * (γF0 + 1))))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    refine lt_min ?_ ?_
    · nlinarith
    · refine lt_min ?_ ?_
      · positivity
      · positivity
  have hε_le_rhoD_half : ε ≤ ρD / 2 := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_lt_ρD : ε < ρD := by
    have hhalf_lt : ρD / 2 < ρD := by
      nlinarith
    exact lt_of_le_of_lt hε_le_rhoD_half hhalf_lt
  have hε_le_δratio : ε ≤ δ / (6 * γF0 + 1) := by
    dsimp [ε]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε_le_inv : ε ≤ 1 / (4 * ξ * (γF0 + 1)) := by
    dsimp [ε]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hγF0_add_one_pos : 0 < γF0 + 1 := by
    nlinarith
  have h6γF0ε : 6 * γF0 * ε ≤ δ := by
    have hden_pos : 0 < 6 * γF0 + 1 := by
      nlinarith
    have htmp : ε * (6 * γF0 + 1) ≤ δ := by
      exact (le_div_iff₀ hden_pos).mp hε_le_δratio
    nlinarith
  have hγpart :
      ξ * (γF0 * ε) ≤ 1 / 4 := by
    have hγF0ε :
        γF0 * ε ≤ (γF0 + 1) * ε := by
      nlinarith
    have hmain :
        (γF0 + 1) * ε ≤ (γF0 + 1) * (1 / (4 * ξ * (γF0 + 1))) := by
      exact mul_le_mul_of_nonneg_left hε_le_inv (by nlinarith)
    have hrewrite :
        (γF0 + 1) * (1 / (4 * ξ * (γF0 + 1))) = 1 / (4 * ξ) := by
      field_simp [hξ_pos.ne', hγF0_add_one_pos.ne']
    have htmp : γF0 * ε ≤ 1 / (4 * ξ) := by
      exact hγF0ε.trans (hmain.trans_eq hrewrite)
    have hmul : ξ * (γF0 * ε) ≤ ξ * (1 / (4 * ξ)) := by
      exact mul_le_mul_of_nonneg_left htmp (le_of_lt hξ_pos)
    have hξrewrite : ξ * (1 / (4 * ξ)) = 1 / 4 := by
      field_simp [hξ_pos.ne']
    exact hmul.trans_eq hξrewrite
  have hδpart : ξ * (2 * δ) ≤ 1 / 4 := by
    have htwoδ :
        2 * δ ≤ 2 * (1 / (8 * ξ)) := by
      exact mul_le_mul_of_nonneg_left hδ_le_inv (by positivity)
    have htwoδ' : 2 * δ ≤ 1 / (4 * ξ) := by
      have hrewrite : 2 * (1 / (8 * ξ)) = 1 / (4 * ξ) := by
        field_simp [hξ_pos.ne']
        ring
      exact htwoδ.trans_eq hrewrite
    have hmul : ξ * (2 * δ) ≤ ξ * (1 / (4 * ξ)) := by
      exact mul_le_mul_of_nonneg_left htwoδ' (le_of_lt hξ_pos)
    have hξrewrite : ξ * (1 / (4 * ξ)) = 1 / 4 := by
      field_simp [hξ_pos.ne']
    exact hmul.trans_eq hξrewrite
  have hcontract : ξ * (γF0 * ε + 2 * δ) ≤ 1 / 2 := by
    nlinarith [hγpart, hδpart]
  refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
    intro x B hx hB
    have hxD : x ∈ D := by
      apply hball
      simpa [Metric.mem_ball, dist_eq_norm] using lt_trans hx hε_lt_ρD
    have hdom :
        ‖B - fderiv ℝ F hF.xStar‖ + 6 * γF0 * ‖x - hF.xStar‖ ≤ 2 * δ := by
      nlinarith [le_of_lt hB, le_of_lt hx, h6γF0ε]
    have hBinv :
        B.IsInvertible := by
      apply hInvNear
      exact lt_of_lt_of_le (lt_trans hB hδ_lt_ρ) hρ_le_inv
    exact ⟨⟨hxD, le_of_lt hx, hdom⟩, hBinv⟩
  · refine ⟨?_, ?_⟩
    · intro x B _ _
      -- The Broyden rank-one rule is singleton-valued, so every admissible stage has an update.
      refine ⟨matrixToOperator
        (broydenRankOneUpdate (operatorToMatrix B)
          (quasiNewtonNextIterate F x B - x)
          (F (quasiNewtonNextIterate F x B) - F x)), ?_⟩
      simp [broydenRankOneUpdateFunction]
    · intro x B Bnext hdom hBinv hBnext
      rcases hdom with ⟨hxD, hxε, hlyap⟩
      have hBclose : ‖B - fderiv ℝ F hF.xStar‖ ≤ 2 * δ := by
        nlinarith [hlyap, norm_nonneg (x - hF.xStar), hγF0_nonneg]
      have hBltNorm : ‖B - fderiv ℝ F hF.xStar‖ < ρNorm := by
        exact lt_of_lt_of_le (lt_of_le_of_lt hBclose h2δ_lt_ρ) hρ_le_norm
      have hInvBound : ‖B.inverse‖ ≤ ξ := hInverseBound hBltNorm
      have hnext_half :
          ‖quasiNewtonNextIterate F x B - hF.xStar‖ ≤ (1 / 2 : ℝ) * ‖x - hF.xStar‖ :=
        halfCurrentNextError_of_uniformBounds hF hxD hBinv hInvBound hBclose hxε hcontract
      have hxnext_le_ε : ‖quasiNewtonNextIterate F x B - hF.xStar‖ ≤ ε := by
        calc
          ‖quasiNewtonNextIterate F x B - hF.xStar‖ ≤ (1 / 2 : ℝ) * ‖x - hF.xStar‖ := hnext_half
          _ ≤ ‖x - hF.xStar‖ := by
                have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num
                have hnorm_nonneg : 0 ≤ ‖x - hF.xStar‖ := norm_nonneg (x - hF.xStar)
                simpa using mul_le_mul_of_nonneg_right hhalf_le_one hnorm_nonneg
          _ ≤ ε := hxε
      have hxnextD : quasiNewtonNextIterate F x B ∈ D := by
        apply hball
        have hxnext_lt_ρD : ‖quasiNewtonNextIterate F x B - hF.xStar‖ < ρD := by
          exact lt_of_le_of_lt hxnext_le_ε hε_lt_ρD
        simpa [Metric.mem_ball, dist_eq_norm] using hxnext_lt_ρD
      have hBnext_raw :=
        broydenRankOneUpdateOperatorAdditiveBound hF hxD hxnextD hBnext
      have hnextLyap :
          ‖Bnext - fderiv ℝ F hF.xStar‖ +
              6 * γF0 * ‖quasiNewtonNextIterate F x B - hF.xStar‖ ≤
            2 * δ := by
        set t : ℝ :=
          γF0 * (‖quasiNewtonNextIterate F x B - hF.xStar‖ + 2 * ‖x - hF.xStar‖)
        set s : ℝ := 6 * γF0 * ‖quasiNewtonNextIterate F x B - hF.xStar‖
        have hscalar :
            t + s ≤ 6 * γF0 * ‖x - hF.xStar‖ := by
          have hinner :
              ‖quasiNewtonNextIterate F x B - hF.xStar‖ + 2 * ‖x - hF.xStar‖ +
                  6 * ‖quasiNewtonNextIterate F x B - hF.xStar‖ ≤
                6 * ‖x - hF.xStar‖ := by
            nlinarith [hnext_half, norm_nonneg (x - hF.xStar)]
          have hscaled := mul_le_mul_of_nonneg_left hinner hγF0_nonneg
          calc
            t + s
                = γF0 *
                    (‖quasiNewtonNextIterate F x B - hF.xStar‖ + 2 * ‖x - hF.xStar‖ +
                      6 * ‖quasiNewtonNextIterate F x B - hF.xStar‖) := by
                        simp [t, s]
                        ring
            _ ≤ γF0 * (6 * ‖x - hF.xStar‖) := hscaled
            _ = 6 * γF0 * ‖x - hF.xStar‖ := by ring
        have hBnext_sum :
            ‖Bnext - fderiv ℝ F hF.xStar‖ + s ≤
              ‖B - fderiv ℝ F hF.xStar‖ + (t + s) := by
          have hraw :
              ‖Bnext - fderiv ℝ F hF.xStar‖ + s ≤
                ‖B - fderiv ℝ F hF.xStar‖ + t + s :=
            add_le_add_left hBnext_raw s
          calc
            ‖Bnext - fderiv ℝ F hF.xStar‖ + s
                ≤ ‖B - fderiv ℝ F hF.xStar‖ + t + s := hraw
            _ = ‖B - fderiv ℝ F hF.xStar‖ + (t + s) := by ring
        calc
          ‖Bnext - fderiv ℝ F hF.xStar‖ + s
              ≤ ‖B - fderiv ℝ F hF.xStar‖ + (t + s) := hBnext_sum
          _ ≤ ‖B - fderiv ℝ F hF.xStar‖ + 6 * γF0 * ‖x - hF.xStar‖ := by
                have hraw :
                    ‖B - fderiv ℝ F hF.xStar‖ + (t + s) ≤
                      ‖B - fderiv ℝ F hF.xStar‖ + 6 * γF0 * ‖x - hF.xStar‖ :=
                  add_le_add_right hscalar ‖B - fderiv ℝ F hF.xStar‖
                exact hraw
          _ ≤ 2 * δ := hlyap
      have hnextTerm_nonneg :
          0 ≤ 6 * γF0 * ‖quasiNewtonNextIterate F x B - hF.xStar‖ := by
        positivity
      have hBnextClose : ‖Bnext - fderiv ℝ F hF.xStar‖ ≤ 2 * δ := by
        have hdrop :
            ‖Bnext - fderiv ℝ F hF.xStar‖ ≤
              ‖Bnext - fderiv ℝ F hF.xStar‖ +
                6 * γF0 * ‖quasiNewtonNextIterate F x B - hF.xStar‖ :=
          le_add_of_nonneg_right hnextTerm_nonneg
        exact hdrop.trans hnextLyap
      have hBnextInv :
          Bnext.IsInvertible := by
        apply hInvNear
        exact lt_of_lt_of_le (lt_of_le_of_lt hBnextClose h2δ_lt_ρ) hρ_le_inv
      have hnextDom :
          (quasiNewtonNextIterate F x B, Bnext) ∈
            broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) ε δ := by
        refine ⟨hxnextD, hxnext_le_ε, ?_⟩
        simpa [γF0] using hnextLyap
      exact ⟨hBnextInv, hnextDom⟩

/-- Helper for Chapter05 Theorem 5.4.13: the Lyapunov-domain owner for the rank-one Broyden
update satisfies the additive-update hypotheses of Theorem 5.4.9. -/
lemma broydenLyapunovAdditiveUpdateCondition
    (D : Set (BroydenPoint n)) (F : BroydenPoint n → BroydenPoint n)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    ∃ ε > 0, ∃ δ > 0,
      SatisfiesAdditiveLocalUpdateBound
        (broydenRankOneUpdateFunction F) F hF.xStar (fderiv ℝ F hF.xStar)
        (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) ε δ)
        (4 * max hF.gamma 0) := by
  rcases broydenLyapunovSupport_of_smallRadii D F hF with ⟨ε, hε, δ, hδ, hSupport⟩
  refine ⟨ε, hε, δ, hδ, ?_⟩
  refine ⟨hSupport, ?_⟩
  intro x B Bnext hdom hBinv hBnext
  have hAdvance := hSupport.2.2 x B Bnext hdom hBinv hBnext
  rcases hdom with ⟨hxD, _, _⟩
  rcases hAdvance with ⟨_, hnextDom⟩
  have hxnextD : quasiNewtonNextIterate F x B ∈ D := hnextDom.1
  set a : ℝ := ‖quasiNewtonNextIterate F x B - hF.xStar‖
  set b : ℝ := ‖x - hF.xStar‖
  have ha : 0 ≤ a := by
    simp [a]
  have hb : 0 ≤ b := by
    simp [b]
  have hγ_nonneg : 0 ≤ max hF.gamma 0 := by
    simp
  have hscalar :
      max hF.gamma 0 * (a + 2 * b) ≤
        ((4 * max hF.gamma 0) / 2) * (a + b) := by
    -- Compare the source Broyden coefficient with the additive-owner coefficient from
    -- Theorem 5.4.9 only after the update estimate is already on the correct norm surface.
    nlinarith
  -- Reuse the operator-surface additive estimate and then widen the scalar coefficient once.
  calc
    ‖Bnext - fderiv ℝ F hF.xStar‖
        ≤ ‖B - fderiv ℝ F hF.xStar‖ +
            max hF.gamma 0 *
              (‖quasiNewtonNextIterate F x B - hF.xStar‖ + 2 * ‖x - hF.xStar‖) :=
      broydenRankOneUpdateOperatorAdditiveBound hF hxD hxnextD hBnext
    _ = ‖B - fderiv ℝ F hF.xStar‖ + max hF.gamma 0 * (a + 2 * b) := by
          simp [a, b]
    _ ≤ ‖B - fderiv ℝ F hF.xStar‖ + ((4 * max hF.gamma 0) / 2) * (a + b) := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left hscalar ‖B - fderiv ℝ F hF.xStar‖
    _ = ‖B - fderiv ℝ F hF.xStar‖ +
          ((4 * max hF.gamma 0) / 2) *
            (‖quasiNewtonNextIterate F x B - hF.xStar‖ + ‖x - hF.xStar‖) := by
          simp [a, b]

/-- Helper for Chapter05 Theorem 5.4.13: a sufficiently small initial point and Jacobian matrix
produce the abstract Jacobian-side small-start convergence package for the singleton Broyden
update rule. -/
lemma broydenRankOne_smallStartConvergenceData
    (D : Set (BroydenPoint n)) (F : BroydenPoint n → BroydenPoint n)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    ∃ εDom > 0, ∃ δDom > 0, ∃ ε > 0, ∃ δ > 0,
      ∀ x0 : BroydenPoint n, ∀ B0 : BroydenMatrix n,
      ‖x0 - hF.xStar‖ < ε →
      ‖B0 - fderivMatrix F hF.xStar‖ < δ →
        JacobianQuasiNewtonSmallStartConvergence D F
          (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
          (broydenRankOneUpdateFunction F) hF.xStar x0 (matrixToOperator B0) := by
  rcases broydenLyapunovAdditiveUpdateCondition D F hF with
    ⟨εDom, hεDom, δDom, hδDom, hUpdate⟩
  rcases
      jacobianQuasiNewtonSmallStartConvergence_of_update_condition D F hF
        (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
        (broydenRankOneUpdateFunction F)
        (Or.inl ⟨4 * max hF.gamma 0, hUpdate⟩) with
    ⟨ε, hε, δ, hδ, hsmall⟩
  refine ⟨εDom, hεDom, δDom, hδDom, ε, hε, δ, hδ, ?_⟩
  intro x0 B0 hx0 hB0
  have hB0op :
      ‖matrixToOperator B0 - fderiv ℝ F hF.xStar‖ < δ := by
    have hnormEq :
        ‖matrixToOperator B0 - fderiv ℝ F hF.xStar‖ =
          ‖B0 - fderivMatrix F hF.xStar‖ := by
      simpa [fderivMatrix] using
        (matrixToOperator_sub_norm_eq B0 (fderivMatrix F hF.xStar))
    rw [hnormEq]
    exact hB0
  -- Route correction: keep the concrete Lyapunov owner visible, and let Theorem 5.4.9 provide
  -- the executable small-start radii for that fixed owner.
  simpa using hsmall x0 (matrixToOperator B0) hx0 hB0op

/-- Helper for Chapter05 Theorem 5.4.13: the scalar inequality
`√(a² - b²) ≤ a - b² / (2a)` behind `(5.4.71)` holds for `0 ≤ b ≤ a`. -/
lemma sqrt_sq_sub_sq_le
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    Real.sqrt (a ^ 2 - b ^ 2) ≤ a - b ^ 2 / (2 * a) := by
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := by
      nlinarith
    subst ha0
    subst hb0
    simp
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hright_nonneg : 0 ≤ a - b ^ 2 / (2 * a) := by
      have hdiv : b ^ 2 / (2 * a) ≤ a / 2 := by
        have htwoa_pos : 0 < 2 * a := by positivity
        refine (div_le_iff₀ htwoa_pos).2 ?_
        nlinarith
      nlinarith
    refine Real.sqrt_le_iff.mpr ?_
    constructor
    · exact hright_nonneg
    · have hsq :
          a ^ 2 - b ^ 2 ≤ (a - b ^ 2 / (2 * a)) ^ 2 := by
        -- After clearing the positive denominator, the desired bound is the elementary
        -- quadratic identity behind `(5.4.71)`.
        field_simp [ha0]
        nlinarith
      simpa using hsq

/-- Helper for Chapter05 Theorem 5.4.13: the Frobenius norm of the normalized rank-one
correction `((sᵀ s)⁻¹) u sᵀ` is at most `‖u‖ / ‖s‖`. -/
lemma frobeniusNormalizedRankOneCorrection_norm_le
    (u s : BroydenPoint n) :
    ‖((((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec u s : BroydenMatrix n))‖_F ≤ ‖u‖ / ‖s‖ := by
  -- The `_F` notation is an abbreviation, so provide the Frobenius norm structure explicitly for
  -- the few generic norm lemmas used below.
  letI := Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  letI := Matrix.frobeniusNormedSpace (m := Fin n) (n := Fin n) (R := ℝ) (α := ℝ)
  letI := Matrix.frobeniusNormSMulClass (R := ℝ) (m := Fin n) (n := Fin n) (α := ℝ)
  by_cases hs : s = 0
  · -- The degenerate branch collapses because the rank-one factor itself is zero.
    subst hs
    simp [matrixFrobeniusNorm]
  · have hs_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs
    have hdot : dotProduct s s = ‖s‖ ^ (2 : ℕ) := by
      simpa [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq s).symm
    have hdot_nonneg : 0 ≤ dotProduct s s := by
      rw [hdot]
      positivity
    have hrank :
        ((((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec u s : BroydenMatrix n)) =
          Matrix.vecMulVec (((dotProduct s s)⁻¹ : ℝ) • u) s := by
      ext i j
      simp [Matrix.vecMulVec_apply, smul_eq_mul, mul_assoc]
    -- Rewrite the Frobenius norm of the rank-one matrix into a scalar times the exact
    -- Frobenius norm formula for `Matrix.vecMulVec`.
    calc
      ‖((((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec u s : BroydenMatrix n))‖_F
          = ‖Matrix.vecMulVec (((dotProduct s s)⁻¹ : ℝ) • u) s‖_F := by
              rw [hrank]
      _ = ‖(((dotProduct s s)⁻¹ : ℝ) • u)‖ * ‖s‖ := by
            simpa [matrixFrobeniusNorm] using
              frobenius_norm_vecMulVec_eq (((dotProduct s s)⁻¹ : ℝ) • u) s
      _ = |(dotProduct s s)⁻¹| * (‖u‖ * ‖s‖) := by
            rw [norm_smul, Real.norm_eq_abs]
            ring
      _ = (dotProduct s s)⁻¹ * (‖u‖ * ‖s‖) := by
            rw [abs_of_nonneg (inv_nonneg.mpr hdot_nonneg)]
      _ = (‖s‖ ^ (2 : ℕ))⁻¹ * (‖u‖ * ‖s‖) := by
            rw [hdot]
      _ = (‖u‖ * ‖s‖) / ‖s‖ ^ (2 : ℕ) := by
            rw [div_eq_mul_inv, mul_comm]
      _ ≤ ‖u‖ / ‖s‖ := by
            exact le_of_eq <| by
              field_simp [hs_pos.ne']

/-- Helper for Chapter05 Theorem 5.4.13: Lyapunov-domain membership bounds the Frobenius norm of
the Jacobian error matrices by the fixed dimension-dependent constant `√n * (2 * δDom)`. -/
lemma broydenFrobeniusError_uniformBound
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {εDom δDom : ℝ} {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    (A : JacobianQuasiNewtonIteration D F
      (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
      (broydenRankOneUpdateFunction F) x0 (matrixToOperator B0)) :
    ∀ k,
      ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F ≤
        Real.sqrt (n : ℝ) * (2 * δDom) := by
  intro k
  rcases A.in_dom k with ⟨_, _, hlyap⟩
  have hγ_nonneg : 0 ≤ max hF.gamma 0 := by
    simp
  have hop :
      ‖A.B k - fderiv ℝ F hF.xStar‖ ≤ 2 * δDom := by
    -- Drop the nonnegative Lyapunov correction term to isolate the operator-norm error.
    nlinarith [hlyap, norm_nonneg (A.x k - hF.xStar), hγ_nonneg]
  have hmatrix :
      ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖ ≤ 2 * δDom := by
    have hEq :
        ‖A.B k - fderiv ℝ F hF.xStar‖ =
          ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖ := by
      simpa [fderivMatrix] using
        matrixToOperator_sub_norm_eq
          (operatorToMatrix (A.B k)) (fderivMatrix F hF.xStar)
    rw [hEq] at hop
    exact hop
  -- Compare the Frobenius norm to the matrix `ℓ₂` operator norm once.
  calc
    ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F
        ≤ Real.sqrt (n : ℝ) *
            ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖ :=
          matrixFrobeniusNorm_le_sqrt_cols_mul_matrixL2OperatorNorm _
    _ ≤ Real.sqrt (n : ℝ) * (2 * δDom) := by
          gcongr

/-- Helper for Chapter05 Theorem 5.4.13: the secant-error ratio for the Jacobian-side Broyden
iteration is exactly the matrix-action ratio for the matrix error `operatorToMatrix (A.B k) -
fderivMatrix F hF.xStar`. -/
lemma broydenSecantRatio_eq_matrixRatio
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {εDom δDom : ℝ} {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    (A : JacobianQuasiNewtonIteration D F
      (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
      (broydenRankOneUpdateFunction F) x0 (matrixToOperator B0))
    (k : ℕ) :
    quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k =
      ‖Matrix.toEuclideanLin
          (operatorToMatrix (A.B k) - fderivMatrix F hF.xStar)
          (A.x (k + 1) - A.x k)‖ / ‖A.x (k + 1) - A.x k‖ := by
  -- Rewrite the operator difference through `operatorToMatrix` once, then stay on the matrix side.
  rw [quasiNewtonSecantErrorRatio_apply]
  have hdiff :
      matrixToOperator
          (operatorToMatrix (A.B k) - fderivMatrix F hF.xStar) =
        A.B k - fderiv ℝ F hF.xStar := by
    calc
      matrixToOperator
          (operatorToMatrix (A.B k) - fderivMatrix F hF.xStar)
          =
            matrixToOperator (operatorToMatrix (A.B k)) -
              matrixToOperator (fderivMatrix F hF.xStar) := by
                simp
      _ = A.B k - fderiv ℝ F hF.xStar := by
            simp [fderivMatrix]
  rw [← hdiff, matrixToOperator_apply]

/-- Helper for Chapter05 Theorem 5.4.13: the secant-error ratio is bounded by the Frobenius norm
of the matrix error once the quotient is rewritten on the matrix side. -/
lemma broydenSecantRatio_le_frobeniusError
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {εDom δDom : ℝ} {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    (A : JacobianQuasiNewtonIteration D F
      (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
      (broydenRankOneUpdateFunction F) x0 (matrixToOperator B0))
    (k : ℕ) :
    quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k ≤
      ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F := by
  letI := Matrix.frobeniusSeminormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  letI := Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  by_cases hstep : A.x (k + 1) = A.x k
  · -- A zero step makes the secant quotient vanish outright.
    rw [broydenSecantRatio_eq_matrixRatio hF A k]
    have hnonneg : 0 ≤ ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F := by
      exact norm_nonneg _
    simp [hstep, hnonneg]
  · have hstepPos : 0 < ‖A.x (k + 1) - A.x k‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hstep)
    -- Otherwise divide the matrix-vector Frobenius estimate by the positive step norm.
    rw [broydenSecantRatio_eq_matrixRatio hF A k]
    refine (div_le_iff₀ hstepPos).2 ?_
    simpa [Matrix.toLpLin_apply (p := (2 : ENNReal)) (q := (2 : ENNReal)), Matrix.sub_mulVec,
      l2Norm, lpNorm, mul_comm] using
      (matrixMulVecTwoNorm_le_matrixFrobeniusNorm_mul_vectorTwoNorm
        (operatorToMatrix (A.B k) - fderivMatrix F hF.xStar)
        (A.x (k + 1) - A.x k).ofLp)

/-- Helper for Chapter05 Theorem 5.4.13: the Broyden Jacobian error matrix satisfies the exact
projector-plus-remainder decomposition `(5.4.65)` at each iteration. -/
lemma broydenFrobeniusOneStepDecomposition
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {εDom δDom : ℝ} {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    (A : JacobianQuasiNewtonIteration D F
      (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
      (broydenRankOneUpdateFunction F) x0 (matrixToOperator B0))
    (k : ℕ) :
    operatorToMatrix (A.B (k + 1)) - fderivMatrix F hF.xStar =
      (operatorToMatrix (A.B k) - fderivMatrix F hF.xStar) *
          ((1 : BroydenMatrix n) -
            (dotProduct (A.x (k + 1) - A.x k) (A.x (k + 1) - A.x k))⁻¹ •
              Matrix.vecMulVec (A.x (k + 1) - A.x k) (A.x (k + 1) - A.x k)) +
        (dotProduct (A.x (k + 1) - A.x k) (A.x (k + 1) - A.x k))⁻¹ •
          Matrix.vecMulVec
            (F (A.x (k + 1)) - F (A.x k) -
              Matrix.toEuclideanLin (fderivMatrix F hF.xStar) (A.x (k + 1) - A.x k))
            (A.x (k + 1) - A.x k) := by
  -- Unpack the singleton Broyden update rule and then invoke the exact matrix decomposition.
  have hupdate :
      A.B (k + 1) =
        matrixToOperator
          (broydenRankOneUpdate
            (operatorToMatrix (A.B k))
            (A.x (k + 1) - A.x k)
            (F (A.x (k + 1)) - F (A.x k))) := by
    have hmem :=
      (mem_broydenRankOneUpdateFunction_iff F (A.x k) (A.B k) (A.B (k + 1))).1
        (A.update_mem k)
    simpa [A.step_eq k] using hmem
  rw [hupdate, operatorToMatrix_matrixToOperator]
  -- Route correction: keep the exact Broyden update on the matrix side before applying norms.
  simpa using
    broydenRankOneUpdate_sub_fderivMatrix_eq
      F hF.xStar (operatorToMatrix (A.B k)) (A.x (k + 1) - A.x k)
      (F (A.x (k + 1)) - F (A.x k))

/-- Helper for Chapter05 Theorem 5.4.13: the orthogonal-projector complement from `(5.4.65)`
has the exact Frobenius square identity appearing in `(5.4.70)`. -/
lemma broydenProjectorComplement_frobenius_sq
    (E : BroydenMatrix n) (s : BroydenPoint n) :
    ‖E * ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s)‖_F ^ 2 =
      ‖E‖_F ^ 2 - (‖Matrix.toEuclideanLin E s‖ / ‖s‖) ^ 2 := by
  -- Local instance justification (normed-space): the `_F` notation is shorthand for the
  -- Frobenius norm structure on matrices, and the generic norm lemmas below need that instance.
  letI := Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  letI := Matrix.frobeniusNormedSpace (m := Fin n) (n := Fin n) (R := ℝ) (α := ℝ)
  letI := Matrix.frobeniusNormSMulClass (R := ℝ) (m := Fin n) (n := Fin n) (α := ℝ)
  have hdot : dotProduct s s = ‖s‖ ^ (2 : ℕ) := by
    simpa [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq s).symm
  calc
    ‖E * ((1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s)‖_F ^ 2
        = ‖E‖_F ^ 2 +
            ((-2 * dotProduct s s + ‖s‖ ^ 2) / (dotProduct s s) ^ 2) *
              ‖Matrix.toEuclideanLin E s‖ ^ 2 := by
              simpa [matrixFrobeniusNorm] using
                (frobenius_right_mul_self_rank_one_sq E s (dotProduct s s))
    _ = ‖E‖_F ^ 2 - (‖Matrix.toEuclideanLin E s‖ / ‖s‖) ^ 2 := by
          by_cases hs : s = 0
          · subst hs
            simp
          · have hs_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs
            rw [hdot]
            field_simp [hs_pos.ne']
            ring

/-- Helper for Chapter05 Theorem 5.4.13: the Frobenius norm of the Broyden Jacobian error
satisfies the additive one-step bound behind the telescope gap. -/
lemma broydenFrobeniusOneStepUpperBound
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {εDom δDom : ℝ} {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    (A : JacobianQuasiNewtonIteration D F
      (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
      (broydenRankOneUpdateFunction F) x0 (matrixToOperator B0))
    (k : ℕ) :
    ‖operatorToMatrix (A.B (k + 1)) - fderivMatrix F hF.xStar‖_F ≤
      ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F +
        max hF.gamma 0 * (‖A.x (k + 1) - hF.xStar‖ + 2 * ‖A.x k - hF.xStar‖) := by
  -- Local instance justification (normed-space): use the Frobenius norm as the only matrix norm
  -- surface while proving the additive bound.
  letI := Matrix.frobeniusSeminormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  letI := Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  letI := Matrix.frobeniusNormedSpace (m := Fin n) (n := Fin n) (R := ℝ) (α := ℝ)
  letI := Matrix.frobeniusNormSMulClass (R := ℝ) (m := Fin n) (n := Fin n) (α := ℝ)
  let E : BroydenMatrix n := operatorToMatrix (A.B k) - fderivMatrix F hF.xStar
  let ENext : BroydenMatrix n := operatorToMatrix (A.B (k + 1)) - fderivMatrix F hF.xStar
  let s : BroydenPoint n := A.x (k + 1) - A.x k
  let P : BroydenMatrix n :=
    (1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s
  let u : BroydenPoint n :=
    F (A.x (k + 1)) - F (A.x k) - Matrix.toEuclideanLin (fderivMatrix F hF.xStar) s
  let corr : BroydenMatrix n :=
    ((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec u s
  let rem : ℝ := max hF.gamma 0 * (‖A.x (k + 1) - hF.xStar‖ + 2 * ‖A.x k - hF.xStar‖)
  have hdecomp : ENext = E * P + corr := by
    -- Route correction: keep the update identity on the matrix side before taking Frobenius
    -- norms.
    simpa [E, ENext, s, P, u, corr] using broydenFrobeniusOneStepDecomposition hF A k
  have hremVec :
      ‖u‖ ≤ rem * ‖s‖ := by
    have hDFapply :
        Matrix.toEuclideanLin (fderivMatrix F hF.xStar) s = (fderiv ℝ F hF.xStar) s := by
      simpa [fderivMatrix, s] using
        (matrixToOperator_apply (fderivMatrix F hF.xStar) s).symm
    -- Rewrite the linearization remainder exactly on the Broyden secant step.
    simpa [u, rem, s, hDFapply] using
      linearizationRemainder_le_errorControl F hF (A.iterates_mem (k + 1)) (A.iterates_mem k)
  have hcorr :
      ‖corr‖_F ≤ rem := by
    by_cases hs : s = 0
    · have hrem_nonneg : 0 ≤ rem := by
        positivity
      have hcorr_zero : ‖corr‖_F = 0 := by
        simp [corr, s, hs]
      rw [hcorr_zero]
      exact hrem_nonneg
    · have hs_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs
      -- Divide the normalized rank-one Frobenius estimate by the positive step norm.
      refine (frobeniusNormalizedRankOneCorrection_norm_le u s).trans ?_
      refine (div_le_iff₀ hs_pos).2 ?_
      simpa [rem] using hremVec
  have hproj_le :
      ‖E * P‖_F ≤ ‖E‖_F := by
    have hsq :
        ‖E * P‖_F ^ 2 ≤ ‖E‖_F ^ 2 := by
      calc
        ‖E * P‖_F ^ 2 = ‖E‖_F ^ 2 - (‖Matrix.toEuclideanLin E s‖ / ‖s‖) ^ 2 := by
          simpa [E, P, s] using broydenProjectorComplement_frobenius_sq E s
        _ ≤ ‖E‖_F ^ 2 := by
            nlinarith [sq_nonneg (‖Matrix.toEuclideanLin E s‖ / ‖s‖)]
    have hleft_nonneg : 0 ≤ ‖E * P‖_F := by
      exact norm_nonneg _
    have hright_nonneg : 0 ≤ ‖E‖_F := by
      exact norm_nonneg _
    exact (sq_le_sq₀ hleft_nonneg hright_nonneg).1 hsq
  have htriangle :
      ‖E * P + corr‖_F ≤ ‖E * P‖_F + ‖corr‖_F := by
    simpa using (norm_add_le (E * P) corr)
  -- Bound the next Frobenius error by the projector contribution and the remainder term.
  calc
    ‖operatorToMatrix (A.B (k + 1)) - fderivMatrix F hF.xStar‖_F = ‖ENext‖_F := by
      rfl
    _ = ‖E * P + corr‖_F := by
          simpa using congrArg matrixFrobeniusNorm hdecomp
    _ ≤ ‖E * P‖_F + ‖corr‖_F := htriangle
    _ ≤ ‖E‖_F + rem := by
          gcongr
    _ = ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F +
          max hF.gamma 0 * (‖A.x (k + 1) - hF.xStar‖ + 2 * ‖A.x k - hF.xStar‖) := by
          rfl

/-- Helper for Chapter05 Theorem 5.4.13: the Frobenius norm of the Broyden Jacobian error
satisfies the scalar one-step recurrence needed for the secant-square telescope. -/
lemma broydenFrobeniusOneStepRecurrence
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {εDom δDom : ℝ} {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    (A : JacobianQuasiNewtonIteration D F
      (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
      (broydenRankOneUpdateFunction F) x0 (matrixToOperator B0))
    (k : ℕ) :
    (quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k) ^ 2 ≤
      2 * ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F *
        ((‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F -
            ‖operatorToMatrix (A.B (k + 1)) - fderivMatrix F hF.xStar‖_F) +
          max hF.gamma 0 * (‖A.x (k + 1) - hF.xStar‖ + 2 * ‖A.x k - hF.xStar‖)) := by
  -- Local instance justification (normed-space): keep the whole proof in one Frobenius norm
  -- world and only use generic norm lemmas after installing the matrix instances once.
  letI := Matrix.frobeniusSeminormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  letI := Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  letI := Matrix.frobeniusNormedSpace (m := Fin n) (n := Fin n) (R := ℝ) (α := ℝ)
  letI := Matrix.frobeniusNormSMulClass (R := ℝ) (m := Fin n) (n := Fin n) (α := ℝ)
  let E : BroydenMatrix n := operatorToMatrix (A.B k) - fderivMatrix F hF.xStar
  let ENext : BroydenMatrix n := operatorToMatrix (A.B (k + 1)) - fderivMatrix F hF.xStar
  let s : BroydenPoint n := A.x (k + 1) - A.x k
  let P : BroydenMatrix n :=
    (1 : BroydenMatrix n) - (dotProduct s s)⁻¹ • Matrix.vecMulVec s s
  let u : BroydenPoint n :=
    F (A.x (k + 1)) - F (A.x k) - Matrix.toEuclideanLin (fderivMatrix F hF.xStar) s
  let corr : BroydenMatrix n :=
    ((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec u s
  let a : ℝ := ‖E‖_F
  let aNext : ℝ := ‖ENext‖_F
  let r : ℝ := quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k
  let rem : ℝ := max hF.gamma 0 * (‖A.x (k + 1) - hF.xStar‖ + 2 * ‖A.x k - hF.xStar‖)
  have hdecomp : ENext = E * P + corr := by
    -- Route correction: keep the exact Broyden update decomposition on the matrix side and only
    -- then apply Frobenius estimates.
    simpa [E, ENext, s, P, u, corr] using broydenFrobeniusOneStepDecomposition hF A k
  have hratioEq : r = ‖Matrix.toEuclideanLin E s‖ / ‖s‖ := by
    simpa [r, E, s] using broydenSecantRatio_eq_matrixRatio hF A k
  have ha_nonneg : 0 ≤ a := by
    exact norm_nonneg _
  have hr_nonneg : 0 ≤ r := by
    rw [hratioEq]
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hr_le : r ≤ a := by
    simpa [r, a, E] using broydenSecantRatio_le_frobeniusError hF A k
  have hremVec :
      ‖u‖ ≤ rem * ‖s‖ := by
    have hDFapply :
        Matrix.toEuclideanLin (fderivMatrix F hF.xStar) s = (fderiv ℝ F hF.xStar) s := by
      simpa [fderivMatrix, s] using
        (matrixToOperator_apply (fderivMatrix F hF.xStar) s).symm
    -- Rewrite the nonlinear remainder exactly on the secant step `s = x_{k+1} - x_k`.
    simpa [u, rem, s, hDFapply] using
      linearizationRemainder_le_errorControl F hF (A.iterates_mem (k + 1)) (A.iterates_mem k)
  have hcorr :
      ‖corr‖_F ≤ rem := by
    by_cases hs : s = 0
    · -- On a zero step, the normalized rank-one correction vanishes because its right factor is
      -- the zero vector.
      have hrem_nonneg : 0 ≤ rem := by
        positivity
      have hcorr_zero : ‖corr‖_F = 0 := by
        simp [corr, s, hs]
      rw [hcorr_zero]
      exact hrem_nonneg
    · have hs_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs
      -- Otherwise divide the normalized rank-one Frobenius bound by the positive step norm.
      refine (frobeniusNormalizedRankOneCorrection_norm_le u s).trans ?_
      refine (div_le_iff₀ hs_pos).2 ?_
      simpa [rem] using hremVec
  have hprojSq :
      ‖E * P‖_F ^ 2 = a ^ 2 - r ^ 2 := by
    calc
      ‖E * P‖_F ^ 2 = ‖E‖_F ^ 2 - (‖Matrix.toEuclideanLin E s‖ / ‖s‖) ^ 2 := by
        simpa [E, P, s] using broydenProjectorComplement_frobenius_sq E s
      _ = a ^ 2 - r ^ 2 := by
        rw [show ‖E‖_F = a by rfl, ← hratioEq]
  have hprojEq :
      ‖E * P‖_F = Real.sqrt (a ^ 2 - r ^ 2) := by
    have hproj_nonneg : 0 ≤ ‖E * P‖_F := by
      exact norm_nonneg _
    calc
      ‖E * P‖_F = Real.sqrt (‖E * P‖_F ^ 2) := by
        simp
      _ = Real.sqrt (a ^ 2 - r ^ 2) := by rw [hprojSq]
  have hnext_le :
      aNext ≤ Real.sqrt (a ^ 2 - r ^ 2) + rem := by
    -- Bound the next Frobenius error by the projector contribution plus the normalized
    -- correction term.
    calc
      aNext = ‖ENext‖_F := by rfl
      _ = ‖E * P + corr‖_F := by
            simpa using congrArg matrixFrobeniusNorm hdecomp
      _ ≤ ‖E * P‖_F + ‖corr‖_F := by
            simpa using (norm_add_le (E * P) corr)
      _ ≤ ‖E * P‖_F + rem := by
            gcongr
      _ = Real.sqrt (a ^ 2 - r ^ 2) + rem := by rw [hprojEq]
  have hsqrt_le :
      Real.sqrt (a ^ 2 - r ^ 2) ≤ a - r ^ 2 / (2 * a) := by
    exact sqrt_sq_sub_sq_le ha_nonneg hr_nonneg hr_le
  have hlinearized :
      aNext ≤ a - r ^ 2 / (2 * a) + rem := by
    calc
      aNext ≤ Real.sqrt (a ^ 2 - r ^ 2) + rem := hnext_le
      _ ≤ (a - r ^ 2 / (2 * a)) + rem := by
            gcongr
  by_cases ha0 : a = 0
  · have hr0 : r = 0 := by
      exact (le_antisymm hr_nonneg (by simpa [ha0] using hr_le)).symm
    change r ^ 2 ≤ 2 * a * ((a - aNext) + rem)
    rw [hr0, ha0]
    simp
  · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (Ne.symm ha0)
    have hdiv :
        r ^ 2 / (2 * a) ≤ (a - aNext) + rem := by
      linarith
    have hmul :
        r ^ 2 ≤ ((a - aNext) + rem) * (2 * a) := by
      exact (div_le_iff₀ (show 0 < 2 * a by positivity)).mp hdiv
    change r ^ 2 ≤ 2 * a * ((a - aNext) + rem)
    nlinarith [hmul]

/-- Helper for Chapter05 Theorem 5.4.13: the squared secant-error ratio is controlled by a
telescoping Frobenius term plus the summable forcing term coming from iterate errors. -/
lemma broydenSecantSq_le_telescopeTerm
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {εDom δDom : ℝ} {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    (A : JacobianQuasiNewtonIteration D F
      (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
      (broydenRankOneUpdateFunction F) x0 (matrixToOperator B0))
    (k : ℕ) :
    (quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k) ^ 2 ≤
      2 * (max 1 (Real.sqrt (n : ℝ) * (2 * δDom))) *
        ((‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F -
            ‖operatorToMatrix (A.B (k + 1)) - fderivMatrix F hF.xStar‖_F) +
          max hF.gamma 0 * (‖A.x (k + 1) - hF.xStar‖ + 2 * ‖A.x k - hF.xStar‖)) := by
  let a : ℝ := ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F
  let aNext : ℝ := ‖operatorToMatrix (A.B (k + 1)) - fderivMatrix F hF.xStar‖_F
  let rem : ℝ := max hF.gamma 0 * (‖A.x (k + 1) - hF.xStar‖ + 2 * ‖A.x k - hF.xStar‖)
  let M : ℝ := max 1 (Real.sqrt (n : ℝ) * (2 * δDom))
  have hrec :
      (quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k) ^ 2 ≤
        2 * a * ((a - aNext) + rem) := by
    simpa [a, aNext, rem] using broydenFrobeniusOneStepRecurrence hF A k
  have ha_le_M : a ≤ M := by
    -- Reuse the Lyapunov-domain Frobenius bound, then dominate it by the fixed majorant `M`.
    calc
      a ≤ Real.sqrt (n : ℝ) * (2 * δDom) := by
            simpa [a] using broydenFrobeniusError_uniformBound hF A k
      _ ≤ M := le_max_right _ _
  have hgap_nonneg :
      0 ≤ (a - aNext) + rem := by
    have hupper : aNext ≤ a + rem := by
      simpa [a, aNext, rem] using broydenFrobeniusOneStepUpperBound hF A k
    nlinarith
  have hmajor :
      2 * a * ((a - aNext) + rem) ≤ 2 * M * ((a - aNext) + rem) := by
    gcongr
  exact
    (hrec.trans <| by
      simpa [a, aNext, rem, M] using hmajor)

/-- Helper for Chapter05 Theorem 5.4.13: finite sums of adjacent differences telescope to the
endpoint gap. -/
lemma sum_range_adjacent_sub (a : ℕ → ℝ) (N : ℕ) :
    Finset.sum (Finset.range N) (fun i ↦ a i - a (i + 1)) = a 0 - a N := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      -- Peel off the last summand and use the induction hypothesis on the preceding range.
      rw [Finset.sum_range_succ, ih]
      ring

/-- Helper for Chapter05 Theorem 5.4.13: the forcing remainder sequence in the scalar telescope is
summable along any linearly convergent Jacobian-side Broyden run. -/
lemma broydenRemainder_summable_of_linearConvergence
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {εDom δDom : ℝ} {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    (A : JacobianQuasiNewtonIteration D F
      (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
      (broydenRankOneUpdateFunction F) x0 (matrixToOperator B0))
    (hlinearA : LinearlyConvergesTo A.x hF.xStar) :
    Summable
      (fun k ↦ max hF.gamma 0 * (‖A.x (k + 1) - hF.xStar‖ + 2 * ‖A.x k - hF.xStar‖)) := by
  rcases linearlyConvergesTo_tendsto_and_summableErrorNorm hlinearA with ⟨_, herrorSum⟩
  have herrorShift : Summable (fun k ↦ ‖A.x (k + 1) - hF.xStar‖) := by
    have hshift0 : Summable (fun k ↦ ‖A.x (Nat.succ k) - hF.xStar‖) :=
      herrorSum.comp_injective Nat.succ_injective
    simpa [Nat.succ_eq_add_one] using hshift0
  have hdouble : Summable (fun k ↦ (2 : ℝ) * ‖A.x k - hF.xStar‖) := herrorSum.mul_left 2
  have hadd :
      Summable (fun k ↦ ‖A.x (k + 1) - hF.xStar‖ + (2 : ℝ) * ‖A.x k - hF.xStar‖) :=
    herrorShift.add hdouble
  simpa using hadd.mul_left (max hF.gamma 0)

/-- Helper for Chapter05 Theorem 5.4.13: on the explicit Jacobian-side Broyden iteration chosen
from the small-start package, the squared secant-error ratios are summable. -/
lemma broydenSecantRatio_sqSummable_of_iteration
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {εDom δDom : ℝ} {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    (A : JacobianQuasiNewtonIteration D F
      (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
      (broydenRankOneUpdateFunction F) x0 (matrixToOperator B0))
    (hlinearA : LinearlyConvergesTo A.x hF.xStar) :
    Summable (fun k ↦ (quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k) ^ 2) := by
  letI := Matrix.frobeniusSeminormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  letI := Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  let a : ℕ → ℝ := fun k ↦ ‖operatorToMatrix (A.B k) - fderivMatrix F hF.xStar‖_F
  let rem : ℕ → ℝ :=
    fun k ↦ max hF.gamma 0 * (‖A.x (k + 1) - hF.xStar‖ + 2 * ‖A.x k - hF.xStar‖)
  let M : ℝ := max 1 (Real.sqrt (n : ℝ) * (2 * δDom))
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    exact norm_nonneg _
  have hrem_nonneg : ∀ k, 0 ≤ rem k := by
    intro k
    positivity
  have hremSum : Summable rem := by
    simpa [rem] using broydenRemainder_summable_of_linearConvergence hF A hlinearA
  -- Sum the pointwise telescope inequality, telescope the adjacent differences, and absorb the
  -- forcing partial sums into the convergent `tsum`.
  refine summable_of_sum_range_le (c := 2 * M * (a 0 + ∑' i : ℕ, rem i)) (fun k ↦ sq_nonneg _) ?_
  intro N
  calc
    ∑ i ∈ Finset.range N, (quasiNewtonSecantErrorRatio F hF.xStar A.B A.x i) ^ 2
        ≤
          ∑ i ∈ Finset.range N,
            2 * M * (((a i - a (i + 1)) + rem i)) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              simpa [a, rem, M] using broydenSecantSq_le_telescopeTerm hF A i
    _ = 2 * M * ∑ i ∈ Finset.range N, ((a i - a (i + 1)) + rem i) := by
          rw [← Finset.mul_sum]
    _ = 2 * M * ((∑ i ∈ Finset.range N, (a i - a (i + 1))) + ∑ i ∈ Finset.range N, rem i) := by
          rw [Finset.sum_add_distrib]
    _ = 2 * M * ((a 0 - a N) + ∑ i ∈ Finset.range N, rem i) := by
          rw [sum_range_adjacent_sub]
    _ ≤ 2 * M * (a 0 + ∑ i ∈ Finset.range N, rem i) := by
          gcongr
          have hAN_nonneg : 0 ≤ a N := ha_nonneg N
          nlinarith
    _ ≤ 2 * M * (a 0 + ∑' i : ℕ, rem i) := by
          gcongr
          exact Summable.sum_le_tsum _ (fun i _ ↦ hrem_nonneg i) hremSum

/-- Helper for Chapter05 Theorem 5.4.13: along a well-defined linearly convergent Broyden
rank-one run, the secant-error ratio tends to `0`. -/
lemma broydenRankOne_secantErrorRatio_tendsto_zero
    {D : Set (BroydenPoint n)} {F : BroydenPoint n → BroydenPoint n}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {εDom δDom : ℝ}
    {x0 : BroydenPoint n} {B0 : BroydenMatrix n}
    {x : ℕ → BroydenPoint n} {B : ℕ → BroydenMatrix n}
    (hsmall :
      JacobianQuasiNewtonSmallStartConvergence D F
        (broydenLyapunovDom D hF.xStar (fderiv ℝ F hF.xStar) (max hF.gamma 0) εDom δDom)
        (broydenRankOneUpdateFunction F) hF.xStar x0 (matrixToOperator B0))
    (hgen : IsGeneratedBroydenRankOneIteration F x0 B0 x B)
    :
    Tendsto
      (quasiNewtonSecantErrorRatio F hF.xStar (fun k ↦ matrixToOperator (B k)) x)
      atTop
      (nhds 0) := by
  rcases hsmall.exists_iteration with ⟨A, hlinearA⟩
  have hsummable :
      Summable (fun k ↦ (quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k) ^ 2) :=
    broydenSecantRatio_sqSummable_of_iteration hF A hlinearA
  have hsq_tendsto :
      Tendsto
        (fun k ↦ (quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k) ^ 2)
        atTop
        (nhds 0) := by
    exact Summable.tendsto_atTop_zero hsummable
  have hratioA_nonneg :
      ∀ k, 0 ≤ quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k := by
    intro k
    rw [quasiNewtonSecantErrorRatio_apply]
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hratioA :
      Tendsto (quasiNewtonSecantErrorRatio F hF.xStar A.B A.x) atTop (nhds 0) := by
    have hsqrt_tendsto :
        Tendsto
          (fun k ↦ Real.sqrt ((quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k) ^ 2))
          atTop
          (nhds (Real.sqrt 0)) := by
      exact (Continuous.tendsto Real.continuous_sqrt 0).comp hsq_tendsto
    simpa [Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg, hratioA_nonneg] using hsqrt_tendsto
  have hmatch := generated_eq_jacobianBroydenIteration A hgen
  have hEq :
      quasiNewtonSecantErrorRatio F hF.xStar (fun k ↦ matrixToOperator (B k)) x =
        quasiNewtonSecantErrorRatio F hF.xStar A.B A.x := by
    funext k
    rcases hmatch k with ⟨hxk, hBk⟩
    rcases hmatch (k + 1) with ⟨hxnext, _⟩
    simp [quasiNewtonSecantErrorRatio_apply, hxk, hxnext, hBk]
  simpa [hEq] using hratioA

/-- Chapter05 Theorem 5.4.13: if `F : ℝ^n → ℝ^n` satisfies
`HasQuasiNewtonLocalConvergenceAssumptions D F`, then there exist `ε`, `δ > 0` such that every
initial point `x0` and initial Jacobian approximation `B0` with
`‖x0 - hF.xStar‖ < ε` and `‖B0 - fderivMatrix F hF.xStar‖ < δ` have the property that every
sequence pair `x`, `B` generated by Broyden's rank-one update `(5.4.63)`-`(5.4.64)` from
`x0`, `B0` is well-defined and the iterate sequence `x` converges to `hF.xStar`
`Q`-superlinearly. -/
theorem broydenRankOne_qSuperlinearConvergence_of_small_initial_pair
    (D : Set (BroydenPoint n)) (F : BroydenPoint n → BroydenPoint n)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    ∃ ε > 0, ∃ δ > 0, ∀ x0 : BroydenPoint n, ∀ B0 : BroydenMatrix n,
      ‖x0 - hF.xStar‖ < ε →
      ‖B0 - fderivMatrix F hF.xStar‖ < δ →
      ∀ x : ℕ → BroydenPoint n, ∀ B : ℕ → BroydenMatrix n,
        IsGeneratedBroydenRankOneIteration F x0 B0 x B →
          IsWellDefinedBroydenRankOneIteration D F x0 B0 x B ∧
            HasQSuperlinearConvergenceTo x hF.xStar := by
  -- Route correction: reduce the source theorem to the abstract small-start owner from
  -- Theorem 5.4.9, transport that package back to the singleton Broyden recursion, and isolate
  -- the genuinely Broyden-specific secant-ratio limit as the only remaining hard input.
  rcases broydenRankOne_smallStartConvergenceData D F hF with
    ⟨εDom, hεDom, δDom, hδDom, ε, hε, δ, hδ, hsmall⟩
  refine ⟨ε, hε, δ, hδ, ?_⟩
  intro x0 B0 hx0 hB0 x B hgen
  have hsmall0 := hsmall x0 B0 hx0 hB0
  rcases
      wellDefinedAndLinear_of_smallStartConvergence hF hsmall0 hgen with
    ⟨hwell, hlinear⟩
  have hsecant :
      Tendsto
        (quasiNewtonSecantErrorRatio F hF.xStar (fun k ↦ matrixToOperator (B k)) x)
        atTop
        (nhds 0) :=
    broydenRankOne_secantErrorRatio_tendsto_zero
      (εDom := εDom) (δDom := δDom) hF hsmall0 hgen
  exact
    ⟨hwell, qSuperlinear_of_wellDefinedLinearAndSecantErrorRatio hF hwell hlinear hsecant⟩

end Chapter05Theorem5413
