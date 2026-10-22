/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Lemma_11_5_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Theorem_11_5_5.Comparison

noncomputable section

open Filter

section Chapter11Theorem1155

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * source-facing layer: the accumulation-point KKT conclusion for Algorithm 11.5.2.
-- * current-chapter owners reused here:
--   `LinearlyConstrainedQuarteringSearchMethod`,
--   `IsLinearlyConstrainedProjectedTrialPath`,
--   `linearlyConstrainedAcceptanceCondition11513`, and
--   `LinearEqualityConstrainedProblem`.
-- * bridge/view layer reused here from `Theorem_11_5_5.Comparison`: the problem attached to a
--   method and objective, together with the Chapter 8 KKT view already exported by
--   `LinearEqualityConstrainedProblem`.

/-- Helper for Chapter11 Theorem 11.5.5: a limit of feasible iterates along the accumulation
subsequence remains feasible because the linear feasible set is closed. -/
lemma accumulationPoint_mem_feasibleSet
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {xStar : Point} {φ : ℕ → ℕ}
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar)) :
    xStar ∈ method.feasibleSet := by
  -- Every sampled iterate is feasible, so closedness passes feasibility to the limit point.
  exact
    IsClosed.mem_of_tendsto
      ((LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method).isClosed)
      hxStar <|
      Eventually.of_forall fun k ↦
        iterate_mem_feasibleSet
          f method h_projectedTrialPath
          (Nat.succ_le_succ (Nat.zero_le (φ k)))

/-- Helper for Chapter11 Theorem 11.5.5: the accepted objective values
`k ↦ f (method.iterate (k + 1))` form an antitone sequence because each accepted step satisfies
the source decrease inequality `(11.5.13)`. -/
lemma acceptedObjectiveValues_antitone
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    (h_accepts_eq_11513 :
      ∀ k α, 1 ≤ k →
        method.acceptedAt k α ↔
          linearlyConstrainedAcceptanceCondition11513 f method k α) :
    Antitone (fun k : ℕ ↦ f (method.iterate (k + 1))) := by
  refine antitone_nat_of_succ_le ?_
  intro k
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have haccepted :
      method.acceptedAt (k + 1) (method.stepSize (k + 1)) :=
    LinearlyConstrainedQuarteringSearchMethod.stepSize_accepted method hk
  have h_accepts_step :
      (1 ≤ k + 1 → method.acceptedAt (k + 1) (method.stepSize (k + 1))) ↔
        linearlyConstrainedAcceptanceCondition11513
          f method (k + 1) (method.stepSize (k + 1)) :=
    h_accepts_eq_11513 (k + 1) (method.stepSize (k + 1))
  have h11513 :
      linearlyConstrainedAcceptanceCondition11513
        f method (k + 1) (method.stepSize (k + 1)) :=
    h_accepts_step.1 (fun _ ↦ haccepted)
  have hdecrease :
      f (method.iterate (k + 2)) ≤
        f (method.iterate (k + 1)) -
          method.μ / method.stepSize (k + 1) *
            ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ^ (2 : ℕ) := by
    -- Rewrite the accepted projected trial point as the next iterate.
    simpa [linearlyConstrainedAcceptanceCondition11513,
      h_projectedTrialPath (k + 1) (method.stepSize (k + 1)) hk,
      LinearlyConstrainedQuarteringSearchMethod.iterate_succ_eq_trialPoint method hk,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h11513
  have hμ_nonneg : 0 ≤ method.μ := le_of_lt method.mu_mem.1
  have hstep_nonneg : 0 ≤ method.stepSize (k + 1) := by
    exact le_of_lt (stepSize_pos method hk)
  have hnorm_sq_nonneg :
      0 ≤ ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ^ (2 : ℕ) := by
    positivity
  have hpenalty_nonneg :
      0 ≤ method.μ / method.stepSize (k + 1) *
        ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ^ (2 : ℕ) := by
    exact mul_nonneg (div_nonneg hμ_nonneg hstep_nonneg) hnorm_sq_nonneg
  -- Dropping the nonnegative penalty term yields monotonic decrease.
  exact le_trans hdecrease (sub_le_self _ hpenalty_nonneg)

/-- Helper for Chapter11 Theorem 11.5.5: once an accumulation subsequence converges to `xStar`,
the accepted objective drops `f (x_k) - f (x_(k+1))` tend to `0`. -/
lemma subsequenceObjectiveDrop_tendsto_zero
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_diffAt_feasible : ∀ x ∈ method.feasibleSet, DifferentiableAt ℝ f x)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    (h_accepts_eq_11513 :
      ∀ k α, 1 ≤ k →
        method.acceptedAt k α ↔
          linearlyConstrainedAcceptanceCondition11513 f method k α)
    {xStar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar)) :
    Tendsto (fun k : ℕ ↦ f (method.iterate (k + 1)) - f (method.iterate (k + 2)))
      atTop (nhds 0) := by
  have hxStarFeasible :
      xStar ∈ method.feasibleSet :=
    accumulationPoint_mem_feasibleSet f method h_projectedTrialPath hxStar
  have h_antitone :
      Antitone (fun k : ℕ ↦ f (method.iterate (k + 1))) :=
    acceptedObjectiveValues_antitone f method h_projectedTrialPath h_accepts_eq_11513
  have h_obj_subseq :
      Tendsto (fun k : ℕ ↦ f (method.iterate (φ k + 1))) atTop (nhds (f xStar)) := by
    have h_contWithin : ContinuousWithinAt f method.feasibleSet xStar :=
      (h_diffAt_feasible xStar hxStarFeasible).continuousAt.continuousWithinAt
    -- Restrict the convergent subsequence to the feasible set, then apply continuity on that set.
    exact h_contWithin.tendsto.comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        (fun k : ℕ ↦ method.iterate (φ k + 1)) hxStar <|
        Eventually.of_forall fun k ↦
          iterate_mem_feasibleSet
            f method h_projectedTrialPath
            (Nat.succ_le_succ (Nat.zero_le (φ k)))
  have h_obj :
      Tendsto (fun k : ℕ ↦ f (method.iterate (k + 1))) atTop (nhds (f xStar)) := by
    -- An antitone real sequence converges to the same limit as any convergent subsequence.
    exact
      (tendsto_iff_tendsto_subseq_of_antitone h_antitone hφ.tendsto_atTop).2
        h_obj_subseq
  have h_obj_succ :
      Tendsto (fun k : ℕ ↦ f (method.iterate (k + 2))) atTop (nhds (f xStar)) := by
    simpa [Nat.add_assoc] using (Filter.tendsto_add_atTop_iff_nat 1).2 h_obj
  -- Subtract the shifted convergent objective sequence from the original one.
  simpa [Nat.add_assoc] using h_obj.sub h_obj_succ

/-- Helper for Chapter11 Theorem 11.5.5: the normalized projected-trial displacement is
independent of the positive trial step, so it can be evaluated at the accepted step size. -/
lemma trialRatio_eq_stepRatio
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 < α) :
    ‖method.trialPoint k α - method.iterate k‖ / α =
      ‖method.iterate (k + 1) - method.iterate k‖ / method.stepSize k := by
  have hstep_pos : 0 < method.stepSize k :=
    stepSize_pos method hk
  have hscaled :
      method.stepSize k • (method.trialPoint k α - method.iterate k) =
        α • (method.iterate (k + 1) - method.iterate k) := by
    -- Use homogeneity, then rewrite the accepted trial point as the next iterate.
    simpa [LinearlyConstrainedQuarteringSearchMethod.iterate_succ_eq_trialPoint method hk] using
      projected_trial_displacement_homogeneous
        f method h_projectedTrialPath hk α (method.stepSize k)
  have hnorm_scaled :
      method.stepSize k * ‖method.trialPoint k α - method.iterate k‖ =
        α * ‖method.iterate (k + 1) - method.iterate k‖ := by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hstep_pos, abs_of_pos hα] using
      congrArg norm hscaled
  -- Dividing the norm identity by the positive step sizes gives the normalized ratio identity.
  field_simp [ne_of_gt hα, ne_of_gt hstep_pos] at hnorm_scaled ⊢
  linarith

/-- Helper for Chapter11 Theorem 11.5.5: the accepted normalized displacement at stage `k` is
exactly the norm of the orthogonal projection of `gradient f (x_k)` onto the feasible-direction
kernel `ker Aᵀ`. -/
lemma stepRatio_eq_constraintKernelProjectionNorm
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖method.iterate (k + 1) - method.iterate k‖ / method.stepSize k =
      ‖(LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose)).starProjection
          (gradient f (method.iterate k))‖ := by
  let K : Submodule ℝ Point :=
    LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose)
  have hstep_pos : 0 < method.stepSize k :=
    stepSize_pos method hk
  have hdisp :
      method.iterate (k + 1) - method.iterate k =
        K.starProjection (-method.stepSize k • gradient f (method.iterate k)) := by
    -- Rewrite the accepted displacement through the same star-projection normal form as every
    -- positive projected trial step.
    simpa [K, LinearlyConstrainedQuarteringSearchMethod.iterate_succ_eq_trialPoint method hk] using
      projected_trial_displacement_eq_starProjection
        f method h_projectedTrialPath hk (method.stepSize k)
  -- The star-projection is linear, so the normalized accepted displacement is exactly the norm of
  -- the projected feasible-direction gradient component.
  rw [hdisp]
  simp [K, norm_smul, Real.norm_eq_abs, abs_of_pos hstep_pos, ne_of_gt hstep_pos]

/-- Helper for Chapter11 Theorem 11.5.5: for the affine feasible set of a linear
equality-constrained problem, fixing one positive projected-gradient step already fixes every
smaller nonnegative step, because the positive fixed point yields the variational pairing
condition from Lemma 11.5.4. -/
lemma projectionFixedInterval_of_fixedPositiveStep
    (problem : LinearEqualityConstrainedProblem n m)
    (xStar : Point)
    (hxStar : xStar ∈ problem)
    {α0 : ℝ}
    (hα0 : 0 < α0)
    (hfixed :
      nearestPointProjection
          problem.feasibleSet
          ⟨xStar, hxStar⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          (xStar - α0 • gradient problem.objective xStar) = xStar) :
    ∃ δBar : ℝ,
      0 < δBar ∧
        ∀ α ∈ Set.Icc (0 : ℝ) δBar,
          nearestPointProjection
              problem.feasibleSet
              ⟨xStar, hxStar⟩
              problem.isComplete_feasibleSet
              problem.convex_feasibleSet
              (xStar - α • gradient problem.objective xStar) = xStar := by
  have hpair :
      ∀ x : Point, x ∈ problem → 0 ≤ inner ℝ (x - xStar) (gradient problem.objective xStar) :=
    (LinearEqualityConstrainedProblem.projection_fixed_iff_nonnegative_pairing
      problem xStar hxStar
      (gradient problem.objective xStar) hα0).1 hfixed
  refine ⟨α0, hα0, ?_⟩
  intro α hα
  rcases hα with ⟨hα_nonneg, _hα_le⟩
  rcases eq_or_lt_of_le hα_nonneg with rfl | hα_pos
  · -- The zero step is fixed because `xStar` is already feasible.
    simpa using
      nearestPointProjection_eq_self
        problem.feasibleSet
        ⟨xStar, hxStar⟩
        problem.isComplete_feasibleSet
        problem.convex_feasibleSet
        hxStar
  · -- The pairing condition obtained from the positive fixed point handles every smaller step.
    exact
      (LinearEqualityConstrainedProblem.projection_fixed_iff_nonnegative_pairing
        problem xStar hxStar
        (gradient problem.objective xStar) hα_pos).2 hpair

/-- Helper for Chapter11 Theorem 11.5.5: for the affine feasible set of a linear
equality-constrained problem, the displacement from a feasible base point `x` to the nearest
projection of `x - α • g` is exactly the orthogonal projection of `-α • g` onto the constraint
kernel `ker Aᵀ`. -/
lemma projectionDisplacement_eq_constraintKernelStarProjection
    (problem : LinearEqualityConstrainedProblem n m)
    {x : Point} (hx : x ∈ problem) (g : Point) (α : ℝ) :
    nearestPointProjection
        problem.feasibleSet
        ⟨x, hx⟩
        problem.isComplete_feasibleSet
        problem.convex_feasibleSet
        (x - α • g) - x =
      (LinearMap.ker (Matrix.toEuclideanLin problem.constraintMatrix.transpose)).starProjection
        (-α • g) := by
  let K : Submodule ℝ Point :=
    LinearMap.ker (Matrix.toEuclideanLin problem.constraintMatrix.transpose)
  let projection :=
    nearestPointProjection
      problem.feasibleSet
      ⟨x, hx⟩
      problem.isComplete_feasibleSet
      problem.convex_feasibleSet
      (x - α • g)
  have hprojection_mem : projection ∈ problem := by
    -- The nearest-point projection stays in the affine feasible set.
    exact
      nearestPointProjection_mem
        problem.feasibleSet
        ⟨x, hx⟩
        problem.isComplete_feasibleSet
        problem.convex_feasibleSet
        (x - α • g)
  have hprojection_sub_mem : projection - x ∈ K := by
    -- Two feasible points differ by a direction in the linear constraint kernel.
    change
      Matrix.toEuclideanLin problem.constraintMatrix.transpose (projection - x) = 0
    have hprojection_eq :
        Matrix.toEuclideanLin problem.constraintMatrix.transpose projection =
          problem.constraintTarget := by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) ((problem.mem_feasibleSet_iff projection).1 hprojection_mem)
    have hx_eq :
        Matrix.toEuclideanLin problem.constraintMatrix.transpose x =
          problem.constraintTarget := by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) ((problem.mem_feasibleSet_iff x).1 hx)
    rw [LinearMap.map_sub, hprojection_eq, hx_eq, sub_self]
  have hresidual_mem : (-α • g - (projection - x)) ∈ Kᗮ := by
    refine (Submodule.mem_orthogonal' K (-α • g - (projection - x))).2 ?_
    intro d hd
    have hprojection_add_mem : projection + d ∈ problem := by
      -- Adding a kernel direction preserves the affine feasibility equation.
      have hprojection_eq :
          Matrix.toEuclideanLin problem.constraintMatrix.transpose projection =
            problem.constraintTarget := by
        simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
          congrArg (WithLp.toLp 2) ((problem.mem_feasibleSet_iff projection).1 hprojection_mem)
      have hprojection_add_eq :
          Matrix.toEuclideanLin problem.constraintMatrix.transpose (projection + d) =
            problem.constraintTarget := by
        calc
          Matrix.toEuclideanLin problem.constraintMatrix.transpose (projection + d)
              =
                Matrix.toEuclideanLin problem.constraintMatrix.transpose projection +
                  Matrix.toEuclideanLin problem.constraintMatrix.transpose d := by
                    simp
          _ = problem.constraintTarget := by
                simp [hprojection_eq, show
                  Matrix.toEuclideanLin problem.constraintMatrix.transpose d = 0 from by
                    simpa [K] using hd]
      exact (problem.mem_feasibleSet_iff (projection + d)).2 <| by
        simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
          congrArg WithLp.ofLp hprojection_add_eq
    have hprojection_sub_mem : projection - d ∈ problem := by
      -- The opposite kernel direction stays feasible for the same reason.
      have hprojection_eq :
          Matrix.toEuclideanLin problem.constraintMatrix.transpose projection =
            problem.constraintTarget := by
        simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
          congrArg (WithLp.toLp 2) ((problem.mem_feasibleSet_iff projection).1 hprojection_mem)
      have hprojection_sub_eq :
          Matrix.toEuclideanLin problem.constraintMatrix.transpose (projection - d) =
            problem.constraintTarget := by
        calc
          Matrix.toEuclideanLin problem.constraintMatrix.transpose (projection - d)
              =
                Matrix.toEuclideanLin problem.constraintMatrix.transpose projection -
                  Matrix.toEuclideanLin problem.constraintMatrix.transpose d := by
                    simp
          _ = problem.constraintTarget := by
                simp [hprojection_eq, show
                  Matrix.toEuclideanLin problem.constraintMatrix.transpose d = 0 from by
                    simpa [K] using hd]
      exact (problem.mem_feasibleSet_iff (projection - d)).2 <| by
        simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
          congrArg WithLp.ofLp hprojection_sub_eq
    have hplus_le :
        inner ℝ ((x - α • g) - projection) d ≤ 0 := by
      -- The projection variational inequality against `projection + d` gives one sign.
      simpa [projection, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        real_inner_sub_nearestPointProjection_le_zero
          problem.feasibleSet
          ⟨x, hx⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          (x - α • g)
          (projection + d)
          hprojection_add_mem
    have hminus_le :
        inner ℝ ((x - α • g) - projection) (-d) ≤ 0 := by
      -- Applying the same inequality to `projection - d` forces the opposite sign.
      simpa [projection, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        real_inner_sub_nearestPointProjection_le_zero
          problem.feasibleSet
          ⟨x, hx⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          (x - α • g)
          (projection - d)
          hprojection_sub_mem
    have hnonneg : 0 ≤ inner ℝ ((x - α • g) - projection) d := by
      exact neg_nonpos.mp (by simpa [inner_neg_right] using hminus_le)
    have hzero : inner ℝ ((x - α • g) - projection) d = 0 :=
      le_antisymm hplus_le hnonneg
    -- Rewrite the residual into the star-projection normal form.
    simpa [projection, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
  -- The kernel component with orthogonal residual is uniquely the star projection.
  simpa [K, projection] using
    (K.eq_starProjection_of_mem_orthogonal
      hprojection_sub_mem
      hresidual_mem).symm

/-- Helper for Chapter11 Theorem 11.5.5: if the unit projected-gradient step at a feasible point
is not fixed by the nearest-point projection, then the corresponding constraint-kernel component
of the gradient has strictly positive norm. -/
lemma constraintKernelProjectionNorm_pos_of_nonfixedProjection
    (problem : LinearEqualityConstrainedProblem n m)
    {x : Point} (hx : x ∈ problem) (g : Point)
    (hprojection :
      nearestPointProjection
          problem.feasibleSet
          ⟨x, hx⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          (x - g) ≠ x) :
    0 <
      ‖(LinearMap.ker (Matrix.toEuclideanLin problem.constraintMatrix.transpose)).starProjection
          g‖ := by
  let K : Submodule ℝ Point :=
    LinearMap.ker (Matrix.toEuclideanLin problem.constraintMatrix.transpose)
  by_contra hnonpos
  have hnorm_zero :
      ‖K.starProjection g‖ = 0 := by
    exact le_antisymm (le_of_not_gt hnonpos) (norm_nonneg _)
  have hstar_zero : K.starProjection g = 0 := norm_eq_zero.mp hnorm_zero
  have hdisp_zero :
      nearestPointProjection
          problem.feasibleSet
          ⟨x, hx⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          (x - g) - x = 0 := by
    -- Rewrite the projection displacement into the kernel projection normal form.
    calc
      nearestPointProjection
          problem.feasibleSet
          ⟨x, hx⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          (x - g) - x
          =
            K.starProjection (-g) := by
              simpa [K] using
                projectionDisplacement_eq_constraintKernelStarProjection
                  problem hx g (1 : ℝ)
      _ = -K.starProjection g := by simp
      _ = 0 := by simp [hstar_zero]
  -- Vanishing of the kernel component forces the projection to fix `x`.
  exact hprojection (sub_eq_zero.mp hdisp_zero)

/-- Helper for Chapter11 Theorem 11.5.5: if there is no positive interval of projected-gradient
steps fixing `xStar`, then the unit projected-gradient step is already nonfixed. -/
lemma unitProjectionNonfixed_of_noProjectionFixedInterval
    (problem : LinearEqualityConstrainedProblem n m)
    (xStar : Point)
    (hxStar : xStar ∈ problem)
    (hNoInterval :
      ¬ ∃ δBar : ℝ,
        0 < δBar ∧
          ∀ α ∈ Set.Icc (0 : ℝ) δBar,
            nearestPointProjection
                problem.feasibleSet
                ⟨xStar, hxStar⟩
                problem.isComplete_feasibleSet
                problem.convex_feasibleSet
                (xStar - α • gradient problem.objective xStar) = xStar) :
    nearestPointProjection
        problem.feasibleSet
        ⟨xStar, hxStar⟩
        problem.isComplete_feasibleSet
        problem.convex_feasibleSet
        (xStar - gradient problem.objective xStar) ≠ xStar := by
  intro hfixed
  -- A fixed unit step would extend to a full positive interval by the affine projection lemma.
  exact hNoInterval <|
    projectionFixedInterval_of_fixedPositiveStep
      problem xStar hxStar zero_lt_one <| by
        simpa using hfixed

/-- Helper for Chapter11 Theorem 11.5.5: the constraint-kernel projection norm of the ambient
gradient converges along the given accumulation subsequence. -/
lemma constraintKernelProjectionNorm_tendsto_alongAccumulation
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_gradientContinuousOn : ContinuousOn (gradient f) method.feasibleSet)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {xStar : Point} {φ : ℕ → ℕ}
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar)) :
    Tendsto
      (fun k : ℕ ↦
        ‖(LinearMap.ker
            (Matrix.toEuclideanLin method.constraintMatrix.transpose)).starProjection
            (gradient f (method.iterate (φ k + 1)))‖)
      atTop
      (nhds
        ‖(LinearMap.ker
            (Matrix.toEuclideanLin method.constraintMatrix.transpose)).starProjection
            (gradient f xStar)‖) := by
  let K : Submodule ℝ Point :=
    LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose)
  have hxStarFeasible :
      xStar ∈ method.feasibleSet :=
    accumulationPoint_mem_feasibleSet f method h_projectedTrialPath hxStar
  have hgrad_cont :
      ContinuousWithinAt (gradient f) method.feasibleSet xStar :=
    h_gradientContinuousOn xStar hxStarFeasible
  have hproj_cont :
      ContinuousWithinAt
        (fun x : Point ↦ ‖K.starProjection (gradient f x)‖)
        method.feasibleSet
        xStar := by
    have houter :
        ContinuousWithinAt
          (fun y : Point ↦ ‖K.starProjection y‖)
          Set.univ
          (gradient f xStar) :=
      (K.starProjection.continuous.norm).continuousWithinAt
    exact houter.comp hgrad_cont (by intro y hy; simp)
  -- Restrict the convergent subsequence to the feasible set, then apply the projected-gradient
  -- continuity there.
  exact hproj_cont.tendsto.comp <|
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun k : ℕ ↦ method.iterate (φ k + 1)) hxStar <|
      Eventually.of_forall fun k ↦
        iterate_mem_feasibleSet
          f method h_projectedTrialPath
          (Nat.succ_le_succ (Nat.zero_le (φ k)))

/-- Helper for Chapter11 Theorem 11.5.5: if the accepted normalized displacements stay bounded
below by a positive constant along an accumulation subsequence, then both the accepted
displacements and the accepted step sizes on that subsequence tend to `0`. -/
lemma accumulationRatioLowerBoundForcesSmallSteps
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_diffAt_feasible : ∀ x ∈ method.feasibleSet, DifferentiableAt ℝ f x)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    (h_accepts_eq_11513 :
      ∀ k α, 1 ≤ k →
        method.acceptedAt k α ↔
          linearlyConstrainedAcceptanceCondition11513 f method k α)
    {xStar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar))
    {δ : ℝ} (hδ : 0 < δ)
    (h_lower :
      ∀ j : ℕ,
        δ ≤
          ‖method.iterate (φ j + 2) - method.iterate (φ j + 1)‖ /
            method.stepSize (φ j + 1)) :
    Tendsto
        (fun j : ℕ ↦ ‖method.iterate (φ j + 2) - method.iterate (φ j + 1)‖)
        atTop
        (nhds 0) ∧
      Tendsto
        (fun j : ℕ ↦ method.stepSize (φ j + 1))
        atTop
        (nhds 0) := by
  let drop : ℕ → ℝ :=
    fun k : ℕ ↦ f (method.iterate (k + 1)) - f (method.iterate (k + 2))
  let disp : ℕ → ℝ :=
    fun k : ℕ ↦ ‖method.iterate (k + 2) - method.iterate (k + 1)‖
  have h_drop_zero :=
    subsequenceObjectiveDrop_tendsto_zero
      f method h_diffAt_feasible h_projectedTrialPath h_accepts_eq_11513 hφ hxStar
  have h_drop_subseq :
      Tendsto (fun j : ℕ ↦ drop (φ j)) atTop (nhds 0) := by
    exact h_drop_zero.comp hφ.tendsto_atTop
  have h_drop_lower :
      ∀ j : ℕ, method.μ * δ * disp (φ j) ≤ drop (φ j) := by
    intro j
    let k : ℕ := φ j + 1
    have hk : 1 ≤ k := Nat.succ_le_succ (Nat.zero_le (φ j))
    have h_accepts_step :
        (1 ≤ k → method.acceptedAt k (method.stepSize k)) ↔
          linearlyConstrainedAcceptanceCondition11513
            f method k (method.stepSize k) :=
      h_accepts_eq_11513 k (method.stepSize k)
    have h11513 :
        linearlyConstrainedAcceptanceCondition11513
          f method k (method.stepSize k) :=
      h_accepts_step.1
        (fun _ ↦ LinearlyConstrainedQuarteringSearchMethod.stepSize_accepted method hk)
    have hdecrease :
        f (method.iterate (k + 1)) +
            method.μ / method.stepSize k *
              ‖method.iterate (k + 1) - method.iterate k‖ ^ (2 : ℕ) ≤
          f (method.iterate k) := by
      have hproj_eq :
          method.iterate (k + 1) =
            nearestPointProjection
              method.feasibleSet
              method.feasibleSet_nonempty
              (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
              (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
              (method.iterate k - method.stepSize k • gradient f (method.iterate k)) := by
        rw [LinearlyConstrainedQuarteringSearchMethod.iterate_succ_eq_trialPoint method hk]
        simpa [sub_eq_add_neg] using h_projectedTrialPath k (method.stepSize k) hk
      have hdecrease' :
          f (method.iterate (k + 1)) ≤
            f (method.iterate k) -
              method.μ / method.stepSize k *
                ‖method.iterate (k + 1) - method.iterate k‖ ^ (2 : ℕ) := by
        have h11513' := h11513
        rw [linearlyConstrainedAcceptanceCondition11513] at h11513'
        rw [show
              nearestPointProjection
                  method.feasibleSet
                  method.feasibleSet_nonempty
                  (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
                  (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
                  (method.iterate k - method.stepSize k • gradient f (method.iterate k)) =
                method.iterate (k + 1) from hproj_eq.symm] at h11513'
        -- Rewrite the accepted projected point into the next iterate before reading the decrease.
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h11513'
      -- The accepted-step decrease gives a penalty term controlling the accepted displacement.
      linarith
    have h_ratio_scaled :
        method.μ * δ * ‖method.iterate (k + 1) - method.iterate k‖ ≤
          method.μ / method.stepSize k *
            ‖method.iterate (k + 1) - method.iterate k‖ ^ (2 : ℕ) := by
      have hscale_nonneg :
          0 ≤ method.μ * ‖method.iterate (k + 1) - method.iterate k‖ := by
        exact mul_nonneg (le_of_lt method.mu_mem.1) (norm_nonneg _)
      have hscaled := mul_le_mul_of_nonneg_left (h_lower j) hscale_nonneg
      simpa [k, disp, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using hscaled
    have h_penalty_le :
        method.μ / method.stepSize k *
            ‖method.iterate (k + 1) - method.iterate k‖ ^ (2 : ℕ) ≤
          f (method.iterate k) - f (method.iterate (k + 1)) := by
      linarith
    have h_bound_k :
        method.μ * δ * ‖method.iterate (k + 1) - method.iterate k‖ ≤
          f (method.iterate k) - f (method.iterate (k + 1)) :=
      le_trans h_ratio_scaled h_penalty_le
    simpa [k, drop, disp, Nat.add_assoc] using h_bound_k
  have h_disp_zero :
      Tendsto (fun j : ℕ ↦ disp (φ j)) atTop (nhds 0) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    have hbound_pos : 0 < method.μ * δ * ε := by
      exact mul_pos (mul_pos method.mu_mem.1 hδ) hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h_drop_subseq (method.μ * δ * ε) hbound_pos
    refine ⟨N, ?_⟩
    intro j hj
    have hdrop_nonneg : 0 ≤ drop (φ j) := by
      have hdisp_nonneg : 0 ≤ disp (φ j) := by
        exact norm_nonneg _
      have hlower_nonneg : 0 ≤ method.μ * δ * disp (φ j) := by
        exact mul_nonneg (mul_nonneg (le_of_lt method.mu_mem.1) (le_of_lt hδ)) hdisp_nonneg
      exact le_trans hlower_nonneg (h_drop_lower j)
    have hdrop_small : drop (φ j) < method.μ * δ * ε := by
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hdrop_nonneg] using hN j hj
    have hdisp_scaled :
        method.μ * δ * disp (φ j) < method.μ * δ * ε :=
      lt_of_le_of_lt (h_drop_lower j) hdrop_small
    have hdisp_small :
        disp (φ j) < ε :=
      lt_of_mul_lt_mul_left hdisp_scaled (le_of_lt (mul_pos method.mu_mem.1 hδ))
    simpa [disp, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hdisp_small
  have h_step_zero :
      Tendsto (fun j : ℕ ↦ method.stepSize (φ j + 1)) atTop (nhds 0) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    have hbound_pos : 0 < δ * ε := mul_pos hδ hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h_disp_zero (δ * ε) hbound_pos
    refine ⟨N, ?_⟩
    intro j hj
    have hstep_pos :
        0 < method.stepSize (φ j + 1) := by
      exact stepSize_pos method (Nat.succ_le_succ (Nat.zero_le (φ j)))
    have hdisp_small :
        disp (φ j) < δ * ε := by
      simpa [disp, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hN j hj
    have hstep_scaled :
        δ * method.stepSize (φ j + 1) ≤ disp (φ j) := by
      exact (le_div_iff₀ hstep_pos).mp (h_lower j)
    have hstep_small_scaled :
        δ * method.stepSize (φ j + 1) < δ * ε :=
      lt_of_le_of_lt hstep_scaled hdisp_small
    have hstep_small :
        method.stepSize (φ j + 1) < ε :=
      lt_of_mul_lt_mul_left hstep_small_scaled hδ.le
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hstep_pos.le] using hstep_small
  exact ⟨h_disp_zero, h_step_zero⟩

/-- Helper for Chapter11 Theorem 11.5.5: around the accumulation point `xStar`, continuity of
the ambient gradient on the feasible set yields a uniform first-order upper model on all short
feasible segments whose base point stays sufficiently close to `xStar`. -/
lemma localUniformFeasibleUpperModelNearAccumulation
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_diffAt_feasible : ∀ x ∈ method.feasibleSet, DifferentiableAt ℝ f x)
    (h_gradientContinuousOn : ContinuousOn (gradient f) method.feasibleSet)
    {xStar : Point} {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∃ η > 0, ∀ {x y : Point},
      x ∈ method.feasibleSet →
      y ∈ method.feasibleSet →
      ‖x - xStar‖ < ρ →
      ‖y - x‖ < η →
      f y ≤ f x + inner ℝ (y - x) (gradient f x) + ε * ‖y - x‖ := by
  let D0 : Set Point := Metric.closedBall xStar 1 ∩ method.feasibleSet
  have hD0compact : IsCompact D0 := by
    simpa [D0, Set.inter_comm] using
      (isCompact_closedBall xStar (1 : ℝ)).inter_right
        ((LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method).isClosed)
  have hUniform : UniformContinuousOn (gradient f) D0 := by
    -- Compactness converts the local continuity hypothesis on the feasible set into a usable
    -- uniform modulus on a fixed closed feasible neighborhood of `xStar`.
    refine hD0compact.uniformContinuousOn_of_continuous ?_
    exact h_gradientContinuousOn.mono (by intro z hz; exact hz.2)
  rw [Metric.uniformContinuousOn_iff] at hUniform
  obtain ⟨η0, hη0_pos, hη0⟩ := hUniform ε hε
  let ρ : ℝ := min (1 / 4 : ℝ) (η0 / 2)
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_le_quarter : ρ ≤ 1 / 4 := by
    exact min_le_left _ _
  have hρ_le_eta0 : ρ ≤ η0 := by
    have hhalf_le : η0 / 2 ≤ η0 := by linarith
    exact le_trans (min_le_right _ _) hhalf_le
  refine ⟨ρ, hρ_pos, ρ, hρ_pos, ?_⟩
  intro x y hx hy hx_near hxy
  let D : Set Point := method.feasibleSet ∩ Metric.ball x ρ
  have hxD : x ∈ D := by
    refine ⟨hx, ?_⟩
    simpa [D, Metric.mem_ball] using hρ_pos
  have hyD : y ∈ D := by
    refine ⟨hy, ?_⟩
    simpa [D, Metric.mem_ball, dist_eq_norm] using hxy
  have hxD0 : x ∈ D0 := by
    refine ⟨?_, hx⟩
    have hx_lt_one : dist x xStar < 1 := by
      have hρ_lt_one : ρ < 1 := by
        nlinarith [hρ_le_quarter]
      simpa [dist_eq_norm] using lt_of_lt_of_le hx_near (le_of_lt hρ_lt_one)
    exact le_of_lt hx_lt_one
  have hGateaux :
      ∀ z ∈ D,
        IsGateauxDerivativeWithinAt ℝ D f z
          (InnerProductSpace.toDual ℝ Point (gradient f z)) := by
    intro z hz d
    -- Restrict the ambient gradient derivative formula from the whole feasible set to the short
    -- feasible neighborhood centered at the current base point `x`.
    exact
      (ambient_gradient_gateaux_on_feasible_set
        f method hz.1 (h_diffAt_feasible z hz.1) d).mono
        (by intro w hw; exact hw.1)
  have hbound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖InnerProductSpace.toDual ℝ Point (gradient f (x + t • (y - x))) -
            InnerProductSpace.toDual ℝ Point (gradient f x)‖ ≤ ε := by
    intro t ht
    have hzt_feasible : x + t • (y - x) ∈ method.feasibleSet := by
      exact
        (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method).add_smul_sub_mem
          hx hy ht
    have ht_abs : |t| ≤ 1 := by
      simpa [abs_of_nonneg ht.1] using ht.2
    have hnorm_le :
        ‖t • (y - x)‖ ≤ ‖y - x‖ := by
      calc
        ‖t • (y - x)‖ = |t| * ‖y - x‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * ‖y - x‖ := by
              exact mul_le_mul_of_nonneg_right ht_abs (norm_nonneg _)
        _ = ‖y - x‖ := by ring
    have hdist_le :
        dist (x + t • (y - x)) x ≤ ‖y - x‖ := by
      simpa [dist_eq_norm] using hnorm_le
    have hzt_dist_x : dist (x + t • (y - x)) x < η0 := by
      exact lt_of_le_of_lt hdist_le (lt_of_lt_of_le hxy hρ_le_eta0)
    have hztD0 : x + t • (y - x) ∈ D0 := by
      refine ⟨?_, hzt_feasible⟩
      have hx_dist : dist x xStar < ρ := by
        simpa [dist_eq_norm] using hx_near
      have hzt_dist : dist (x + t • (y - x)) x < ρ := by
        exact lt_of_le_of_lt hdist_le hxy
      have hzt_lt_one : dist (x + t • (y - x)) xStar < 1 := by
        have hsum_lt :
            dist (x + t • (y - x)) x + dist x xStar < ρ + ρ :=
          add_lt_add hzt_dist hx_dist
        have htriangle :
            dist (x + t • (y - x)) xStar ≤
              dist (x + t • (y - x)) x + dist x xStar :=
          dist_triangle _ _ _
        nlinarith
      exact le_of_lt hzt_lt_one
    have hgrad_dist :
        dist (gradient f (x + t • (y - x))) (gradient f x) < ε :=
      hη0 (x + t • (y - x)) hztD0 x hxD0 hzt_dist_x
    have hgrad_norm :
        ‖gradient f (x + t • (y - x)) - gradient f x‖ < ε := by
      simpa [dist_eq_norm] using hgrad_dist
    have hdual_dist :
        ‖InnerProductSpace.toDual ℝ Point
            (gradient f (x + t • (y - x)) - gradient f x)‖ < ε := by
      rw [(InnerProductSpace.toDual ℝ Point).norm_map]
      exact hgrad_norm
    have htoDual_sub :
        InnerProductSpace.toDual ℝ Point
            (gradient f (x + t • (y - x)) - gradient f x) =
          InnerProductSpace.toDual ℝ Point (gradient f (x + t • (y - x))) -
            InnerProductSpace.toDual ℝ Point (gradient f x) := by
      exact
        (InnerProductSpace.toDual ℝ Point).map_sub
          (gradient f (x + t • (y - x)))
          (gradient f x)
    exact le_of_lt <| by
      rw [← htoDual_sub]
      exact hdual_dist
  have hremainder :
      ‖f y - f x - inner ℝ (y - x) (gradient f x)‖ ≤ ε * ‖y - x‖ := by
    have hremainder' :
        ‖f y - f x -
            (InnerProductSpace.toDual ℝ Point (gradient f x)) (y - x)‖ ≤
          ε * ‖y - x‖ := by
      -- Apply the chapter remainder theorem on the short feasible neighborhood where the
      -- derivative field is the ambient gradient and the gradient deviation is uniformly bounded.
      exact
        norm_image_sub_sub_le_of_segment_fderiv_deviation_bound
          (D := D)
          (F := f)
          (F' := fun z => InnerProductSpace.toDual ℝ Point (gradient f z))
          (x := x)
          (y := y)
          (z := x)
          (C := ε)
          ((LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method).inter
            (convex_ball x ρ))
          hGateaux
          hbound
          hyD
          hxD
    simpa [D, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hremainder'
  have hscalar_bound :
      f y - f x - inner ℝ (y - x) (gradient f x) ≤ ε * ‖y - x‖ := by
    -- Pass from the norm remainder bound to the one-sided upper estimate used by the source
    -- acceptance contradiction.
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hremainder)
  have hsub_le :
      f y - f x ≤ inner ℝ (y - x) (gradient f x) + ε * ‖y - x‖ := by
    linarith
  have hfinal :
      f y ≤ f x + (inner ℝ (y - x) (gradient f x) + ε * ‖y - x‖) := by
    linarith
  simpa [add_assoc, add_left_comm, add_comm] using hfinal

/-- Chapter11 Theorem 11.5.5: assume `f` is continuously differentiable on the feasible set
`method.feasibleSet` in the ambient sense, namely `f` is differentiable at each feasible point and
the ambient gradient field `gradient f` is continuous on `method.feasibleSet`. If `method` is the
Algorithm 11.5.2 sequence for the projected trial path and the Step `(11.5.13)` acceptance test
determined by `f`, then any accumulation point of the iterate sequence `{x_k}`, encoded by a
strictly monotone subsequence of the source stages `k ≥ 1` converging to `xStar`, admits a
multiplier vector making `xStar` a Chapter 8 KKT point of the equality-only constrained-problem
bridge attached to `f` and the constraint system of `method`. -/
theorem linearlyConstrainedQuarteringSearchMethod_accumulationPoint_isKKTPoint
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_diffAt_feasible : ∀ x ∈ method.feasibleSet, DifferentiableAt ℝ f x)
    (h_gradientContinuousOn : ContinuousOn (gradient f) method.feasibleSet)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    (h_accepts_eq_11513 :
      ∀ k α, 1 ≤ k →
        method.acceptedAt k α ↔
          linearlyConstrainedAcceptanceCondition11513 f method k α)
    {xStar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar)) :
    ∃ multiplier : Multiplier,
      (method.toLinearEqualityConstrainedProblem f).toConstrainedOptimizationProblem.IsKKTPoint
        xStar.ofLp multiplier.ofLp := by
  let problem := method.toLinearEqualityConstrainedProblem f
  let K : Submodule ℝ Point :=
    LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose)
  have hxStarFeasible :
      xStar ∈ method.feasibleSet :=
    accumulationPoint_mem_feasibleSet f method h_projectedTrialPath hxStar
  have hxStarProblem : xStar ∈ problem := by
    simpa [problem] using hxStarFeasible
  have hDiffAt : DifferentiableAt ℝ f xStar :=
    h_diffAt_feasible xStar hxStarFeasible
  refine
    (LinearEqualityConstrainedProblem.exists_isKKTPoint_toConstrainedOptimizationProblem_iff_projection_fixedPoint
      problem xStar hxStarProblem hDiffAt).2 ?_
  -- Route correction: reduce the KKT conclusion to the Chapter 11 projection fixed-point
  -- criterion, then replay the rejected-quarter-step contradiction only along the given
  -- accumulation subsequence and inside a compact feasible neighborhood of `xStar`.
  by_contra hNoInterval
  let c : ℝ := ‖K.starProjection (gradient f xStar)‖
  let δ : ℝ := c / 2
  have hunit_nonfixed :
      nearestPointProjection
          problem.feasibleSet
          ⟨xStar, hxStarProblem⟩
          problem.isComplete_feasibleSet
          problem.convex_feasibleSet
          (xStar - gradient problem.objective xStar) ≠ xStar :=
    unitProjectionNonfixed_of_noProjectionFixedInterval
      problem xStar hxStarProblem hNoInterval
  have hc_pos_problem :
      0 <
        ‖(LinearMap.ker
            (Matrix.toEuclideanLin problem.constraintMatrix.transpose)).starProjection
            (gradient f xStar)‖ :=
    constraintKernelProjectionNorm_pos_of_nonfixedProjection
      problem hxStarProblem (gradient f xStar) hunit_nonfixed
  have hc_pos : 0 < c := by
    dsimp [c, K, problem]
    exact hc_pos_problem
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  have hproj_tendsto :
      Tendsto
        (fun k : ℕ ↦ ‖K.starProjection (gradient f (method.iterate (φ k + 1)))‖)
        atTop
        (nhds c) := by
    simpa [K, c] using
      constraintKernelProjectionNorm_tendsto_alongAccumulation
        f method h_gradientContinuousOn h_projectedTrialPath hxStar
  have hratio_eventually :
      ∀ᶠ j : ℕ in atTop,
        δ ≤
          ‖method.iterate (φ j + 2) - method.iterate (φ j + 1)‖ /
            method.stepSize (φ j + 1) := by
    have hproj_lower :
        ∀ᶠ j : ℕ in atTop, δ < ‖K.starProjection (gradient f (method.iterate (φ j + 1)))‖ := by
      have hnhds : Set.Ioi δ ∈ nhds c := by
        apply Ioi_mem_nhds
        dsimp [δ]
        linarith
      exact hproj_tendsto hnhds
    filter_upwards [hproj_lower] with j hj
    have hk : 1 ≤ φ j + 1 := Nat.succ_le_succ (Nat.zero_le (φ j))
    have hratio_eq :
        ‖method.iterate (φ j + 2) - method.iterate (φ j + 1)‖ /
            method.stepSize (φ j + 1) =
          ‖K.starProjection (gradient f (method.iterate (φ j + 1)))‖ := by
      simpa [K, Nat.add_assoc] using
        stepRatio_eq_constraintKernelProjectionNorm
          f method h_projectedTrialPath hk
    rw [hratio_eq]
    exact le_of_lt hj
  rcases Filter.eventually_atTop.1 hratio_eventually with ⟨N, hN⟩
  let ψ : ℕ → ℕ := fun j : ℕ ↦ φ (j + N)
  have hψmono : StrictMono ψ := by
    intro i j hij
    exact hφ (Nat.add_lt_add_right hij N)
  have hshift : Tendsto (fun j : ℕ ↦ j + N) atTop atTop :=
    (Filter.tendsto_add_atTop_iff_nat N).2 tendsto_id
  have hxStarψ :
      Tendsto (fun j : ℕ ↦ method.iterate (ψ j + 1)) atTop (nhds xStar) := by
    change
      Tendsto
        ((fun k : ℕ ↦ method.iterate (φ k + 1)) ∘ fun j : ℕ ↦ j + N)
        atTop
        (nhds xStar)
    exact hxStar.comp hshift
  have hratio_lower :
      ∀ j : ℕ,
        δ ≤
          ‖method.iterate (ψ j + 2) - method.iterate (ψ j + 1)‖ /
            method.stepSize (ψ j + 1) := by
    intro j
    simpa [ψ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      hN (j + N) (Nat.le_add_left N j)
  have hsmall_steps :=
    accumulationRatioLowerBoundForcesSmallSteps
      f method h_diffAt_feasible h_projectedTrialPath h_accepts_eq_11513
      hψmono hxStarψ hδ_pos hratio_lower
  have hε_pos : 0 < (1 - method.μ) * δ := by
    exact mul_pos (sub_pos.mpr method.mu_mem.2) hδ_pos
  obtain ⟨ρ, hρ_pos, η, hη_pos, hmodel⟩ :=
    localUniformFeasibleUpperModelNearAccumulation
      f method h_diffAt_feasible h_gradientContinuousOn
      (xStar := xStar) hε_pos
  have hnear_eventually :
      ∀ᶠ j : ℕ in atTop, ‖method.iterate (ψ j + 1) - xStar‖ < ρ := by
    have hball : Metric.ball xStar ρ ∈ nhds xStar :=
      Metric.ball_mem_nhds xStar hρ_pos
    refine Filter.mem_of_superset (hxStarψ hball) ?_
    intro z hz
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz
  have hdisp_small_eventually :
      ∀ᶠ j : ℕ in atTop,
        ‖method.iterate (ψ j + 2) - method.iterate (ψ j + 1)‖ < η / 4 := by
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hsmall_steps.1 (η / 4) (by positivity)
    refine Filter.eventually_atTop.2 ⟨M, ?_⟩
    intro j hj
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hM j hj
  have hstep_small_eventually :
      ∀ᶠ j : ℕ in atTop, method.stepSize (ψ j + 1) < method.γ := by
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hsmall_steps.2 method.γ method.gamma_pos
    refine Filter.eventually_atTop.2 ⟨M, ?_⟩
    intro j hj
    have hstep_pos :
        0 < method.stepSize (ψ j + 1) := by
      exact stepSize_pos method (Nat.succ_le_succ (Nat.zero_le (ψ j)))
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hstep_pos.le] using hM j hj
  have h_eventually_false : ∀ᶠ j : ℕ in atTop, False := by
    filter_upwards
      [hnear_eventually, hdisp_small_eventually, hstep_small_eventually]
      with j hj_near hj_disp hj_step
    let k : ℕ := ψ j + 1
    have hk : 1 ≤ k := Nat.succ_le_succ (Nat.zero_le (ψ j))
    rcases previous_quartered_step_rejected (method := method) hk hj_step with
      ⟨hquarter, hαbar_eq, hαbar_rejected⟩
    let αbar : ℝ := method.trialStepAt k (method.quarteringCount k - 1)
    have hratio_pair :
        ‖method.trialPoint k αbar - method.iterate k‖ / αbar =
            ‖method.iterate (k + 1) - method.iterate k‖ / method.stepSize k ∧
          ‖method.trialPoint k αbar - method.iterate k‖ =
            (αbar / method.stepSize k) * ‖method.iterate (k + 1) - method.iterate k‖ := by
      simpa [αbar] using
        rejected_trial_ratio_eq f method h_projectedTrialPath hk hquarter
    have hδ_ratio :
        δ ≤ ‖method.trialPoint k αbar - method.iterate k‖ / αbar := by
      calc
        δ ≤
            ‖method.iterate (k + 1) - method.iterate k‖ /
              method.stepSize k := by
              simpa [k, Nat.add_assoc] using hratio_lower j
        _ = ‖method.trialPoint k αbar - method.iterate k‖ / αbar := by
              simpa using hratio_pair.1.symm
    have hx : method.iterate k ∈ method.feasibleSet :=
      iterate_mem_feasibleSet f method h_projectedTrialPath hk
    have hy : method.trialPoint k αbar ∈ method.feasibleSet := by
      rw [h_projectedTrialPath k αbar hk]
      exact
        LinearlyConstrainedQuarteringSearchMethod.projectedTrialPoint_mem_feasibleSet
          method f k αbar
    have hαbar_pos : 0 < αbar := by
      have hstep_pos : 0 < method.stepSize k := stepSize_pos method hk
      have hαbar_eq' : αbar = 4 * method.stepSize k := by
        simpa [αbar] using hαbar_eq
      rw [hαbar_eq']
      nlinarith
    have hnorm_eq :
        ‖method.trialPoint k αbar - method.iterate k‖ =
          4 * ‖method.iterate (k + 1) - method.iterate k‖ := by
      have hstep_ne : method.stepSize k ≠ 0 := ne_of_gt (stepSize_pos method hk)
      have hαbar_eq' : αbar = 4 * method.stepSize k := by
        simpa [αbar] using hαbar_eq
      calc
        ‖method.trialPoint k αbar - method.iterate k‖ =
            (αbar / method.stepSize k) *
              ‖method.iterate (k + 1) - method.iterate k‖ := hratio_pair.2
        _ = ((4 * method.stepSize k) / method.stepSize k) *
              ‖method.iterate (k + 1) - method.iterate k‖ := by
              rw [hαbar_eq']
        _ = 4 * ‖method.iterate (k + 1) - method.iterate k‖ := by
              field_simp [hstep_ne]
    have hdisp_lt : ‖method.trialPoint k αbar - method.iterate k‖ < η := by
      rw [hnorm_eq]
      nlinarith
    have hmodel_bound :
        f (method.trialPoint k αbar) ≤
          f (method.iterate k) +
            inner ℝ (method.trialPoint k αbar - method.iterate k)
              (gradient f (method.iterate k)) +
              ((1 - method.μ) * δ) *
                ‖method.trialPoint k αbar - method.iterate k‖ := by
      -- The local compact-neighborhood model now applies at the subsequence base point.
      exact hmodel hx hy (by simpa [k, dist_eq_norm, norm_sub_rev] using hj_near) hdisp_lt
    have hacceptance :
        linearlyConstrainedAcceptanceCondition11513 f method k αbar := by
      -- The rejected quartered step satisfies the source upper model and the ratio lower bound,
      -- so it must in fact pass the acceptance test.
      exact
        rejected_trial_acceptance_of_upper_model
          f method h_projectedTrialPath hk hαbar_pos hmodel_bound hδ_ratio le_rfl
    have haccepted_iff :
        (1 ≤ k → method.acceptedAt k αbar) ↔
          linearlyConstrainedAcceptanceCondition11513 f method k αbar :=
      h_accepts_eq_11513 k αbar
    exact hαbar_rejected ((haccepted_iff.2 hacceptance) hk)
  rcases Filter.eventually_atTop.1 h_eventually_false with ⟨M, hM⟩
  exact hM M le_rfl

namespace LinearlyConstrainedQuarteringSearchMethod

/-- Source-facing companion to Theorem 11.5.5: the accumulation point `xStar` is feasible, so the
ambient differentiability hypothesis on feasible points supplies the Chapter 8 differentiability
input needed to rewrite the KKT conclusion on `method.toLinearEqualityConstrainedProblem f` as the
Chapter 11 stationarity system `∇ f(xStar) = A λ` together with feasibility of `xStar`. -/
theorem accumulationPoint_kktSystem
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_diffAt_feasible : ∀ x ∈ method.feasibleSet, DifferentiableAt ℝ f x)
    (h_gradientContinuousOn : ContinuousOn (gradient f) method.feasibleSet)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    (h_accepts_eq_11513 :
      ∀ k α, 1 ≤ k →
        method.acceptedAt k α ↔
          linearlyConstrainedAcceptanceCondition11513 f method k α)
    {xStar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar)) :
    ∃ multiplier : Multiplier,
      xStar ∈ method.toLinearEqualityConstrainedProblem f ∧
        gradient f xStar = method.constraintMatrix.mulVec multiplier := by
  let problem := method.toLinearEqualityConstrainedProblem f
  have hxStarFeasible : xStar ∈ method.feasibleSet :=
    accumulationPoint_mem_feasibleSet f method h_projectedTrialPath hxStar
  have h_diffAt : DifferentiableAt ℝ f xStar :=
    h_diffAt_feasible xStar hxStarFeasible
  rcases
    linearlyConstrainedQuarteringSearchMethod_accumulationPoint_isKKTPoint
      f method h_diffAt_feasible h_gradientContinuousOn
      h_projectedTrialPath h_accepts_eq_11513 hφ hxStar with
    ⟨multiplier, hKKT⟩
  -- Rewrite the Chapter 8 KKT witness back into the Chapter 11 stationarity system.
  exact
    ⟨multiplier,
      (LinearEqualityConstrainedProblem.isKKTPoint_toConstrainedOptimizationProblem_iff
        problem xStar multiplier h_diffAt).1 hKKT⟩

end LinearlyConstrainedQuarteringSearchMethod

#print axioms nearestPointProjection
#print axioms LinearlyConstrainedQuarteringSearchMethod.toLinearEqualityConstrainedProblem

end Chapter11Theorem1155
