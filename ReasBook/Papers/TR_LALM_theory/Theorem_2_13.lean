/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import TR_LALM_theory.Assumption_2_5.Region
public import TR_LALM_theory.Definition_2_2.KKT
public import TR_LALM_theory.Lemma_2_7
public import TR_LALM_theory.Lemma_2_8
public import TR_LALM_theory.Lemma_2_11
public import TR_LALM_theory.Theorem_2_10
public import TR_LALM_theory.Theorem_2_13.KurdykaLojasiewicz
public import TR_LALM_theory.Theorem_2_13.LiftedState

public section

open Filter Topology
open scoped LALM

namespace LALM

variable {n m : ℕ}

namespace Run

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {ρ β : ℝ}

/-- Helper for Theorem 2.13: a multiplier update changes the augmented
Lagrangian by the squared multiplier increment divided by the penalty. -/
private lemma augmentedLagrangian_multiplier_succ_eq
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (k : ℕ) :
    ℒ[f, c; params.rho](run.point (k + 1), run.multiplier (k + 1)) =
      ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) +
        ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho := by
  -- Expand only the multiplier-dependent term and normalize the update law.
  rw [augmentedLagrangian_def, augmentedLagrangian_def, run.multiplier_succ,
    inner_add_left, inner_smul_left, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos run.rho_pos, real_inner_self_eq_norm_sq,
    starRingEnd_apply, star_trivial]
  -- Positivity of the penalty permits cancellation of the denominator.
  field_simp [run.rho_pos.ne']
  ring

/-- Helper for Theorem 2.13: admissibility bounds the multiplier correction
coefficient by one eighth of the proximal parameter. -/
private lemma multiplierPrimalConstant_div_rho_le_beta_div_eight
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho ≤ params.beta / 8 := by
  -- First clear the positive proximal denominator in Assumption 2.3.
  have hscaled :
      8 * multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound ≤ params.rho * params.beta :=
    (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.1).1
      params.multiplierPrimalConstant_le
  -- Then clear the positive penalty denominator and collect scalar factors.
  apply (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.2.1).2
  nlinarith

/-- Helper for Theorem 2.13: the lifted energy controls the square of the
natural two-step trajectory length. -/
private lemma liftedEnergyDescent
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hk : 1 ≤ k) :
    (params.beta / 16) * (‖run.step k‖ + ‖run.step (k - 1)‖) ^ 2 ≤
      liftedEnergy f c params.rho params.beta (run.liftedIterate k) -
        liftedEnergy f c params.rho params.beta (run.liftedIterate (k + 1)) := by
  -- Lemmas 2.7 and 2.8 supply primal descent and the multiplier-update cost.
  have hAdmissible := allPrefixesAdmissible h params h_region run (k + 1)
  have hLagrangian :=
    run.augmentedLagrangianDescent h params hAdmissible (Nat.lt_succ_self k)
  have hMultiplier :=
    run.norm_multiplier_succ_sub_sq_le h params hAdmissible hk (Nat.lt_succ_self k)
  have hMultiplierDiv :
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
            (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
    exact (div_le_div_iff_of_pos_right run.rho_pos).2 hMultiplier |>.trans_eq (by ring)
  have hCoefficient := multiplierPrimalConstant_div_rho_le_beta_div_eight h params
  have hCorrection :
      (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
            (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) ≤
        (params.beta / 8) *
            (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hCoefficient
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hTwoStepSquare :
      (‖run.step k‖ + ‖run.step (k - 1)‖) ^ 2 ≤
        2 * (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
    nlinarith [sq_nonneg (‖run.step k‖ - ‖run.step (k - 1)‖)]
  -- Expand the two lifted energies once; all correction terms now combine linearly.
  rw [liftedIterate_apply, liftedIterate_apply, liftedEnergy_liftedState,
    liftedEnergy_liftedState, Nat.add_sub_cancel,
    augmentedLagrangian_multiplier_succ_eq h params run]
  nlinarith [run.beta_pos]

/-- Helper for Theorem 2.13: lifted states whose primal coordinate lies in the
regularity region. -/
private def liftedRegularityRegion (h : EqualityConstrained.Regularity f c) :
    Set (LiftedState n m) :=
  {u | u.fst ∈ h.region}

/-- Helper for Theorem 2.13: the lifted regularity region is open. -/
private lemma isOpen_liftedRegularityRegion
    (h : EqualityConstrained.Regularity f c) :
    IsOpen (liftedRegularityRegion h) := by
  exact h.isOpen_region.preimage (WithLp.continuous_fst 2 _ _)

/-- Helper for Theorem 2.13: primal--multiplier pairs whose primal coordinate
lies in the regularity region. -/
private def pairRegularityRegion (h : EqualityConstrained.Regularity f c) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  {z | z.1 ∈ h.region}

/-- Helper for Theorem 2.13: the primal--multiplier regularity region is open. -/
private lemma isOpen_pairRegularityRegion
    (h : EqualityConstrained.Regularity f c) :
    IsOpen (pairRegularityRegion h) := by
  exact h.isOpen_region.preimage continuous_fst

/-- Helper for Theorem 2.13: all lifted iterates lie in one compact subset of
the lifted finite-dimensional state space. -/
private lemma existsCompactLiftedIterateRange
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_compact : IsCompact (deterministicSublevel h params)) :
    ∃ K : Set (LiftedState n m), IsCompact K ∧
      K ⊆ liftedRegularityRegion h ∧ ∀ k, run.liftedIterate k ∈ K := by
  let source : Set ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ×
      EuclideanSpace ℝ (Fin n)) :=
    (deterministicSublevel h params ×ˢ
      Metric.closedBall 0 params.multiplierBound) ×ˢ
        Metric.closedBall 0 params.delta
  let assemble :
      ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ×
        EuclideanSpace ℝ (Fin n)) → LiftedState n m :=
    fun z ↦ liftedState z.1.1 z.1.2 z.2
  have hSource : IsCompact source := by
    -- The primal sublevel is compact by hypothesis and both uniform norm bounds
    -- give compact Euclidean closed balls.
    exact (h_compact.prod (isCompact_closedBall 0 params.multiplierBound)).prod
      (isCompact_closedBall 0 params.delta)
  have hAssemble : Continuous assemble := by
    -- `liftedState` is the canonical nested `L²` product homeomorphism.
    unfold assemble liftedState
    fun_prop
  refine ⟨assemble '' source, hSource.image hAssemble, ?_, fun k ↦ ?_⟩
  · rintro u ⟨z, hz, rfl⟩
    change z.1.1 ∈ h.region
    apply h_region
    exact Metric.self_subset_cthickening (deterministicSublevel h params) hz.1.1
  -- Use the global point, multiplier, and step bounds as the image witness.
  rw [liftedIterate_apply]
  refine ⟨((run.point k, run.multiplier k), run.step (k - 1)), ?_, rfl⟩
  change ((run.point k ∈ deterministicSublevel h params ∧
      run.multiplier k ∈ Metric.closedBall 0 params.multiplierBound) ∧
        run.step (k - 1) ∈ Metric.closedBall 0 params.delta)
  refine ⟨⟨point_mem_deterministicSublevel h params h_region run k, ?_⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using
      norm_multiplier_le_global h params h_region run k
  · simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using
      norm_step_le_global h params h_region run (k - 1)

/-- Helper for Theorem 2.13: stationarity is continuous on primal--multiplier
pairs whose primal coordinate lies in the regularity region. -/
private lemma continuousOn_stationarity
    (h : EqualityConstrained.Regularity f c) :
    ContinuousOn
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        KKT.stationarity f c z.1 z.2)
      (pairRegularityRegion h) := by
  intro z hz
  change z.1 ∈ h.region at hz
  have hGradient : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        gradient f z.1) z :=
    (h.continuousAt_gradient hz).comp continuous_fst.continuousAt
  have hConstraintGradient : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        EqualityConstrained.constraintGradient c z.1) z :=
    (h.continuousAt_constraintGradient hz).comp continuous_fst.continuousAt
  have hStationarity : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        gradient f z.1 + EqualityConstrained.constraintGradient c z.1 z.2) z :=
    hGradient.add (hConstraintGradient.clm_apply continuous_snd.continuousAt)
  apply ContinuousAt.continuousWithinAt
  simpa only [KKT.stationarity_def] using hStationarity

/-- Helper for Theorem 2.13: the aggregate KKT residual is continuous on
primal--multiplier pairs whose primal coordinate lies in the regularity region. -/
private lemma continuousOn_residual
    (h : EqualityConstrained.Regularity f c) :
    ContinuousOn
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        KKT.residual f c z.1 z.2)
      (pairRegularityRegion h) := by
  intro z hz
  have hzPair : z ∈ pairRegularityRegion h := hz
  have hStationarity : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        KKT.stationarity f c z.1 z.2) z :=
    (continuousOn_stationarity h).continuousAt
      ((isOpen_pairRegularityRegion h).mem_nhds hzPair)
  change z.1 ∈ h.region at hz
  have hConstraint : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦ c z.1) z :=
    (h.continuousAt_constraint hz).comp continuous_fst.continuousAt
  have hResidualSquare : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        ‖KKT.stationarity f c z.1 z.2‖ ^ 2 + ‖c z.1‖ ^ 2) z :=
    ((hStationarity.norm.pow 2).add (hConstraint.norm.pow 2))
  have hResidual : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        Real.sqrt (‖KKT.stationarity f c z.1 z.2‖ ^ 2 + ‖c z.1‖ ^ 2)) z :=
    Real.continuous_sqrt.continuousAt.comp hResidualSquare
  apply ContinuousAt.continuousWithinAt
  simpa only [KKT.residual_def] using hResidual

/-- Helper for Theorem 2.13: the lifted energy is continuous wherever its
primal coordinate lies in the regularity region. -/
private lemma continuousOn_liftedEnergy
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ) :
    ContinuousOn (liftedEnergy f c rho beta) (liftedRegularityRegion h) := by
  intro u hu
  change u.fst ∈ h.region at hu
  have hObjective : ContinuousAt f u.fst := h.continuousAt_objective hu
  have hConstraint : ContinuousAt c u.fst := h.continuousAt_constraint hu
  apply ContinuousAt.continuousWithinAt
  unfold liftedEnergy augmentedLagrangian
  fun_prop

/-- Helper for Theorem 2.13: the gradient of the lifted energy separates into
stationarity, feasibility, and the quadratic preceding-step correction. -/
private lemma hasGradientAt_liftedEnergy_liftedState
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ)
    (x step : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (hx : x ∈ h.region) :
    HasGradientAt (liftedEnergy f c rho beta)
      (liftedState (KKT.stationarity f c x (multiplier + rho • c x))
        (c x) ((beta / 2) • step))
      (liftedState x multiplier step) := by
  let pointMap : LiftedState n m →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    WithLp.fstL 2 ℝ _ _
  let remainderMap : LiftedState n m →L[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    WithLp.sndL 2 ℝ _ _
  let multiplierMap : LiftedState n m →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (WithLp.fstL 2 ℝ _ _).comp remainderMap
  let stepMap : LiftedState n m →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.sndL 2 ℝ _ _).comp remainderMap
  have hPoint : HasFDerivAt (fun u : LiftedState n m ↦ u.fst) pointMap
      (liftedState x multiplier step) := by
    refine pointMap.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards with u
    simp only [pointMap, WithLp.fstL_apply]
  have hMultiplier : HasFDerivAt (fun u : LiftedState n m ↦ u.snd.fst) multiplierMap
      (liftedState x multiplier step) := by
    refine multiplierMap.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards with u
    simp only [multiplierMap, remainderMap, ContinuousLinearMap.comp_apply,
      WithLp.fstL_apply, WithLp.sndL_apply]
  have hStep : HasFDerivAt (fun u : LiftedState n m ↦ u.snd.snd) stepMap
      (liftedState x multiplier step) := by
    refine stepMap.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards with u
    simp only [stepMap, remainderMap, ContinuousLinearMap.comp_apply,
      WithLp.sndL_apply]
  have hObjectiveAt : HasFDerivAt f (fderiv ℝ f x) x :=
    h.hasFDerivAt_objective hx
  have hConstraintAt : HasFDerivAt c (fderiv ℝ c x) x :=
    h.hasFDerivAt_constraint hx
  have hObjective := hObjectiveAt.comp (liftedState x multiplier step) hPoint
  have hConstraint := hConstraintAt.comp (liftedState x multiplier step) hPoint
  have hPairing := hMultiplier.inner ℝ hConstraint
  have hConstraintSquare := hConstraint.norm_sq
  have hStepSquare := hStep.norm_sq
  have hDerivative :=
    (hObjective.add hPairing).add (hConstraintSquare.const_mul (rho / 2)) |>.add
      (hStepSquare.const_mul (beta / 4))
  -- Identify the assembled Fréchet derivative with the Riesz dual of the
  -- three-coordinate gradient displayed in the statement.
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hDerivative.congr_of_eventuallyEq ?_).congr_fderiv ?_
  · filter_upwards with u
    rfl
  · ext direction
    simp only [pointMap, remainderMap, multiplierMap, stepMap,
      liftedState_multiplier, Function.comp_apply, liftedState_point,
      liftedState_step, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, WithLp.fstL_apply, WithLp.sndL_apply,
      fderivInnerCLM_apply, smul_apply, coe_innerSL_apply, nsmul_eq_mul,
      Nat.cast_ofNat, smul_eq_mul, KKT.stationarity_def,
      EqualityConstrained.constraintGradient_def,
      InnerProductSpace.toDual_apply_apply, WithLp.prod_inner_apply,
      WithLp.ofLp_fst, WithLp.ofLp_snd, map_add, map_smul]
    rw [inner_add_left, inner_add_left, inner_smul_left, inner_gradient_left,
      ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]
    simp only [starRingEnd_apply, star_trivial, inner_smul_left]
    rw [real_inner_comm direction.snd.fst (c x)]
    ring

/-- Helper for Theorem 2.13: the norm of an assembled lifted state is bounded
by the sum of the norms of its three coordinates. -/
private lemma norm_liftedState_le
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (step : EuclideanSpace ℝ (Fin n)) :
    ‖liftedState x multiplier step‖ ≤ ‖x‖ + ‖multiplier‖ + ‖step‖ := by
  -- Compare squares using the exact nested `L²` product norm formula.
  apply (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))).1
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  simp only [liftedState_point, liftedState_multiplier, liftedState_step]
  nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg multiplier),
    mul_nonneg (norm_nonneg x) (norm_nonneg step),
    mul_nonneg (norm_nonneg multiplier) (norm_nonneg step)]

/-- Helper for Theorem 2.13: a desingularizer remains a desingularizer after
restricting its positive energy window. -/
private lemma isDesingularizer_of_le
    {eta eta' : ℝ} {phi : ℝ → ℝ}
    (hPhi : KurdykaLojasiewicz.IsDesingularizer eta phi)
    (hEta : eta' ≤ eta) :
    KurdykaLojasiewicz.IsDesingularizer eta' phi := by
  rw [KurdykaLojasiewicz.isDesingularizer_iff] at hPhi ⊢
  rcases hPhi with ⟨hMaps, hContinuous, hZero, hContDiff, hDeriv, hConcave⟩
  have hIco : Set.Ico 0 eta' ⊆ Set.Ico 0 eta := by
    intro x hx
    exact ⟨hx.1, hx.2.trans_le hEta⟩
  have hIoo : Set.Ioo 0 eta' ⊆ Set.Ioo 0 eta := by
    intro x hx
    exact ⟨hx.1, hx.2.trans_le hEta⟩
  -- Restrict each defining regularity and positivity property to the smaller interval.
  refine ⟨hMaps.mono hIco Set.Subset.rfl, hContinuous.mono hIco, hZero,
    hContDiff.mono hIoo, ?_, ⟨convex_Ico 0 eta', ?_⟩⟩
  · intro x hx
    exact hDeriv x (hIoo hx)
  · intro x hx y hy a b ha hb hab
    exact hConcave.2 (hIco hx) (hIco hy) ha hb hab

/-- Helper for Theorem 2.13: a nonempty finite sum of desingularizers on a
common window is again a desingularizer on that window. -/
private lemma isDesingularizer_finsetSum
    {index : Type*} (s : Finset index) (hNonempty : s.Nonempty)
    (eta : ℝ) (phi : index → ℝ → ℝ)
    (hPhi : ∀ i ∈ s, KurdykaLojasiewicz.IsDesingularizer eta (phi i)) :
    KurdykaLojasiewicz.IsDesingularizer eta
      (fun x ↦ ∑ i ∈ s, phi i x) := by
  classical
  simp only [KurdykaLojasiewicz.isDesingularizer_iff] at hPhi ⊢
  have hConcaveSum : ∀ t : Finset index,
      (∀ i ∈ t, ConcaveOn ℝ (Set.Ico 0 eta) (phi i)) →
        ConcaveOn ℝ (Set.Ico 0 eta) (fun x ↦ ∑ i ∈ t, phi i x) := by
    intro t hConcave
    induction t using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (concaveOn_const (0 : ℝ) (convex_Ico 0 eta))
    | @insert i t hi ih =>
        simp only [Finset.sum_insert hi]
        exact (hConcave i (Finset.mem_insert_self i t)).add
          (ih fun j hj ↦ hConcave j (Finset.mem_insert_of_mem hj))
  -- Verify the six defining properties componentwise over the finite family.
  refine ⟨?_, ?_, ?_, ?_, ?_, hConcaveSum s fun i hi ↦ (hPhi i hi).2.2.2.2.2⟩
  · intro x hx
    simp only [Set.mem_Ici]
    exact Finset.sum_nonneg fun i hi ↦ (hPhi i hi).1 hx
  · exact tendsto_finsetSum s fun i hi ↦ (hPhi i hi).2.1
  · exact Finset.sum_eq_zero fun i hi ↦ (hPhi i hi).2.2.1
  · exact ContDiffOn.sum fun i hi ↦ (hPhi i hi).2.2.2.1
  · intro x hx
    have hDifferentiable : ∀ i ∈ s, DifferentiableAt ℝ (phi i) x := by
      intro i hi
      exact ((hPhi i hi).2.2.2.1 x hx).differentiableWithinAt (by norm_num)
        |>.differentiableAt (isOpen_Ioo.mem_nhds hx)
    rw [deriv_fun_sum hDifferentiable]
    exact Finset.sum_pos (fun i hi ↦ (hPhi i hi).2.2.2.2.1 x hx) hNonempty

/-- Helper for Theorem 2.13: the lifted gradient at iterate `k + 1` is
bounded by a fixed multiple of the natural two-step length at `k`. -/
private lemma norm_gradient_liftedEnergy_liftedIterate_succ_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    ∃ B : ℝ, 0 < B ∧ ∀ k, 1 ≤ k →
      ‖gradient (liftedEnergy f c params.rho params.beta)
        (run.liftedIterate (k + 1))‖ ≤
          B * (‖run.step k‖ + ‖run.step (k - 1)‖) := by
  -- Enlarge the residual coefficient once so componentwise square bounds turn
  -- into linear bounds by the same two-step trajectory length.
  let residualCoefficient := residualComparisonConstant h params.delta params.beta
    params.rho params.multiplierBound
  let comparison := residualCoefficient + 1
  let B := (2 + (params.rho : ℝ) * h.constraintGradientBound) * comparison +
    (params.beta : ℝ) / 2
  have hResidualCoefficient : 0 ≤ residualCoefficient := by
    dsimp only [residualCoefficient]
    rw [residualComparisonConstant_def, multiplierPrimalConstant_def]
    positivity
  have hComparisonNonneg : 0 ≤ comparison := by
    dsimp only [comparison]
    linarith
  have hComparisonPos : 0 < comparison := by
    dsimp only [comparison]
    linarith
  have hComparisonSquare : residualCoefficient ≤ comparison ^ 2 := by
    dsimp only [comparison]
    nlinarith [sq_nonneg residualCoefficient]
  have hBPos : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hBPos, fun k hk ↦ ?_⟩
  let twoStep := ‖run.step k‖ + ‖run.step (k - 1)‖
  have hTwoStepNonneg : 0 ≤ twoStep := by
    dsimp only [twoStep]
    positivity
  have hTwoStepSquare :
      ‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2 ≤ twoStep ^ 2 := by
    dsimp only [twoStep]
    nlinarith [mul_nonneg (norm_nonneg (run.step k))
      (norm_nonneg (run.step (k - 1)))]
  have hAdmissible := allPrefixesAdmissible h params h_region run (k + 1)
  have hResidualSquare := residual_sq_le h params run hAdmissible hk (Nat.lt_succ_self k)
  have hResidualComponents :
      ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ^ 2 +
          ‖c (run.point (k + 1))‖ ^ 2 ≤
        residualCoefficient *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
    rw [KKT.residual_def, Real.sq_sqrt
      (add_nonneg (sq_nonneg _) (sq_nonneg _))] at hResidualSquare
    simpa only [residualCoefficient] using hResidualSquare
  have hStationaritySquare :
      ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ^ 2 ≤
        (comparison * twoStep) ^ 2 := by
    calc
      _ ≤ residualCoefficient *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) :=
        (le_add_of_nonneg_right (sq_nonneg _)).trans hResidualComponents
      _ ≤ residualCoefficient * twoStep ^ 2 :=
        mul_le_mul_of_nonneg_left hTwoStepSquare hResidualCoefficient
      _ ≤ comparison ^ 2 * twoStep ^ 2 :=
        mul_le_mul_of_nonneg_right hComparisonSquare (sq_nonneg _)
      _ = (comparison * twoStep) ^ 2 := by ring
  have hConstraintSquare :
      ‖c (run.point (k + 1))‖ ^ 2 ≤ (comparison * twoStep) ^ 2 := by
    calc
      _ ≤ ‖KKT.stationarity f c (run.point (k + 1))
            (run.multiplier (k + 1))‖ ^ 2 + ‖c (run.point (k + 1))‖ ^ 2 :=
        le_add_of_nonneg_left (sq_nonneg _)
      _ ≤ residualCoefficient *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := hResidualComponents
      _ ≤ residualCoefficient * twoStep ^ 2 :=
        mul_le_mul_of_nonneg_left hTwoStepSquare hResidualCoefficient
      _ ≤ comparison ^ 2 * twoStep ^ 2 :=
        mul_le_mul_of_nonneg_right hComparisonSquare (sq_nonneg _)
      _ = (comparison * twoStep) ^ 2 := by ring
  have hStationarity :
      ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ≤
        comparison * twoStep :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hComparisonNonneg hTwoStepNonneg)).1
      hStationaritySquare
  have hConstraint : ‖c (run.point (k + 1))‖ ≤ comparison * twoStep :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hComparisonNonneg hTwoStepNonneg)).1
      hConstraintSquare
  have hSegments := (run.isAdmissiblePrefix_iff h (k + 1)).1 hAdmissible
  have hPointMem : run.point (k + 1) ∈ h.region :=
    hSegments k (Nat.lt_succ_self k) (right_mem_segment ℝ _ _)
  have hOperator := h.norm_constraintGradient_le (run.point (k + 1)) hPointMem
  have hCorrection :
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1))
          ((params.rho : ℝ) • c (run.point (k + 1)))‖ ≤
        (params.rho : ℝ) * h.constraintGradientBound * comparison * twoStep := by
    calc
      _ ≤ ‖EqualityConstrained.constraintGradient c (run.point (k + 1))‖ *
          ‖(params.rho : ℝ) • c (run.point (k + 1))‖ :=
        (EqualityConstrained.constraintGradient c (run.point (k + 1))).le_opNorm _
      _ = ‖EqualityConstrained.constraintGradient c (run.point (k + 1))‖ *
          ((params.rho : ℝ) * ‖c (run.point (k + 1))‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
      _ ≤ h.constraintGradientBound *
          ((params.rho : ℝ) * ‖c (run.point (k + 1))‖) :=
        mul_le_mul_of_nonneg_right hOperator (mul_nonneg run.rho_pos.le (norm_nonneg _))
      _ ≤ h.constraintGradientBound *
          ((params.rho : ℝ) * (comparison * twoStep)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hConstraint run.rho_pos.le)
          (NNReal.coe_nonneg h.constraintGradientBound)
      _ = (params.rho : ℝ) * h.constraintGradientBound * comparison * twoStep := by ring
  -- The exact lifted-gradient formula separates the shifted stationarity,
  -- feasibility, and stored-step coordinates before their norms are combined.
  have hShiftedStationarity :
      ‖KKT.stationarity f c (run.point (k + 1))
          (run.multiplier (k + 1) +
            (params.rho : ℝ) • c (run.point (k + 1)))‖ ≤
        (1 + (params.rho : ℝ) * h.constraintGradientBound) * comparison * twoStep := by
    have hIdentity :
        KKT.stationarity f c (run.point (k + 1))
            (run.multiplier (k + 1) +
              (params.rho : ℝ) • c (run.point (k + 1))) =
          KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1)) +
            EqualityConstrained.constraintGradient c (run.point (k + 1))
              ((params.rho : ℝ) • c (run.point (k + 1))) := by
      simp only [KKT.stationarity_def, map_add]
      abel
    rw [hIdentity]
    exact (norm_add_le _ _).trans (add_le_add hStationarity hCorrection) |>.trans_eq (by ring)
  have hGradient :
      gradient (liftedEnergy f c params.rho params.beta)
          (run.liftedIterate (k + 1)) =
        liftedState
          (KKT.stationarity f c (run.point (k + 1))
            (run.multiplier (k + 1) +
              (params.rho : ℝ) • c (run.point (k + 1))))
          (c (run.point (k + 1))) ((params.beta / 2 : ℝ) • run.step k) := by
    rw [liftedIterate_apply, Nat.add_sub_cancel]
    exact (hasGradientAt_liftedEnergy_liftedState h params.rho params.beta
      (run.point (k + 1)) (run.step k) (run.multiplier (k + 1)) hPointMem).gradient
  have hStepPart : ‖(params.beta / 2 : ℝ) • run.step k‖ ≤
      ((params.beta : ℝ) / 2) * twoStep := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos run.beta_pos (by norm_num))]
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (norm_nonneg (run.step (k - 1)))) (by positivity)
  rw [hGradient]
  calc
    _ ≤ ‖KKT.stationarity f c (run.point (k + 1))
          (run.multiplier (k + 1) +
            (params.rho : ℝ) • c (run.point (k + 1)))‖ +
          ‖c (run.point (k + 1))‖ + ‖(params.beta / 2 : ℝ) • run.step k‖ :=
      norm_liftedState_le _ _ _
    _ ≤ (1 + (params.rho : ℝ) * h.constraintGradientBound) * comparison * twoStep +
          comparison * twoStep + ((params.beta : ℝ) / 2) * twoStep :=
      add_le_add (add_le_add hShiftedStationarity hConstraint) hStepPart
    _ = B * (‖run.step k‖ + ‖run.step (k - 1)‖) := by
      dsimp only [B, twoStep]
      ring

/-- Helper for Theorem 2.13: summability of the natural two-step length implies
summability of primal steps together with multiplier increments. -/
private lemma summableStepAndMultiplierIncrement_of_summableTwoStep
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (hTwoStep : Summable (fun k ↦ ‖run.step k‖ + ‖run.step (k - 1)‖)) :
    Summable (fun k ↦
      ‖run.step k‖ + ‖run.multiplier (k + 1) - run.multiplier k‖) := by
  let coefficient := multiplierPrimalConstant h params.delta params.beta params.rho
    params.multiplierBound
  let comparison := coefficient + 1
  have hCoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    rw [multiplierPrimalConstant_def]
    positivity
  have hComparison : 0 ≤ comparison := by
    dsimp only [comparison]
    linarith
  have hComparisonSq : coefficient ≤ comparison ^ 2 := by
    dsimp only [comparison]
    nlinarith [sq_nonneg coefficient]
  have hShiftedTwoStep :
      Summable (fun k ↦ ‖run.step (k + 1)‖ + ‖run.step k‖) := by
    simpa only [Nat.add_sub_cancel] using (summable_nat_add_iff 1).2 hTwoStep
  have hDominating : Summable (fun k ↦
      (comparison + 1) * (‖run.step (k + 1)‖ + ‖run.step k‖)) :=
    hShiftedTwoStep.mul_left (comparison + 1)
  rw [← summable_nat_add_iff 1]
  apply hDominating.of_nonneg_of_le
  · intro k
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro k
    have hMultiplierSq := norm_multiplier_succ_sub_sq_le h params run
      (allPrefixesAdmissible h params h_region run (k + 2)) (by omega : 1 ≤ k + 1)
      (by omega : k + 1 < k + 2)
    have hTwoStepSquare :
        ‖run.step (k + 1)‖ ^ 2 + ‖run.step k‖ ^ 2 ≤
          (‖run.step (k + 1)‖ + ‖run.step k‖) ^ 2 := by
      nlinarith [mul_nonneg (norm_nonneg (run.step (k + 1))) (norm_nonneg (run.step k))]
    have hMultiplierSquareBound :
        ‖run.multiplier (k + 2) - run.multiplier (k + 1)‖ ^ 2 ≤
          (comparison * (‖run.step (k + 1)‖ + ‖run.step k‖)) ^ 2 := by
      calc
        ‖run.multiplier (k + 2) - run.multiplier (k + 1)‖ ^ 2 ≤
            coefficient * (‖run.step (k + 1)‖ ^ 2 + ‖run.step k‖ ^ 2) := by
          simpa only [coefficient, Nat.add_sub_cancel] using hMultiplierSq
        _ ≤ coefficient * (‖run.step (k + 1)‖ + ‖run.step k‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hTwoStepSquare hCoefficient
        _ ≤ comparison ^ 2 * (‖run.step (k + 1)‖ + ‖run.step k‖) ^ 2 :=
          mul_le_mul_of_nonneg_right hComparisonSq (sq_nonneg _)
        _ = (comparison * (‖run.step (k + 1)‖ + ‖run.step k‖)) ^ 2 := by ring
    have hMultiplierBound :
        ‖run.multiplier (k + 2) - run.multiplier (k + 1)‖ ≤
          comparison * (‖run.step (k + 1)‖ + ‖run.step k‖) :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hComparison (add_nonneg (norm_nonneg _) (norm_nonneg _)))).1
          hMultiplierSquareBound
    have hStepBound :
        ‖run.step (k + 1)‖ ≤ ‖run.step (k + 1)‖ + ‖run.step k‖ :=
      le_add_of_nonneg_right (norm_nonneg _)
    simpa only [Nat.add_assoc] using
      add_le_add hStepBound hMultiplierBound |>.trans_eq (by ring)

/-- Helper for Theorem 2.13: a nonnegative sequence is summable when twice
each successor is controlled by its predecessor and a telescoping potential. -/
private lemma summable_of_two_mul_shift_le
    (d q : ℕ → ℝ)
    (hDNonneg : ∀ k, 0 ≤ d k)
    (hQNonneg : ∀ k, 0 ≤ q k)
    (hRecurrence : ∀ k, 2 * d (k + 1) ≤ d k + q k - q (k + 1)) :
    Summable d := by
  -- The recurrence preserves a bound for a partial sum plus its two boundary terms.
  have hPartial : ∀ k,
      (∑ i ∈ Finset.range (k + 1), d i) + d k + q k ≤ 2 * d 0 + q 0 := by
    intro k
    induction k with
    | zero =>
        rw [Finset.sum_range_one]
        ring_nf
        exact le_rfl
    | succ k hk =>
        rw [Finset.sum_range_succ]
        have hStep := hRecurrence k
        nlinarith
  -- Dropping the nonnegative boundary terms gives a uniform partial-sum bound.
  apply summable_of_sum_range_le (c := 2 * d 0 + q 0) hDNonneg
  intro k
  cases k with
  | zero =>
      have hDZero := hDNonneg 0
      have hQZero := hQNonneg 0
      simp only [Finset.range_zero, Finset.sum_empty]
      nlinarith
  | succ k =>
      have hBoundary := add_nonneg (hDNonneg k) (hQNonneg k)
      have hBound := hPartial k
      nlinarith

/-- Helper for Theorem 2.13: pointwise KL inequalities on a compact cluster
set combine into one eventual inequality with a common desingularizer. -/
private lemma eventually_uniformKL_of_compactCluster
    (energy : LiftedState n m → ℝ) (u : ℕ → LiftedState n m)
    (K : Set (LiftedState n m)) (hKCompact : IsCompact K)
    (hKRange : ∀ k, u k ∈ K)
    (hKL : KurdykaLojasiewicz.HasAtClusterPoints energy atTop u)
    (energyLimit : ℝ)
    (hClusterEnergy : ∀ x,
      MapClusterPt x atTop u → energy x = energyLimit) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ phi : ℝ → ℝ,
      KurdykaLojasiewicz.IsDesingularizer eta phi ∧
        ∀ᶠ k in atTop,
          energyLimit < energy (u k) → energy (u k) < energyLimit + eta →
            1 ≤ deriv phi (energy (u k) - energyLimit) *
              ‖gradient energy (u k)‖ := by
  classical
  -- Intersect compact containment with the closed set of mapped cluster points.
  let omega : Set (LiftedState n m) :=
    K ∩ {x | MapClusterPt x atTop u}
  have hClusterClosed : IsClosed {x | MapClusterPt x atTop u} := by
    change IsClosed {x | ClusterPt x (Filter.map u atTop)}
    exact isClosed_setOf_clusterPt
  have hOmegaCompact : IsCompact omega := by
    exact hKCompact.inter_right hClusterClosed
  have hMapRange : Filter.map u atTop ≤ Filter.principal K := by
    rw [le_principal_iff]
    exact Filter.mem_map.mpr (Filter.Eventually.of_forall hKRange)
  obtain ⟨xCluster, hxK, hxCluster⟩ := hKCompact.exists_mapClusterPt hMapRange
  have hOmegaNonempty : omega.Nonempty :=
    ⟨xCluster, hxK, hxCluster⟩
  -- Choose the local KL data pointwise, then compactness reduces them to a
  -- nonempty finite family of neighborhoods.
  have hLocalData : ∀ x : omega, ∃ eta : ℝ, 0 < eta ∧ ∃ phi : ℝ → ℝ,
      KurdykaLojasiewicz.IsDesingularizer eta phi ∧
        ∀ᶠ y in 𝓝 (x : LiftedState n m),
          energy x < energy y → energy y < energy x + eta →
            1 ≤ deriv phi (energy y - energy x) * ‖gradient energy y‖ := by
    intro x
    exact (KurdykaLojasiewicz.hasAt_iff energy x).1
      ((KurdykaLojasiewicz.hasAtClusterPoints_iff energy atTop u).1 hKL x x.2.2)
  choose localEta hLocalEta localPhi hLocalPhi hLocalInequality using hLocalData
  let neighborhood : omega → Set (LiftedState n m) := fun x ↦
    {y | energy x < energy y → energy y < energy x + localEta x →
      1 ≤ deriv (localPhi x) (energy y - energy x) * ‖gradient energy y‖}
  have hNeighborhood : ∀ x : omega, neighborhood x ∈ 𝓝 (x : LiftedState n m) := by
    intro x
    change ∀ᶠ y in 𝓝 (x : LiftedState n m),
      energy x < energy y → energy y < energy x + localEta x →
        1 ≤ deriv (localPhi x) (energy y - energy x) * ‖gradient energy y‖
    exact hLocalInequality x
  obtain ⟨cover, hCover⟩ := hOmegaCompact.elim_nhds_subcover_nhdsSet'
    (fun x hx ↦ neighborhood ⟨x, hx⟩)
    (fun x hx ↦ hNeighborhood ⟨x, hx⟩)
  have hOmegaSubset : omega ⊆ ⋃ x ∈ cover, neighborhood x :=
    subset_of_mem_nhdsSet hCover
  have hCoverNonempty : cover.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    obtain ⟨x, hx⟩ := hOmegaNonempty
    have hxUnion := hOmegaSubset hx
    rw [hEmpty] at hxUnion
    simp at hxUnion
  let eta : ℝ := cover.inf' hCoverNonempty localEta
  have hEtaPos : 0 < eta := by
    dsimp only [eta]
    exact (Finset.lt_inf'_iff hCoverNonempty).2 fun i hi ↦ hLocalEta i
  have hEtaLe : ∀ i ∈ cover, eta ≤ localEta i := by
    intro i hi
    exact Finset.inf'_le localEta hi
  let phi : ℝ → ℝ := fun t ↦ ∑ i ∈ cover, localPhi i t
  have hRestricted : ∀ i ∈ cover,
      KurdykaLojasiewicz.IsDesingularizer eta (localPhi i) := by
    intro i hi
    exact isDesingularizer_of_le (hLocalPhi i) (hEtaLe i hi)
  have hPhi : KurdykaLojasiewicz.IsDesingularizer eta phi := by
    exact isDesingularizer_finsetSum cover hCoverNonempty eta localPhi hRestricted
  -- Every sufficiently late iterate lies in the finite cover; the derivative
  -- of the sum dominates the selected local derivative there.
  have hApproachOmega : Tendsto u atTop (nhdsSet omega) := by
    exact hKCompact.tendsto_nhdsSet_of_mapClusterPt
      (Filter.Eventually.of_forall hKRange) fun x hxK hxCluster ↦ ⟨hxK, hxCluster⟩
  have hEventuallyCovered : ∀ᶠ k in atTop,
      u k ∈ ⋃ x ∈ cover, neighborhood x :=
    hApproachOmega hCover
  refine ⟨eta, hEtaPos, phi, hPhi, ?_⟩
  filter_upwards [hEventuallyCovered] with k hkCovered
  intro hAbove hBelow
  rcases Set.mem_iUnion.1 hkCovered with ⟨i, hkCovered⟩
  rcases Set.mem_iUnion.1 hkCovered with ⟨hiCover, hiNeighborhood⟩
  have hCenter : energy i = energyLimit := hClusterEnergy i i.2.2
  have hChart : 1 ≤ deriv (localPhi i) (energy (u k) - energyLimit) *
      ‖gradient energy (u k)‖ := by
    have hWindow : energyLimit + eta ≤ energyLimit + localEta i := by
      linarith [hEtaLe i hiCover]
    rw [← hCenter]
    exact hiNeighborhood (by rwa [hCenter])
      (by rw [hCenter]; exact hBelow.trans_le hWindow)
  have hGap : energy (u k) - energyLimit ∈ Set.Ioo 0 eta :=
    ⟨sub_pos.mpr hAbove, sub_lt_iff_lt_add'.mpr hBelow⟩
  have hDifferentiable : ∀ j ∈ cover,
      DifferentiableAt ℝ (localPhi j) (energy (u k) - energyLimit) := by
    intro j hj
    have hRestrictedSpec :=
      (KurdykaLojasiewicz.isDesingularizer_iff eta (localPhi j)).1
        (hRestricted j hj)
    exact (hRestrictedSpec.2.2.2.1 _ hGap).differentiableWithinAt (by norm_num)
      |>.differentiableAt (isOpen_Ioo.mem_nhds hGap)
  have hComponentLe : deriv (localPhi i) (energy (u k) - energyLimit) ≤
      deriv phi (energy (u k) - energyLimit) := by
    dsimp only [phi]
    rw [deriv_fun_sum hDifferentiable]
    apply Finset.single_le_sum _ hiCover
    intro j hj
    have hRestrictedSpec :=
      (KurdykaLojasiewicz.isDesingularizer_iff eta (localPhi j)).1
        (hRestricted j hj)
    exact (hRestrictedSpec.2.2.2.2.1 _ hGap).le
  exact hChart.trans
    (mul_le_mul_of_nonneg_right hComponentLe (norm_nonneg _))

/-- Convergence of lifted iterates to a state with zero step implies convergence
of the whole point--multiplier sequence to the same pair. -/
theorem pairTendsto_of_liftedTendsto
    (run : Run f c ρ β x₀ multiplier₀)
    (xStar : EuclideanSpace ℝ (Fin n))
    (multiplierStar : EuclideanSpace ℝ (Fin m))
    (h_lifted : Tendsto run.liftedIterate atTop
      (𝓝 (liftedState xStar multiplierStar 0))) :
    Tendsto (fun k ↦ (run.point k, run.multiplier k)) atTop
      (𝓝 (xStar, multiplierStar)) := by
  -- Project the lifted convergence onto its point and multiplier coordinates.
  have hPoint : Tendsto (fun k ↦ run.point k) atTop (𝓝 xStar) := by
    have hProjection : Continuous (fun u : LiftedState n m ↦ u.fst) :=
      WithLp.continuous_fst 2 _ _
    have hProjected :=
      (hProjection.tendsto (liftedState xStar multiplierStar 0)).comp h_lifted
    exact hProjected.congr fun k ↦ by
      simp only [Function.comp_apply, liftedIterate_apply, liftedState_point]
  have hMultiplier : Tendsto (fun k ↦ run.multiplier k) atTop (𝓝 multiplierStar) := by
    have hProjection : Continuous (fun u : LiftedState n m ↦ u.snd.fst) :=
      (WithLp.continuous_fst 2 _ _).comp (WithLp.continuous_snd 2 _ _)
    have hProjected :=
      (hProjection.tendsto (liftedState xStar multiplierStar 0)).comp h_lifted
    exact hProjected.congr fun k ↦ by
      simp only [Function.comp_apply, liftedIterate_apply, liftedState_multiplier]
  -- Reassemble the two coordinate limits in the product topology.
  exact hPoint.prodMk_nhds hMultiplier

/-- Theorem 2.13 (1): compactness of the deterministic sublevel and the
Kurdyka--Łojasiewicz property at every lifted cluster point imply summability of
the primal-step and multiplier-increment lengths. -/
theorem summableStepAndMultiplierIncrement
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_compact : IsCompact (deterministicSublevel h params))
    (h_KL : KurdykaLojasiewicz.HasAtClusterPoints
      (liftedEnergy f c params.rho params.beta) atTop run.liftedIterate) :
    Summable (fun k ↦
      ‖run.step k‖ + ‖run.multiplier (k + 1) - run.multiplier k‖) := by
  -- Compact containment and sufficient decrease establish the global KL setup.
  obtain ⟨K, hKCompact, hKSubset, hKRange⟩ :=
    existsCompactLiftedIterateRange h params h_region run h_compact
  let length : ℕ → ℝ := fun k ↦ ‖run.step k‖ + ‖run.step (k - 1)‖
  have hLengthNonneg : ∀ k, 0 ≤ length k :=
    fun k ↦ add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hDescent : ∀ᶠ k in atTop,
      (params.beta / 16) * length k ^ 2 ≤
        liftedEnergy f c params.rho params.beta (run.liftedIterate k) -
          liftedEnergy f c params.rho params.beta (run.liftedIterate (k + 1)) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact liftedEnergyDescent h params h_region run k hk
  have hEnergyContinuous := continuousOn_liftedEnergy h params.rho params.beta
  -- Route correction: separate energy convergence, compact KL uniformization,
  -- and the scalar telescoping argument instead of combining them in one helper.
  let energy : LiftedState n m → ℝ :=
    liftedEnergy f c params.rho params.beta
  let energyTail : ℕ → ℝ := fun k ↦ energy (run.liftedIterate (k + 1))
  have hEnergyTailAntitone : Antitone energyTail := by
    apply antitone_nat_of_succ_le
    intro k
    have hStep := liftedEnergyDescent h params h_region run (k + 1) (by omega)
    have hCoefficientNonneg : 0 ≤ (params.beta : ℝ) / 16 := by
      positivity
    have hLengthSquareNonneg :
        0 ≤ (‖run.step (k + 1)‖ + ‖run.step (k + 1 - 1)‖) ^ 2 :=
      sq_nonneg _
    dsimp only [energyTail, energy]
    nlinarith
  have hEnergyTailBddBelow : BddBelow (Set.range energyTail) := by
    have hCompactImage : BddBelow (energy '' K) :=
      hKCompact.bddBelow_image (hEnergyContinuous.mono hKSubset)
    apply hCompactImage.mono
    rintro y ⟨k, rfl⟩
    exact ⟨run.liftedIterate (k + 1), hKRange (k + 1), rfl⟩
  let energyLimit : ℝ := ⨅ k, energyTail k
  have hEnergyTailTendsto : Tendsto energyTail atTop (𝓝 energyLimit) := by
    exact tendsto_atTop_ciInf hEnergyTailAntitone hEnergyTailBddBelow
  have hEnergyTendsto : Tendsto (fun k ↦ energy (run.liftedIterate k)) atTop
      (𝓝 energyLimit) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [energyTail] using hEnergyTailTendsto
  have hClusterEnergy : ∀ xBar,
      MapClusterPt xBar atTop run.liftedIterate → energy xBar = energyLimit := by
    intro xBar hxBar
    obtain ⟨subsequence, hSubsequence, hLiftedSubsequence⟩ := hxBar.tendsto_subseq
    have hxK : xBar ∈ K :=
      hKCompact.isClosed.mem_of_tendsto hLiftedSubsequence
        (Filter.Eventually.of_forall fun k ↦ hKRange (subsequence k))
    have hxRegion : xBar ∈ liftedRegularityRegion h := hKSubset hxK
    have hEnergyAtCluster : Tendsto
        (fun k ↦ energy (run.liftedIterate (subsequence k))) atTop
        (𝓝 (energy xBar)) := by
      have hEnergyAt : ContinuousAt energy xBar :=
        hEnergyContinuous.continuousAt
          ((isOpen_liftedRegularityRegion h).mem_nhds hxRegion)
      have hComposed := hEnergyAt.tendsto.comp hLiftedSubsequence
      simpa [Function.comp_def, energy] using hComposed
    have hEnergyAlongSubsequence : Tendsto
        (fun k ↦ energy (run.liftedIterate (subsequence k))) atTop
        (𝓝 energyLimit) := by
      exact hEnergyTendsto.comp hSubsequence.tendsto_atTop
    exact tendsto_nhds_unique hEnergyAtCluster hEnergyAlongSubsequence
  have hSummableLength : Summable length := by
    -- Uniform compactness supplies one KL chart, while Lemma 2.11 supplies its
    -- trajectory-relative gradient estimate with the correct predecessor index.
    obtain ⟨eta, hEtaPos, phi, hPhi, hUniformKL⟩ :=
      eventually_uniformKL_of_compactCluster energy run.liftedIterate K hKCompact
        hKRange h_KL energyLimit hClusterEnergy
    obtain ⟨B, hBPos, hGradientBound⟩ :=
      norm_gradient_liftedEnergy_liftedIterate_succ_le h params h_region run
    let gap : ℕ → ℝ := fun k ↦ energyTail k - energyLimit
    let coefficient : ℝ := (params.beta : ℝ) / 16
    let potential : ℕ → ℝ := fun k ↦
      (B / coefficient) * phi (gap k)
    have hCoefficientPos : 0 < coefficient := by
      dsimp only [coefficient]
      exact div_pos run.beta_pos (by norm_num)
    have hGapNonneg : ∀ k, 0 ≤ gap k := by
      intro k
      dsimp only [gap]
      exact sub_nonneg.mpr
        (hEnergyTailAntitone.le_of_tendsto hEnergyTailTendsto k)
    have hGapAntitone : Antitone gap := by
      intro i j hij
      dsimp only [gap]
      exact sub_le_sub_right (hEnergyTailAntitone hij) energyLimit
    have hGapTendsto : Tendsto gap atTop (𝓝 0) := by
      have hConstant : Tendsto (fun _ : ℕ ↦ energyLimit) atTop (𝓝 energyLimit) :=
        tendsto_const_nhds
      dsimp only [gap]
      simpa only [sub_self] using hEnergyTailTendsto.sub hConstant
    have hGapLt : ∀ᶠ k in atTop, gap k < eta :=
      hGapTendsto (Iio_mem_nhds hEtaPos)
    have hUniformKLShift : ∀ᶠ k in atTop,
        0 < gap k → gap k < eta →
          1 ≤ deriv phi (gap k) *
            ‖gradient energy (run.liftedIterate (k + 1))‖ := by
      have hShifted := (tendsto_add_atTop_nat 1) hUniformKL
      filter_upwards [hShifted] with k hk
      intro hGapPos hGapUpper
      apply hk
      · dsimp only [gap, energyTail] at hGapPos ⊢
        linarith
      · dsimp only [gap, energyTail] at hGapUpper ⊢
        linarith
    have hPhiSpec :=
      (KurdykaLojasiewicz.isDesingularizer_iff eta phi).1 hPhi
    have hEventualRecurrence : ∀ᶠ k in atTop,
        2 * length (k + 1) ≤
          length k + potential k - potential (k + 1) := by
      filter_upwards [hUniformKLShift, hGapLt, eventually_ge_atTop 1]
        with k hKLAt hGapUpper hk
      have hGapNextLe : gap (k + 1) ≤ gap k :=
        hGapAntitone (Nat.le_succ k)
      have hGapNextUpper : gap (k + 1) < eta :=
        hGapNextLe.trans_lt hGapUpper
      have hDescentStep : coefficient * length (k + 1) ^ 2 ≤
          gap k - gap (k + 1) := by
        have hStep := liftedEnergyDescent h params h_region run (k + 1) (by omega)
        dsimp only [coefficient, length, gap, energyTail, energy] at ⊢
        nlinarith
      by_cases hGapZero : gap k = 0
      · have hGapNextZero : gap (k + 1) = 0 := by
          have hNextNonneg := hGapNonneg (k + 1)
          nlinarith
        have hLengthNextZero : length (k + 1) = 0 := by
          rw [hGapZero, hGapNextZero, sub_self] at hDescentStep
          have hProductZero : coefficient * length (k + 1) ^ 2 = 0 :=
            le_antisymm hDescentStep
              (mul_nonneg hCoefficientPos.le (sq_nonneg _))
          have hSquareZero : length (k + 1) ^ 2 = 0 :=
            (mul_eq_zero.mp hProductZero).resolve_left hCoefficientPos.ne'
          exact sq_eq_zero_iff.mp hSquareZero
        dsimp only [potential]
        rw [hGapZero, hGapNextZero, hPhiSpec.2.2.1, hLengthNextZero]
        simpa only [mul_zero, zero_mul, add_zero, sub_zero] using hLengthNonneg k
      · have hGapPos : 0 < gap k :=
          lt_of_le_of_ne (hGapNonneg k) (Ne.symm hGapZero)
        have hDerivPos : 0 < deriv phi (gap k) :=
          hPhiSpec.2.2.2.2.1 _ ⟨hGapPos, hGapUpper⟩
        have hRelative : 1 ≤
            deriv phi (gap k) * (B * length k) := by
          calc
            1 ≤ deriv phi (gap k) *
                ‖gradient energy (run.liftedIterate (k + 1))‖ :=
              hKLAt hGapPos hGapUpper
            _ ≤ deriv phi (gap k) * (B * length k) := by
              apply mul_le_mul_of_nonneg_left _ hDerivPos.le
              simpa only [energy, length] using hGradientBound k hk
        by_cases hGapEqual : gap (k + 1) = gap k
        · have hLengthNextZero : length (k + 1) = 0 := by
            rw [hGapEqual, sub_self] at hDescentStep
            have hProductZero : coefficient * length (k + 1) ^ 2 = 0 :=
              le_antisymm hDescentStep
                (mul_nonneg hCoefficientPos.le (sq_nonneg _))
            have hSquareZero : length (k + 1) ^ 2 = 0 :=
              (mul_eq_zero.mp hProductZero).resolve_left hCoefficientPos.ne'
            exact sq_eq_zero_iff.mp hSquareZero
          dsimp only [potential]
          rw [hGapEqual, hLengthNextZero]
          nlinarith [hLengthNonneg k]
        · have hGapStrict : gap (k + 1) < gap k :=
            lt_of_le_of_ne hGapNextLe hGapEqual
          have hDifferentiable : DifferentiableAt ℝ phi (gap k) :=
            (hPhiSpec.2.2.2.1 _ ⟨hGapPos, hGapUpper⟩).differentiableWithinAt
              (by norm_num) |>.differentiableAt
                (isOpen_Ioo.mem_nhds ⟨hGapPos, hGapUpper⟩)
          have hSlope := hPhiSpec.2.2.2.2.2.deriv_le_slope
            ⟨hGapNonneg (k + 1), hGapNextUpper⟩
            ⟨hGapPos.le, hGapUpper⟩ hGapStrict hDifferentiable
          have hConcavityProduct :
              deriv phi (gap k) * (gap k - gap (k + 1)) ≤
                phi (gap k) - phi (gap (k + 1)) := by
            rw [slope_def_field] at hSlope
            exact (le_div_iff₀ (sub_pos.mpr hGapStrict)).1 hSlope
          have hPhiDrop : coefficient * deriv phi (gap k) *
                length (k + 1) ^ 2 ≤
              phi (gap k) - phi (gap (k + 1)) := by
            calc
              coefficient * deriv phi (gap k) * length (k + 1) ^ 2 =
                  deriv phi (gap k) *
                    (coefficient * length (k + 1) ^ 2) := by ring
              _ ≤ deriv phi (gap k) * (gap k - gap (k + 1)) :=
                mul_le_mul_of_nonneg_left hDescentStep hDerivPos.le
              _ ≤ phi (gap k) - phi (gap (k + 1)) := hConcavityProduct
          have hScaledSquare : coefficient * length (k + 1) ^ 2 ≤
              B * length k * (phi (gap k) - phi (gap (k + 1))) := by
            calc
              coefficient * length (k + 1) ^ 2 =
                  1 * (coefficient * length (k + 1) ^ 2) := by ring
              _ ≤
                  (deriv phi (gap k) * (B * length k)) *
                    (coefficient * length (k + 1) ^ 2) :=
                mul_le_mul_of_nonneg_right hRelative
                  (mul_nonneg hCoefficientPos.le (sq_nonneg _))
              _ = B * length k *
                  (coefficient * deriv phi (gap k) * length (k + 1) ^ 2) := by ring
              _ ≤ B * length k *
                  (phi (gap k) - phi (gap (k + 1))) :=
                mul_le_mul_of_nonneg_left hPhiDrop
                  (mul_nonneg hBPos.le (hLengthNonneg k))
          let drop : ℝ :=
            (B / coefficient) * (phi (gap k) - phi (gap (k + 1)))
          have hDropNonneg : 0 ≤ drop := by
            dsimp only [drop]
            have hPhiDropNonneg : 0 ≤ phi (gap k) - phi (gap (k + 1)) :=
              le_trans (mul_nonneg
                (mul_nonneg hCoefficientPos.le hDerivPos.le) (sq_nonneg _)) hPhiDrop
            exact mul_nonneg (div_nonneg hBPos.le hCoefficientPos.le) hPhiDropNonneg
          have hSquareProduct : length (k + 1) ^ 2 ≤ length k * drop := by
            dsimp only [drop]
            calc
              length (k + 1) ^ 2 ≤
                  (B * length k *
                    (phi (gap k) - phi (gap (k + 1)))) / coefficient := by
                apply (le_div_iff₀ hCoefficientPos).2
                simpa only [mul_comm] using hScaledSquare
              _ = length k *
                  ((B / coefficient) *
                    (phi (gap k) - phi (gap (k + 1)))) := by ring
          have hTwoSquare : (2 * length (k + 1)) ^ 2 ≤
              (length k + drop) ^ 2 := by
            nlinarith [sq_nonneg (length k - drop)]
          have hTwoLength : 2 * length (k + 1) ≤ length k + drop :=
            (sq_le_sq₀ (mul_nonneg (by norm_num) (hLengthNonneg _))
              (add_nonneg (hLengthNonneg _) hDropNonneg)).1 hTwoSquare
          calc
            2 * length (k + 1) ≤ length k + drop := hTwoLength
            _ = length k + potential k - potential (k + 1) := by
              dsimp only [drop, potential]
              ring
    -- Shift beyond the eventual threshold; the scalar lemma then telescopes
    -- the finite sum of desingularized energy drops.
    have hEventualGood : ∀ᶠ k in atTop,
        (2 * length (k + 1) ≤
          length k + potential k - potential (k + 1)) ∧ gap k < eta :=
      hEventualRecurrence.and hGapLt
    obtain ⟨N, hTail⟩ := (eventually_atTop.1 hEventualGood)
    rw [← summable_nat_add_iff N]
    apply summable_of_two_mul_shift_le
      (fun k ↦ length (k + N)) (fun k ↦ potential (k + N))
    · intro k
      exact hLengthNonneg (k + N)
    · intro k
      have hGood := hTail (k + N) (by omega)
      have hGapMem : gap (k + N) ∈ Set.Ico 0 eta :=
        ⟨hGapNonneg (k + N), hGood.2⟩
      dsimp only [potential]
      exact mul_nonneg (div_nonneg hBPos.le hCoefficientPos.le)
        (hPhiSpec.1 hGapMem)
    · intro k
      have hGood := hTail (k + N) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hGood.1
  -- The proved comparison helper converts the KL length series to the source series.
  apply summableStepAndMultiplierIncrement_of_summableTwoStep h params h_region run
  simpa only [length] using hSummableLength

/-- Theorem 2.13 (2): under the same compactness and cluster-point
Kurdyka--Łojasiewicz hypotheses, the point and multiplier increments have finite
total length. -/
theorem summablePointAndMultiplierIncrement
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_compact : IsCompact (deterministicSublevel h params))
    (h_KL : KurdykaLojasiewicz.HasAtClusterPoints
      (liftedEnergy f c params.rho params.beta) atTop run.liftedIterate) :
    Summable (fun k ↦
      ‖run.point (k + 1) - run.point k‖ +
        ‖run.multiplier (k + 1) - run.multiplier k‖) := by
  simpa [run.point_succ] using
    summableStepAndMultiplierIncrement h params h_region run h_compact h_KL

/-- Under the hypotheses of Theorem 2.13, the lifted iterates converge to a KKT
pair with zero limiting step. -/
theorem existsLiftedKKTLimit
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_compact : IsCompact (deterministicSublevel h params))
    (h_KL : KurdykaLojasiewicz.HasAtClusterPoints
      (liftedEnergy f c params.rho params.beta) atTop run.liftedIterate) :
    ∃ limit : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m),
      KKT.IsPair f c limit.1 limit.2 ∧
        Tendsto run.liftedIterate atTop
          (𝓝 (liftedState limit.1 limit.2 0)) := by
  -- Split the finite-length result into summability of each nonnegative component.
  have hLength :=
    summableStepAndMultiplierIncrement h params h_region run h_compact h_KL
  have hStepNorm : Summable (fun k ↦ ‖run.step k‖) :=
    hLength.of_nonneg_of_le (fun k ↦ norm_nonneg (run.step k))
      (fun k ↦ le_add_of_nonneg_right (norm_nonneg _))
  have hMultiplierIncrementNorm :
      Summable (fun k ↦ ‖run.multiplier (k + 1) - run.multiplier k‖) :=
    hLength.of_nonneg_of_le (fun k ↦ norm_nonneg _)
      (fun k ↦ le_add_of_nonneg_left (norm_nonneg _))
  have hPointDistance :
      Summable (fun k ↦ dist (run.point k) (run.point k.succ)) := by
    simpa only [dist_eq_norm, run.point_succ, sub_add_eq_sub_sub, sub_self,
      zero_sub, norm_neg] using hStepNorm
  have hMultiplierDistance :
      Summable (fun k ↦ dist (run.multiplier k) (run.multiplier k.succ)) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hMultiplierIncrementNorm
  -- Completeness turns the two finite-length trajectories into convergent sequences.
  obtain ⟨xStar, hPoint⟩ :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hPointDistance)
  obtain ⟨multiplierStar, hMultiplier⟩ :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hMultiplierDistance)
  have hStep : Tendsto run.step atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 hStepNorm.tendsto_atTop_zero
  have hPreviousStep : Tendsto (fun k ↦ run.step (k - 1)) atTop (𝓝 0) :=
    hStep.comp (tendsto_sub_atTop_nat 1)
  have hLifted : Tendsto run.liftedIterate atTop
      (𝓝 (liftedState xStar multiplierStar 0)) := by
    have hCoordinates := hPoint.prodMk_nhds (hMultiplier.prodMk_nhds hPreviousStep)
    have hAssembly : Continuous
        (fun z : EuclideanSpace ℝ (Fin n) ×
            (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ↦
          liftedState z.1 z.2.1 z.2.2) := by
      unfold liftedState
      fun_prop
    have hAssembled :=
      (hAssembly.tendsto (xStar, multiplierStar, 0)).comp hCoordinates
    exact hAssembled.congr fun k ↦ by
      simp only [Function.comp_apply, liftedIterate_apply]
  obtain ⟨K, hKCompact, hKSubset, hKRange⟩ :=
    existsCompactLiftedIterateRange h params h_region run h_compact
  have hLiftedLimitMemK : liftedState xStar multiplierStar 0 ∈ K :=
    hKCompact.isClosed.mem_of_tendsto hLifted
      (Filter.Eventually.of_forall hKRange)
  have hLiftedLimitRegion :
      liftedState xStar multiplierStar 0 ∈ liftedRegularityRegion h :=
    hKSubset hLiftedLimitMemK
  have hPairLimitRegion : (xStar, multiplierStar) ∈ pairRegularityRegion h := by
    change xStar ∈ h.region
    exact hLiftedLimitRegion
  -- Lemma 2.11 and the vanishing steps force the aggregate KKT residual to zero.
  let comparison := residualComparisonConstant h params.delta params.beta params.rho
    params.multiplierBound
  have hStepNormZero : Tendsto (fun k ↦ ‖run.step k‖) atTop (𝓝 0) :=
    hStepNorm.tendsto_atTop_zero
  have hPreviousStepNormZero : Tendsto (fun k ↦ ‖run.step (k - 1)‖) atTop (𝓝 0) :=
    hStepNormZero.comp (tendsto_sub_atTop_nat 1)
  have hComparisonZero :
      Tendsto (fun k ↦ comparison *
        (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [pow_two, zero_mul, add_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ comparison) atTop (𝓝 comparison)).mul
        ((hStepNormZero.pow 2).add (hPreviousStepNormZero.pow 2))
  have hResidualSqBound : ∀ᶠ k in atTop,
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 ≤
        comparison * (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact residual_sq_le h params run
      (allPrefixesAdmissible h params h_region run (k + 1)) hk (Nat.lt_succ_self k)
  have hResidualSq :
      Tendsto (fun k ↦
        KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2)
        atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun k ↦ sq_nonneg _) hResidualSqBound hComparisonZero
  have hResidual : Tendsto (fun k ↦
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)))
      atTop (𝓝 0) := by
    have hSqrt : Tendsto (fun k ↦ Real.sqrt
        (KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2))
        atTop (𝓝 0) := by
      have hComposed := (Real.continuous_sqrt.tendsto 0).comp hResidualSq
      have hAtZero : Tendsto ((fun x ↦ Real.sqrt x) ∘ fun k ↦
          KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2)
          atTop (𝓝 0) := by
        simpa only [Real.sqrt_zero] using hComposed
      exact hAtZero.congr fun k ↦ rfl
    exact hSqrt.congr fun k ↦ by
      apply Real.sqrt_sq
      rw [KKT.residual_def]
      exact Real.sqrt_nonneg _
  -- Continuity identifies the limiting residual, hence the limit is exactly KKT.
  have hPair := hPoint.prodMk_nhds hMultiplier
  have hPairSucc := hPair.comp (tendsto_add_atTop_nat 1)
  have hResidualAtLimit : Tendsto (fun k ↦
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1))) atTop
      (𝓝 (KKT.residual f c xStar multiplierStar)) := by
    have hResidualContinuousAt : ContinuousAt
        (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
          KKT.residual f c z.1 z.2) (xStar, multiplierStar) :=
      (continuousOn_residual h).continuousAt
        ((isOpen_pairRegularityRegion h).mem_nhds hPairLimitRegion)
    have hContinuous := hResidualContinuousAt.tendsto.comp hPairSucc
    exact hContinuous.congr fun k ↦ by
      simp only [Function.comp_apply]
  have hResidualZero : KKT.residual f c xStar multiplierStar = 0 :=
    tendsto_nhds_unique hResidualAtLimit hResidual
  have hKKT : KKT.IsPair f c xStar multiplierStar := by
    have hApproximate : KKT.IsApproximatePair f c 0 xStar multiplierStar :=
      KKT.IsApproximatePair.of_residual_le (by rw [hResidualZero]; exact le_rfl)
    apply (KKT.isPair_iff f c xStar multiplierStar).2
    constructor
    · exact norm_le_zero_iff.mp (by simpa using hApproximate.stationarity_le)
    · exact norm_le_zero_iff.mp (by simpa using hApproximate.feasibility_le)
  exact ⟨(xStar, multiplierStar), hKKT, hLifted⟩

/-- Theorem 2.13 (3): under the same hypotheses, the whole point--multiplier
sequence converges to a KKT pair. -/
theorem existsKKTLimit
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_compact : IsCompact (deterministicSublevel h params))
    (h_KL : KurdykaLojasiewicz.HasAtClusterPoints
      (liftedEnergy f c params.rho params.beta) atTop run.liftedIterate) :
    ∃ limit : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m),
      KKT.IsPair f c limit.1 limit.2 ∧
        Tendsto (fun k ↦ (run.point k, run.multiplier k)) atTop (𝓝 limit) := by
  obtain ⟨limit, h_limit, h_lifted⟩ :=
    existsLiftedKKTLimit h params h_region run h_compact h_KL
  exact ⟨limit, h_limit,
    pairTendsto_of_liftedTendsto run limit.1 limit.2 h_lifted⟩

end Run

end LALM

end
