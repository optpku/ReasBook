/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycle
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Trajectory
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Optimality
public import glowinski_admm_counterexample.ReasLib.Convex.ExtendedReal

@[expose] public section

open Filter

namespace ConsensusADMM.IsProjectionCycle

open ConsensusADMM ProjectionCycle

universe u

variable {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonself-support certificate extends from the phase vertices and the origin
to their convex hull. -/
private lemma nonselfSupports_convexHull {p n : ZMod N → E}
    (supports : NonselfSupports p n) (i : ZMod N) (z : E)
    (hz : z ∈ convexHull ℝ (Set.insert 0 (Set.range p))) :
    0 ≤ inner ℝ (n i) (p i - z) := by
  -- Express the supporting half-space in a form whose convexity is immediate
  -- from linearity in the comparison point.
  let H : Set E := {w | inner ℝ (n i) w ≤ inner ℝ (n i) (p i)}
  have generators_mem : Set.insert 0 (Set.range p) ⊆ H := by
    intro w hw
    rcases hw with rfl | ⟨j, rfl⟩
    · have origin_support := (nonselfSupports_iff.mp supports i).1
      simpa only [H, Set.mem_setOf_eq, inner_zero_right, sub_zero,
        inner_sub_right, sub_nonneg] using origin_support
    · by_cases hji : j = i
      · subst j
        simp only [H, Set.mem_setOf_eq, le_refl]
      · have vertex_support := (nonselfSupports_iff.mp supports i).2 j hji
        simpa only [H, Set.mem_setOf_eq, inner_sub_right, sub_nonneg] using vertex_support
  have convex_H : Convex ℝ H := by
    intro x hx y hy a b ha hb hab
    simp only [H, Set.mem_setOf_eq, inner_add_right, inner_smul_right] at hx hy ⊢
    calc
      a * inner ℝ (n i) x + b * inner ℝ (n i) y ≤
          a * inner ℝ (n i) (p i) + b * inner ℝ (n i) (p i) :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = inner ℝ (n i) (p i) := by rw [← add_mul, hab, one_mul]
  -- Minimality of the convex hull now places every feasible comparison point
  -- in the same supporting half-space.
  have hzH : z ∈ H := convexHull_min generators_mem convex_H hz
  simpa only [H, Set.mem_setOf_eq, inner_sub_right, sub_nonneg] using hzH

/-- A supported feasible point is the unique minimizer of its indicator plus
an affine quadratic objective. -/
private lemma extendedIndicatorAugmented_uniqueMinimizer {X : Set E} {p center dual : E}
    (hp : p ∈ X)
    (supports : ∀ z ∈ X, 0 ≤ inner ℝ (center - dual - p) (p - z)) :
    (∀ z,
      extendedIndicator X p +
          ((inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 : ℝ) : EReal) ≤
        extendedIndicator X z +
          ((inner ℝ dual (z - center) + ‖z - center‖ ^ 2 / 2 : ℝ) : EReal)) ∧
      (∀ z,
        extendedIndicator X z +
            ((inner ℝ dual (z - center) + ‖z - center‖ ^ 2 / 2 : ℝ) : EReal) ≤
          extendedIndicator X p +
            ((inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 : ℝ) : EReal) →
        z = p) ∧
      extendedIndicator X p ≠ ⊤ := by
  -- Completing the square records the objective gap as the support term plus
  -- half the squared distance from the candidate.
  have objective_gap (z : E) :
      inner ℝ dual (z - center) + ‖z - center‖ ^ 2 / 2 =
        inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 +
          inner ℝ (center - dual - p) (p - z) + ‖z - p‖ ^ 2 / 2 := by
    have displacement : z - center = (p - center) + (z - p) := by
      abel
    rw [displacement, norm_add_sq_real]
    simp only [inner_add_right, inner_sub_left, inner_sub_right]
    ring
  constructor
  · intro z
    by_cases hz : z ∈ X
    · rw [extendedIndicator_of_mem hp, extendedIndicator_of_mem hz]
      simp only [zero_add, EReal.coe_le_coe_iff]
      rw [objective_gap z]
      nlinarith [supports z hz, sq_nonneg ‖z - p‖]
    · rw [extendedIndicator_of_mem hp, extendedIndicator_of_not_mem hz]
      simp
  constructor
  · intro z objective_le
    by_cases hz : z ∈ X
    · have real_objective_le :
          inner ℝ dual (z - center) + ‖z - center‖ ^ 2 / 2 ≤
            inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 := by
        simpa only [extendedIndicator_of_mem hz, extendedIndicator_of_mem hp,
          zero_add, EReal.coe_le_coe_iff] using objective_le
      have distance_zero : ‖z - p‖ = 0 := by
        rw [objective_gap z] at real_objective_le
        nlinarith [supports z hz, sq_nonneg ‖z - p‖, norm_nonneg (z - p)]
      exact sub_eq_zero.mp (norm_eq_zero.mp distance_zero)
    · have top_le : ⊤ ≤
          extendedIndicator X p +
            ((inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 : ℝ) : EReal) := by
        rw [extendedIndicator_of_not_mem hz,
          EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at objective_le
        exact objective_le
      have finite_ne_top :
          extendedIndicator X p +
              ((inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 : ℝ) : EReal) ≠ ⊤ := by
        rw [extendedIndicator_of_mem hp, zero_add]
        exact EReal.coe_ne_top _
      exact (finite_ne_top (top_unique top_le)).elim
  · rw [extendedIndicator_of_mem hp]
    exact EReal.coe_ne_top 0

/-- Indicators of two sets containing the origin make the origin a KKT point
and a primal minimizer of value zero. -/
private lemma indicatorOriginOptimality {X Y : Set E} (zero_mem_X : 0 ∈ X)
    (zero_mem_Y : 0 ∈ Y) :
    IsKKT (extendedIndicator X) (extendedIndicator Y) 0 0 0 ∧
      IsPrimalMinimizer (extendedIndicator X) (extendedIndicator Y) 0 ∧
      extendedIndicator X 0 + extendedIndicator Y 0 = 0 := by
  -- At the zero multiplier, each KKT inequality is just nonnegativity of an
  -- indicator, handled separately on and off its feasible set.
  have kkt : IsKKT (extendedIndicator X) (extendedIndicator Y) 0 0 0 := by
    rw [kkt_iff]
    refine ⟨rfl, ?_, ?_⟩
    · intro z
      by_cases z_mem : z ∈ X
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem z_mem]
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_not_mem z_mem]
    · intro z
      by_cases z_mem : z ∈ Y
      · simp [extendedIndicator_of_mem zero_mem_Y, extendedIndicator_of_mem z_mem]
      · simp [extendedIndicator_of_mem zero_mem_Y, extendedIndicator_of_not_mem z_mem]
  -- The same membership split proves global primal minimality.
  have primal : IsPrimalMinimizer (extendedIndicator X) (extendedIndicator Y) 0 := by
    rw [primalMinimizer_iff]
    intro z
    by_cases z_mem_X : z ∈ X
    · by_cases z_mem_Y : z ∈ Y
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem zero_mem_Y,
          extendedIndicator_of_mem z_mem_X, extendedIndicator_of_mem z_mem_Y]
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem zero_mem_Y,
          extendedIndicator_of_mem z_mem_X, extendedIndicator_of_not_mem z_mem_Y]
    · by_cases z_mem_Y : z ∈ Y
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem zero_mem_Y,
          extendedIndicator_of_not_mem z_mem_X, extendedIndicator_of_mem z_mem_Y]
      · simp [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem zero_mem_Y,
          extendedIndicator_of_not_mem z_mem_X, extendedIndicator_of_not_mem z_mem_Y]
  -- Both finite branches are zero at the origin.
  have value : extendedIndicator X 0 + extendedIndicator Y 0 = 0 := by
    rw [extendedIndicator_of_mem zero_mem_X, extendedIndicator_of_mem zero_mem_Y]
    exact add_zero 0
  exact ⟨kkt, primal, value⟩

/-- Every natural-valued period has a least positive divisor among the positive
periods of a sequence. -/
private lemma existsExactPeriod_dvd_of_periodic {x y dual : ℕ → E} {period : ℕ}
    (period_pos : 0 < period)
    (periodic : Function.Periodic (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) period) :
    ∃ d : ℕ, 0 < d ∧ d ∣ period ∧ HasExactPeriod d x y dual := by
  classical
  let state : ℕ → E × E × E := fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))
  let IsPositivePeriod : ℕ → Prop := fun n ↦ 0 < n ∧ Function.Periodic state n
  have exists_period : ∃ n, IsPositivePeriod n := ⟨period, period_pos, periodic⟩
  let d := Nat.find exists_period
  have d_spec : IsPositivePeriod d := Nat.find_spec exists_period
  have d_pos : 0 < d := d_spec.1
  have d_periodic : Function.Periodic state d := d_spec.2
  -- The remainder on division by the least positive period is itself a period:
  -- append enough `d`-steps to reach the known `period`-step.
  have multiple_periodic (q : ℕ) : Function.Periodic state (q * d) := by
    induction q with
    | zero =>
        intro k
        simp only [Nat.zero_mul, add_zero]
    | succ q induction_hypothesis =>
        intro k
        rw [Nat.succ_mul]
        calc
          state (k + (q * d + d)) = state ((k + q * d) + d) := by
            rw [Nat.add_assoc]
          _ = state (k + q * d) := d_periodic (k + q * d)
          _ = state k := induction_hypothesis k
  have remainder_periodic : Function.Periodic state (period % d) := by
    intro k
    calc
      state (k + period % d) = state ((k + period % d) + (period / d) * d) :=
        (multiple_periodic (period / d) (k + period % d)).symm
      _ = state (k + period) := by
        apply congrArg state
        have division := Nat.mod_add_div period d
        rw [Nat.mul_comm (period / d) d]
        omega
      _ = state k := periodic k
  have remainder_zero : period % d = 0 := by
    by_contra remainder_ne
    have remainder_pos : 0 < period % d := Nat.pos_of_ne_zero remainder_ne
    have d_le_remainder : d ≤ period % d :=
      Nat.find_min' exists_period ⟨remainder_pos, remainder_periodic⟩
    have remainder_lt : period % d < d := Nat.mod_lt period d_pos
    omega
  have d_dvd_period : d ∣ period := Nat.dvd_of_mod_eq_zero remainder_zero
  -- Minimality in `Nat.find` is exactly the lower-bound clause of exact period.
  have exact : HasExactPeriod d x y dual := by
    rw [exactPeriod_iff]
    refine ⟨d_periodic, ?_⟩
    intro n n_pos n_periodic
    exact Nat.find_min' exists_period ⟨n_pos, n_periodic⟩
  exact ⟨d, d_pos, d_dvd_period, exact⟩

/-- The two supported projection steps simultaneously give the prescribed
trajectory and uniqueness of both block updates. -/
private lemma blockUpdates (γ : ℝ) (η ν : ZMod N → E) (hγ : 0 < γ)
    (hcycle : ConsensusADMM.IsProjectionCycle γ η ν) :
    IsTrajectory γ (extendedIndicator (xSet γ η ν)) (extendedIndicator (ySet η))
        (xSequence γ η ν) (ySequence η) (dualSequence ν) ∧
      HasUniqueUpdates (extendedIndicator (xSet γ η ν)) (extendedIndicator (ySet η))
        (xSequence γ η ν) (ySequence η) (dualSequence ν) := by
  obtain ⟨first_supports, second_supports⟩ := isProjectionCycle_iff.mp hcycle
  -- Each phase vertex belongs to its corresponding convex hull.
  have firstVertex_mem (i : ZMod N) : xVertex γ η ν i ∈ xSet γ η ν := by
    rw [xSet_def]
    exact (subset_convexHull ℝ (Set.insert 0 (Set.range (xVertex γ η ν))))
      (Or.inr ⟨i, rfl⟩)
  have secondVertex_mem (i : ZMod N) : η i ∈ ySet η := by
    rw [ySet_def]
    exact (subset_convexHull ℝ (Set.insert 0 (Set.range η))) (Or.inr ⟨i, rfl⟩)
  -- Extend both finite support tables over the complete feasible hulls.
  have firstHull_support (i : ZMod N) (z : E) (hz : z ∈ xSet γ η ν) :
      0 ≤ inner ℝ (firstNormal γ η ν i) (xVertex γ η ν i - z) := by
    apply nonselfSupports_convexHull first_supports i z
    simpa only [xSet_def] using hz
  have secondHull_support (i : ZMod N) (z : E) (hz : z ∈ ySet η) :
      0 ≤ inner ℝ (secondNormal γ ν i) (η i - z) := by
    apply nonselfSupports_convexHull second_supports i z
    simpa only [ySet_def] using hz
  -- The first normal is exactly the negative gradient of the first quadratic
  -- at its prescribed phase vertex.
  have firstGradient_support (i : ZMod N) :
      ∀ z ∈ xSet γ η ν,
        0 ≤ inner ℝ (η (i - 1) - ν (i - 1) - xVertex γ η ν i)
          (xVertex γ η ν i - z) := by
    intro z hz
    simpa only [firstNormal_apply] using firstHull_support i z hz
  have firstUpdate (i : ZMod N) :=
    extendedIndicatorAugmented_uniqueMinimizer (firstVertex_mem i)
      (firstGradient_support i)
  -- For the second block, reversing the displacement changes the affine term
  -- into the same generic quadratic form with multiplier `-ν (i - 1)`.
  have secondNormal_as_gradient (i : ZMod N) :
      xVertex γ η ν i - (-ν (i - 1)) - η i = secondNormal γ ν i := by
    rw [xVertex_apply, secondNormal_apply]
    abel
  have secondGradient_support (i : ZMod N) :
      ∀ z ∈ ySet η,
        0 ≤ inner ℝ (xVertex γ η ν i - (-ν (i - 1)) - η i) (η i - z) := by
    intro z hz
    rw [secondNormal_as_gradient i]
    exact secondHull_support i z hz
  have secondUpdate (i : ZMod N) :=
    extendedIndicatorAugmented_uniqueMinimizer (secondVertex_mem i)
      (secondGradient_support i)
  have secondObjective (i : ZMod N) (z : E) :
      inner ℝ (-ν (i - 1)) (z - xVertex γ η ν i) +
          ‖z - xVertex γ η ν i‖ ^ 2 / 2 =
        inner ℝ (ν (i - 1)) (xVertex γ η ν i - z) +
          ‖xVertex γ η ν i - z‖ ^ 2 / 2 := by
    have reverse_displacement :
        z - xVertex γ η ν i = -(xVertex γ η ν i - z) := by
      abel
    rw [reverse_displacement, inner_neg_left, inner_neg_right, norm_neg, neg_neg]
  constructor
  · rw [trajectory_iff]
    intro k
    -- Normalize the stored sequences to their common phase and use the two
    -- unique-minimizer certificates for the block inequalities and finiteness.
    rw [xSequence_succ, ySequence_succ, ySequence_apply, dualSequence_succ,
      dualSequence_apply]
    refine ⟨(firstUpdate (k : ZMod N)).1, ?_,
      (firstUpdate (k : ZMod N)).2.2, (secondUpdate (k : ZMod N)).2.2, ?_⟩
    · intro z
      have update := (secondUpdate (k : ZMod N)).1 z
      rw [secondObjective (k : ZMod N) (η (k : ZMod N)),
        secondObjective (k : ZMod N) z] at update
      exact update
    · -- The residual definition turns the relaxed multiplier step into the
      -- neighboring phase difference.
      rw [xVertex_apply, add_sub_cancel_left, residual_apply, smul_smul]
      simp [hγ.ne']
  · rw [uniqueUpdates_iff]
    intro k
    -- The first uniqueness implication already has the generic orientation;
    -- reverse both second-block displacements before applying its certificate.
    rw [xSequence_succ, ySequence_succ, ySequence_apply, dualSequence_apply]
    refine ⟨(firstUpdate (k : ZMod N)).2.1, ?_⟩
    intro z objective_le
    apply (secondUpdate (k : ZMod N)).2.1 z
    rw [secondObjective (k : ZMod N) z,
      secondObjective (k : ZMod N) (η (k : ZMod N))]
    exact objective_le

/-- The prescribed cyclic sequences form a unit-penalty consensus ADMM trajectory
for the extended indicators of the two cycle polytopes. -/
theorem isTrajectory (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hcycle : ConsensusADMM.IsProjectionCycle γ η ν) :
    IsTrajectory γ (extendedIndicator (xSet γ η ν)) (extendedIndicator (ySet η))
      (xSequence γ η ν) (ySequence η) (dualSequence ν) := by
  -- The shared block-update interface contains the complete trajectory proof.
  exact (blockUpdates γ η ν hγ hcycle).1

/-- Every block minimum along the prescribed projection-cycle trajectory is unique. -/
theorem hasUniqueUpdates (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hcycle : ConsensusADMM.IsProjectionCycle γ η ν) :
    HasUniqueUpdates (extendedIndicator (xSet γ η ν)) (extendedIndicator (ySet η))
      (xSequence γ η ν) (ySequence η) (dualSequence ν) := by
  -- The same phasewise certificates also contain both uniqueness implications.
  exact (blockUpdates γ η ν hγ hcycle).2

/-- The origin triple satisfies the consensus KKT conditions for the two cycle polytopes. -/
theorem isKKT (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hcycle : ConsensusADMM.IsProjectionCycle γ η ν) :
    IsKKT (extendedIndicator (xSet γ η ν)) (extendedIndicator (ySet η)) 0 0 0 := by
  -- Both defining convex hulls contain their explicitly inserted origin.
  have zero_mem_X : 0 ∈ xSet γ η ν := by
    rw [xSet_def]
    exact (subset_convexHull ℝ (Set.insert 0 (Set.range (xVertex γ η ν))))
      (Set.mem_insert 0 (Set.range (xVertex γ η ν)))
  have zero_mem_Y : 0 ∈ ySet η := by
    rw [ySet_def]
    exact (subset_convexHull ℝ (Set.insert 0 (Set.range η)))
      (Set.mem_insert 0 (Set.range η))
  -- Project the KKT clause of the generic origin-indicator result.
  exact (indicatorOriginOptimality zero_mem_X zero_mem_Y).1

/-- The origin is primal optimal for the two cycle polytopes and has objective value zero. -/
theorem isOptimalValueZero (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hcycle : ConsensusADMM.IsProjectionCycle γ η ν) :
    IsPrimalMinimizer (extendedIndicator (xSet γ η ν)) (extendedIndicator (ySet η)) 0 ∧
      extendedIndicator (xSet γ η ν) 0 + extendedIndicator (ySet η) 0 = 0 := by
  -- Both defining convex hulls contain their explicitly inserted origin.
  have zero_mem_X : 0 ∈ xSet γ η ν := by
    rw [xSet_def]
    exact (subset_convexHull ℝ (Set.insert 0 (Set.range (xVertex γ η ν))))
      (Set.mem_insert 0 (Set.range (xVertex γ η ν)))
  have zero_mem_Y : 0 ∈ ySet η := by
    rw [ySet_def]
    exact (subset_convexHull ℝ (Set.insert 0 (Set.range η)))
      (Set.mem_insert 0 (Set.range η))
  -- Project primal minimality and the value identity from the common result.
  exact (indicatorOriginOptimality zero_mem_X zero_mem_Y).2

/-- A nonzero phase residual prevents the prescribed primal residuals from converging to zero. -/
theorem residual_not_tendsto (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hcycle : ConsensusADMM.IsProjectionCycle γ η ν)
    (hnonzero : ∃ i, residual γ ν i ≠ 0) :
    ¬ Tendsto (primalResidual γ η ν) atTop (nhds 0) := by
  obtain ⟨i, residual_ne⟩ := hnonzero
  have residual_norm_pos : 0 < ‖residual γ ν i‖ := norm_pos_iff.mpr residual_ne
  intro converges
  rw [Metric.tendsto_atTop] at converges
  obtain ⟨K, eventually_close⟩ := converges ‖residual γ ν i‖ residual_norm_pos
  have N_pos : 0 < N := by omega
  -- Local instance justification (proof-local temporary data): the return-phase `ZMod`
  -- calculation needs the temporary `NeZero N`, which is not inferable from `hN`.
  letI : NeZero N := ⟨Nat.ne_of_gt N_pos⟩
  let returnTime := i.val + K * N
  have K_le_returnTime : K ≤ returnTime := by
    dsimp only [returnTime]
    have K_le_multiple : K ≤ K * N := by nlinarith
    nlinarith
  have return_phase : ((returnTime : ℕ) : ZMod N) = i := by
    dsimp only [returnTime]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
      ZMod.natCast_zmod_val]
  -- At the return time the strict convergence estimate reads `‖r‖ < ‖r‖`.
  have impossible := eventually_close returnTime K_le_returnTime
  rw [primalResidual_apply, return_phase, dist_zero_right] at impossible
  exact (lt_irrefl ‖residual γ ν i‖) impossible

/-- The positive minimal period of the prescribed trajectory divides the number of phases. -/
theorem minimalPeriod_dvd (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hcycle : ConsensusADMM.IsProjectionCycle γ η ν) :
    ∃ d : ℕ, 0 < d ∧ d ∣ N ∧
      HasExactPeriod d (xSequence γ η ν) (ySequence η) (dualSequence ν) := by
  -- Every post-update component depends only on the phase in `ZMod N`, hence
  -- the entire state repeats after `N` steps.
  have state_periodic :
      Function.Periodic
        (fun k ↦
          (xSequence γ η ν (k + 1), ySequence η (k + 1), dualSequence ν (k + 1))) N := by
    intro k
    simp only [xSequence_succ, ySequence_succ, dualSequence_succ, Nat.cast_add,
      ZMod.natCast_self, add_zero]
  -- Choose the least positive state period; the generic remainder argument
  -- proves that it divides the displayed `N`-period.
  have N_pos : 0 < N := by omega
  exact existsExactPeriod_dvd_of_periodic N_pos state_periodic

end ConsensusADMM.IsProjectionCycle
