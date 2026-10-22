/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_2.IndexSets
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_13.ProjectedGradient
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_6.Projection
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_9.CriticalPoint
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_7
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_14
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_15.Projector
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8.FeasibleSet
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Remark_9_11.StrictComplementarity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.ExtrClosure
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.EMetricSpace.Lipschitz

public section

noncomputable section

namespace GradientProjection

/-- Helper for Theorem 9.17: a convergent sequence that stays in the
nonnegative-orthant feasible set has a feasible limit. -/
private lemma limit_memFeasibleSet_of_tendsto
    (n : ℕ)
    {u : ℕ → EuclideanSpace ℝ (Fin n)}
    (hu : ∀ v, u v ∈ NonnegativeOrthant.feasibleSet n)
    {f : EuclideanSpace ℝ (Fin n)}
    (hconv : Filter.Tendsto u Filter.atTop (nhds f)) :
    f ∈ NonnegativeOrthant.feasibleSet n := by
  -- Closedness of the feasible orthant transports feasible membership to the limit.
  exact
    (NonnegativeOrthant.closedConvex_feasibleSet n).isClosed.mem_of_tendsto
      hconv
      (Filter.Eventually.of_forall hu)

/-- Helper for Theorem 9.17: every successor projected-gradient iterate lies in
the nonnegative-orthant feasible set. -/
private lemma iteratesSucc_memFeasibleSet
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n)) (v : ℕ) :
    GradientProjection.iterates
        (NonnegativeOrthant.projector n)
        J τ f0
        (v + 1) ∈
      NonnegativeOrthant.feasibleSet n := by
  -- Rewrite the successor iterate as an orthant projection and use projector feasibility.
  rw [GradientProjection.iterates_succ]
  rw [GradientProjection.update_eq_projector_sub_smul_gradient]
  exact NonnegativeOrthant.projector_mem_feasibleSet n _

/-- Helper for Theorem 9.17: every iterate from index `1` onward is feasible
for the nonnegative orthant. -/
private lemma iterate_memFeasibleSet_of_one_le
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    {v : ℕ}
    (hv : 1 ≤ v) :
    (GradientProjection.iterates
      (NonnegativeOrthant.projector n)
      J τ f0 v) ∈
        NonnegativeOrthant.feasibleSet n := by
  -- Any positive iterate is a successor iterate, so feasibility comes from the projector step.
  have hv_ne_zero : v ≠ 0 := by
    omega
  rcases Nat.exists_eq_succ_of_ne_zero hv_ne_zero with ⟨w, rfl⟩
  simpa [Nat.succ_eq_add_one] using iteratesSucc_memFeasibleSet n J τ f0 w

/-- Helper for Theorem 9.17: if a limit coordinate of the iterate sequence is
strictly positive, then the corresponding iterate coordinates are eventually
strictly positive as well. -/
private lemma eventually_pos_on_inactiveCoordinates
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fStar : EuclideanSpace ℝ (Fin n))
    (hconv :
      Filter.Tendsto
        (GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0)
        Filter.atTop
        (nhds fStar)) :
    ∀ {i : Fin n}, 0 < fStar i →
      ∃ v0 : ℕ,
        ∀ v ≥ v0,
          0 <
            (GradientProjection.iterates
              (NonnegativeOrthant.projector n)
              J τ f0 v) i := by
  intro i hi
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  have happly :
      Continuous (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) := by
    simpa using
      (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i)
  have happlyContAt : ContinuousAt (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) fStar :=
    happly.continuousAt
  have hcoord : Filter.Tendsto (fun v ↦ (u v) i) Filter.atTop (nhds (fStar i)) := by
    -- Postcompose the iterate convergence with the continuous coordinate evaluation.
    exact happlyContAt.tendsto.comp hconv
  have heventually :
      ∀ᶠ v : ℕ in Filter.atTop, fStar i / 2 < (u v) i := by
    -- A neighborhood strictly below the positive limit forces eventual positivity.
    refine hcoord.eventually ?_
    exact Ioi_mem_nhds (by linarith : fStar i / 2 < fStar i)
  obtain ⟨v0, hv0⟩ := Filter.eventually_atTop.mp heventually
  refine ⟨v0, ?_⟩
  intro v hv
  have hhalf : fStar i / 2 < (u v) i := hv0 v hv
  linarith

/-- Helper for Theorem 9.17: at a strictly complementary active coordinate, the
gradient component along the iterate sequence is eventually strictly positive. -/
private lemma eventually_pos_gradient_on_activeCoordinates
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fStar : EuclideanSpace ℝ (Fin n))
    (K : NNReal)
    (hGradLip : LipschitzWith K (gradient J))
    (hconv :
      Filter.Tendsto
        (GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0)
        Filter.atTop
        (nhds fStar))
    (hsc : NonnegativeOrthant.StrictComplementarity J fStar) :
    ∀ {i : Fin n}, fStar i = 0 →
      ∃ v0 : ℕ,
        ∀ v ≥ v0,
          0 <
            gradient J
              ((GradientProjection.iterates
                (NonnegativeOrthant.projector n)
                J τ f0) v) i := by
  intro i hi
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  have hgradPos : 0 < gradient J fStar i :=
    NonnegativeOrthant.pos_of_eq_zero hsc hi
  have happly :
      Continuous (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) := by
    simpa using
      (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i)
  have happlyContAt : ContinuousAt (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) (gradient J fStar) :=
    happly.continuousAt
  have hgradContAt : ContinuousAt (gradient J) fStar := by
    exact hGradLip.continuous.continuousAt
  have hgradTendsto :
      Filter.Tendsto (fun v ↦ gradient J (u v)) Filter.atTop (nhds (gradient J fStar)) := by
    exact hgradContAt.tendsto.comp hconv
  have hcoord :
      Filter.Tendsto
        (fun v ↦ gradient J (u v) i)
        Filter.atTop
        (nhds (gradient J fStar i)) := by
    -- Continuity of the gradient and coordinate evaluation transports sequence convergence.
    exact happlyContAt.tendsto.comp hgradTendsto
  have heventually :
      ∀ᶠ v : ℕ in Filter.atTop,
        gradient J fStar i / 2 <
          gradient J (u v) i := by
    -- Staying above half the strictly positive limit gives a uniform positive lower bound.
    refine hcoord.eventually ?_
    exact Ioi_mem_nhds (by linarith : gradient J fStar i / 2 < gradient J fStar i)
  obtain ⟨v0, hv0⟩ := Filter.eventually_atTop.mp heventually
  refine ⟨v0, ?_⟩
  intro v hv
  have hhalf : gradient J fStar i / 2 < gradient J (u v) i := hv0 v hv
  linarith

/-- Helper for Theorem 9.17: the nonnegative-orthant projector is continuous. -/
private lemma continuous_projector
    (n : ℕ) :
    Continuous (NonnegativeOrthant.projector n) := by
  -- The orthant projector is the Euclidean projection onto the closed convex feasible set.
  rw [show NonnegativeOrthant.projector n =
      EuclideanProjection.proj
        (NonnegativeOrthant.feasibleSet n)
        (NonnegativeOrthant.feasibleSet_nonempty n)
        (NonnegativeOrthant.closedConvex_feasibleSet n) by
      funext x
      exact NonnegativeOrthant.projector_eq_proj n x]
  exact
    EuclideanProjection.continuous_proj
      (NonnegativeOrthant.feasibleSet n)
      (NonnegativeOrthant.feasibleSet_nonempty n)
      (NonnegativeOrthant.closedConvex_feasibleSet n)

/-- Helper for Theorem 9.17: the projected line-search profile is exactly the
algorithm update evaluated by the objective. -/
private lemma profileDirection_apply_eq_update_local
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (α : ℝ) :
    LineSearch.profile
        (J ∘ NonnegativeOrthant.projector n)
        x
        (direction J x)
        α =
      J (update (NonnegativeOrthant.projector n) J α x) := by
  -- Route correction: this file now reuses the canonical owner-level bridge
  -- instead of shadowing it with a same-named local declaration.
  simpa using
    (GradientProjection.profileDirection_apply_eq_update
      (NonnegativeOrthant.projector n) J x α)

/-- Helper for Theorem 9.17: the projected line-search profile is exactly the
objective evaluated at a projected gradient step. -/
private lemma profile_projectedUpdate_eq
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (α : ℝ) :
    LineSearch.profile
        (J ∘ NonnegativeOrthant.projector n)
        x
        (GradientProjection.direction J x)
        α =
      J (NonnegativeOrthant.projector n (x - α • gradient J x)) := by
  -- Route correction: normalize the profile through the owner-level update API
  -- before rewriting that update to the projected-gradient step surface.
  rw [profileDirection_apply_eq_update_local]
  simp [GradientProjection.update_eq_projector_sub_smul_gradient]

/-- Helper for Theorem 9.17: exact line search compares the accepted step
against every positive projected update. -/
private lemma exactLineSearch_le_projectedUpdate
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0)
    (v : ℕ)
    {α : ℝ}
    (hα : 0 < α) :
    let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
    J (u (v + 1)) ≤
      J (NonnegativeOrthant.projector n (u v - α • gradient J (u v))) := by
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  rw [GradientProjection.isExactLineSearch_iff] at hLineSearch
  have hmin := hLineSearch v
  rw [isMinOn_iff] at hmin
  have hcompare := hmin α hα
  -- Rewrite the minimizing profile inequality onto the stable projected-update surface.
  simpa [u, profile_projectedUpdate_eq, GradientProjection.iterates_succ,
    GradientProjection.update_eq_projector_sub_smul_gradient] using hcompare

/-- Helper for Theorem 9.17: vanishing projected updates converge back to a
feasible base point. -/
private lemma tendsto_projectedStep_at_zero
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ NonnegativeOrthant.feasibleSet n) :
    Filter.Tendsto
      (fun α : ℝ ↦ NonnegativeOrthant.projector n (x - α • gradient J x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds x) := by
  -- The step map is continuous in `α`, and the projector fixes feasible points at `α = 0`.
  have hcont :
      Continuous fun α : ℝ ↦
        NonnegativeOrthant.projector n (x - α • gradient J x) := by
    refine (continuous_projector n).comp ?_
    exact continuous_const.sub (continuous_id.smul continuous_const)
  have hzero :
      NonnegativeOrthant.projector n (x - (0 : ℝ) • gradient J x) = x := by
    simp [NonnegativeOrthant.projector_eq_self_of_mem, hx]
  have hzero' : NonnegativeOrthant.projector n x = x := by
    simpa using hzero
  have hcontWithin :
      ContinuousWithinAt
        (fun α : ℝ ↦ NonnegativeOrthant.projector n (x - α • gradient J x))
        (Set.Ioi 0)
        0 := by
    exact hcont.continuousAt.continuousWithinAt
  have hcontWithinTendsto :
      Filter.Tendsto
        (fun α : ℝ ↦ NonnegativeOrthant.projector n (x - α • gradient J x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (NonnegativeOrthant.projector n (x - (0 : ℝ) • gradient J x))) := by
    exact hcontWithin.tendsto
  have hlim :
      Filter.Tendsto
        (fun α : ℝ ↦ NonnegativeOrthant.projector n (x - α • gradient J x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (NonnegativeOrthant.projector n (x - (0 : ℝ) • gradient J x))) :=
    hcontWithinTendsto
  simpa [hzero'] using hlim

/-- Helper for Theorem 9.17: exact line search makes the feasible-tail
objective values monotone nonincreasing. -/
private lemma iterates_value_step_le
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ_diff :
      ∀ x ∈ NonnegativeOrthant.feasibleSet n,
        DifferentiableAt ℝ J x)
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0)
    (v : ℕ) :
    let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
    J (u (v + 2)) ≤ J (u (v + 1)) := by
  let _ := K
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  have hv_feasible : u (v + 1) ∈ NonnegativeOrthant.feasibleSet n := by
    simpa [u] using iteratesSucc_memFeasibleSet n J τ f0 v
  have hvalue_tendsto :
      Filter.Tendsto
        (fun α : ℝ ↦
          J (NonnegativeOrthant.projector n
            (u (v + 1) - α • gradient J (u (v + 1)))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (J (u (v + 1)))) := by
    -- Continuity of `J` at the feasible iterate transports the projected-step limit.
    have hJContAt : ContinuousAt J (u (v + 1)) := (hJ_diff _ hv_feasible).continuousAt
    exact
      hJContAt.tendsto.comp
        (tendsto_projectedStep_at_zero n J hv_feasible)
  have hcompare :
      (fun _ : ℝ ↦ J (u (v + 2))) ≤ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun α : ℝ ↦
          J (NonnegativeOrthant.projector n
            (u (v + 1) - α • gradient J (u (v + 1)))) := by
    -- Every positive candidate step dominates the exact line-search choice at stage `v + 1`.
    have hpositive : ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < α := by
      change Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)
      exact self_mem_nhdsWithin
    filter_upwards [hpositive] with α hα
    simpa [u, Nat.add_assoc] using
      exactLineSearch_le_projectedUpdate n J τ f0 hLineSearch (v + 1) hα
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hvalue_tendsto hcompare

/-- Helper for Theorem 9.17: below the coordinatewise clipping thresholds, the
projected update agrees with subtracting the projected gradient. -/
private lemma projectedUpdate_eq_sub_projectedGradient_of_coordThreshold
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ NonnegativeOrthant.feasibleSet n)
    {α : ℝ}
    (hα_nonneg : 0 ≤ α)
    (hthreshold :
      ∀ i : Fin n, 0 < f i → 0 < gradient J f i → α ≤ f i / gradient J f i) :
    NonnegativeOrthant.projector n (f - α • gradient J f) =
      f - α • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩ := by
  ext i
  change
      (NonnegativeOrthant.projector n (f - α • gradient J f)) i =
        (f - α • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) i
  -- Compare both sides coordinatewise through the explicit orthant clipping formula.
  rw [NonnegativeOrthant.projector_apply_eq_max]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hfi_pos : 0 < f i
  · by_cases hgrad_pos : 0 < gradient J f i
    · have hmul : α * gradient J f i ≤ f i := by
        exact (le_div_iff₀ hgrad_pos).mp (hthreshold i hfi_pos hgrad_pos)
      have hsub_nonneg : 0 ≤ f i - α * gradient J f i := sub_nonneg.mpr hmul
      -- Positive coordinates with positive gradient stay above the clipping boundary.
      rw [max_eq_left hsub_nonneg,
        NonnegativeOrthant.projectedGradient_apply_of_pos J f hf i hfi_pos]
    · have hmul_nonpos : α * gradient J f i ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos hα_nonneg (le_of_not_gt hgrad_pos)
      have hsub_nonneg : 0 ≤ f i - α * gradient J f i := by
        have hfi_nonneg : 0 ≤ f i := le_of_lt hfi_pos
        linarith
      -- If the gradient is nonpositive, the projected step still stays on the positive branch.
      rw [max_eq_left hsub_nonneg,
        NonnegativeOrthant.projectedGradient_apply_of_pos J f hf i hfi_pos]
  · have hfi_eq_zero : f i = 0 := by
      exact
        le_antisymm
          (le_of_not_gt hfi_pos)
          ((NonnegativeOrthant.mem_feasibleSet.mp hf) i)
    by_cases hgrad_pos : 0 < gradient J f i
    · have hterm_nonpos : f i - α * gradient J f i ≤ 0 := by
        rw [hfi_eq_zero]
        have hmul_nonneg : 0 ≤ α * gradient J f i := mul_nonneg hα_nonneg hgrad_pos.le
        linarith
      have hterm_nonpos' : 0 - α * gradient J f i ≤ 0 := by
        simpa [hfi_eq_zero] using hterm_nonpos
      -- A zero coordinate with positive gradient is clipped back to zero.
      rw [hfi_eq_zero]
      rw [NonnegativeOrthant.projectedGradient_apply_of_eq_zero J f hf i hfi_eq_zero]
      rw [min_eq_left hgrad_pos.le]
      rw [max_eq_right hterm_nonpos']
      simp
    · have hgrad_nonpos : gradient J f i ≤ 0 := le_of_not_gt hgrad_pos
      have hterm_nonneg : 0 ≤ f i - α * gradient J f i := by
        rw [hfi_eq_zero]
        have hmul_nonpos : α * gradient J f i ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hα_nonneg hgrad_nonpos
        linarith
      have hterm_nonneg' : 0 ≤ 0 - α * gradient J f i := by
        simpa [hfi_eq_zero] using hterm_nonneg
      -- A zero coordinate with nonpositive gradient follows the clipped gradient formula.
      rw [hfi_eq_zero]
      rw [NonnegativeOrthant.projectedGradient_apply_of_eq_zero J f hf i hfi_eq_zero]
      rw [min_eq_right hgrad_nonpos]
      rw [max_eq_left hterm_nonneg']

/-- Helper for Theorem 9.17: a nonzero projected gradient gives a genuine
descent direction at a feasible orthant point. -/
private lemma projectedGradient_inner_ge_sqNorm
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ NonnegativeOrthant.feasibleSet n) :
    ‖NonnegativeOrthant.projectedGradient J ⟨f, hf⟩‖ ^ 2 ≤
      inner ℝ (gradient J f) (NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) := by
  let pg := NonnegativeOrthant.projectedGradient J ⟨f, hf⟩
  have hcoord :
      ∀ i : Fin n,
        gradient J f i * pg i = pg i * pg i := by
    intro i
    by_cases hfi_pos : 0 < f i
    · -- Positive feasible coordinates keep the full gradient, so the product is a square.
      rw [NonnegativeOrthant.projectedGradient_apply_of_pos J f hf i hfi_pos]
    · have hfi_eq_zero : f i = 0 := by
        exact
          le_antisymm
            (le_of_not_gt hfi_pos)
            ((NonnegativeOrthant.mem_feasibleSet.mp hf) i)
      by_cases hgrad_pos : 0 < gradient J f i
      · -- Positive active-coordinate gradients are clipped to zero.
        rw [NonnegativeOrthant.projectedGradient_apply_of_eq_zero J f hf i hfi_eq_zero]
        rw [min_eq_left hgrad_pos.le]
        simp
      · have hgrad_nonpos : gradient J f i ≤ 0 := le_of_not_gt hgrad_pos
        -- Nonpositive active-coordinate gradients again contribute a square.
        rw [NonnegativeOrthant.projectedGradient_apply_of_eq_zero J f hf i hfi_eq_zero]
        rw [min_eq_right hgrad_nonpos]
  have hinner_eq :
      inner ℝ (gradient J f) pg = inner ℝ pg pg := by
    -- Expand both Euclidean inner products into the coordinate sum and compare summands.
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa [mul_comm] using hcoord i
  -- The real self-inner-product of `pg` is its squared norm.
  rw [hinner_eq]
  exact le_of_eq (real_inner_self_eq_norm_sq _).symm

/-- Helper for Theorem 9.17: the projected profile agrees with the linear
projected-gradient slice on any interval below every coordinate threshold. -/
private lemma projectedProfile_eq_linearProfile_on_Icc_of_coordThreshold
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ NonnegativeOrthant.feasibleSet n)
    {β : ℝ}
    (_hβ_nonneg : 0 ≤ β)
    (hthreshold :
      ∀ i : Fin n, 0 < f i → 0 < gradient J f i → β ≤ f i / gradient J f i) :
    Set.EqOn
      (fun α : ℝ ↦ J (NonnegativeOrthant.projector n (f - α • gradient J f)))
      (fun α : ℝ ↦ J (f - α • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩))
      (Set.Icc (0 : ℝ) β) := by
  intro α hα
  have hα_nonneg : 0 ≤ α := hα.1
  have hα_threshold :
      ∀ i : Fin n, 0 < f i → 0 < gradient J f i → α ≤ f i / gradient J f i := by
    intro i hfi_pos hgrad_pos
    exact le_trans hα.2 (hthreshold i hfi_pos hgrad_pos)
  -- Specialize the pointwise clipping-threshold rewrite to the chosen `α` in the interval.
  simpa using
    congrArg J
      (projectedUpdate_eq_sub_projectedGradient_of_coordThreshold
        n J hf hα_nonneg hα_threshold)

/-- Helper for Theorem 9.17: along a short projected-gradient ray, the shifted
base points still see `-pg` as a strict descent direction. -/
private lemma projectedGradient_inner_neg_on_smallLinearSlice
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : NNReal)
    (hGradLip : LipschitzWith K (gradient J))
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ NonnegativeOrthant.feasibleSet n)
    (hpg :
      NonnegativeOrthant.projectedGradient J ⟨f, hf⟩ ≠ 0)
    {α : ℝ}
    (hα_nonneg : 0 ≤ α)
    (hα_lt : α < 1 / ((K : ℝ) + 1)) :
    inner ℝ
      (gradient J
        (f - α • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩))
      (-NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) < 0 := by
  let pg := NonnegativeOrthant.projectedGradient J ⟨f, hf⟩
  have hK_nonneg : 0 ≤ (K : ℝ) := K.2
  have hK_plus_one_pos : 0 < (K : ℝ) + 1 := by positivity
  have hα_mul_lt_one : ((K : ℝ) + 1) * α < 1 := by
    -- Multiply the small-step bound by the positive denominator to expose the linear factor.
    have hmul := mul_lt_mul_of_pos_right hα_lt hK_plus_one_pos
    have hinv : ((↑K + 1 : ℝ)⁻¹) * (↑K + 1) = 1 := by
      field_simp [hK_plus_one_pos.ne']
    have hmul' : α * ((K : ℝ) + 1) < 1 := by
      simpa [hinv] using hmul
    simpa [mul_comm] using hmul'
  have hKα_lt_one : (K : ℝ) * α < 1 := by
    have hKα_le : (K : ℝ) * α ≤ ((K : ℝ) + 1) * α := by
      nlinarith
    exact lt_of_le_of_lt hKα_le hα_mul_lt_one
  have hstep_norm :
      ‖(f - α • pg) - f‖ = α * ‖pg‖ := by
    -- On the positive ray, the displacement norm is exactly `α * ‖pg‖`.
    calc
      ‖(f - α • pg) - f‖ = ‖-(α • pg)‖ := by
        simp [sub_eq_add_neg, add_left_comm, add_comm]
      _ = ‖α • pg‖ := by rw [norm_neg]
      _ = |α| * ‖pg‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = α * ‖pg‖ := by simp [abs_of_nonneg hα_nonneg]
  have hnormDiff_le :
      ‖gradient J (f - α • pg) - gradient J f‖ ≤ (K : ℝ) * α * ‖pg‖ := by
    -- Lipschitz continuity controls how much the gradient can rotate along the ray.
    calc
      ‖gradient J (f - α • pg) - gradient J f‖ ≤ (K : ℝ) * ‖(f - α • pg) - f‖ :=
        hGradLip.norm_sub_le _ _
      _ = (K : ℝ) * α * ‖pg‖ := by rw [hstep_norm]; ring
  let diff := gradient J (f - α • pg) - gradient J f
  have habs_inner :
      |inner ℝ diff pg| ≤ (K : ℝ) * α * ‖pg‖ ^ 2 := by
    -- Cauchy-Schwarz turns the Lipschitz bound into a linear inner-product error term.
    calc
      |inner ℝ diff pg| ≤ ‖diff‖ * ‖pg‖ := abs_real_inner_le_norm _ _
      _ ≤ ((K : ℝ) * α * ‖pg‖) * ‖pg‖ := by
        exact mul_le_mul_of_nonneg_right hnormDiff_le (norm_nonneg _)
      _ = (K : ℝ) * α * ‖pg‖ ^ 2 := by ring
  have hdiff_lower :
      -((K : ℝ) * α * ‖pg‖ ^ 2) ≤ inner ℝ diff pg :=
    (abs_le.mp habs_inner).1
  have hbase :
      ‖pg‖ ^ 2 ≤ inner ℝ (gradient J f) pg :=
    projectedGradient_inner_ge_sqNorm n J hf
  have hsplit :
      inner ℝ (gradient J f) pg + inner ℝ diff pg =
        inner ℝ (gradient J (f - α • pg)) pg := by
    -- Split the shifted inner product into the base term and the Lipschitz perturbation.
    dsimp [diff]
    rw [inner_sub_left]
    ring
  have hinner_ge :
      (1 - (K : ℝ) * α) * ‖pg‖ ^ 2 ≤
        inner ℝ (gradient J (f - α • pg)) pg := by
    calc
      (1 - (K : ℝ) * α) * ‖pg‖ ^ 2
          = ‖pg‖ ^ 2 - (K : ℝ) * α * ‖pg‖ ^ 2 := by ring
      _ ≤ inner ℝ (gradient J f) pg + inner ℝ diff pg := by
        nlinarith
      _ = inner ℝ (gradient J (f - α • pg)) pg := hsplit
  have hpg_norm_pos : 0 < ‖pg‖ := norm_pos_iff.mpr hpg
  have hnorm_sq_pos : 0 < ‖pg‖ ^ 2 := by nlinarith
  have hfactor_pos : 0 < 1 - (K : ℝ) * α := by linarith
  have hinner_pos :
      0 < inner ℝ (gradient J (f - α • pg)) pg :=
    lt_of_lt_of_le (by nlinarith) hinner_ge
  have hneg : -inner ℝ (gradient J (f - α • pg)) pg < 0 := by linarith
  simpa [pg, inner_neg_right] using hneg

/-- Helper for Theorem 9.17: any pre-hit point on the short projected-gradient
ray admits a slightly later point with smaller objective value. -/
private lemma linearProjectedGradient_existsLowerLaterPoint
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : NNReal)
    (hJ : ContDiff ℝ 1 J)
    (hGradLip : LipschitzWith K (gradient J))
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ NonnegativeOrthant.feasibleSet n)
    (hpg :
      NonnegativeOrthant.projectedGradient J ⟨f, hf⟩ ≠ 0) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀ {α β : ℝ}, 0 ≤ α → α < β → β ≤ δ →
          ∃ ε : ℝ,
            0 < ε ∧
              α + ε < β ∧
                J (f - (α + ε) • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) <
                  J (f - α • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) := by
  let pg := NonnegativeOrthant.projectedGradient J ⟨f, hf⟩
  let δ : ℝ := 1 / ((K : ℝ) + 1)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ_pos, ?_⟩
  intro α β hα_nonneg hα_ltβ hβ_leδ
  let xα := f - α • pg
  have hinner_neg : inner ℝ (gradient J xα) (-pg) < 0 := by
    -- Recenter the short-ray negativity estimate at the chosen base point `xα`.
    have hα_ltδ : α < δ := lt_of_lt_of_le hα_ltβ hβ_leδ
    simpa [xα, pg, δ] using
      projectedGradient_inner_neg_on_smallLinearSlice n J K hGradLip hf hpg
        hα_nonneg
        hα_ltδ
  have hdescent : LineSearch.IsDescentDirection J xα (-pg) :=
    LineSearch.isDescentDirection_of_inner_gradient_neg
      (hJ.differentiable_one xα)
      hinner_neg
  rw [LineSearch.isDescentDirection_iff] at hdescent
  rcases hdescent with ⟨η, hη_pos, hη⟩
  let ε := min (η / 2) ((β - α) / 2)
  have hε_pos : 0 < ε := by
    -- Halving both the descent window and the remaining no-hit interval keeps the step positive.
    dsimp [ε]
    refine lt_min ?_ ?_
    · linarith
    · linarith
  have hε_ltη : ε < η := by
    -- The chosen increment stays inside the local descent window at `xα`.
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hα_addε_ltβ : α + ε < β := by
    -- The same choice also keeps the improved point below the prescribed upper bound `β`.
    have hε_lt_gap : ε < β - α := by
      dsimp [ε]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    linarith
  have hlt : J (xα + ε • (-pg)) < J xα := by
    -- Apply the descent-direction witness at the shorter increment `ε`.
    simpa using hη hε_pos hε_ltη
  refine ⟨ε, hε_pos, hα_addε_ltβ, ?_⟩
  -- Rewrite the improved point back onto the original projected-gradient ray.
  simpa [xα, pg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul] using hlt

/-- Helper for Theorem 9.17: on the explicit short radius `1 / ((K : ℝ) + 1)`,
the linear projected-gradient ray always admits a slightly later point with
strictly smaller objective value. -/
private lemma linearProjectedGradient_existsLowerLaterPoint_smallRadius
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : NNReal)
    (hJ : ContDiff ℝ 1 J)
    (hGradLip : LipschitzWith K (gradient J))
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ NonnegativeOrthant.feasibleSet n)
    (hpg :
      NonnegativeOrthant.projectedGradient J ⟨f, hf⟩ ≠ 0)
    {α β : ℝ}
    (hα_nonneg : 0 ≤ α)
    (hα_ltβ : α < β)
    (hβ_le :
      β ≤ 1 / ((K : ℝ) + 1)) :
    ∃ ε : ℝ,
      0 < ε ∧
        α + ε < β ∧
          J (f - (α + ε) • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) <
            J (f - α • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) := by
  let pg := NonnegativeOrthant.projectedGradient J ⟨f, hf⟩
  let xα := f - α • pg
  have hinner_neg :
      inner ℝ (gradient J xα) (-pg) < 0 := by
    -- The explicit small-radius negativity estimate applies at every point before `β`.
    simpa [xα, pg] using
      projectedGradient_inner_neg_on_smallLinearSlice n J K hGradLip hf hpg
        hα_nonneg
        (lt_of_lt_of_le hα_ltβ hβ_le)
  have hdescent : LineSearch.IsDescentDirection J xα (-pg) :=
    LineSearch.isDescentDirection_of_inner_gradient_neg
      (hJ.differentiable_one xα)
      hinner_neg
  rw [LineSearch.isDescentDirection_iff] at hdescent
  rcases hdescent with ⟨η, hη_pos, hη⟩
  let ε := min (η / 2) ((β - α) / 2)
  have hε_pos : 0 < ε := by
    -- Halving both the descent window and the remaining interval keeps the step positive.
    dsimp [ε]
    refine lt_min ?_ ?_
    · linarith
    · linarith
  have hε_ltη : ε < η := by
    -- The chosen increment stays inside the descent window at `xα`.
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hα_addε_ltβ : α + ε < β := by
    -- The same choice also stays below the target point `β`.
    have hε_lt_gap : ε < β - α := by
      dsimp [ε]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    linarith
  have hlt : J (xα + ε • (-pg)) < J xα := by
    -- Apply the descent-direction witness at the shorter increment `ε`.
    simpa using hη hε_pos hε_ltη
  refine ⟨ε, hε_pos, hα_addε_ltβ, ?_⟩
  -- Rewrite the improved point back onto the original projected-gradient ray.
  simpa [xα, pg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul] using hlt

/-- Helper for Theorem 9.17: if the exact line-search step stays below the
first clipping threshold, the local descent witness contradicts minimality. -/
private lemma exactLineSearch_step_ge_firstHitThreshold
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ NonnegativeOrthant.feasibleSet n)
    {τ δ θ : ℝ}
    (hLater :
      ∀ {α β : ℝ}, 0 ≤ α → α < β → β ≤ δ →
        ∃ ε : ℝ,
          0 < ε ∧
            α + ε < β ∧
              J (f - (α + ε) • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) <
                J (f - α • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩))
    (hExact :
      IsMinOn
        (LineSearch.profile
          (J ∘ NonnegativeOrthant.projector n)
          f
          (GradientProjection.direction J f))
        (Set.Ioi (0 : ℝ))
        τ)
    (hτ_pos : 0 < τ)
    (hEq :
      Set.EqOn
        (fun α : ℝ ↦ J (NonnegativeOrthant.projector n (f - α • gradient J f)))
        (fun α : ℝ ↦ J (f - α • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩))
        (Set.Icc (0 : ℝ) θ))
    (_hθ_pos : 0 < θ)
    (hθ_leδ : θ ≤ δ) :
    θ ≤ τ := by
  by_contra hτ_ltθ
  obtain ⟨ε, hε_pos, hβ_ltθ, hbetter⟩ :=
    hLater hτ_pos.le (lt_of_not_ge hτ_ltθ) hθ_leδ
  let β := τ + ε
  have hβ_pos : 0 < β := by
    dsimp [β]
    linarith
  have hτ_mem : τ ∈ Set.Icc (0 : ℝ) θ := ⟨hτ_pos.le, (lt_of_not_ge hτ_ltθ).le⟩
  have hβ_mem : β ∈ Set.Icc (0 : ℝ) θ := ⟨hβ_pos.le, hβ_ltθ.le⟩
  rw [isMinOn_iff] at hExact
  have hcompare : LineSearch.profile
      (J ∘ NonnegativeOrthant.projector n) f (GradientProjection.direction J f) τ ≤
        LineSearch.profile
          (J ∘ NonnegativeOrthant.projector n) f (GradientProjection.direction J f) β :=
    hExact β hβ_pos
  have hτ_rewrite :
      LineSearch.profile
          (J ∘ NonnegativeOrthant.projector n) f (GradientProjection.direction J f) τ =
        J (f - τ • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) := by
    -- Before the first hit, rewrite the exact-line-search profile onto the linear slice at `τ`.
    rw [profile_projectedUpdate_eq]
    exact hEq hτ_mem
  have hβ_rewrite :
      LineSearch.profile
          (J ∘ NonnegativeOrthant.projector n) f (GradientProjection.direction J f) β =
        J (f - β • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) := by
    -- The same interval-level bridge rewrites the contradiction point `β`.
    rw [profile_projectedUpdate_eq]
    exact hEq hβ_mem
  have hcompare_linear :
      J (f - τ • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) ≤
        J (f - β • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) := by
    rw [hτ_rewrite, hβ_rewrite] at hcompare
    simpa [β] using hcompare
  have hbetter' :
      J (f - β • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) <
        J (f - τ • NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) := by
    simpa [β] using hbetter
  linarith

/-- Helper for Theorem 9.17: a strictly complementary active coordinate is sent
to zero by every positive projected step once that coordinate itself is zero. -/
private lemma activeCoordinate_projectedStep_eq_zero
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    {f : EuclideanSpace ℝ (Fin n)}
    (i : Fin n)
    (hi : f i = 0)
    {α : ℝ}
    (hα : 0 < α)
    (hgrad : 0 < gradient J f i) :
    (NonnegativeOrthant.projector n (f - α • gradient J f)) i = 0 := by
  -- Expand the orthant projector coordinatewise and use the strict positivity
  -- of the active gradient to force clipping back to zero.
  rw [NonnegativeOrthant.projector_apply_eq_max]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hi]
  have hterm_nonpos : 0 - α * gradient J f i ≤ 0 := by
    have hmul_nonneg : 0 ≤ α * gradient J f i := mul_nonneg hα.le hgrad.le
    linarith
  exact max_eq_right hterm_nonpos

/-- Helper for Theorem 9.17: a positive coordinate is clipped to zero once the
projected step reaches its first-hit threshold. -/
private lemma positiveCoordinate_projectedStep_eq_zero_of_hitThreshold
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    {f : EuclideanSpace ℝ (Fin n)}
    (i : Fin n)
    (_hfi : 0 < f i)
    {α : ℝ}
    (_hα_nonneg : 0 ≤ α)
    (hgrad : 0 < gradient J f i)
    (hhit : f i / gradient J f i ≤ α) :
    (NonnegativeOrthant.projector n (f - α • gradient J f)) i = 0 := by
  -- Expand the orthant projector coordinatewise and use the hit-threshold inequality.
  rw [NonnegativeOrthant.projector_apply_eq_max]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  have hterm_nonpos : f i - α * gradient J f i ≤ 0 := by
    exact sub_nonpos.mpr ((div_le_iff₀ hgrad).mp hhit)
  exact max_eq_right hterm_nonpos

/-- Helper for Theorem 9.17: a nonzero projected gradient gives a genuine
descent direction at a feasible orthant point. -/
private lemma inner_gradient_neg_of_projectedGradient_ne_zero
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ NonnegativeOrthant.feasibleSet n)
    (hpg :
      NonnegativeOrthant.projectedGradient J ⟨f, hf⟩ ≠ 0) :
    inner ℝ (gradient J f) (-NonnegativeOrthant.projectedGradient J ⟨f, hf⟩) < 0 := by
  let pg := NonnegativeOrthant.projectedGradient J ⟨f, hf⟩
  have hcoord_nonzero : ∃ i : Fin n, pg i ≠ 0 := by
    by_contra hzero
    apply hpg
    ext i
    by_contra hi
    exact hzero ⟨i, hi⟩
  rcases hcoord_nonzero with ⟨i, hi_nonzero⟩
  have hterm_nonneg : ∀ j : Fin n, 0 ≤ gradient J f j * pg j := by
    intro j
    by_cases hfj_pos : 0 < f j
    · -- Positive feasible coordinates contribute a gradient square.
      rw [NonnegativeOrthant.projectedGradient_apply_of_pos J f hf j hfj_pos]
      nlinarith [sq_nonneg (gradient J f j)]
    · have hfj_eq_zero : f j = 0 := by
        exact
          le_antisymm
            (le_of_not_gt hfj_pos)
            ((NonnegativeOrthant.mem_feasibleSet.mp hf) j)
      by_cases hgrad_pos : 0 < gradient J f j
      · -- Positive outward gradients are clipped to zero on active coordinates.
        rw [NonnegativeOrthant.projectedGradient_apply_of_eq_zero J f hf j hfj_eq_zero]
        rw [min_eq_left hgrad_pos.le]
        simp
      · have hgrad_nonpos : gradient J f j ≤ 0 := le_of_not_gt hgrad_pos
        -- Nonpositive active-coordinate gradients again contribute a square.
        rw [NonnegativeOrthant.projectedGradient_apply_of_eq_zero J f hf j hfj_eq_zero]
        rw [min_eq_right hgrad_nonpos]
        nlinarith [sq_nonneg (gradient J f j)]
  have hterm_pos : 0 < gradient J f i * pg i := by
    by_cases hfi_pos : 0 < f i
    · have hgrad_ne : gradient J f i ≠ 0 := by
        rw [NonnegativeOrthant.projectedGradient_apply_of_pos J f hf i hfi_pos] at hi_nonzero
        exact hi_nonzero
      rw [NonnegativeOrthant.projectedGradient_apply_of_pos J f hf i hfi_pos]
      have hsq : 0 < (gradient J f i) ^ 2 := sq_pos_iff.mpr hgrad_ne
      simpa [pow_two] using hsq
    · have hfi_eq_zero : f i = 0 := by
        exact
          le_antisymm
            (le_of_not_gt hfi_pos)
            ((NonnegativeOrthant.mem_feasibleSet.mp hf) i)
      by_cases hgrad_pos : 0 < gradient J f i
      · rw [NonnegativeOrthant.projectedGradient_apply_of_eq_zero J f hf i hfi_eq_zero]
          at hi_nonzero
        rw [min_eq_left hgrad_pos.le] at hi_nonzero
        simp at hi_nonzero
      · have hgrad_nonpos : gradient J f i ≤ 0 := le_of_not_gt hgrad_pos
        have hgrad_ne : gradient J f i ≠ 0 := by
          rw [NonnegativeOrthant.projectedGradient_apply_of_eq_zero J f hf i hfi_eq_zero]
            at hi_nonzero
          rw [min_eq_right hgrad_nonpos] at hi_nonzero
          exact hi_nonzero
        rw [NonnegativeOrthant.projectedGradient_apply_of_eq_zero J f hf i hfi_eq_zero]
        rw [min_eq_right hgrad_nonpos]
        have hsq : 0 < (gradient J f i) ^ 2 := sq_pos_iff.mpr hgrad_ne
        simpa [pow_two] using hsq
  have hsum_pos :
      0 < ∑ j : Fin n, gradient J f j * pg j := by
    exact lt_of_lt_of_le hterm_pos <|
      by simpa [pg] using
        (Finset.single_le_sum (fun j _ ↦ hterm_nonneg j) (Finset.mem_univ i))
  have hinner_pos : 0 < inner ℝ (gradient J f) pg := by
    -- Expand the Euclidean inner product into its coordinate sum.
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa [pg, dotProduct, mul_comm]
      using hsum_pos
  have hneg : -inner ℝ (gradient J f) pg < 0 := by
    linarith
  simpa [pg, inner_neg_right] using hneg

/-- Helper for Theorem 9.17: one can choose a positive step size below both a
given descent window and every active coordinate threshold. -/
private lemma exists_smallStep_lt_coordThreshold
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    {f : EuclideanSpace ℝ (Fin n)}
    {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ α : ℝ,
      0 < α ∧
        α < δ ∧
        ∀ i : Fin n, 0 < f i → 0 < gradient J f i → α ≤ f i / gradient J f i := by
  let s : Finset (Fin n) :=
    Finset.univ.filter fun i : Fin n ↦ 0 < f i ∧ 0 < gradient J f i
  by_cases hs : s.Nonempty
  · let ratios : Finset ℝ := s.image fun i : Fin n ↦ f i / gradient J f i
    have hratios : ratios.Nonempty := by
      rcases hs with ⟨i, hi⟩
      exact ⟨f i / gradient J f i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    let m : ℝ := ratios.min' hratios
    have hm_pos : 0 < m := by
      rcases Finset.mem_image.mp (Finset.min'_mem ratios hratios) with ⟨i, hi, hm_eq⟩
      have hi' := Finset.mem_filter.mp hi
      simpa [m, hm_eq] using div_pos hi'.2.1 hi'.2.2
    refine ⟨min (δ / 2) (m / 2), ?_⟩
    constructor
    · -- Halving both positive bounds keeps the chosen step positive.
      refine lt_min ?_ ?_
      · linarith
      · linarith
    constructor
    · -- The chosen step lies inside the descent window.
      have hhalf : δ / 2 < δ := by linarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf
    · intro i hfi_pos hgrad_pos
      have his : i ∈ s := by
        simp [s, hfi_pos, hgrad_pos]
      have hm_le : m ≤ f i / gradient J f i := by
        exact Finset.min'_le ratios (f i / gradient J f i) (Finset.mem_image.mpr ⟨i, his, rfl⟩)
      have hstep_le_half : min (δ / 2) (m / 2) ≤ m / 2 := min_le_right _ _
      linarith
  · refine ⟨δ / 2, ?_⟩
    constructor
    · linarith
    constructor
    · linarith
    · intro i hfi_pos hgrad_pos
      exfalso
      exact hs ⟨i, by simp [s, hfi_pos, hgrad_pos]⟩

/-- Helper for Theorem 9.17: on an active-limit coordinate, the clipping
threshold eventually becomes arbitrarily small, while the coordinate gradient
stays strictly positive. -/
private lemma activeThreshold_eventually_small
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fStar : EuclideanSpace ℝ (Fin n))
    (K : NNReal)
    (hGradLip : LipschitzWith K (gradient J))
    (hconv :
      Filter.Tendsto
        (GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0)
        Filter.atTop
        (nhds fStar))
    (hsc : NonnegativeOrthant.StrictComplementarity J fStar) :
    ∀ {i : Fin n}, fStar i = 0 →
      ∀ {η : ℝ}, 0 < η →
        ∃ v0 : ℕ,
          ∀ v ≥ v0,
            0 <
              (GradientProjection.iterates
                (NonnegativeOrthant.projector n)
                J τ f0 v) i →
              0 <
                gradient J
                  ((GradientProjection.iterates
                    (NonnegativeOrthant.projector n)
                    J τ f0) v) i ∧
                ((GradientProjection.iterates
                  (NonnegativeOrthant.projector n)
                  J τ f0) v) i /
                    gradient J
                      ((GradientProjection.iterates
                        (NonnegativeOrthant.projector n)
                        J τ f0) v) i < η := by
  intro i hi η hη
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  have hgradStar_pos : 0 < gradient J fStar i :=
    NonnegativeOrthant.pos_of_eq_zero hsc hi
  have happly :
      Continuous (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) := by
    simpa using
      (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i)
  have hcoordTendsto :
      Filter.Tendsto (fun v ↦ (u v) i) Filter.atTop (nhds (fStar i)) := by
    -- Coordinate evaluation transports the iterate convergence to the active coordinate.
    exact happly.continuousAt.tendsto.comp hconv
  have hgradTendsto :
      Filter.Tendsto (fun v ↦ gradient J (u v) i) Filter.atTop (nhds (gradient J fStar i)) := by
    -- Continuity of the gradient and coordinate evaluation control the denominator.
    exact
      happly.continuousAt.tendsto.comp
        (hGradLip.continuous.continuousAt.tendsto.comp hconv)
  have hcoordSmall :
      ∀ᶠ v : ℕ in Filter.atTop, (u v) i < η * (gradient J fStar i / 2) := by
    -- The active coordinate converges to `0`, so eventually it sits below the target product.
    have hcoordTendsto_zero :
        Filter.Tendsto (fun v ↦ (u v) i) Filter.atTop (nhds (0 : ℝ)) := by
      simpa [hi] using hcoordTendsto
    have hbound_pos : 0 < η * (gradient J fStar i / 2) := by
      have hhalf_pos : 0 < gradient J fStar i / 2 := by linarith
      nlinarith
    simpa using
      hcoordTendsto_zero.eventually (Iio_mem_nhds hbound_pos)
  have hgradLower :
      ∀ᶠ v : ℕ in Filter.atTop,
        gradient J fStar i / 2 < gradient J (u v) i := by
    -- The active-coordinate gradient stays above half of its strictly positive limit.
    simpa using
      hgradTendsto.eventually
        (Ioi_mem_nhds (by linarith : gradient J fStar i / 2 < gradient J fStar i))
  obtain ⟨vCoord, hvCoord⟩ := Filter.eventually_atTop.mp hcoordSmall
  obtain ⟨vGrad, hvGrad⟩ := Filter.eventually_atTop.mp hgradLower
  refine ⟨max vCoord vGrad, ?_⟩
  intro v hv hu_pos
  have hcoord_bound : (u v) i < η * (gradient J fStar i / 2) := by
    exact hvCoord v (le_trans (Nat.le_max_left _ _) hv)
  have hgrad_bound : gradient J fStar i / 2 < gradient J (u v) i := by
    exact hvGrad v (le_trans (Nat.le_max_right _ _) hv)
  have hgrad_pos : 0 < gradient J (u v) i := by
    linarith
  refine ⟨hgrad_pos, ?_⟩
  -- Compare the shrinking numerator against the fixed positive denominator lower bound.
  apply (div_lt_iff₀ hgrad_pos).2
  nlinarith

/-- Helper for Theorem 9.17: inactive-limit coordinates have clipping
thresholds uniformly bounded away from zero on a late tail. -/
private lemma inactiveThresholds_eventually_boundedBelow
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fStar : EuclideanSpace ℝ (Fin n))
    (K : NNReal)
    (hGradLip : LipschitzWith K (gradient J))
    (hconv :
      Filter.Tendsto
        (GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0)
        Filter.atTop
        (nhds fStar)) :
    ∃ η : ℝ,
      0 < η ∧
        ∃ v0 : ℕ,
          ∀ v ≥ v0,
            ∀ {j : Fin n}, 0 < fStar j →
              0 <
                gradient J
                  ((GradientProjection.iterates
                    (NonnegativeOrthant.projector n)
                    J τ f0) v) j →
                η ≤
                  ((GradientProjection.iterates
                    (NonnegativeOrthant.projector n)
                    J τ f0) v) j /
                    gradient J
                      ((GradientProjection.iterates
                        (NonnegativeOrthant.projector n)
                        J τ f0) v) j := by
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  let inactive : Finset (Fin n) := Finset.univ.filter fun j : Fin n ↦ 0 < fStar j
  have happly :
      ∀ i : Fin n, Continuous (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) := by
    intro i
    simpa using
      (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i)
  have hcoordLower :
      ∀ {j : Fin n}, 0 < fStar j →
        ∃ v0 : ℕ,
          ∀ v ≥ v0,
            fStar j / 2 < (u v) j := by
    intro j hj
    have hcoordTendsto :
        Filter.Tendsto (fun v ↦ (u v) j) Filter.atTop (nhds (fStar j)) := by
      -- Coordinate evaluation transports convergence to the inactive coordinate.
      exact (happly j).continuousAt.tendsto.comp hconv
    have hEventually :
        ∀ᶠ v : ℕ in Filter.atTop, fStar j / 2 < (u v) j := by
      -- The inactive coordinate stays above half of its strictly positive limit.
      refine hcoordTendsto.eventually ?_
      exact Ioi_mem_nhds (by linarith : fStar j / 2 < fStar j)
    exact Filter.eventually_atTop.mp hEventually
  have hgradUpper :
      ∀ j : Fin n,
        ∃ v0 : ℕ,
          ∀ v ≥ v0,
            gradient J (u v) j < |gradient J fStar j| + 1 := by
    intro j
    have hgradTendsto :
        Filter.Tendsto (fun v ↦ gradient J (u v) j) Filter.atTop (nhds (gradient J fStar j)) := by
      -- Gradient continuity keeps the denominator uniformly bounded above.
      exact
        (happly j).continuousAt.tendsto.comp
          (hGradLip.continuous.continuousAt.tendsto.comp hconv)
    have hEventually :
        ∀ᶠ v : ℕ in Filter.atTop,
          gradient J (u v) j < |gradient J fStar j| + 1 := by
      have hupper : gradient J fStar j < |gradient J fStar j| + 1 := by
        have habs : gradient J fStar j ≤ |gradient J fStar j| := le_abs_self _
        linarith
      simpa using hgradTendsto.eventually (Iio_mem_nhds hupper)
    exact Filter.eventually_atTop.mp hEventually
  by_cases hinactive : inactive.Nonempty
  · classical
    let bounds : Finset ℝ :=
      inactive.image fun j : Fin n ↦ (fStar j / 2) / (|gradient J fStar j| + 1)
    have hbounds_nonempty : bounds.Nonempty := by
      rcases hinactive with ⟨j, hj⟩
      exact ⟨(fStar j / 2) / (|gradient J fStar j| + 1), Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
    let η : ℝ := bounds.min' hbounds_nonempty
    have hη_pos : 0 < η := by
      rcases Finset.mem_image.mp (Finset.min'_mem bounds hbounds_nonempty) with ⟨j, hj, hη_eq⟩
      have hjpos : 0 < fStar j := (Finset.mem_filter.mp hj).2
      have hden_pos : 0 < |gradient J fStar j| + 1 := by positivity
      have hnum_pos : 0 < fStar j / 2 := by linarith
      simpa [η, hη_eq] using div_pos hnum_pos hden_pos
    let cutoff : Fin n → ℕ := fun j ↦
      if hpos : 0 < fStar j then
        max
          (Classical.choose (hcoordLower hpos))
          (Classical.choose (hgradUpper j))
      else
        0
    refine ⟨η, hη_pos, Finset.univ.sup cutoff, ?_⟩
    intro v hv j hjpos hgrad_pos
    have hcutoff :
        cutoff j ≤ v := by
      exact le_trans (Finset.le_sup (Finset.mem_univ j)) hv
    have hcoord_index :
        Classical.choose (hcoordLower hjpos) ≤ v := by
      exact le_trans (le_max_left _ _) (by simpa [cutoff, hjpos] using hcutoff)
    have hgrad_index :
        Classical.choose (hgradUpper j) ≤ v := by
      exact le_trans (le_max_right _ _) (by simpa [cutoff, hjpos] using hcutoff)
    have hcoord_bound : fStar j / 2 < (u v) j :=
      (Classical.choose_spec (hcoordLower hjpos)) v hcoord_index
    have hgrad_bound : gradient J (u v) j < |gradient J fStar j| + 1 :=
      (Classical.choose_spec (hgradUpper j)) v hgrad_index
    have hη_le_bound :
        η ≤ (fStar j / 2) / (|gradient J fStar j| + 1) := by
      exact
        Finset.min'_le bounds
          ((fStar j / 2) / (|gradient J fStar j| + 1))
          (Finset.mem_image.mpr ⟨j, by simp [inactive, hjpos], rfl⟩)
    have hratio_bound :
        (fStar j / 2) / (|gradient J fStar j| + 1) ≤ (u v) j / gradient J (u v) j := by
      have hden_pos : 0 < |gradient J fStar j| + 1 := by positivity
      have hden_upper : gradient J (u v) j ≤ |gradient J fStar j| + 1 := by
        linarith
      exact
        (div_le_div_iff₀ hden_pos hgrad_pos).2 <|
          by nlinarith [le_of_lt hcoord_bound, hden_upper]
    exact le_trans hη_le_bound hratio_bound
  · refine ⟨1, by positivity, 0, ?_⟩
    intro v hv j hjpos hgrad_pos
    exfalso
    exact hinactive ⟨j, by simp [inactive, hjpos]⟩

/-- Helper for Theorem 9.17: once an active-limit coordinate is zero and its
gradient is positive, the next exact-line-search iterate keeps it at zero. -/
private lemma zeroTailCoordinate_staysZero
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (hStepPos : ∀ v : ℕ, 0 < τ v)
    {i : Fin n}
    {v : ℕ}
    (hzero :
      ((GradientProjection.iterates
        (NonnegativeOrthant.projector n)
        J τ f0) v) i = 0)
    (hgrad :
      0 <
        gradient J
          ((GradientProjection.iterates
            (NonnegativeOrthant.projector n)
            J τ f0) v) i) :
    ((GradientProjection.iterates
      (NonnegativeOrthant.projector n)
      J τ f0) (v + 1)) i = 0 := by
  -- Rewrite the successor iterate and clip the zero coordinate again.
  rw [GradientProjection.iterates_succ]
  rw [GradientProjection.update_eq_projector_sub_smul_gradient]
  exact activeCoordinate_projectedStep_eq_zero n J i hzero (hStepPos v) hgrad

/-- Helper for Theorem 9.17: on a late tail, every positive active-limit
coordinate at step `v + 1` was already positive at step `v`. -/
private lemma remainingActive_succ_subset
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fStar : EuclideanSpace ℝ (Fin n))
    (K : NNReal)
    (hGradLip : LipschitzWith K (gradient J))
    (hStepPos : ∀ v : ℕ, 0 < τ v)
    (hconv :
      Filter.Tendsto
        (GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0)
        Filter.atTop
        (nhds fStar))
    (hsc : NonnegativeOrthant.StrictComplementarity J fStar) :
    ∃ v0 : ℕ,
      1 ≤ v0 ∧
        ∀ v ≥ v0,
          let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
          let A := fun w : ℕ ↦
            Finset.univ.filter fun j : Fin n ↦ fStar j = 0 ∧ 0 < u w j
          A (v + 1) ⊆ A v := by
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  have hgradTail :
      ∀ {j : Fin n}, fStar j = 0 →
        ∃ v0 : ℕ,
          ∀ v ≥ v0,
            0 < gradient J (u v) j :=
    eventually_pos_gradient_on_activeCoordinates n J τ f0 fStar K hGradLip hconv hsc
  let cutoff : Fin n → ℕ := fun j ↦
    if hzero : fStar j = 0 then
      Classical.choose (hgradTail hzero)
    else
      0
  refine ⟨max 1 (Finset.univ.sup cutoff), Nat.le_max_left _ _, ?_⟩
  intro v hv
  let A := fun w : ℕ ↦
    Finset.univ.filter fun j : Fin n ↦ fStar j = 0 ∧ 0 < u w j
  change A (v + 1) ⊆ A v
  intro j hj
  have hj_mem : j ∈ A (v + 1) := hj
  have hj_data := Finset.mem_filter.mp hj_mem
  have hj_zero : fStar j = 0 := hj_data.2.1
  have hj_next_pos : 0 < u (v + 1) j := hj_data.2.2
  have hv_one : 1 ≤ v := le_trans (Nat.le_max_left _ _) hv
  have hv_feasible : u v ∈ NonnegativeOrthant.feasibleSet n :=
    iterate_memFeasibleSet_of_one_le n J τ f0 hv_one
  have hj_prev_pos : 0 < u v j := by
    by_contra hj_prev_not_pos
    have hj_prev_zero : u v j = 0 := by
      exact
        le_antisymm
          (le_of_not_gt hj_prev_not_pos)
          ((NonnegativeOrthant.mem_feasibleSet.mp hv_feasible) j)
    have hcutoff :
        cutoff j ≤ v := by
      exact
        le_trans
          (Finset.le_sup (Finset.mem_univ j))
          (le_trans (Nat.le_max_right _ _) hv)
    have hgrad_index :
        Classical.choose (hgradTail hj_zero) ≤ v := by
      simpa [cutoff, hj_zero] using hcutoff
    have hj_grad_pos : 0 < gradient J (u v) j :=
      (Classical.choose_spec (hgradTail hj_zero)) v hgrad_index
    have hj_next_zero : u (v + 1) j = 0 :=
      zeroTailCoordinate_staysZero n J τ f0 hStepPos hj_prev_zero hj_grad_pos
    exact hj_next_pos.ne' hj_next_zero
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨hj_zero, hj_prev_pos⟩⟩

/-- Helper for Theorem 9.17: on a late tail, any nonempty residual-active set
strictly loses at least one coordinate at the next iterate. -/
private lemma remainingActiveCard_succ_lt
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fStar : EuclideanSpace ℝ (Fin n))
    (K : NNReal)
    (hJ : ContDiff ℝ 1 J)
    (hGradLip : LipschitzWith K (gradient J))
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0)
    (hStepPos : ∀ v : ℕ, 0 < τ v)
    (hconv :
      Filter.Tendsto
        (GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0)
        Filter.atTop
        (nhds fStar))
    (hsc : NonnegativeOrthant.StrictComplementarity J fStar) :
    ∃ v0 : ℕ,
      1 ≤ v0 ∧
        ∀ v ≥ v0,
          let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
          let A := fun w : ℕ ↦
            Finset.univ.filter fun j : Fin n ↦ fStar j = 0 ∧ 0 < u w j
          (A v).Nonempty →
            (A (v + 1)).card < (A v).card := by
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  obtain ⟨vSubset, hvSubset_one, hvSubset⟩ :=
    remainingActive_succ_subset n J τ f0 fStar K hGradLip hStepPos hconv hsc
  obtain ⟨ηInactive, hηInactive_pos, vInactive, hvInactive⟩ :=
    inactiveThresholds_eventually_boundedBelow n J τ f0 fStar K hGradLip hconv
  let η : ℝ := min ηInactive (1 / ((K : ℝ) + 1))
  have hη_pos : 0 < η := by
    have hradius_pos : 0 < (1 / ((K : ℝ) + 1) : ℝ) := by positivity
    exact lt_min hηInactive_pos hradius_pos
  have hactiveSmall :
      ∀ {j : Fin n}, fStar j = 0 →
        ∃ v0 : ℕ,
          ∀ v ≥ v0,
            0 < u v j →
              0 < gradient J (u v) j ∧ u v j / gradient J (u v) j < η :=
    fun {j} hj ↦ activeThreshold_eventually_small n J τ f0 fStar K hGradLip hconv hsc hj hη_pos
  let cutoffActive : Fin n → ℕ := fun j ↦
    if hzero : fStar j = 0 then
      Classical.choose (hactiveSmall hzero)
    else
      0
  let v0 : ℕ := max vSubset (max vInactive (Finset.univ.sup cutoffActive))
  refine ⟨v0, le_trans hvSubset_one (Nat.le_max_left _ _), ?_⟩
  intro v hv
  let A := fun w : ℕ ↦
    Finset.univ.filter fun j : Fin n ↦ fStar j = 0 ∧ 0 < u w j
  change (A v).Nonempty → (A (v + 1)).card < (A v).card
  intro hA_nonempty
  classical
  rcases hA_nonempty with ⟨iA, hiA_mem⟩
  have hiA_data := Finset.mem_filter.mp hiA_mem
  have hiA_zero : fStar iA = 0 := hiA_data.2.1
  have hiA_pos : 0 < u v iA := hiA_data.2.2
  have hvActive :
      Finset.univ.sup cutoffActive ≤ v := by
    exact le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) hv)
  have hiA_cutoff :
      Classical.choose (hactiveSmall hiA_zero) ≤ v := by
    have hcutoff_iA : cutoffActive iA ≤ v :=
      le_trans (Finset.le_sup (Finset.mem_univ iA)) hvActive
    simpa [cutoffActive, hiA_zero] using hcutoff_iA
  have hiA_active :
      0 < gradient J (u v) iA ∧ u v iA / gradient J (u v) iA < η :=
    (Classical.choose_spec (hactiveSmall hiA_zero)) v hiA_cutoff hiA_pos
  let C : Finset (Fin n) :=
    Finset.univ.filter fun j : Fin n ↦ 0 < u v j ∧ 0 < gradient J (u v) j
  have hC_nonempty : C.Nonempty := by
    exact ⟨iA, by simp [C, hiA_pos, hiA_active.1]⟩
  let ratios : Finset ℝ := C.image fun j : Fin n ↦ u v j / gradient J (u v) j
  have hratios_nonempty : ratios.Nonempty := by
    rcases hC_nonempty with ⟨j, hj⟩
    exact ⟨u v j / gradient J (u v) j, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  let θ : ℝ := ratios.min' hratios_nonempty
  rcases Finset.mem_image.mp (Finset.min'_mem ratios hratios_nonempty) with ⟨j0, hj0C, hθ_eq⟩
  have hj0_pos : 0 < u v j0 := (Finset.mem_filter.mp hj0C).2.1
  have hj0_grad_pos : 0 < gradient J (u v) j0 := (Finset.mem_filter.mp hj0C).2.2
  have hθ_pos : 0 < θ := by
    simpa [θ, hθ_eq] using div_pos hj0_pos hj0_grad_pos
  have hθ_le :
      ∀ j : Fin n, 0 < u v j → 0 < gradient J (u v) j →
        θ ≤ u v j / gradient J (u v) j := by
    intro j hj_pos hj_grad_pos
    exact
      Finset.min'_le ratios
        (u v j / gradient J (u v) j)
        (Finset.mem_image.mpr ⟨j, by simp [C, hj_pos, hj_grad_pos], rfl⟩)
  have htailFeasible :
      ∀ w : ℕ, u (w + 1) ∈ NonnegativeOrthant.feasibleSet n := by
    intro w
    simpa [u] using iteratesSucc_memFeasibleSet n J τ f0 w
  have htailTendsto :
      Filter.Tendsto (fun w ↦ u (w + 1)) Filter.atTop (nhds fStar) := by
    -- Shifting the convergent iterate sequence preserves the same limit.
    exact hconv.comp (Filter.tendsto_add_atTop_nat 1)
  have hfStar : fStar ∈ NonnegativeOrthant.feasibleSet n :=
    limit_memFeasibleSet_of_tendsto n htailFeasible htailTendsto
  have hj0_zero : fStar j0 = 0 := by
    by_contra hj0_ne_zero
    have hj0_fstar_nonneg : 0 ≤ fStar j0 :=
      (NonnegativeOrthant.mem_feasibleSet.mp hfStar) j0
    have hj0_fstar_pos : 0 < fStar j0 := lt_of_le_of_ne hj0_fstar_nonneg <| by
      simpa [eq_comm] using hj0_ne_zero
    have hvInactiveTail :
        vInactive ≤ v := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) hv)
    have hj0_inactive :
        ηInactive ≤ u v j0 / gradient J (u v) j0 :=
      hvInactive v hvInactiveTail hj0_fstar_pos hj0_grad_pos
    have hθ_lt_eta : θ < η := lt_of_le_of_lt (hθ_le iA hiA_pos hiA_active.1) hiA_active.2
    have hη_le_theta : η ≤ θ := by
      calc
        η ≤ ηInactive := min_le_left _ _
        _ ≤ u v j0 / gradient J (u v) j0 := hj0_inactive
        _ = θ := hθ_eq
    linarith
  have hv_one : 1 ≤ v := le_trans (le_trans hvSubset_one (Nat.le_max_left _ _)) hv
  have hv_feasible : u v ∈ NonnegativeOrthant.feasibleSet n :=
    iterate_memFeasibleSet_of_one_le n J τ f0 hv_one
  have hpg_nonzero :
      NonnegativeOrthant.projectedGradient J ⟨u v, hv_feasible⟩ ≠ 0 := by
    intro hpg_zero
    have hcoord_zero :
        NonnegativeOrthant.projectedGradient J ⟨u v, hv_feasible⟩ j0 = 0 := by
      simp [hpg_zero]
    rw
      [NonnegativeOrthant.projectedGradient_apply_of_pos
        J
        (u v)
        hv_feasible
        j0
        hj0_pos] at hcoord_zero
    exact hj0_grad_pos.ne' hcoord_zero
  have hθ_radius : θ ≤ 1 / ((K : ℝ) + 1) := by
    have hθ_lt_eta : θ < η := lt_of_le_of_lt (hθ_le iA hiA_pos hiA_active.1) hiA_active.2
    exact hθ_lt_eta.le.trans (min_le_right _ _)
  have hLater :
      ∀ {α β : ℝ}, 0 ≤ α → α < β → β ≤ θ →
        ∃ ε : ℝ,
          0 < ε ∧
            α + ε < β ∧
              J (u v - (α + ε) • NonnegativeOrthant.projectedGradient J ⟨u v, hv_feasible⟩) <
                J (u v - α • NonnegativeOrthant.projectedGradient J ⟨u v, hv_feasible⟩) := by
    intro α β hα_nonneg hα_ltβ hβ_leθ
    exact
      linearProjectedGradient_existsLowerLaterPoint_smallRadius
        n J K hJ hGradLip hv_feasible hpg_nonzero hα_nonneg hα_ltβ
        (le_trans hβ_leθ hθ_radius)
  have hEq :
      Set.EqOn
        (fun α : ℝ ↦ J (NonnegativeOrthant.projector n (u v - α • gradient J (u v))))
        (fun α : ℝ ↦ J (u v - α • NonnegativeOrthant.projectedGradient J ⟨u v, hv_feasible⟩))
        (Set.Icc (0 : ℝ) θ) := by
    -- Below the first-hit threshold, the projected profile agrees with the linear slice.
    exact
      projectedProfile_eq_linearProfile_on_Icc_of_coordThreshold
        n J hv_feasible hθ_pos.le hθ_le
  have hθ_le_step : θ ≤ τ v := by
    -- Exact line search cannot stop before the first clipping threshold.
    have hExact :
        IsMinOn
          (LineSearch.profile
            (J ∘ NonnegativeOrthant.projector n)
            (u v)
            (GradientProjection.direction J (u v)))
          (Set.Ioi (0 : ℝ))
          (τ v) := by
      rw [GradientProjection.isExactLineSearch_iff] at hLineSearch
      exact hLineSearch v
    exact
      exactLineSearch_step_ge_firstHitThreshold
        n J hv_feasible hLater
        hExact
        (hStepPos v) hEq hθ_pos le_rfl
  have hj0_next_zero : u (v + 1) j0 = 0 := by
    -- Hitting the minimal threshold clips the chosen active coordinate to zero.
    have hhit :
        u v j0 / gradient J (u v) j0 ≤ τ v := by
      simpa [hθ_eq] using hθ_le_step
    simpa
        [u, GradientProjection.iterates_succ,
          GradientProjection.update_eq_projector_sub_smul_gradient] using
      positiveCoordinate_projectedStep_eq_zero_of_hitThreshold
        (n := n) (J := J) (f := u v) j0 hj0_pos (hStepPos v).le hj0_grad_pos hhit
  have hsubset :
      A (v + 1) ⊆ A v := hvSubset v (le_trans (Nat.le_max_left _ _) hv)
  have hj0_in_Av : j0 ∈ A v := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ j0, ⟨hj0_zero, hj0_pos⟩⟩
  have hj0_not_in_A_next : j0 ∉ A (v + 1) := by
    intro hj0_mem
    have hj0_data := Finset.mem_filter.mp hj0_mem
    exact hj0_data.2.2.ne' hj0_next_zero
  exact
    Finset.card_lt_card <|
      (Finset.ssubset_iff_of_subset hsubset).2 ⟨j0, hj0_in_Av, hj0_not_in_A_next⟩

/-- Helper for Theorem 9.17: once a strictly complementary active coordinate
enters the tail where the exact line search forces clipping, that coordinate
stays zero forever. -/
private lemma eventually_zero_on_activeCoordinates
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fStar : EuclideanSpace ℝ (Fin n))
    (K : NNReal)
    (hJ : ContDiff ℝ 1 J)
    (hGradLip : LipschitzWith K (gradient J))
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0)
    (hStepPos : ∀ v : ℕ, 0 < τ v)
    (hconv :
      Filter.Tendsto
        (GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0)
        Filter.atTop
        (nhds fStar))
    (hsc : NonnegativeOrthant.StrictComplementarity J fStar) :
    ∀ {i : Fin n}, fStar i = 0 →
      ∃ v0 : ℕ,
        ∀ v ≥ v0,
          ((GradientProjection.iterates
            (NonnegativeOrthant.projector n)
            J τ f0) v) i = 0 := by
  intro i hi
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  let A := fun w : ℕ ↦
    Finset.univ.filter fun j : Fin n ↦ fStar j = 0 ∧ 0 < u w j
  obtain ⟨vSubset, hvSubset_one, hvSubset⟩ :=
    remainingActive_succ_subset n J τ f0 fStar K hGradLip hStepPos hconv hsc
  obtain ⟨vDrop, hvDrop_one, hvDrop⟩ :=
    remainingActiveCard_succ_lt n J τ f0 fStar K hJ hGradLip hLineSearch hStepPos hconv hsc
  let vBase : ℕ := max vSubset vDrop
  have hvBase_one : 1 ≤ vBase := le_trans hvSubset_one (Nat.le_max_left _ _)
  have hsubsetBase :
      ∀ v ≥ vBase, A (v + 1) ⊆ A v := by
    intro v hv
    exact hvSubset v (le_trans (Nat.le_max_left _ _) hv)
  have hdropBase :
      ∀ v ≥ vBase, (A v).Nonempty → (A (v + 1)).card < (A v).card := by
    intro v hv
    exact hvDrop v (le_trans (Nat.le_max_right _ _) hv)
  let m : ℕ := (A vBase).card
  have hcard_bound :
      ∀ k : ℕ, (A (vBase + k)).card ≤ m - k := by
    intro k
    induction k with
    | zero =>
        simp [m]
    | succ k ih =>
        by_cases hnonempty : (A (vBase + k)).Nonempty
        · have hk_ge : vBase ≤ vBase + k := Nat.le_add_right _ _
          have hlt :
              (A (vBase + k + 1)).card < (A (vBase + k)).card := by
            simpa [Nat.add_assoc] using hdropBase (vBase + k) hk_ge hnonempty
          have hlt_bound : (A (vBase + k + 1)).card < m - k :=
            lt_of_lt_of_le hlt ih
          have hsuc : (A (vBase + (k + 1))).card + 1 ≤ m - k := by
            simpa [Nat.add_assoc] using
              (Nat.succ_le_of_lt hlt_bound)
          have hsuc' : (A (vBase + (k + 1))).card + 1 ≤ m - k := hsuc
          omega
        · have hk_ge : vBase ≤ vBase + k := Nat.le_add_right _ _
          have hsubset :
              A (vBase + k + 1) ⊆ A (vBase + k) := by
            simpa [Nat.add_assoc] using hsubsetBase (vBase + k) hk_ge
          have hk_empty : A (vBase + k) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
          have hnext_empty : A (vBase + k + 1) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.2
            intro j hj
            have hj_prev : j ∈ A (vBase + k) := hsubset hj
            simp [hk_empty] at hj_prev
          have hnext_card : (A (vBase + k + 1)).card = 0 := by
            simp [hnext_empty]
          have hnext_card' : (A (vBase + (k + 1))).card = 0 := by
            simpa [Nat.add_assoc] using hnext_card
          rw [hnext_card']
          exact Nat.zero_le _
  have hbase_empty : A (vBase + m) = ∅ := by
    have hcard_zero : (A (vBase + m)).card = 0 := by
      have hbound := hcard_bound m
      simpa [m] using hbound
    exact Finset.card_eq_zero.mp hcard_zero
  have htail_empty :
      ∀ v ≥ vBase + m, A v = ∅ := by
    intro v hv
    rcases Nat.exists_eq_add_of_le hv with ⟨d, rfl⟩
    induction d with
    | zero =>
        simpa using hbase_empty
    | succ d ih =>
        have hd_ge : vBase ≤ vBase + m + d := by
          omega
        have hsubset :
            A (vBase + m + d + 1) ⊆ A (vBase + m + d) := by
          simpa [Nat.add_assoc] using hsubsetBase (vBase + m + d) hd_ge
        apply Finset.eq_empty_iff_forall_notMem.2
        intro j hj
        have hj_prev : j ∈ A (vBase + m + d) := hsubset hj
        simp [ih] at hj_prev
  refine ⟨vBase + m, ?_⟩
  intro v hv
  have hv_feasible : u v ∈ NonnegativeOrthant.feasibleSet n :=
    iterate_memFeasibleSet_of_one_le n J τ f0
      (le_trans hvBase_one (le_trans (Nat.le_add_right _ _) hv))
  have hv_empty : A v = ∅ := htail_empty v hv
  by_contra hu_nonzero
  have hu_pos : 0 < u v i := by
    have hu_nonneg : 0 ≤ u v i := (NonnegativeOrthant.mem_feasibleSet.mp hv_feasible) i
    have hu_ne : 0 ≠ u v i := by
      simpa [eq_comm] using hu_nonzero
    exact lt_of_le_of_ne hu_nonneg hu_ne
  have hi_mem : i ∈ A v := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨hi, hu_pos⟩⟩
  simp [hv_empty] at hi_mem

/-- Companion for Theorem 9.17: if `gradient J` is Lipschitz continuous and
`fBar` is a
cluster point of the gradient-projection iterates for `(9.16)`, then `fBar` is
a critical point for `(9.16)`. In Lean we also assume `ContDiff ℝ 1 J` so
`gradient J` is the genuine derivative field used by the Chapter 9 criticality
bridges. -/
private lemma clusterPt_isCriticalPoint
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fBar : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ : ContDiff ℝ 1 J)
    (hGradLip : LipschitzWith K (gradient J))
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0)
    (hCluster :
      MapClusterPt
        fBar
        Filter.atTop
        (GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0)) :
    NonnegativeOrthant.IsCriticalPoint J fBar := by
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  have hJ_diff :
      ∀ x ∈ NonnegativeOrthant.feasibleSet n,
        DifferentiableAt ℝ J x := by
    intro x hx
    let _ := hx
    exact hJ.differentiable_one x
  have htail_feasible :
      ∀ᶠ v : ℕ in Filter.atTop, u v ∈ NonnegativeOrthant.feasibleSet n := by
    refine Filter.mem_atTop_sets.2 ⟨1, ?_⟩
    intro v hv
    cases v with
    | zero =>
        cases hv
    | succ w =>
        simpa [u] using iteratesSucc_memFeasibleSet n J τ f0 w
  have hfBar : fBar ∈ NonnegativeOrthant.feasibleSet n := by
    -- Feasibility is closed, and every tail iterate is feasible.
    exact
      (NonnegativeOrthant.closedConvex_feasibleSet n).isClosed.mem_of_mapClusterPt
        hCluster
        htail_feasible
  obtain ⟨ψ, hψ_mono, hψ⟩ := MapClusterPt.tendsto_subseq hCluster
  have hψ_atTop : Filter.Tendsto ψ Filter.atTop Filter.atTop := hψ_mono.tendsto_atTop
  have hJ_bar :
      Filter.Tendsto (fun k ↦ J (u (ψ k))) Filter.atTop (nhds (J fBar)) := by
    -- The cluster subsequence transports convergence through continuity of `J` at `fBar`.
    have hJContAt : ContinuousAt J fBar := (hJ_diff _ hfBar).continuousAt
    exact hJContAt.tendsto.comp hψ
  have hClusterSucc :
      MapClusterPt fBar Filter.atTop (fun v : ℕ ↦ u (v + 1)) := by
    -- Shifting the sequence by one step preserves the same cluster points at `atTop`.
    change MapClusterPt fBar Filter.atTop (u ∘ fun v : ℕ ↦ v + 1)
    rw [mapClusterPt_comp]
    simpa [u, Filter.map_add_atTop_eq_nat 1] using hCluster
  obtain ⟨ψSucc, hψSucc_mono, hψSucc⟩ := MapClusterPt.tendsto_subseq hClusterSucc
  have hψSucc_atTop : Filter.Tendsto ψSucc Filter.atTop Filter.atTop :=
    hψSucc_mono.tendsto_atTop
  have htail_antitone : Antitone fun v : ℕ ↦ J (u (v + 1)) := by
    -- Exact line search makes the feasible-tail objective sequence monotone decreasing.
    refine antitone_nat_of_succ_le fun v ↦ ?_
    simpa [u, Nat.add_assoc] using
      iterates_value_step_le n J τ f0 K hJ_diff hLineSearch v
  have htail_values_tendsto :
      Filter.Tendsto (fun v : ℕ ↦ J (u (v + 1))) Filter.atTop (nhds (J fBar)) := by
    have hsubseq :
        Filter.Tendsto
          ((fun v : ℕ ↦ J (u (v + 1))) ∘ ψSucc)
          Filter.atTop
          (nhds (J fBar)) := by
      -- Along a convergent subsequence of successors, the tail values converge to `J fBar`.
      have hJContAt : ContinuousAt J fBar := (hJ_diff _ hfBar).continuousAt
      simpa [Function.comp_def, u] using
        hJContAt.tendsto.comp hψSucc
    exact
      (tendsto_iff_tendsto_subseq_of_antitone htail_antitone hψSucc_atTop).2
        hsubseq
  have hsucc_values :
      Filter.Tendsto (fun k ↦ J (u (ψ k + 1))) Filter.atTop (nhds (J fBar)) := by
    -- The whole tail objective sequence converges, so every subsequence of successors does too.
    simpa [Function.comp_def, u] using htail_values_tendsto.comp hψ_atTop
  have hlimit_compare :
      ∀ {α : ℝ}, 0 < α →
        J fBar ≤ J (NonnegativeOrthant.projector n (fBar - α • gradient J fBar)) := by
    intro α hα
    let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun x ↦ NonnegativeOrthant.projector n (x - α • gradient J x)
    have hstep_cont :
        Continuous g := by
      -- The projector and the Lipschitz gradient are both continuous.
      have hbase : Continuous fun x : EuclideanSpace ℝ (Fin n) ↦ x - α • gradient J x := by
        change Continuous (id - α • gradient J)
        exact continuous_id.sub (hGradLip.continuous.const_smul α)
      change
        Continuous
          (NonnegativeOrthant.projector n ∘
            fun x : EuclideanSpace ℝ (Fin n) ↦ x - α • gradient J x)
      exact (continuous_projector n).comp hbase
    have hright :
        Filter.Tendsto
          (fun k ↦ J (NonnegativeOrthant.projector n (u (ψ k) - α • gradient J (u (ψ k)))))
          Filter.atTop
          (nhds (J (NonnegativeOrthant.projector n (fBar - α • gradient J fBar)))) := by
      have hstep_mem :
          g fBar ∈ NonnegativeOrthant.feasibleSet n :=
        NonnegativeOrthant.projector_mem_feasibleSet n _
      have hgContAt : ContinuousAt g fBar := hstep_cont.continuousAt
      have hg :
          Filter.Tendsto g (nhds fBar) (nhds (g fBar)) :=
        hgContAt.tendsto
      have hJContAt : ContinuousAt J (g fBar) := (hJ_diff _ hstep_mem).continuousAt
      -- First transport the iterate subsequence through the projected-step map,
      -- then through continuity of `J` at the feasible projected limit.
      simpa [g, Function.comp_def, u] using
        (hJContAt.tendsto.comp (hg.comp hψ))
    have hcompare :
        ∀ᶠ k : ℕ in Filter.atTop,
          J (u (ψ k + 1)) ≤
            J (NonnegativeOrthant.projector n (u (ψ k) - α • gradient J (u (ψ k)))) := by
      -- Exact line search dominates every positive projected step along the cluster subsequence.
      refine Filter.Eventually.of_forall ?_
      intro k
      simpa [u] using
        exactLineSearch_le_projectedUpdate n J τ f0 hLineSearch (ψ k) hα
    exact le_of_tendsto_of_tendsto hsucc_values hright hcompare
  -- Route correction: keep the contradiction on the projected-gradient surface,
  -- then convert the vanishing projected gradient to criticality only at the end.
  refine
    (NonnegativeOrthant.isCriticalPoint_iff_projectedGradient_eq_zero J ⟨fBar, hfBar⟩).2 ?_
  by_contra hpg
  have hinner_neg :
      inner ℝ (gradient J fBar)
        (-NonnegativeOrthant.projectedGradient J ⟨fBar, hfBar⟩) < 0 :=
    inner_gradient_neg_of_projectedGradient_ne_zero n J hfBar hpg
  have hdescent :
      LineSearch.IsDescentDirection
        J
        fBar
        (-NonnegativeOrthant.projectedGradient J ⟨fBar, hfBar⟩) :=
    LineSearch.isDescentDirection_of_inner_gradient_neg (hJ_diff _ hfBar) hinner_neg
  rw [LineSearch.isDescentDirection_iff] at hdescent
  rcases hdescent with ⟨δ, hδ_pos, hδ⟩
  obtain ⟨α, hα_pos, hα_ltδ, hthreshold⟩ :=
    @exists_smallStep_lt_coordThreshold n J fBar δ hδ_pos
  have hrewrite :
      NonnegativeOrthant.projector n (fBar - α • gradient J fBar) =
        fBar - α • NonnegativeOrthant.projectedGradient J ⟨fBar, hfBar⟩ := by
    -- For a sufficiently small step, the orthant projector agrees with the
    -- projected gradient formula.
    exact
      projectedUpdate_eq_sub_projectedGradient_of_coordThreshold
        n J hfBar hα_pos.le hthreshold
  have hstrict :
      J (NonnegativeOrthant.projector n (fBar - α • gradient J fBar)) < J fBar := by
    have hdescent_lt :
        J (fBar - α • NonnegativeOrthant.projectedGradient J ⟨fBar, hfBar⟩) < J fBar := by
      simpa [sub_eq_add_neg] using hδ hα_pos hα_ltδ
    simpa [hrewrite] using hdescent_lt
  have hlimit_le : J fBar ≤ J (NonnegativeOrthant.projector n (fBar - α • gradient J fBar)) :=
    hlimit_compare hα_pos
  linarith

/-- Companion for Theorem 9.17: if `gradient J` is Lipschitz continuous and the
gradient-projection iterates for `(9.16)` converge to a local minimizer `fStar`
satisfying strict complementarity `(9.20)`, then the optimal active set is
identified after finitely many iterations. In Lean we also assume
`ContDiff ℝ 1 J` so the Chapter 9 local-minimizer and projector fixed-point
lemmas apply to the actual gradient of `J`, and we record the algorithmic side
condition `0 < τ v` for each exact-line-search step because
`GradientProjection.IsExactLineSearch` does not itself retain that membership
fact from `Set.Ioi (0 : ℝ)`. -/
private lemma eventually_eq_activeSet_of_limit
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fStar : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ : ContDiff ℝ 1 J)
    (hGradLip : LipschitzWith K (gradient J))
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0)
    (hStepPos : ∀ v : ℕ, 0 < τ v)
    (hconv :
      Filter.Tendsto
        (GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0)
        Filter.atTop
        (nhds fStar))
    (hmin : IsLocalMinOn J (NonnegativeOrthant.feasibleSet n) fStar)
    (hsc : NonnegativeOrthant.StrictComplementarity J fStar) :
    ∃ v0 : ℕ,
      ∀ v ≥ v0,
        ActiveSet.active
            (fun i x ↦ x i)
            ((GradientProjection.iterates
              (NonnegativeOrthant.projector n)
              J τ f0) v) =
          ActiveSet.active (fun i x ↦ x i) fStar := by
  let _ := hmin
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  have htailFeasible :
      ∀ v : ℕ, u (v + 1) ∈ NonnegativeOrthant.feasibleSet n := by
    intro v
    simpa [u] using iteratesSucc_memFeasibleSet n J τ f0 v
  have htailTendsto :
      Filter.Tendsto (fun v ↦ u (v + 1)) Filter.atTop (nhds fStar) := by
    -- Shifting the convergent iterate sequence preserves the limit.
    exact hconv.comp (Filter.tendsto_add_atTop_nat 1)
  have hfStar : fStar ∈ NonnegativeOrthant.feasibleSet n :=
    limit_memFeasibleSet_of_tendsto n htailFeasible htailTendsto
  have hinactiveTail :
      ∀ {i : Fin n}, 0 < fStar i →
        ∃ v0 : ℕ, ∀ v ≥ v0, 0 < u v i :=
    eventually_pos_on_inactiveCoordinates n J τ f0 fStar hconv
  have hactiveTail :
      ∀ {i : Fin n}, fStar i = 0 →
        ∃ v0 : ℕ, ∀ v ≥ v0, u v i = 0 :=
    eventually_zero_on_activeCoordinates
      n J τ f0 fStar K hJ hGradLip hLineSearch hStepPos hconv hsc
  let cutoff : Fin n → ℕ := fun i ↦
    if hpos : 0 < fStar i then
      Classical.choose (hinactiveTail hpos)
    else
      Classical.choose
        (hactiveTail
          (le_antisymm (le_of_not_gt hpos) ((NonnegativeOrthant.mem_feasibleSet.mp hfStar) i)))
  refine ⟨Finset.univ.sup cutoff, ?_⟩
  intro v hv
  ext i
  by_cases hpos : 0 < fStar i
  · have hcutoff :
        cutoff i ≤ v := by
      exact le_trans (Finset.le_sup (Finset.mem_univ i)) hv
    have hcutoff' :
        Classical.choose (hinactiveTail hpos) ≤ v := by
      simpa [cutoff, hpos] using hcutoff
    have huPos : 0 < u v i := by
      exact (Classical.choose_spec (hinactiveTail hpos)) v hcutoff'
    -- Inactive coordinates stay strictly positive, so they never enter the active set.
    rw [ActiveSet.mem_active, ActiveSet.mem_active]
    constructor <;> intro h
    · exact (huPos.ne' h).elim
    · exact (hpos.ne' h).elim
  · have hfi :
        fStar i = 0 := by
      exact le_antisymm (le_of_not_gt hpos) ((NonnegativeOrthant.mem_feasibleSet.mp hfStar) i)
    have hcutoff :
        cutoff i ≤ v := by
      exact le_trans (Finset.le_sup (Finset.mem_univ i)) hv
    have hcutoff' :
        Classical.choose (hactiveTail hfi) ≤ v := by
      simpa [cutoff, hfi] using hcutoff
    have huZero : u v i = 0 := by
      exact (Classical.choose_spec (hactiveTail hfi)) v hcutoff'
    -- Active coordinates eventually match the zero pattern of the limit point.
    rw [ActiveSet.mem_active, ActiveSet.mem_active]
    simpa [hfi, huZero]

/-- Theorem 9.17. Assume that `gradient J` is Lipschitz continuous. Then

(i) any cluster point of the gradient-projection iterates for `(9.16)` is a
critical point for `(9.16)`;

(ii) if the gradient-projection iterates converge to a local minimizer `fStar`
for `(9.16)` satisfying the strict complementarity condition `(9.20)`, then the
optimal active set is identified in finitely many iterations. -/
theorem thm_9_17
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ : ContDiff ℝ 1 J)
    (hGradLip : LipschitzWith K (gradient J))
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0) :
    (∀ fBar : EuclideanSpace ℝ (Fin n),
        MapClusterPt
            fBar
            Filter.atTop
            (GradientProjection.iterates
              (NonnegativeOrthant.projector n)
              J τ f0) →
          NonnegativeOrthant.IsCriticalPoint J fBar) ∧
      ∀ fStar : EuclideanSpace ℝ (Fin n),
        (∀ v : ℕ, 0 < τ v) →
          Filter.Tendsto
              (GradientProjection.iterates
                (NonnegativeOrthant.projector n)
                J τ f0)
              Filter.atTop
              (nhds fStar) →
            IsLocalMinOn J (NonnegativeOrthant.feasibleSet n) fStar →
              NonnegativeOrthant.StrictComplementarity J fStar →
                ∃ v0 : ℕ,
                  ∀ v ≥ v0,
                    ActiveSet.active
                        (fun i x ↦ x i)
                        ((GradientProjection.iterates
                          (NonnegativeOrthant.projector n)
                          J τ f0) v) =
                      ActiveSet.active (fun i x ↦ x i) fStar := by
  constructor
  · intro fBar hCluster
    -- Part (i): any cluster point of the iterate sequence is critical.
    simpa using
      clusterPt_isCriticalPoint n J τ f0 fBar K hJ hGradLip hLineSearch hCluster
  · intro fStar hStepPos hconv hmin hsc
    -- Part (ii): strict complementarity forces finite active-set identification.
    simpa using
      eventually_eq_activeSet_of_limit
        n J τ f0 fStar K hJ hGradLip hLineSearch hStepPos hconv hmin hsc

end GradientProjection
