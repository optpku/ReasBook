/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_29
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Remark_9_10
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Theorem_9_17

public section

noncomputable section

namespace GradientProjection

open Filter

/-- Helper for Corollary 9.18: coercivity places any prescribed objective level
below all sufficiently large norms. -/
private lemma exists_normThreshold_le_of_coercive
    {H : Type*} [SeminormedAddCommGroup H]
    (J : H → ℝ) (A : ℝ) (hJ_coercive : coercive J) :
    ∃ R, ∀ x, R ≤ ‖x‖ → A ≤ J x := by
  by_contra hR
  push Not at hR
  have hRnat : ∀ n : ℕ, ∃ x : H, (n : ℝ) ≤ ‖x‖ ∧ J x < A := by
    intro n
    exact hR n
  choose x hx using hRnat
  have hnorm : ∀ n : ℕ, (n : ℝ) ≤ ‖x n‖ := fun n ↦ (hx n).1
  have hsmall : ∀ n : ℕ, J (x n) < A := fun n ↦ (hx n).2
  have hnorm_top : Filter.Tendsto (fun n ↦ ‖x n‖) Filter.atTop Filter.atTop := by
    -- The counterexample sequence escapes to infinity by construction.
    refine Filter.tendsto_atTop.2 ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge b
    refine Filter.mem_atTop_sets.2 ⟨N, ?_⟩
    intro n hn
    exact le_trans hN <| le_trans (by exact_mod_cast hn) (hnorm n)
  have hJ_top : Filter.Tendsto (fun n ↦ J (x n)) Filter.atTop Filter.atTop :=
    (coercive_iff.mp hJ_coercive) hnorm_top
  have hEventually : ∀ᶠ n in Filter.atTop, A + 1 ≤ J (x n) :=
    (Filter.tendsto_atTop.1 hJ_top) (A + 1)
  rcases Filter.mem_atTop_sets.1 hEventually with ⟨N, hN⟩
  have hlarge : A + 1 ≤ J (x N) := hN N le_rfl
  have hlt : J (x N) < A := hsmall N
  linarith

/-- Helper for Corollary 9.18: the orthant projector is continuous. -/
private lemma continuous_projector
    (n : ℕ) :
    Continuous (NonnegativeOrthant.projector n) := by
  -- Identify the orthant projector with the ambient Euclidean projection API.
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

/-- Helper for Corollary 9.18: every successor gradient-projection iterate is
feasible for the nonnegative orthant. -/
private lemma iteratesSucc_memFeasibleSet
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n)) (v : ℕ) :
    GradientProjection.iterates
        (NonnegativeOrthant.projector n)
        J τ f0
        (v + 1) ∈
      NonnegativeOrthant.feasibleSet n := by
  -- Rewrite the iterate update through the projector recurrence.
  rw [GradientProjection.iterates_succ]
  rw [GradientProjection.update_eq_projector_sub_smul_gradient]
  exact NonnegativeOrthant.projector_mem_feasibleSet n _

/-- Helper for Corollary 9.18: exact line search compares the chosen update
against any positive projected gradient step. -/
private lemma profile_projectedStep_eq
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
  -- Normalize the profile through the owner-level profile/update bridge, then
  -- rewrite the update onto the projected-step surface.
  rw [GradientProjection.profileDirection_apply_eq_update]
  simp [GradientProjection.update_eq_projector_sub_smul_gradient]

/-- Helper for Corollary 9.18: vanishing projected gradient steps converge back
to a feasible base point. -/
private lemma tendsto_projectedStep_at_zero
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ NonnegativeOrthant.feasibleSet n) :
    Tendsto
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
  have hlim :
      Tendsto
        (fun α : ℝ ↦ NonnegativeOrthant.projector n (x - α • gradient J x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (NonnegativeOrthant.projector n (x - (0 : ℝ) • gradient J x))) :=
    hcont.continuousAt.continuousWithinAt.tendsto
  simpa [hzero'] using hlim

/-- Helper for Corollary 9.18: exact line search compares the chosen update
against any positive projected gradient step. -/
private lemma exactLineSearch_le_projectedStep
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
  -- Rewrite the minimizing profile inequality onto the projected-step surface.
  simpa [u, profile_projectedStep_eq, GradientProjection.iterates_succ,
    GradientProjection.update_eq_projector_sub_smul_gradient] using hcompare

/-- Helper for Corollary 9.18: exact line search makes the objective values
nonincreasing along the feasible tail of the iterate sequence. -/
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
      Tendsto
        (fun α : ℝ ↦
          J (NonnegativeOrthant.projector n
            (u (v + 1) - α • gradient J (u (v + 1)))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (J (u (v + 1)))) := by
    -- Continuity of `J` at the feasible iterate transports the projected-step limit.
    exact
      (hJ_diff _ hv_feasible).continuousAt.tendsto.comp
        (tendsto_projectedStep_at_zero n J hv_feasible)
  have hcompare :
      (fun _ : ℝ ↦ J (u (v + 2))) ≤ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun α : ℝ ↦
          J (NonnegativeOrthant.projector n
            (u (v + 1) - α • gradient J (u (v + 1)))) := by
    -- Every positive candidate step dominates the exact line-search choice at stage `v + 1`.
    have hpositive : ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < α := by
      have hmem : {α : ℝ | 0 < α} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
        exact mem_inf_of_right (Filter.mem_principal.2 (by intro α hα; exact hα))
      exact hmem
    filter_upwards [hpositive] with α hα
    simpa [u, Nat.add_assoc] using
      exactLineSearch_le_projectedStep n J τ f0 hLineSearch (v + 1) hα
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hvalue_tendsto hcompare

/-- Helper for Corollary 9.18: every feasible-tail objective value is bounded
above by the first feasible iterate. -/
private lemma iterates_value_le_firstFeasible
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ_diff :
      ∀ x ∈ NonnegativeOrthant.feasibleSet n,
        DifferentiableAt ℝ J x)
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0) :
    ∀ v : ℕ,
      let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
      J (u (v + 1)) ≤ J (u 1) := by
  intro v
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  induction v with
  | zero =>
      -- The first feasible iterate bounds itself.
      simp
  | succ v hv =>
      -- Append one monotonicity step to the inductive tail bound.
      have hstep : J (u (v + 2)) ≤ J (u (v + 1)) := by
        simpa [u, Nat.add_assoc] using
          iterates_value_step_le n J τ f0 K hJ_diff hLineSearch v
      exact le_trans hstep (by simpa [u] using hv)

/-- Helper for Corollary 9.18: the objective values of the iterate sequence are
bounded above by the initial value and the first feasible iterate. -/
private lemma iterates_values_bddAbove
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ_diff :
      ∀ x ∈ NonnegativeOrthant.feasibleSet n,
        DifferentiableAt ℝ J x)
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0) :
    BddAbove
      (Set.range fun v ↦
        J ((GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0) v)) := by
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  refine ⟨max (J (u 0)) (J (u 1)), ?_⟩
  rintro _ ⟨v, rfl⟩
  cases v with
  | zero =>
      -- The initial value is bounded by the chosen maximum.
      exact le_max_left _ _
  | succ v =>
      -- Every later value is bounded by the first feasible iterate.
      have htail : J (u (v + 1)) ≤ J (u 1) := by
        simpa [u] using
          iterates_value_le_firstFeasible n J τ f0 K hJ_diff hLineSearch v
      exact le_trans htail (le_max_right _ _)

/-- Helper for Corollary 9.18: below the coordinatewise clipping thresholds, the
orthant projector agrees with subtracting the projected gradient. -/
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

/-- Helper for Corollary 9.18: a nonzero projected gradient gives a genuine
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

/-- Helper for Corollary 9.18: one can choose a positive step size below both a
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

/-- Helper for Corollary 9.18: any cluster point of the exact line-search
gradient-projection iterates is a critical point under the differentiability
and Lipschitz hypotheses used in Corollary 9.18. -/
private lemma clusterPt_isCriticalPoint_of_differentiableOn
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fBar : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ_diff :
      ∀ x ∈ NonnegativeOrthant.feasibleSet n,
        DifferentiableAt ℝ J x)
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
    -- The cluster subsequence transfers convergence through continuity of `J` at `fBar`.
    exact ((hJ_diff _ hfBar).continuousAt.tendsto).comp hψ
  have hClusterSucc :
      MapClusterPt fBar Filter.atTop (fun v : ℕ ↦ u (v + 1)) := by
    -- Shifting the sequence by one step preserves the same cluster points at `atTop`.
    change MapClusterPt fBar Filter.atTop (u ∘ fun v : ℕ ↦ v + 1)
    rw [mapClusterPt_comp]
    simpa [u, map_add_atTop_eq_nat 1] using hCluster
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
      simpa [Function.comp_def, u] using
        ((hJ_diff _ hfBar).continuousAt.tendsto).comp hψSucc
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
      have hg :
          Filter.Tendsto g (nhds fBar) (nhds (g fBar)) :=
        hstep_cont.continuousAt.tendsto
      -- First transport the iterate subsequence through the projected-step map,
      -- then through continuity of `J` at the feasible projected limit.
      simpa [g, Function.comp_def, u] using
        ((hJ_diff _ hstep_mem).continuousAt.tendsto.comp (hg.comp hψ))
    have hcompare :
        ∀ᶠ k : ℕ in Filter.atTop,
          J (u (ψ k + 1)) ≤
            J (NonnegativeOrthant.projector n (u (ψ k) - α • gradient J (u (ψ k)))) := by
      -- Exact line search dominates every positive projected step along the cluster subsequence.
      refine Filter.Eventually.of_forall ?_
      intro k
      simpa [u] using
        exactLineSearch_le_projectedStep n J τ f0 hLineSearch (ψ k) hα
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
    exists_smallStep_lt_coordThreshold n J (f := fBar) hδ_pos
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

/-- Any cluster point of the nonnegative-orthant gradient-projection iterates
coincides with a global minimizer when `J` is strictly convex on the feasible
set. -/
theorem clusterPt_eq_globalMinimizer_of_strictConvexOn
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fBar fStar : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ_diff :
      ∀ x ∈ NonnegativeOrthant.feasibleSet n,
        DifferentiableAt ℝ J x)
    (hJ_strict :
      StrictConvexOn ℝ (NonnegativeOrthant.feasibleSet n) J)
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
          J τ f0))
    (hfStar : fStar ∈ NonnegativeOrthant.feasibleSet n)
    (hmin : IsMinOn J (NonnegativeOrthant.feasibleSet n) fStar) :
    fBar = fStar := by
  -- First identify the cluster point as a constrained critical point.
  have hcrit : NonnegativeOrthant.IsCriticalPoint J fBar :=
    clusterPt_isCriticalPoint_of_differentiableOn
      n J τ f0 fBar K hJ_diff hGradLip hLineSearch hCluster
  have hbar_min :
      IsMinOn J (NonnegativeOrthant.feasibleSet n) fBar :=
    NonnegativeOrthant.isMinOn_of_isCriticalPoint_of_strictConvexOn
      hJ_diff hJ_strict hcrit
  -- Strict convexity forces any two feasible minimizers to coincide.
  exact hJ_strict.eq_of_isMinOn hbar_min hmin hcrit.mem_feasibleSet hfStar

/-- Helper for Corollary 9.18: any subsequence of the iterate sequence has a
further subsequence converging to the same global minimizer. -/
private lemma subseq_hasSubseqTendsto_of_isMinOn_of_coercive
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fStar : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ_diff :
      ∀ x ∈ NonnegativeOrthant.feasibleSet n,
        DifferentiableAt ℝ J x)
    (hJ_strict :
      StrictConvexOn ℝ (NonnegativeOrthant.feasibleSet n) J)
    (hJ_coercive : coercive J)
    (hGradLip : LipschitzWith K (gradient J))
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0)
    (hfStar : fStar ∈ NonnegativeOrthant.feasibleSet n)
    (hmin : IsMinOn J (NonnegativeOrthant.feasibleSet n) fStar)
    (ns : ℕ → ℕ)
    (hns : Filter.Tendsto ns Filter.atTop Filter.atTop) :
    ∃ ψ : ℕ → ℕ,
      StrictMono ψ ∧
        Filter.Tendsto
          ((GradientProjection.iterates
              (NonnegativeOrthant.projector n)
              J τ f0) ∘ ns ∘ ψ)
          Filter.atTop
          (nhds fStar) := by
  let u := GradientProjection.iterates (NonnegativeOrthant.projector n) J τ f0
  have hvalues_bdd :
      BddAbove (Set.range fun k ↦ J ((u ∘ ns) k)) := by
    rcases iterates_values_bddAbove n J τ f0 K hJ_diff hLineSearch with ⟨A, hA⟩
    refine ⟨A, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hA ⟨ns k, rfl⟩
  obtain ⟨R, hR⟩ :=
    exists_norm_le_of_coercive_of_bddAbove (J := J) (f := u ∘ ns) hJ_coercive hvalues_bdd
  have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg _) (hR 0)
  have hball :
      ∀ k : ℕ, (u ∘ ns) k ∈ Metric.closedBall 0 R := by
    intro k
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR k
  obtain ⟨fBar, _hfBar_mem, ψ, hψ_mono, hψ_tendsto⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).tendsto_subseq hball
  have hcomp_tendsto :
      Filter.Tendsto (ns ∘ ψ) Filter.atTop Filter.atTop := by
    -- Passing to a strict-mono subsubsequence preserves divergence to `atTop`.
    simpa [Function.comp_def] using hns.comp hψ_mono.tendsto_atTop
  have hsub_cluster :
      MapClusterPt fBar Filter.atTop (u ∘ ns ∘ ψ) := by
    -- A convergent subsubsequence is automatically a cluster point of that subsubsequence.
    simpa [Function.comp_def] using Filter.Tendsto.mapClusterPt hψ_tendsto
  have hcluster :
      MapClusterPt fBar Filter.atTop u := by
    -- Transport the convergent subsubsequence back to a cluster point of the full iterate sequence.
    exact MapClusterPt.of_comp hcomp_tendsto <| by
      simpa [Function.comp_def] using hsub_cluster
  have hbar_eq :
      fBar = fStar :=
    clusterPt_eq_globalMinimizer_of_strictConvexOn
      n J τ f0 fBar fStar K hJ_diff hJ_strict hGradLip hLineSearch hcluster hfStar hmin
  refine ⟨ψ, hψ_mono, ?_⟩
  -- Replace the identified cluster point by the prescribed minimizer.
  simpa [u, Function.comp_def, hbar_eq] using hψ_tendsto

/-- If `fStar` is a global minimizer of `J` on the nonnegative orthant, then
the gradient-projection iterates for `(9.16)` converge to `fStar` under the
strict-convexity, coercivity, and Lipschitz hypotheses of Corollary 9.18. -/
theorem tendsto_of_isMinOn_of_strictConvexOn_of_coercive
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 fStar : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ_diff :
      ∀ x ∈ NonnegativeOrthant.feasibleSet n,
        DifferentiableAt ℝ J x)
    (hJ_strict :
      StrictConvexOn ℝ (NonnegativeOrthant.feasibleSet n) J)
    (hJ_coercive : coercive J)
    (hGradLip : LipschitzWith K (gradient J))
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0)
    (hfStar : fStar ∈ NonnegativeOrthant.feasibleSet n)
    (hmin : IsMinOn J (NonnegativeOrthant.feasibleSet n) fStar) :
    Filter.Tendsto
      (GradientProjection.iterates
        (NonnegativeOrthant.projector n)
        J τ f0)
      Filter.atTop
      (nhds fStar) := by
  -- Use the standard subsequence criterion, with the coercive subsubsequence lemma as input.
  refine Filter.tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ψ, _hψ_mono, hψ_tendsto⟩ :=
    subseq_hasSubseqTendsto_of_isMinOn_of_coercive
      n J τ f0 fStar K hJ_diff hJ_strict hJ_coercive hGradLip hLineSearch hfStar hmin ns hns
  exact ⟨ψ, by simpa [Function.comp_def] using hψ_tendsto⟩

/-- Corollary 9.18. If `J` is strictly convex, coercive, and Lipschitz
continuous, then the gradient-projection iterates for `(9.16)` converge to the
unique global minimizer of `J` on the nonnegative orthant. -/
theorem tendsto_globalMinimizer_of_strictConvexOn_of_coercive
    (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n)) (K : NNReal)
    (hJ_diff :
      ∀ x ∈ NonnegativeOrthant.feasibleSet n,
        DifferentiableAt ℝ J x)
    (hJ_strict :
      StrictConvexOn ℝ (NonnegativeOrthant.feasibleSet n) J)
    (hJ_coercive : coercive J)
    (hGradLip : LipschitzWith K (gradient J))
    (hLineSearch :
      GradientProjection.IsExactLineSearch
        (NonnegativeOrthant.projector n)
        J τ f0) :
    ∃! fStar,
      fStar ∈ NonnegativeOrthant.feasibleSet n ∧
        IsMinOn J (NonnegativeOrthant.feasibleSet n) fStar ∧
        Filter.Tendsto
          (GradientProjection.iterates
            (NonnegativeOrthant.projector n)
            J τ f0)
          Filter.atTop
          (nhds fStar) := by
  have h0_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ NonnegativeOrthant.feasibleSet n := by
    simp [NonnegativeOrthant.mem_feasibleSet]
  obtain ⟨R, hR⟩ :=
    exists_normThreshold_le_of_coercive J (J 0) hJ_coercive
  let S : ℝ := max 0 R
  have h0_ball : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall 0 S := by
    simp [S, Metric.mem_closedBall]
  have hCompact :
      IsCompact (NonnegativeOrthant.feasibleSet n ∩ Metric.closedBall 0 S) := by
    have hClosed :
        IsClosed (NonnegativeOrthant.feasibleSet n ∩ Metric.closedBall 0 S) :=
      (NonnegativeOrthant.closedConvex_feasibleSet n).isClosed.inter Metric.isClosed_closedBall
    exact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) S).of_isClosed_subset
        hClosed (by intro f hf; exact hf.2)
  obtain ⟨fStar, hfStar_mem, hfStar_min⟩ :=
    hCompact.exists_isMinOn ⟨0, ⟨h0_mem, h0_ball⟩⟩ <| by
      intro x hx
      exact (hJ_diff x hx.1).continuousAt.continuousWithinAt
  have hfStar_feasible : fStar ∈ NonnegativeOrthant.feasibleSet n := hfStar_mem.1
  have hfStar_le_zero : J fStar ≤ J 0 := hfStar_min ⟨h0_mem, h0_ball⟩
  have hGlobalMin : IsMinOn J (NonnegativeOrthant.feasibleSet n) fStar := by
    intro f hf
    by_cases hfBall : f ∈ Metric.closedBall 0 S
    · exact hfStar_min ⟨hf, hfBall⟩
    · have hS_lt_norm : S < ‖f‖ := by
        have hnot : ¬ ‖f‖ ≤ S := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hfBall
        exact lt_of_not_ge hnot
      have hR_le_norm : R ≤ ‖f‖ := by
        have hR_le_S : R ≤ S := le_max_right 0 R
        linarith
      exact hfStar_le_zero.trans (hR f hR_le_norm)
  have hTendsto :
      Filter.Tendsto
        (GradientProjection.iterates
          (NonnegativeOrthant.projector n)
          J τ f0)
        Filter.atTop
        (nhds fStar) :=
    tendsto_of_isMinOn_of_strictConvexOn_of_coercive
      n J τ f0 fStar K hJ_diff hJ_strict hJ_coercive hGradLip hLineSearch hfStar_feasible hGlobalMin
  refine ⟨fStar, ⟨hfStar_feasible, hGlobalMin, hTendsto⟩, ?_⟩
  intro g hg
  exact hJ_strict.eq_of_isMinOn hg.2.1 hGlobalMin hg.1 hfStar_feasible

end GradientProjection
