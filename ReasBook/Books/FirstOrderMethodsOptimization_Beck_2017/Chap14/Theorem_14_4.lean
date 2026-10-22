/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_3
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Definition_14_2
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Lemma_14_2
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Theorem_14_3_Helpers.PrefixState
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Theorem_14_3_Helpers.Recovery

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Filter
open scoped Topology

section

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]

/-- Helper for Theorem 14.4: during one composite Algorithm 14.3 step, every Gauss-Seidel prefix
state stays in the effective domain of `F(x) = f(x) + ∑ i, g_i(x_i)` and never exceeds the
starting objective value. -/
private lemma compositeStepPrefixState_mem_effective_domain_and_le
    {f : ((i : Fin p) → Ei i) → EReal}
    {g : (i : Fin p) → Ei i → EReal}
    {x : ℕ → (i : Fin p) → Ei i}
    {k : ℕ}
    (hxk : x k ∈ effective_domain (composite_model_objective f (separableSum g)))
    (hstepk : IsAlternatingMinimizationCompositeStep f g (x k) (x (k + 1))) :
    ∀ n ≤ p,
      alternating_minimization_prefix_state x k n ∈
          effective_domain (composite_model_objective f (separableSum g)) ∧
        composite_model_objective f (separableSum g) (alternating_minimization_prefix_state x k n) ≤
          composite_model_objective f (separableSum g) (x k) := by
  intro n hn
  induction n with
  | zero =>
      -- At stage `0`, the prefix state is exactly the current iterate.
      constructor
      · simpa using hxk
      · simp
  | succ n ihn =>
      have hn_lt : n < p := Nat.lt_of_succ_le hn
      let i : Fin p := ⟨n, hn_lt⟩
      have hold := ihn (Nat.le_of_lt hn_lt)
      rcases hold with ⟨hold_dom, hold_le⟩
      have hmodel : IsAlternatingMinimizationCompositeModel f g :=
        hstepk.toIsAlternatingMinimizationCompositeModel
      have hinactive_ne_bot :
          (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)) ≠ ⊥ := by
        -- The frozen inactive penalty sum avoids `⊥` because every block penalty does.
        exact
          ereal_sum_ne_bot
            (Finset.univ.erase i)
            (fun j ↦ g j (if j.1 < i.1 then x (k + 1) j else x k j))
            (fun j _ ↦ (hmodel.g_proper j).ne_bot _)
      have hactive_ne_bot :
          alternating_minimization_composite_block_objective
              f g (x k) (x (k + 1)) i (x k i) ≠
            ⊥ := by
        -- The displayed active term is finite below because both summands avoid `⊥`.
        simpa [alternating_minimization_composite_block_objective_apply] using
          (EReal.add_ne_bot_iff.2
            ⟨hmodel.f_ne_bot
                (alternating_minimization_partial_state (x k) (x (k + 1)) i (x k i)),
              (hmodel.g_proper i).ne_bot (x k i)⟩)
      have hinactive :
          (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)) =
            (((∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)).toReal :
                ℝ) :
              EReal) := by
        have hold_old_dom :
            alternating_minimization_partial_state (x k) (x (k + 1)) i (x k i) ∈
              effective_domain (composite_model_objective f (separableSum g)) := by
          rw [← alternating_minimization_prefix_state_old_eq_partial_state x k i]
          exact hold_dom
        -- Proposition 14.2 needs the frozen inactive penalty term as a genuine finite constant.
        refine
          inactive_penalty_eq_coe_toReal_of_ne_bot_of_mem_effective_domain
            (f := f)
            (g := g)
            (xk := x k)
            (xNext := x (k + 1))
            (i := i)
            hinactive_ne_bot
            hactive_ne_bot
            hold_old_dom
      have hfull_min :
          IsMinOn
            (alternating_minimization_block_objective
              (composite_model_objective f (separableSum g))
              (x k)
              (x (k + 1))
              i)
            Set.univ
            (x (k + 1) i) := by
        -- Rewrite the composite one-block minimizer statement into the full objective slice.
        exact
          (isMinOn_alternating_minimization_full_objective_iff_isMinOn_composite_block_objective
            (f := f)
            (g := g)
            (xk := x k)
            (xNext := x (k + 1))
            (i := i)
            hinactive
            (x (k + 1) i)).2
            (hstepk.block_isMinOn i)
      have hnew_le_old :
          composite_model_objective f (separableSum g)
              (alternating_minimization_partial_state (x k) (x (k + 1)) i (x (k + 1) i)) ≤
            composite_model_objective f (separableSum g)
              (alternating_minimization_partial_state (x k) (x (k + 1)) i (x k i)) := by
        -- Compare the minimizing block value against the old block value.
        simpa [alternating_minimization_block_objective_apply] using
          (isMinOn_iff.mp hfull_min) (x k i) (by simp)
      have hold_old_dom :
          alternating_minimization_partial_state (x k) (x (k + 1)) i (x k i) ∈
            effective_domain (composite_model_objective f (separableSum g)) := by
        -- The previous prefix state is the mixed state with the old block value.
        rw [← alternating_minimization_prefix_state_old_eq_partial_state x k i]
        exact hold_dom
      have hnew_dom :
          alternating_minimization_partial_state (x k) (x (k + 1)) i (x (k + 1) i) ∈
            effective_domain (composite_model_objective f (separableSum g)) := by
        -- Descent from a feasible comparison point keeps the updated mixed state finite.
        exact
          mem_effective_domain.mpr <|
            lt_of_le_of_lt hnew_le_old (mem_effective_domain.mp hold_old_dom)
      have hold_old_le :
          composite_model_objective f (separableSum g)
              (alternating_minimization_partial_state (x k) (x (k + 1)) i (x k i)) ≤
            composite_model_objective f (separableSum g) (x k) := by
        -- The inductive bound already controls the previous prefix state.
        rw [← alternating_minimization_prefix_state_old_eq_partial_state x k i]
        exact hold_le
      have hnew_le :
          composite_model_objective f (separableSum g)
              (alternating_minimization_partial_state (x k) (x (k + 1)) i (x (k + 1) i)) ≤
            composite_model_objective f (separableSum g) (x k) :=
        le_trans hnew_le_old hold_old_le
      -- The next prefix state is the mixed state with the minimizing new block value.
      rw [alternating_minimization_prefix_state_new_eq_partial_state x k i]
      exact ⟨hnew_dom, hnew_le⟩

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby Chapter 3, 11, and 14 owners.

This item is `source-facing`: it is a convergence corollary for sequences generated by the
composite alternating-minimization method. Domain sampling in the Chapter 14 API shows that the
trajectory owner already exists upstream:
- `is_alternating_minimization_trajectory` from Algorithm 14.1 for generated iterate sequences;
- `IsAlternatingMinimizationCompositeModel` from Algorithm 14.3 for the standing composite-model
  regularity assumptions in Assumption 14.6;
- `isMinOn_alternating_minimization_full_objective_iff_isMinOn_composite_block_objective` from
  Proposition 14.2 for the bridge from the Algorithm 14.3 displayed one-block objective to the
  owner blockwise `IsMinOn` clauses for the full composite objective;
- `alternating_minimization_trajectory_range_bounded` and
  `alternating_minimization_cluster_points_coordinatewise_minima` from Theorem 14.3 for the two
  convergence conclusions on the owner trajectory; and
- `is_stationary_point_of_coordinatewise_minimum` from Lemma 14.2 for the bridge from
  coordinatewise minimality to the Chapter 3 stationary-point owner `is_stationary_point`.

Accordingly, this file no longer keeps a parallel local trajectory predicate. The only local
`bridge/view` is the translation from the Algorithm 14.3 one-step data, through Proposition 14.2,
to the canonical Algorithm 14.1 trajectory for the full composite objective
`composite_model_objective f (separableSum g)`. The public API keeps the source-facing boundedness
and stationarity theorems on the Algorithm 14.3 step data, and also exports the intermediate
bridge from composite-step cluster points to the canonical owner
`is_coordinatewise_minimum (composite_model_objective f (separableSum g))`. This still reuses the
existing `IsAlternatingMinimizationCompositeStep → IsAlternatingMinimizationCompositeModel`
projection from Algorithm 14.3 instead of restating it locally. The target-file check
`lake env lean Books/FirstOrderMethodsOptimization_Beck_2017/Chap14/Theorem_14_4.lean` currently
succeeds; the
remaining debt in this file is proof-only. -/

-- Proof sketch: for each outer iteration and block, start from the owner clause
-- `(hstep k).block_isMinOn i` on `alternating_minimization_composite_block_objective f g ...`,
-- then use Proposition 14.2 to transfer that minimizer statement to the full composite objective.
-- Together with the initial-domain assumption, this yields exactly the defining clauses of
-- `is_alternating_minimization_trajectory` for the composite objective.
/-- If every successive pair `(x^k, x^{k+1})` satisfies the composite Algorithm 14.3 step
conditions and `x^0 ∈ dom(F)`, then `x` is the canonical alternating-minimization trajectory for
the composite objective `F(x) = f(x) + ∑ i, g_i(x_i)`. -/
theorem is_alternating_minimization_trajectory_of_composite_steps
    {f : ((i : Fin p) → Ei i) → EReal}
    {g : (i : Fin p) → Ei i → EReal}
    {x : ℕ → (i : Fin p) → Ei i}
    (hx0 : x 0 ∈ effective_domain (composite_model_objective f (separableSum g)))
    (hstep : ∀ k : ℕ, IsAlternatingMinimizationCompositeStep f g (x k) (x (k + 1))) :
    is_alternating_minimization_trajectory (composite_model_objective f (separableSum g)) x := by
  -- Build the canonical trajectory owner by propagating feasibility and rewriting each composite
  -- one-block minimizer into the full objective slice.
  refine
    { zero_mem_effective_domain := hx0
      step_isMinOn := ?_ }
  intro k i
  have hxk : x k ∈ effective_domain (composite_model_objective f (separableSum g)) := by
    induction k with
    | zero =>
        simpa using hx0
    | succ k ih =>
        -- The terminal prefix state of step `k` is exactly `x (k + 1)`.
        simpa using
          (compositeStepPrefixState_mem_effective_domain_and_le
            (f := f)
            (g := g)
            (x := x)
            (k := k)
            ih
            (hstep k)
            p
            (le_rfl : p ≤ p)).1
  have hold_dom :
      alternating_minimization_prefix_state x k i.1 ∈
        effective_domain (composite_model_objective f (separableSum g)) :=
    (compositeStepPrefixState_mem_effective_domain_and_le
      (f := f)
      (g := g)
      (x := x)
      (k := k)
      hxk
      (hstep k)
      i.1
      (Nat.le_of_lt i.is_lt)).1
  have hmodel : IsAlternatingMinimizationCompositeModel f g :=
    (hstep k).toIsAlternatingMinimizationCompositeModel
  have hinactive_ne_bot :
      (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)) ≠ ⊥ := by
    -- Every inactive penalty term avoids `⊥`.
    exact
      ereal_sum_ne_bot
        (Finset.univ.erase i)
        (fun j ↦ g j (if j.1 < i.1 then x (k + 1) j else x k j))
        (fun j _ ↦ (hmodel.g_proper j).ne_bot _)
  have hactive_ne_bot :
      alternating_minimization_composite_block_objective
          f g (x k) (x (k + 1)) i (x k i) ≠
        ⊥ := by
    -- The displayed active block objective is finite below at the old block value.
    simpa [alternating_minimization_composite_block_objective_apply] using
      (EReal.add_ne_bot_iff.2
        ⟨hmodel.f_ne_bot
            (alternating_minimization_partial_state (x k) (x (k + 1)) i (x k i)),
          (hmodel.g_proper i).ne_bot (x k i)⟩)
  have hinactive :
      (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)) =
        (((∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then x (k + 1) j else x k j)).toReal :
            ℝ) :
          EReal) := by
    -- Convert the frozen inactive penalty sum into the finite-constant form used by
    -- Proposition 14.2.
    refine
      inactive_penalty_eq_coe_toReal_of_ne_bot_of_mem_effective_domain
        (f := f)
        (g := g)
        (xk := x k)
        (xNext := x (k + 1))
        (i := i)
        hinactive_ne_bot
        hactive_ne_bot
        ?_
    rw [← alternating_minimization_prefix_state_old_eq_partial_state x k i]
    exact hold_dom
  -- Proposition 14.2 transports the stored composite block minimizer to the full objective.
  exact
    (isMinOn_alternating_minimization_full_objective_iff_isMinOn_composite_block_objective
      (f := f)
      (g := g)
      (xk := x k)
      (xNext := x (k + 1))
      (i := i)
      hinactive
      (x (k + 1) i)).2
      ((hstep k).block_isMinOn i)

section Boundedness

variable (f : ((i : Fin p) → Ei i) → EReal)
variable (g : (i : Fin p) → Ei i → EReal)
variable (x : ℕ → (i : Fin p) → Ei i)

local notation "F" => composite_model_objective f (separableSum g)

-- Proof sketch: convert the source-facing composite-step data to the canonical owner trajectory
-- for `F`, then apply Theorem 14.3 (1).
/-- Boundedness conclusion of Theorem 14.4: under Assumption 14.6, if every real
level set of the composite objective `F(x) = f(x) + ∑ i, g_i(x_i)` is bounded and
`x^k` is generated by Algorithm 14.3, then the sequence `x^k` is bounded. This
boundedness conclusion uses only the Chapter 14 trajectory and bornology layer,
via the bridge to Theorem 14.3 (1). -/
theorem alternating_minimization_composite_trajectory_bounded
    (hlevel :
      ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (hx0 : x 0 ∈ effective_domain F)
    (hstep : ∀ k : ℕ, IsAlternatingMinimizationCompositeStep f g (x k) (x (k + 1))) :
    Bornology.IsBounded (Set.range x) := by
  -- Convert the source-facing composite-step data to the canonical trajectory owner.
  exact
    alternating_minimization_trajectory_range_bounded
      F
      x
      hlevel
      (is_alternating_minimization_trajectory_of_composite_steps
        (f := f)
        (g := g)
        hx0
        hstep)

end Boundedness

end

section Stationarity

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]

variable (f : ((i : Fin p) → Ei i) → EReal)
variable (g : (i : Fin p) → Ei i → EReal)

local notation "F" => composite_model_objective f (separableSum g)

/-- Helper for Theorem 14.4: the block-separable penalty `x ↦ ∑ i, g_i(x_i)` never attains
`-∞` under Assumption 14.6. -/
private lemma alternating_minimization_separableSum_ne_bot
    (hmodel : IsAlternatingMinimizationCompositeModel f g) :
    ∀ z : (i : Fin p) → Ei i, separableSum g z ≠ ⊥ := by
  intro z
  -- Every block penalty avoids `⊥`, so the finite block sum does as well.
  simpa [separableSum_apply] using
    ereal_sum_ne_bot
      Finset.univ
      (fun i ↦ g i (z i))
      (fun i _ ↦ (hmodel.g_proper i).ne_bot (z i))

/-- Helper for Theorem 14.4: the composite objective `f + separableSum g` never attains `-∞`
under Assumption 14.6. -/
private lemma alternating_minimization_composite_objective_ne_bot
    (hmodel : IsAlternatingMinimizationCompositeModel f g) :
    ∀ z : (i : Fin p) → Ei i, F z ≠ ⊥ := by
  intro z
  -- The smooth term and the block-separable penalty both avoid `⊥`.
  rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
  exact ⟨hmodel.f_ne_bot z, alternating_minimization_separableSum_ne_bot (f := f) (g := g) hmodel z⟩

/-- Helper for Theorem 14.4: any point where the composite objective is finite already lies in the
effective domain of the separable penalty. -/
private lemma effective_domain_composite_model_objective_subset_separable
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F) :
    z ∈ effective_domain (separableSum g) := by
  -- If the separable penalty were `⊤`, then the full composite objective would also be `⊤`.
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  intro hsep_top
  have hF_top : F z = ⊤ := by
    rw [composite_model_objective_apply, hsep_top]
    exact EReal.add_top_of_ne_bot (hmodel.f_ne_bot z)
  exact (lt_top_iff_ne_top.mp (mem_effective_domain.mp hz)) hF_top

/-- Helper for Theorem 14.4: finiteness of the composite objective forces every block penalty
value to be finite. -/
private lemma alternating_minimization_block_mem_effective_domain
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F) (i : Fin p) :
    z i ∈ effective_domain (g i) := by
  -- First move from the composite effective domain to the separable penalty effective domain.
  exact
    block_mem_effective_domain_of_mem_separableSum_effective_domain
      g
      hmodel.g_proper
      (effective_domain_composite_model_objective_subset_separable
        (f := f)
        (g := g)
        hmodel
        hz)
      i

/-- Helper for Theorem 14.4: the effective domain of the composite model has the same
block-replacement closure as the product effective domain of its separable term. -/
private lemma composite_update_mem_effective_domain_of_block_mem
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {z : (i : Fin p) → Ei i} (i : Fin p) {yi : Ei i}
    (hz : z ∈ effective_domain F) (hyi : yi ∈ effective_domain (g i)) :
    Function.update z i yi ∈ effective_domain F := by
  let y : (i : Fin p) → Ei i := Function.update z i yi
  have hzSeparable : z ∈ effective_domain (separableSum g) :=
    effective_domain_composite_model_objective_subset_separable
      (f := f) (g := g) hmodel hz
  have hyBlock : ∀ j : Fin p, y j ∈ effective_domain (g j) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [y]
    · simpa [y, Function.update, hji] using
        block_mem_effective_domain_of_mem_separableSum_effective_domain
          g hmodel.g_proper hzSeparable j
  have hySeparable : y ∈ effective_domain (separableSum g) := by
    rw [mem_effective_domain, separableSum_apply]
    exact
      ereal_sum_lt_top Finset.univ (fun j ↦ g j (y j))
        (fun j _ ↦ mem_effective_domain.mp (hyBlock j))
  have hyF : y ∈ effective_domain f :=
    interior_subset (hmodel.g_effective_domain_subset_interior_f_effective_domain hySeparable)
  change y ∈ effective_domain F
  rw [mem_effective_domain, composite_model_objective_apply]
  exact
    EReal.add_lt_top (mem_effective_domain.mp hyF).ne
      (mem_effective_domain.mp hySeparable).ne

/-- Helper for Theorem 14.4: on the composite effective domain, each block penalty value is a
real coercion in `EReal`. -/
private lemma alternating_minimization_block_value_eq_coe_toReal
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F) (i : Fin p) :
    g i (z i) = ((((g i (z i)).toReal : ℝ)) : EReal) := by
  -- On the composite effective domain, the active block penalty is finite and hence a real
  -- coercion in `EReal`.
  exact
    (EReal.coe_toReal
      (mem_effective_domain.mp
        (alternating_minimization_block_mem_effective_domain
          (f := f)
          (g := g)
          hmodel
          hz
          i)).ne
      ((hmodel.g_proper i).ne_bot (z i))).symm

/-- Helper for Theorem 14.4: the composite objective `f + separableSum g` is lower semicontinuous
and continuous on its effective domain under Assumption 14.6. -/
private lemma alternating_minimization_composite_objective_regular
    (hmodel : IsAlternatingMinimizationCompositeModel f g) :
    LowerSemicontinuous F ∧ ContinuousOn F (effective_domain F) := by
  have hsep_ne_bot :
      ∀ z : (i : Fin p) → Ei i, separableSum g z ≠ ⊥ :=
    alternating_minimization_separableSum_ne_bot (f := f) (g := g) hmodel
  have hdom_subset :
      effective_domain F ⊆ interior (effective_domain f) := by
    intro z hz
    exact
      hmodel.g_effective_domain_subset_interior_f_effective_domain
        (effective_domain_composite_model_objective_subset_separable
          (f := f)
          (g := g)
          hmodel
          hz)
  have hclosed : LowerSemicontinuous F := by
    -- Global lower semicontinuity follows from the model assumptions on `f` and `separableSum g`.
    refine hmodel.f_closed.add' (separableSum_closed g hmodel.g_closed) ?_
    intro z
    exact EReal.continuousAt_add (.inr (hsep_ne_bot z)) (.inl (hmodel.f_ne_bot z))
  have hf_cont :
      ContinuousOn (fun z ↦ ((f z).toReal : EReal)) (effective_domain F) := by
    -- Differentiability on `interior (effective_domain f)` gives continuity of the finite-valued
    -- smooth term on the composite effective domain.
    refine
      (continuous_coe_real_ereal.continuousOn : ContinuousOn ((↑) : ℝ → EReal) Set.univ).comp
        ?_
        ?_
    · intro z hz
      exact
        ContinuousWithinAt.mono
          ((
            hmodel.f_toReal_differentiableOn_interior_effective_domain z (hdom_subset hz)
              ).continuousWithinAt)
          hdom_subset
    · intro z hz
      simp
  have hsep_cont :
      ContinuousOn (separableSum g) (effective_domain F) := by
    classical
    -- Rewrite the separable penalty as a finite real-valued sum on the composite effective domain.
    rw [continuousOn_iff_continuous_restrict]
    have htermReal :
        ∀ i : Fin p, Continuous (fun z : effective_domain F ↦ (g i (z.1 i)).toReal) := by
      intro i
      have htermOn :
          ContinuousOn (fun z : effective_domain F ↦ g i (z.1 i)) Set.univ := by
        refine
          (hmodel.g_continuousOn_effective_domain i).comp
            (((continuous_apply i).comp continuous_subtype_val).continuousOn)
            ?_
        intro z hz
        simpa using
          alternating_minimization_block_mem_effective_domain
            (f := f)
            (g := g)
            hmodel
            z.property
            i
      have htoRealOn :
          ContinuousOn (fun z : effective_domain F ↦ (g i (z.1 i)).toReal) Set.univ := by
        refine EReal.continuousOn_toReal.comp htermOn ?_
        intro z hz
        have hblock :
            z.1 i ∈ effective_domain (g i) :=
          alternating_minimization_block_mem_effective_domain
            (f := f)
            (g := g)
            hmodel
            z.property
            i
        have htop : g i (z.1 i) ≠ ⊤ := (mem_effective_domain.mp hblock).ne
        have hbot : g i (z.1 i) ≠ ⊥ := (hmodel.g_proper i).ne_bot (z.1 i)
        simp [htop, hbot]
      exact continuousOn_univ.mp htoRealOn
    have hsumReal :
        Continuous (fun z : effective_domain F ↦ ∑ i : Fin p, (g i (z.1 i)).toReal) := by
      exact continuous_finset_sum Finset.univ (fun i _ ↦ htermReal i)
    have hsumCoe :
        Continuous
          (fun z : effective_domain F ↦
            (((∑ i : Fin p, (g i (z.1 i)).toReal : ℝ)) : EReal)) :=
      continuous_coe_real_ereal.comp hsumReal
    have hsumEq :
        (fun z : effective_domain F ↦ separableSum g z.1) =
          fun z : effective_domain F ↦
            (((∑ i : Fin p, (g i (z.1 i)).toReal : ℝ)) : EReal) := by
      have hcoeSum (s : Finset (Fin p)) (φ : Fin p → ℝ) :
          (((Finset.sum s φ : ℝ)) : EReal) = Finset.sum s (fun i ↦ ((φ i : ℝ) : EReal)) := by
        induction s using Finset.induction_on with
        | empty =>
            simp
        | @insert a s ha hs =>
            simp [Finset.sum_insert, ha, hs, EReal.coe_add]
      funext z
      rw [separableSum_apply]
      calc
        ∑ i : Fin p, g i (z.1 i) = ∑ i : Fin p, ((((g i (z.1 i)).toReal : ℝ)) : EReal) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact
            alternating_minimization_block_value_eq_coe_toReal
              (f := f)
              (g := g)
              hmodel
              z.property
              i
        _ = (((∑ i : Fin p, (g i (z.1 i)).toReal : ℝ)) : EReal) := by
          simpa using (hcoeSum Finset.univ (fun i : Fin p ↦ (g i (z.1 i)).toReal)).symm
    change Continuous (fun z : effective_domain F ↦ separableSum g z.1)
    rw [hsumEq]
    exact hsumCoe
  have hcont : ContinuousOn F (effective_domain F) := by
    intro z hz
    have hsum :
        ContinuousWithinAt
          (fun y ↦ ((f y).toReal : EReal) + separableSum g y)
          (effective_domain F)
          z := by
      -- At points of `effective_domain F`, both summands are finite and the `EReal` addition map
      -- is continuous at their value pair.
      exact
        ContinuousAt.comp₂_continuousWithinAt
          (f := fun p : EReal × EReal ↦ p.1 + p.2)
          (g := fun y ↦ ((f y).toReal : EReal))
          (h := separableSum g)
          (s := effective_domain F)
          (x := z)
          (EReal.continuousAt_add (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _)))
          (hf_cont z hz)
          (hsep_cont z hz)
    -- On `effective_domain F`, the smooth term equals its `toReal` coercion.
    refine hsum.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp [EReal.coe_toReal
          (mem_effective_domain.mp (interior_subset (hdom_subset hy))).ne
          (hmodel.f_ne_bot y)]
    · simp [EReal.coe_toReal
          (mem_effective_domain.mp (interior_subset (hdom_subset hz))).ne
          (hmodel.f_ne_bot z)]
  exact ⟨hclosed, hcont⟩

end Stationarity

section StationarityCluster

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]
variable [FiniteDimensional ℝ ((i : Fin p) → Ei i)]

variable (f : ((i : Fin p) → Ei i) → EReal)
variable (g : (i : Fin p) → Ei i → EReal)
variable (x : ℕ → (i : Fin p) → Ei i)

local notation "F" => composite_model_objective f (separableSum g)

/-- Composite-domain version of the prefix-state induction used in Theorem 14.4.  Unlike the
generic Theorem 14.3 helper, fixed block competitors can be transported along the moving bases
directly because the nonsmooth term has a product effective domain. -/
private lemma alternating_minimization_composite_prefix_state_stage_induction
    [ProperSpace ((i : Fin p) → Ei i)]
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    (hclosed : LowerSemicontinuous F)
    (hcont : ContinuousOn F (effective_domain F))
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (hlevel : ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (htraj : is_alternating_minimization_trajectory F x)
    {xBar : (i : Fin p) → Ei i}
    (hxBar : MapClusterPt xBar atTop x) :
    ∀ n ≤ p,
      ∃ ψ : ℕ → ℕ,
        StrictMono ψ ∧
          Tendsto (fun m ↦ x (ψ m)) atTop (𝓝 xBar) ∧
            Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) n)
              atTop (𝓝 xBar) ∧
              ∀ j : Fin p, j.1 < n →
                xBar j ∈ alternating_minimization_argmin F xBar j := by
  intro n
  induction n with
  | zero =>
      intro _
      rcases MapClusterPt.tendsto_subseq hxBar with ⟨ψ, hψ, hiter⟩
      refine ⟨ψ, hψ, hiter, ?_, ?_⟩
      · simpa using hiter
      · intro j hj
        exact (Nat.not_lt_zero _ hj).elim
  | succ n ihn =>
      intro hn
      have hnLt : n < p := Nat.lt_of_succ_le hn
      let i : Fin p := ⟨n, hnLt⟩
      rcases ihn (Nat.le_of_lt hnLt) with ⟨ψ, hψ, hiter, hstage, hblocks⟩
      rcases AlternatingMinimization.PrefixState.stage_succ_has_convergent_refinement
          F x hclosed hlevel htraj (ψ := ψ) hnLt with
        ⟨φ, hφ, y, hnext⟩
      let ψ' : ℕ → ℕ := ψ ∘ φ
      have hψ' : StrictMono ψ' := hψ.comp hφ
      have hiter' : Tendsto (fun m ↦ x (ψ' m)) atTop (𝓝 xBar) := by
        simpa [ψ', Function.comp] using hiter.comp hφ.tendsto_atTop
      have hstage' :
          Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) i.1)
            atTop (𝓝 xBar) := by
        simpa [ψ', Function.comp, i] using hstage.comp hφ.tendsto_atTop
      have hnext' :
          Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) (i.1 + 1))
            atTop (𝓝 y) := by
        simpa [ψ', Function.comp] using hnext
      have hxBarDom : xBar ∈ effective_domain F :=
        AlternatingMinimization.ClusterPoint.mem_effective_domain_of_initial_sublevel
          F x hclosed htraj hxBar
      have hFiter : Tendsto (fun m ↦ F (x (ψ' m))) atTop (𝓝 (F xBar)) :=
        alternating_minimization_tendsto_objective_of_tendsto
          F hcont hxBarDom hiter' (fun m ↦
            alternating_minimization_iterate_mem_effective_domain F x htraj (ψ' m))
      have hFshift : Tendsto (fun m ↦ F (x (ψ' m + 1))) atTop (𝓝 (F xBar)) :=
        alternating_minimization_shifted_objective_tendsto F x htraj hψ' hFiter
      have hFstage :
          Tendsto (fun m ↦ F (alternating_minimization_prefix_state x (ψ' m) i.1))
            atTop (𝓝 (F xBar)) :=
        alternating_minimization_tendsto_objective_of_tendsto
          F hcont hxBarDom hstage' (fun m ↦
            (alternating_minimization_prefix_state_mem_effective_domain_and_le
              F x htraj (ψ' m)
              (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ' m))
              i.1 (Nat.le_of_lt i.is_lt)).1)
      have hFnext :
          Tendsto (fun m ↦ F (alternating_minimization_prefix_state x (ψ' m) (i.1 + 1)))
            atTop (𝓝 (F xBar)) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le hFshift hFstage ?_ ?_
        · intro m
          exact alternating_minimization_next_iterate_objective_le_prefix_state
            F x htraj (ψ' m) (i.1 + 1)
        · intro m
          exact alternating_minimization_prefix_state_succ_objective_le
            F x htraj (ψ' m) i.1 i.is_lt
      have hyUpdate : Inseparable y (Function.update xBar i (y i)) :=
        alternating_minimization_prefix_state_limit_inseparable_update
          x ψ' i hstage' hnext'
      have hupdated :=
        alternating_minimization_limit_block_updated_value_eq_cluster_value
          F x hclosed hcont htraj xBar y i hxBarDom hyUpdate hnext' hFnext
      have hyArgmin : y i ∈ alternating_minimization_argmin F xBar i := by
        refine (mem_alternating_minimization_argmin_update_iff).2 ?_
        rw [isMinOn_iff]
        intro zi _
        by_cases hzi : zi ∈ effective_domain (g i)
        · have hzUpdate : Function.update xBar i zi ∈ effective_domain F :=
            composite_update_mem_effective_domain_of_block_mem
              (f := f) (g := g) hmodel i hxBarDom hzi
          have hmovingUpdate :
              ∀ m,
                Function.update
                    (alternating_minimization_prefix_state x (ψ' m) i.1)
                    i zi ∈ effective_domain F := by
            intro m
            have hmDom :=
              (alternating_minimization_prefix_state_mem_effective_domain_and_le
                F x htraj (ψ' m)
                (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ' m))
                i.1 (Nat.le_of_lt i.is_lt)).1
            exact composite_update_mem_effective_domain_of_block_mem
              (f := f) (g := g) hmodel i hmDom hzi
          exact
            alternating_minimization_limit_block_compare_with_recovered_competitor
              F x hcont htraj xBar y i hstage' hFnext hupdated.2 hzUpdate
              tendsto_const_nhds hmovingUpdate
        · have hziTop : g i zi = ⊤ := by
            exact top_unique <| not_lt.mp (by simpa [effective_domain] using hzi)
          have hrestNeBot :
              (∑ j ∈ Finset.univ.erase i,
                  g j ((Function.update xBar i zi) j)) ≠ ⊥ :=
            ereal_sum_ne_bot
              (Finset.univ.erase i)
              (fun j ↦ g j ((Function.update xBar i zi) j))
              (fun j _ ↦ (hmodel.g_proper j).ne_bot _)
          have hsumTop : separableSum g (Function.update xBar i zi) = ⊤ := by
            rw [separableSum_apply]
            have hactiveTop : g i ((Function.update xBar i zi) i) = ⊤ := by
              simpa using hziTop
            calc
              ∑ j : Fin p, g j ((Function.update xBar i zi) j) =
                  g i ((Function.update xBar i zi) i) +
                    ∑ j ∈ Finset.univ.erase i,
                      g j ((Function.update xBar i zi) j) := by
                symm
                exact
                  Finset.add_sum_erase Finset.univ
                    (fun j : Fin p ↦ g j ((Function.update xBar i zi) j))
                    (Finset.mem_univ i)
              _ = ⊤ := by
                rw [hactiveTop, EReal.top_add_of_ne_bot hrestNeBot]
          have hcompetitorTop : F (Function.update xBar i zi) = ⊤ := by
            rw [composite_model_objective_apply, hsumTop]
            exact EReal.add_top_of_ne_bot (hmodel.f_ne_bot _)
          rw [hcompetitorTop]
          exact le_top
      have hyEq : y = xBar :=
        alternating_minimization_limit_block_eq_cluster_point
          F xBar y i hxBarDom hyUpdate hyArgmin hupdated.2 hunique
      refine ⟨ψ', hψ', hiter', ?_, ?_⟩
      · simpa [hyEq] using hnext'
      · intro j hj
        by_cases hji : j = i
        · subst hji
          simpa [hyEq] using hyArgmin
        · have hjLt : j.1 < n := by
            have hjLe : j.1 ≤ n := Nat.lt_succ_iff.mp (by simpa [i] using hj)
            exact lt_of_le_of_ne hjLe (fun hEq ↦ hji (Fin.ext hEq))
          exact hblocks j hjLt

/-- Under the Theorem 14.4 hypotheses before the Chapter 3 stationarity bridge, every cluster
point of the composite alternating-minimization sequence is a coordinate-wise minimum of the
composite objective. This is the reusable bridge from the source-facing Algorithm 14.3 step data
to the canonical Chapter 14 owner `is_coordinatewise_minimum`. -/
theorem alternating_minimization_composite_cluster_point_is_coordinatewise_minimum
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (hlevel :
      ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (hx0 : x 0 ∈ effective_domain F)
    (hstep : ∀ k : ℕ, IsAlternatingMinimizationCompositeStep f g (x k) (x (k + 1)))
    (xBar : (i : Fin p) → Ei i)
    (hxBar : MapClusterPt xBar atTop x) :
    is_coordinatewise_minimum F xBar := by
  letI : NormedAddCommGroup ((i : Fin p) → Ei i) := Pi.normedAddCommGroup
  letI : NormedSpace ℝ ((i : Fin p) → Ei i) := Pi.normedSpace
  letI : ProperSpace ((i : Fin p) → Ei i) := FiniteDimensional.proper ℝ ((i : Fin p) → Ei i)
  have htraj :
      is_alternating_minimization_trajectory F x :=
    is_alternating_minimization_trajectory_of_composite_steps
      (f := f)
      (g := g)
      hx0
      hstep
  have hmodel : IsAlternatingMinimizationCompositeModel f g :=
    (hstep 0).toIsAlternatingMinimizationCompositeModel
  rcases alternating_minimization_composite_objective_regular
      (f := f)
      (g := g)
      hmodel with
    ⟨hclosed, hcont⟩
  have hxBarDom : xBar ∈ effective_domain F :=
    AlternatingMinimization.ClusterPoint.mem_effective_domain_of_initial_sublevel
      F x hclosed htraj hxBar
  rcases alternating_minimization_composite_prefix_state_stage_induction
      (f := f) (g := g) (x := x) hmodel hclosed hcont hunique hlevel htraj hxBar
      p (le_rfl : p ≤ p) with
    ⟨ψ, hψ, hiter, hstage, hblocks⟩
  refine ⟨hxBarDom, ?_⟩
  intro i
  exact (mem_alternating_minimization_argmin_iff).1 (hblocks i i.is_lt)

end StationarityCluster

section StationarityFinal

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, InnerProductSpace ℝ (Ei i)]
variable [hrawTupleFiniteDimensional : FiniteDimensional ℝ ((i : Fin p) → Ei i)]

attribute [-instance] Pi.seminormedAddCommGroup Pi.normedAddCommGroup Pi.normedSpace

local instance theorem14_4_rawTupleNormedAddCommGroup :
    NormedAddCommGroup ((i : Fin p) → Ei i) :=
  rawTupleNormedAddCommGroup

local instance theorem14_4_rawTupleNormedSpace : NormedSpace ℝ ((i : Fin p) → Ei i) :=
  rawTupleNormedSpace

local instance theorem14_4_rawTupleInnerProductSpace :
    InnerProductSpace ℝ ((i : Fin p) → Ei i) :=
  rawTupleInnerProductSpace

local instance theorem14_4_rawTupleFiniteDimensional :
    FiniteDimensional ℝ ((i : Fin p) → Ei i) :=
  rawTupleFiniteDimensional

variable (f : ((i : Fin p) → Ei i) → EReal)
variable (g : (i : Fin p) → Ei i → EReal)
variable (x : ℕ → (i : Fin p) → Ei i)

local notation "F" => composite_model_objective f (separableSum g)

-- Proof sketch: convert the Algorithm 14.3 step data to the canonical owner trajectory for `F`,
-- apply Theorem 14.3 (2) to get coordinate-wise minimality of any cluster point, and then use
-- Lemma 14.2 to translate that coordinate-wise minimality into the Chapter 3 stationarity
-- condition for `f + separableSum g`.
/-- Theorem 14.4 (2): under Assumption 14.6, if each one-block argmin set of the composite
objective `F(x) = f(x) + ∑ i, g_i(x_i)` on `dom(F)` is subsingleton, every real level set of `F`
is bounded, and `x^k` is generated by Algorithm 14.3, then every sequential limit point of `x^k`
is a stationary point of the composite problem. As in `Lemma_14_2`, the Chapter 3 owner
`is_stationary_point` is read using the canonical raw-tuple Euclidean geometry from Chapter 11,
not an arbitrary ambient inner product on `((i : Fin p) → Ei i)`. The properness input required
by Theorem 14.3 is derived here from finite dimensionality of that raw-tuple product space. -/
theorem alternating_minimization_composite_cluster_point_is_stationary
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (hlevel :
      ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (hx0 : x 0 ∈ effective_domain F)
    (hstep : ∀ k : ℕ, IsAlternatingMinimizationCompositeStep f g (x k) (x (k + 1)))
    (xBar : (i : Fin p) → Ei i)
    (hxBar : MapClusterPt xBar atTop x) :
    is_stationary_point f (separableSum g) xBar := by
  have hmodel : IsAlternatingMinimizationCompositeModel f g :=
    (hstep 0).toIsAlternatingMinimizationCompositeModel
  have hcoord :
      is_coordinatewise_minimum F xBar :=
    alternating_minimization_composite_cluster_point_is_coordinatewise_minimum
      (f := f)
      (g := g)
      (x := x)
      hunique
      hlevel
      hx0
      hstep
      xBar
      hxBar
  -- Lemma 14.2 turns coordinatewise minimality into the Chapter 3 stationarity condition.
  exact is_stationary_point_of_coordinatewise_minimum (f := f) (g := g) hmodel hcoord

end StationarityFinal

end
