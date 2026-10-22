/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_15
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_14
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_15
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_17

noncomputable section

open scoped Gradient

universe u

section

variable {E : Type u} {p : ℕ}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace DualBlockMinimizationView

section

variable {E : Type u} {p : ℕ}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Chapter 11 smooth-term view specialized to the block dual variables of Definition 12.17. -/
abbrev smoothTerm (f : E → EReal) : (Fin p → E) → EReal :=
  fun w ↦ (f∗) (∑ i : Fin p, w i)

/-- The Chapter 11 separable regularizer view specialized to the block dual variables of
Definition 12.17. -/
abbrev regularizer (g : Fin p → E → EReal) : (Fin p → E) → EReal :=
  separableSum (fun i z ↦ ((g i)∗) (-z))

/-- The Chapter 11 minimization-view objective specialized to the block dual variables of
Definition 12.17. -/
abbrev objective (f : E → EReal) (g : Fin p → E → EReal) : (Fin p → E) → EReal :=
  composite_model_objective (smoothTerm f) (regularizer g)

@[simp] lemma smoothTerm_apply
    (f : E → EReal) (v : Fin p → E) :
    smoothTerm f v = (f∗) (∑ i : Fin p, v i) :=
  rfl

@[simp] lemma regularizer_apply
    (g : Fin p → E → EReal) (v : Fin p → E) :
    regularizer g v = ∑ i : Fin p, ((g i)∗) (-v i) := by
  simp [regularizer]

@[simp] lemma objective_apply
    (f : E → EReal) (g : Fin p → E → EReal) (v : Fin p → E) :
    objective f g v = smoothTerm f v + regularizer g v :=
  rfl

end

end DualBlockMinimizationView

/-- Shared Chapter 12 bridge: the Chapter 11 minimization surface on block-dual variables is
pointwise the negation of the source-facing block dual objective `q`. -/
lemma dual_block_dual_minimization_view_apply
    (f : E → EReal) (g : Fin p → E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    (v : Fin p → E) :
    DualBlockMinimizationView.objective f g v =
      - q(f, g) v := by
  let a : EReal := (f∗) (∑ i : Fin p, v i)
  let b : EReal := ∑ i : Fin p, ((g i)∗) (-v i)
  have ha_ne_bot : a ≠ ⊥ := by
    simpa [a, conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        f
        hf_proper
        (InnerProductSpace.toDualMap ℝ E (∑ i : Fin p, v i))
  have hb_ne_bot : b ≠ ⊥ := by
    refine ereal_sum_ne_bot Finset.univ (fun i ↦ ((g i)∗) (-v i)) ?_
    intro i _
    simpa [conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        (g i)
        (hg_proper i)
        (InnerProductSpace.toDualMap ℝ E (-v i))
  have ha_top : -a ≠ ⊤ := by
    intro ha_top
    have : a = ⊥ := by
      simpa [a] using congrArg Neg.neg ha_top
    exact ha_ne_bot this
  have hneg : -(-a - b) = a + b := by
    have hraw : -(-a - b) = -(-a) + b := by
      exact EReal.neg_sub (Or.inr hb_ne_bot) (Or.inl ha_top)
    simpa [a, b] using hraw
  rw [DualBlockMinimizationView.objective_apply,
    DualBlockMinimizationView.smoothTerm_apply,
    DualBlockMinimizationView.regularizer_apply,
    dual_block_proximal_gradient_dual_objective_apply]
  change a + b = -(-a - b)
  simpa [a, b] using hneg.symm

/-- Shared Chapter 12 bridge: on the finite domain of `q`, the Chapter 11 minimization-view gap
rewrites to the source-facing scalar dual gap. -/
lemma dual_block_minimization_view_gap_toReal_eq_dual_gap
    (f : E → EReal) (g : Fin p → E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {yBar yStar : Fin p → E}
    (hyStar : yStar ∈ Λ*(f, g))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (hyBar_finite : yBar ∈ finite_domain (q(f, g))) :
    (DualBlockMinimizationView.objective f g yBar).toReal -
        (-EReal.toReal (q_opt(f, g))) =
      (q_opt(f, g) - q(f, g) yBar).toReal := by
  have hyBar_ne_top : q(f, g) yBar ≠ ⊤ := by
    exact (mem_effective_domain.mp (mem_finite_domain.mp hyBar_finite).1).ne
  have hyBar_ne_bot : q(f, g) yBar ≠ ⊥ := by
    exact (mem_finite_domain.mp hyBar_finite).2
  have hobj_real :
      DualBlockMinimizationView.objective f g yBar =
        (((-(q(f, g) yBar).toReal : ℝ)) : EReal) := by
    rw [dual_block_dual_minimization_view_apply f g hf_proper hg_proper yBar]
    simpa using congrArg Neg.neg (EReal.coe_toReal hyBar_ne_top hyBar_ne_bot).symm
  have hgap :
      (q_opt(f, g) - q(f, g) yBar).toReal =
        EReal.toReal (q_opt(f, g)) - (q(f, g) yBar).toReal :=
    dual_gap_toReal_eq_of_mem_finite_domain f g hyStar hyStar_finite hyBar_finite
  calc
    (DualBlockMinimizationView.objective f g yBar).toReal -
        (-EReal.toReal (q_opt(f, g)))
        =
      (-(q(f, g) yBar).toReal) - (-EReal.toReal (q_opt(f, g))) := by
        rw [hobj_real]
        simp
    _ = EReal.toReal (q_opt(f, g)) - (q(f, g) yBar).toReal := by
        ring
    _ = (q_opt(f, g) - q(f, g) yBar).toReal := by
        symm
        exact hgap

namespace DualBlockMinimizationView

/-- A block vector lies in the effective domain of the Chapter 11 minimization-view regularizer
exactly when each block lies in the effective domain of the corresponding conjugate penalty. -/
theorem mem_effective_domain_regularizer_iff
    (g : Fin p → E → EReal)
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {v : Fin p → E} :
    v ∈ effective_domain (regularizer g) ↔
      ∀ i : Fin p, v i ∈ effective_domain (fun z : E ↦ ((g i)∗) (-z)) := by
  constructor
  · intro hv i
    -- A single `⊤` block would force the entire separable regularizer to be `⊤`.
    refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
    intro hi_top
    have hrest_ne_bot :
        Finset.sum (Finset.univ.erase i) (fun j ↦ ((g j)∗) (-v j)) ≠ ⊥ := by
      exact
        ereal_sum_ne_bot
          (Finset.univ.erase i)
          (fun j ↦ ((g j)∗) (-v j))
          (fun j _ ↦ by
            simpa [conjugate_function_primal_apply] using
              conjugate_function_ne_bot_of_proper
                (g j)
                (hg_proper j)
                (InnerProductSpace.toDualMap ℝ E (-v j)))
    have hsum :
        Finset.sum Finset.univ (fun j ↦ ((g j)∗) (-v j)) =
          ((g i)∗) (-v i) + Finset.sum (Finset.univ.erase i) (fun j ↦ ((g j)∗) (-v j)) := by
      symm
      exact Finset.add_sum_erase Finset.univ (fun j ↦ ((g j)∗) (-v j)) (Finset.mem_univ i)
    have hreg_top : regularizer g v = ⊤ := by
      rw [regularizer_apply, hsum, hi_top, EReal.top_add_of_ne_bot hrest_ne_bot]
    exact (lt_top_iff_ne_top.mp (mem_effective_domain.mp hv)) hreg_top
  · intro hv
    -- Coordinatewise finiteness makes the finite separable sum stay below `⊤`.
    rw [mem_effective_domain, regularizer_apply]
    exact
      ereal_sum_lt_top
        Finset.univ
        (fun i ↦ ((g i)∗) (-v i))
        (fun i _ ↦ mem_effective_domain.mp (hv i))

end DualBlockMinimizationView

/-- Helper for DualBlockMinimizationView: once the aggregated smooth conjugate value and every
coordinatewise conjugate block are finite above, the full source-facing dual value `q(v)` is
finite. -/
lemma dual_value_mem_finite_domain_of_smooth_conjugate_mem_effective_domain
    (f : E → EReal) (g : Fin p → E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {v : Fin p → E}
    (hsmooth : (∑ i : Fin p, v i) ∈ effective_domain (fun z : E ↦ (f∗) z))
    (hv : ∀ i : Fin p, v i ∈ effective_domain (fun z : E ↦ ((g i)∗) (-z))) :
    v ∈ finite_domain (q(f, g)) := by
  let a : EReal := (f∗) (∑ i : Fin p, v i)
  let b : EReal := DualBlockMinimizationView.regularizer g v
  have ha_ne_bot : a ≠ ⊥ := by
    -- Properness rules out `⊥` for the smooth conjugate block at every aggregated dual vector.
    simpa [a, conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        f
        hf_proper
        (InnerProductSpace.toDualMap ℝ E (∑ i : Fin p, v i))
  have ha_lt_top : a < ⊤ := by
    -- The helper hypothesis contributes exactly the missing upper finiteness of the smooth term.
    simpa [a] using mem_effective_domain.mp hsmooth
  have hb_eff : v ∈ effective_domain (DualBlockMinimizationView.regularizer g) := by
    -- The coordinatewise conjugate-domain hypotheses exactly reassemble into
    -- regularizer finiteness.
    exact
      (DualBlockMinimizationView.mem_effective_domain_regularizer_iff
        g hg_proper).2 hv
  have hb_lt_top : b < ⊤ := by
    simpa [b] using mem_effective_domain.mp hb_eff
  have hb_ne_bot : b ≠ ⊥ := by
    -- Properness of each block penalty keeps every conjugate term, hence their finite sum, above
    -- `⊥`.
    rw [show b = ∑ i : Fin p, ((g i)∗) (-v i) by simp [b]]
    refine ereal_sum_ne_bot Finset.univ (fun i ↦ ((g i)∗) (-v i)) ?_
    intro i _
    simpa [conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        (g i)
        (hg_proper i)
        (InnerProductSpace.toDualMap ℝ E (-v i))
  have hobj_ne_bot : DualBlockMinimizationView.objective f g v ≠ ⊥ := by
    -- The minimization-view objective is a sum of two non-`⊥` terms.
    rw [DualBlockMinimizationView.objective_apply]
    change a + b ≠ ⊥
    exact EReal.add_ne_bot_iff.mpr ⟨ha_ne_bot, hb_ne_bot⟩
  have hobj_ne_top : DualBlockMinimizationView.objective f g v ≠ ⊤ := by
    -- The same decomposition stays below `⊤` because both summands are finite above.
    rw [DualBlockMinimizationView.objective_apply]
    change a + b ≠ ⊤
    exact ne_of_lt <| EReal.add_lt_top (ne_of_lt ha_lt_top) (ne_of_lt hb_lt_top)
  have hq_ne_top : q(f, g) v ≠ ⊤ := by
    -- Route correction: rather than expanding `q` directly, transfer non-`⊥` of `-q` through the
    -- already-proved identity `objective = -q`.
    intro hq_top
    have hobj_bot : DualBlockMinimizationView.objective f g v = ⊥ := by
      rw [dual_block_dual_minimization_view_apply f g hf_proper hg_proper v, hq_top]
      simp
    exact hobj_ne_bot hobj_bot
  have hq_ne_bot : q(f, g) v ≠ ⊥ := by
    -- The same transport turns non-`⊤` of the minimization view into non-`⊥` of `q`.
    intro hq_bot
    have hobj_top : DualBlockMinimizationView.objective f g v = ⊤ := by
      rw [dual_block_dual_minimization_view_apply f g hf_proper hg_proper v, hq_bot]
      simp
    exact hobj_ne_top hobj_top
  exact
    mem_finite_domain.mpr
      ⟨mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hq_ne_top), hq_ne_bot⟩

/-- DualBlockMinimizationView finite-dimensional repair: if every block dual term `g_i^*(-v_i)` is
finite above, then the
source-facing dual objective value `q(v)` is finite. -/
lemma dual_value_mem_finite_domain_of_coordinatewise_dual_term
    [FiniteDimensional ℝ E]
    (σ : PosReal) (f : E → EReal) (g : Fin p → E → EReal)
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    {v : Fin p → E}
    (hv : ∀ i : Fin p, v i ∈ effective_domain (fun z : E ↦ ((g i)∗) (-z))) :
    v ∈ finite_domain (q(f, g)) := by
  have hconj_finite :
      ∀ z : E, (f∗) z ≠ ⊥ ∧ (f∗) z < ⊤ := by
    intro z
    have hfin :=
      conjugate_function_finite_of_proper_closed_strongConvexOn
        (σ : ℝ)
        σ.2
        f
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex
        (InnerProductSpace.toDual ℝ E z)
    simpa [conjugate_function_strongDual, conjugate_function_primal_apply, conjugate_function]
      using hfin
  have hsmooth :
      (∑ i : Fin p, v i) ∈ effective_domain (fun z : E ↦ (f∗) z) := by
    exact mem_effective_domain.mpr (hconj_finite _).2
  exact
    dual_value_mem_finite_domain_of_smooth_conjugate_mem_effective_domain
      f
      g
      h_problem.toIsProperExtendedRealFunction
      h_problem.g_proper
      hsmooth
      hv

/-- Shared Chapter 12 bridge: finiteness of the source-facing dual value `q(v)` forces each block
dual term `g_i^*(-v_i)` to be finite above. -/
lemma block_dual_term_mem_effective_domain_of_mem_finite_domain
    (f : E → EReal) (g : Fin p → E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {v : Fin p → E} (hv : v ∈ finite_domain (q(f, g))) (i : Fin p) :
    v i ∈ effective_domain (fun z : E ↦ ((g i)∗) (-z)) := by
  let a : EReal := (f∗) (∑ j : Fin p, v j)
  have ha_ne_bot : a ≠ ⊥ := by
    -- Properness already keeps the smooth conjugate block away from `⊥`.
    simpa [a, conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        f
        hf_proper
        (InnerProductSpace.toDualMap ℝ E (∑ j : Fin p, v j))
  have hobj_ne_top : DualBlockMinimizationView.objective f g v ≠ ⊤ := by
    -- Rewriting `objective = -q` turns the `⊥`-exclusion for `q` into the needed `⊤`-exclusion.
    rw [dual_block_dual_minimization_view_apply f g hf_proper hg_proper v]
    simpa [EReal.neg_eq_top_iff] using (mem_finite_domain.mp hv).2
  have hreg_ne_top : DualBlockMinimizationView.regularizer g v ≠ ⊤ := by
    intro hreg_top
    have hobj_top : DualBlockMinimizationView.objective f g v = ⊤ := by
      have hreg_top' : ∑ j : Fin p, ((g j)∗) (-v j) = ⊤ := by
        simpa [DualBlockMinimizationView.regularizer_apply] using hreg_top
      rw [DualBlockMinimizationView.objective_apply,
        DualBlockMinimizationView.smoothTerm_apply,
        DualBlockMinimizationView.regularizer_apply]
      rw [hreg_top', EReal.add_top_of_ne_bot ha_ne_bot]
    exact hobj_ne_top hobj_top
  have hreg :
      v ∈ effective_domain (DualBlockMinimizationView.regularizer g) := by
    -- Finiteness of the whole minimization-view objective forces the regularizer below `⊤`.
    exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hreg_ne_top)
  -- Once the regularizer is finite, the coordinatewise bridge recovers the requested block.
  exact
    (DualBlockMinimizationView.mem_effective_domain_regularizer_iff
      g hg_proper).1 hreg i

/-- Shared Chapter 12 bridge: the initial dual point lies in the effective domain of the Chapter
11 separable minimization-view regularizer. -/
lemma initial_dual_point_mem_effective_domain_minimization_view
    (f : E → EReal) (g : Fin p → E → EReal)
    (y0 : Fin p → E)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    (hy0_finite : y0 ∈ finite_domain (q(f, g))) :
    y0 ∈ effective_domain (DualBlockMinimizationView.regularizer g) := by
  have hy0_blocks :
      ∀ i : Fin p, y0 i ∈ effective_domain (fun z : E ↦ ((g i)∗) (-z)) := by
    -- Recover each coordinatewise conjugate-domain condition from the finite dual value.
    intro i
    exact
      block_dual_term_mem_effective_domain_of_mem_finite_domain
        f
        g
        hf_proper
        hg_proper
        hy0_finite
        i
  -- Reassemble the separable regularizer domain from the blockwise data.
  exact
    (DualBlockMinimizationView.mem_effective_domain_regularizer_iff
      g hg_proper).2 hy0_blocks

/-- Helper for DualBlockMinimizationView: proximal membership already yields the effective-domain
inclusion and affine support inequality, without first upgrading the proximal set to a singleton.
-/
private lemma memProx_implies_effectiveDomain_and_innerSupport
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (x u : E) (hu : u ∈ prox[f] x) :
    u ∈ effective_domain f ∧
      ∀ y ∈ effective_domain f, ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤ f y - f u := by
  -- Route correction: use the original convex-perturbation proof directly from proximal
  -- membership, rather than trying to recover a singleton description first.
  have hu_eff : u ∈ effective_domain f := mem_effective_domain_of_mem_prox f hf_proper x hu
  refine ⟨hu_eff, ?_⟩
  intro y hy_eff
  by_cases hyu : y = u
  · -- At `y = u`, the support inequality is the trivial `0 ≤ 0`.
    subst y
    have hzero : ((0 : ℝ) : EReal) ≤ f u - f u := by
      have hsupport_add :
          ((0 : ℝ) : EReal) + f u ≤ f u := by
        simp
      exact (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
        (.inl (mem_effective_domain.mp hu_eff).ne)).2 hsupport_add
    simpa using hzero
  · set A : ℝ := inner ℝ (x - u) (y - u) - ((f y).toReal - (f u).toReal)
    set B : ℝ := (1 / 2 : ℝ) * ‖y - u‖ ^ (2 : ℕ)
    have hA_le_tB : ∀ {t : ℝ}, 0 < t → t ≤ 1 → A ≤ t * B := by
      intro t ht_pos ht_one
      have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_pos.le, ht_one⟩
      let z : E := t • y + (1 - t) • u
      have hz_eff : z ∈ effective_domain f :=
        combo_mem_effective_domain_of_is_convex_function hf_convex hy_eff hu_eff ht_mem
      have hy_val :
          f y = (((f y).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (mem_effective_domain.mp hy_eff).ne (hf_proper.ne_bot y)).symm
      have hu_min : proximal_objective f x u ≤ proximal_objective f x z := by
        -- Unfold the proximal membership into minimality of the penalized objective.
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
        exact hu z
      have hu_val :
          f u = (((f u).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
      have hz_val :
          f z = (((f z).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hf_proper.ne_bot z)).symm
      have hu_obj_real :
          (f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤
            (f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
        -- Convert proximal minimality from `EReal` to the real line at finite points.
        have hu_min' := hu_min
        rw [proximal_objective_apply, proximal_objective_apply, hu_val, hz_val] at hu_min'
        have hu_min'' :
            ((((f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
              ((((f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
          simpa [EReal.coe_add] using hu_min'
        exact EReal.coe_le_coe_iff.mp hu_min''
      have hz_convE :
          f z ≤ (t : EReal) * f y + ((1 - t : ℝ) : EReal) * f u := by
        -- Convexity controls the objective along the segment from `u` to `y`.
        simpa [z, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
          (is_convex_function_iff_segment_ineq.mp hf_convex) y hy_eff u hu_eff ht_mem
      have hz_conv :
          (f z).toReal ≤ t * (f y).toReal + (1 - t) * (f u).toReal := by
        have hz_convE' := hz_convE
        rw [hz_val, hy_val, hu_val] at hz_convE'
        have hz_convE'' :
            (((f z).toReal : ℝ) : EReal) ≤
              ((((t * (f y).toReal + (1 - t) * (f u).toReal : ℝ)) : EReal)) := by
          simpa [EReal.coe_add, EReal.coe_mul] using hz_convE'
        exact EReal.coe_le_coe_iff.mp hz_convE''
      have hz_sub : z - u = t • (y - u) := by
        have hz_def : z = u + t • (y - u) := by
          dsimp [z]
          rw [smul_sub]
          module
        calc
          z - u = (u + t • (y - u)) - u := by rw [hz_def]
          _ = t • (y - u) := by
            abel
      have hinner_smul :
          inner ℝ (u - x) (t • (y - u)) = -t * inner ℝ (x - u) (y - u) := by
        have hinner_base :
            inner ℝ (u - x) (y - u) = -inner ℝ (x - u) (y - u) := by
          have hneg : u - x = -(x - u) := by
            abel
          rw [hneg, inner_neg_left]
        rw [inner_smul_right]
        rw [hinner_base]
        ring
      have hnorm_smul :
          (1 / 2 : ℝ) * ‖t • (y - u)‖ ^ (2 : ℕ) = t ^ (2 : ℕ) * B := by
        dsimp [B]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_pos.le]
        ring
      have hz_quad :
          (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) =
            (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) - t * inner ℝ (x - u) (y - u) +
              t ^ (2 : ℕ) * B := by
        -- The quadratic identity isolates the linear support term plus a `t^2` remainder.
        calc
          (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) =
              (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) + inner ℝ (u - x) (z - u) +
                (1 / 2 : ℝ) * ‖z - u‖ ^ (2 : ℕ) := quadratic_translate_identity x u z
          _ = (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) - t * inner ℝ (x - u) (y - u) +
                t ^ (2 : ℕ) * B := by
            rw [hz_sub, hinner_smul, hnorm_smul]
            ring
      have hstep :
          (f u).toReal + inner ℝ (x - u) (y - u) - (f y).toReal ≤ t * B := by
        nlinarith [hu_obj_real, hz_conv, hz_quad]
      simpa [A, B, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hstep
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      positivity
    have hA_nonpos : A ≤ 0 := by
      by_contra hA
      have hA_pos : 0 < A := lt_of_not_ge hA
      let t : ℝ := min 1 (A / (B + 1))
      have ht_pos : 0 < t := by
        dsimp [t]
        refine lt_min (by norm_num) ?_
        have hden_pos : 0 < B + 1 := by
          linarith
        exact div_pos hA_pos hden_pos
      have ht_one : t ≤ 1 := by
        dsimp [t]
        exact min_le_left _ _
      have hAt : A ≤ t * B := hA_le_tB ht_pos ht_one
      have ht_bound : t ≤ A / (B + 1) := by
        dsimp [t]
        exact min_le_right _ _
      have hmul_bound : t * B ≤ A * B / (B + 1) := by
        have := mul_le_mul_of_nonneg_right ht_bound hB_nonneg
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have hstrict : A * B / (B + 1) < A := by
        have hden_pos : 0 < B + 1 := by
          linarith
        field_simp [hden_pos.ne']
        nlinarith [hA_pos, hB_nonneg]
      exact (not_lt_of_ge (le_trans hAt hmul_bound)) hstrict
    have hreal :
        inner ℝ (x - u) (y - u) ≤ (f y).toReal - (f u).toReal := by
      dsimp [A] at hA_nonpos
      linarith
    have hsupport_add_real :
        inner ℝ (x - u) (y - u) + (f u).toReal ≤ (f y).toReal := by
      linarith
    have hsupport_addE :
        ((((inner ℝ (x - u) (y - u) + (f u).toReal : ℝ)) : EReal)) ≤
          (((f y).toReal : ℝ) : EReal) := EReal.coe_le_coe hsupport_add_real
    have hu_val :
        f u = (((f u).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
    have hy_val :
        f y = (((f y).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hy_eff).ne (hf_proper.ne_bot y)).symm
    have hsupport_add :
        (((inner ℝ (x - u) (y - u) : ℝ)) : EReal) + f u ≤ f y := by
      rw [hu_val, hy_val]
      simpa [EReal.coe_add] using hsupport_addE
    exact (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
      (.inl (mem_effective_domain.mp hu_eff).ne)).2 hsupport_add

/-- Helper for DualBlockMinimizationView: membership in a scaled proximal set yields the
effective-domain inclusion and affine support inequality for the unscaled block penalty. -/
private lemma memScaledProx_implies_effectiveDomain_and_innerSupport
    (g : E → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g)
    (c : PosReal) {x u : E}
    (hu : u ∈ prox[((c : EReal) • g)] x) :
    u ∈ effective_domain g ∧
      ∀ y ∈ effective_domain g,
        ((inner ℝ ((1 / c : ℝ) • (x - u)) (y - u) : ℝ) : EReal) ≤ g y - g u := by
  let gScaled : E → EReal := ((c : EReal) • g)
  have hgScaled_proper : IsProperExtendedRealFunction gScaled := by
    refine ⟨?_, ?_⟩
    · intro z
      dsimp [gScaled]
      exact
        (EReal.mul_ne_bot _ _).2
          ⟨Or.inl (EReal.coe_ne_bot _),
            Or.inr (hg_proper.ne_bot z),
            Or.inl (EReal.coe_ne_top _),
            Or.inl (by exact_mod_cast c.2.le : (0 : EReal) ≤ (c : ℝ))⟩
    · rcases hg_proper.effective_domain_nonempty with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rw [mem_effective_domain]
      dsimp [gScaled]
      exact
        lt_top_iff_ne_top.mpr <|
          (EReal.mul_ne_top _ _).2
            ⟨Or.inl (EReal.coe_ne_bot _),
              Or.inl (by exact_mod_cast c.2.le : (0 : EReal) ≤ (c : ℝ)),
              Or.inl (EReal.coe_ne_top _),
              Or.inr (mem_effective_domain.mp hz).ne⟩
  have hgScaled_convex : is_convex_function gScaled := by
    rw [is_convex_function]
    intro p hp q hq a b ha hb hab
    have hp0 : gScaled p.1 ≤ (p.2 : EReal) := by
      simpa [Set.mem_setOf_eq, gScaled] using hp
    have hq0 : gScaled q.1 ≤ (q.2 : EReal) := by
      simpa [Set.mem_setOf_eq, gScaled] using hq
    have hc_pos : (0 : EReal) < (c : ℝ) := by
      exact_mod_cast (show 0 < (c : ℝ) from c.2)
    have hc_top : ((c : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    have hp' : (p.1, p.2 / (c : ℝ)) ∈ {r : E × ℝ | g r.1 ≤ (r.2 : EReal)} := by
      rw [Set.mem_setOf_eq, EReal.coe_div]
      dsimp [gScaled] at hp0
      exact (EReal.le_div_iff_mul_le hc_pos hc_top).2 (by simpa [mul_comm] using hp0)
    have hq' : (q.1, q.2 / (c : ℝ)) ∈ {r : E × ℝ | g r.1 ≤ (r.2 : EReal)} := by
      rw [Set.mem_setOf_eq, EReal.coe_div]
      dsimp [gScaled] at hq0
      exact (EReal.le_div_iff_mul_le hc_pos hc_top).2 (by simpa [mul_comm] using hq0)
    have hcombo := hg_convex hp' hq' ha hb hab
    have hdivr :
        a * (p.2 / (c : ℝ)) + b * (q.2 / (c : ℝ)) =
          (a * p.2 + b * q.2) / (c : ℝ) := by
      field_simp [(show 0 < (c : ℝ) from c.2).ne']
    have hcombo' :
        g (a • p.1 + b • q.1) ≤ ((((a * p.2 + b * q.2) / (c : ℝ) : ℝ)) : EReal) := by
      simpa [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hdivr] using hcombo
    rw [Set.mem_setOf_eq]
    dsimp [gScaled]
    rw [EReal.coe_div] at hcombo'
    have hscaled := (EReal.le_div_iff_mul_le hc_pos hc_top).1 hcombo'
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hscaled
  rcases memProx_implies_effectiveDomain_and_innerSupport
      gScaled hgScaled_proper hgScaled_convex x u hu with
    ⟨hu_eff_scaled, hsupport_scaled⟩
  have hu_eff : u ∈ effective_domain g := by
    rw [mem_effective_domain] at hu_eff_scaled ⊢
    refine lt_top_iff_ne_top.mpr ?_
    intro hgu_top
    have hscaled_top : gScaled u = ⊤ := by
      dsimp [gScaled]
      rw [hgu_top]
      exact EReal.coe_mul_top_of_pos c.2
    exact (lt_irrefl (⊤ : EReal)) (hscaled_top ▸ hu_eff_scaled)
  refine ⟨hu_eff, ?_⟩
  intro y hy
  have hy_scaled : y ∈ effective_domain gScaled := by
    rw [mem_effective_domain] at hy ⊢
    dsimp [gScaled]
    exact
      lt_top_iff_ne_top.mpr <|
        (EReal.mul_ne_top _ _).2
          ⟨Or.inl (EReal.coe_ne_bot _),
            Or.inl (by exact_mod_cast c.2.le : (0 : EReal) ≤ (c : ℝ)),
            Or.inl (EReal.coe_ne_top _),
            Or.inr hy.ne⟩
  have hu_val :
      g u = (((g u).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hg_proper.ne_bot u)).symm
  have hy_val :
      g y = (((g y).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hy).ne (hg_proper.ne_bot y)).symm
  have hu_scaled_val :
      gScaled u = (((((c : ℝ) * (g u).toReal : ℝ)) : ℝ) : EReal) := by
    have htoReal : (gScaled u).toReal = (c : ℝ) * (g u).toReal := by
      change (((c : EReal) * g u).toReal) = (c : ℝ) * (g u).toReal
      rw [EReal.toReal_mul, EReal.toReal_coe]
    calc
      gScaled u = (((gScaled u).toReal : ℝ) : EReal) := by
        rw [EReal.coe_toReal (mem_effective_domain.mp hu_eff_scaled).ne (hgScaled_proper.ne_bot u)]
      _ = (((((c : ℝ) * (g u).toReal : ℝ)) : ℝ) : EReal) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) htoReal
  have hy_scaled_val :
      gScaled y = (((((c : ℝ) * (g y).toReal : ℝ)) : ℝ) : EReal) := by
    have htoReal : (gScaled y).toReal = (c : ℝ) * (g y).toReal := by
      change (((c : EReal) * g y).toReal) = (c : ℝ) * (g y).toReal
      rw [EReal.toReal_mul, EReal.toReal_coe]
    calc
      gScaled y = (((gScaled y).toReal : ℝ) : EReal) := by
        rw [EReal.coe_toReal (mem_effective_domain.mp hy_scaled).ne (hgScaled_proper.ne_bot y)]
      _ = (((((c : ℝ) * (g y).toReal : ℝ)) : ℝ) : EReal) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) htoReal
  have hsupport_real :
      inner ℝ (x - u) (y - u) ≤ (c : ℝ) * ((g y).toReal - (g u).toReal) := by
    have hsupportE := hsupport_scaled y hy_scaled
    rw [hu_scaled_val, hy_scaled_val] at hsupportE
    have hsupportE' :
        (((inner ℝ (x - u) (y - u) : ℝ)) : EReal) ≤
          ((((c : ℝ) * ((g y).toReal - (g u).toReal) : ℝ)) : EReal) := by
      simpa [EReal.coe_sub, mul_sub_left_distrib] using hsupportE
    exact EReal.coe_le_coe_iff.mp hsupportE'
  have hsupport_div :
      inner ℝ ((1 / c : ℝ) • (x - u)) (y - u) ≤ (g y).toReal - (g u).toReal := by
    have hscaled :
        (1 / c : ℝ) * inner ℝ (x - u) (y - u) ≤
          (1 / c : ℝ) * ((c : ℝ) * ((g y).toReal - (g u).toReal)) := by
      exact
        mul_le_mul_of_nonneg_left hsupport_real
          (by
            simpa [one_div] using
              inv_nonneg.mpr (show 0 ≤ (c : ℝ) by exact le_of_lt c.2))
    have hcancel :
        (1 / c : ℝ) * ((c : ℝ) * ((g y).toReal - (g u).toReal)) =
          (g y).toReal - (g u).toReal := by
      field_simp [show (c : ℝ) ≠ 0 by exact_mod_cast c.2.ne']
    calc
      inner ℝ ((1 / c : ℝ) • (x - u)) (y - u)
          = (1 / c : ℝ) * inner ℝ (x - u) (y - u) := by
            simpa using inner_smul_left (x - u) (y - u) (1 / c : ℝ)
      _ ≤ (1 / c : ℝ) * ((c : ℝ) * ((g y).toReal - (g u).toReal)) := hscaled
      _ = (g y).toReal - (g u).toReal := hcancel
  have hsupport_realE :
      (((inner ℝ ((1 / c : ℝ) • (x - u)) (y - u) : ℝ)) : EReal) ≤
        (((((g y).toReal - (g u).toReal : ℝ)) : EReal)) :=
    EReal.coe_le_coe hsupport_div
  rw [hy_val, hu_val]
  simpa [EReal.coe_sub] using hsupport_realE

/-- Shared Chapter 12 bridge: a single primal-representation DBPG block update preserves the
finite domain of the source-facing dual objective `q`. -/
lemma dual_block_primal_y_step_mem_finite_domain
    [FiniteDimensional ℝ E]
    (σ : PosReal) (f : E → EReal) (g : Fin p → E → EReal)
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    {xTilde : E} {v yNext : Fin p → E} {i : Fin p}
    (hv : v ∈ finite_domain (q(f, g)))
    (hyNext : yNext ∈ dual_block_proximal_gradient_primal_y_step g σ xTilde v i) :
    yNext ∈ finite_domain (q(f, g)) := by
  rcases (mem_dual_block_proximal_gradient_primal_y_step_iff.mp hyNext) with
    ⟨yiNext, hyiNext, hyupdate⟩
  have hcoords :
      ∀ j : Fin p, yNext j ∈ effective_domain (fun z : E ↦ ((g j)∗) (-z)) := by
    intro j
    by_cases hji : j = i
    · subst j
      rcases (mem_dual_proximal_gradient_primal_y_step_iff.mp hyiNext) with
        ⟨u, hu, hyiEq⟩
      have hp_support :=
        memScaledProx_implies_effectiveDomain_and_innerSupport
          (g i)
          (h_problem.g_proper i)
          (h_problem.g_convex i)
          (σ⁻¹)
          hu
      rcases hp_support with ⟨hp_eff, hsupport⟩
      have hσ_ne : (σ : ℝ) ≠ 0 := ne_of_gt σ.2
      have hvector :
          (1 / (σ⁻¹ : PosReal) : ℝ) •
              ((xTilde - ((σ⁻¹ : PosReal) : ℝ) • v i) - u) =
            -yiNext := by
        -- Normalize the active-block proximal displacement to the final dual variable `-yiNext`.
        rw [hyiEq]
        have hσ :
            (1 / (σ⁻¹ : PosReal) : ℝ) = (σ : ℝ) := by
          change (1 : ℝ) / ((σ : ℝ)⁻¹) = (σ : ℝ)
          field_simp [hσ_ne]
        rw [hσ, smul_sub, smul_sub, smul_smul]
        have hcancel : (σ : ℝ) * (((σ⁻¹ : PosReal) : ℝ)) = 1 := by
          change (σ : ℝ) * ((σ : ℝ)⁻¹) = 1
          field_simp [hσ_ne]
        rw [hcancel, one_smul]
        simp [LinearMap.id_apply]
        abel
      have hsub :
          (InnerProductSpace.toDualMap ℝ E (-yiNext) : Module.Dual ℝ E) ∈
            subdifferential (g i) u := by
        -- Convert the scaled proximal support inequality into an unscaled subgradient witness.
        have hshift : (u - yiNext) - u = -yiNext := by
          abel
        have hsupport_shift :
            u ∈ effective_domain (g i) ∧
              ∀ y ∈ effective_domain (g i),
                ((inner ℝ ((u - yiNext) - u) (y - u) : ℝ) : EReal) ≤ g i y - g i u := by
          refine ⟨hp_eff, ?_⟩
          intro y hy
          calc
            ((inner ℝ ((u - yiNext) - u) (y - u) : ℝ) : EReal)
                = ((inner ℝ (-yiNext) (y - u) : ℝ) : EReal) := by
                    rw [hshift]
            _ =
                ((inner ℝ
                    ((1 / (σ⁻¹ : PosReal) : ℝ) •
                      ((xTilde - ((σ⁻¹ : PosReal) : ℝ) • v i) - u))
                    (y - u) : ℝ) : EReal) := by
                      rw [← hvector]
            _ ≤ g i y - g i u := hsupport y hy
        have hstrong_raw :
            InnerProductSpace.toDualMap ℝ E ((u - yiNext) - u) ∈
              strongDualSubdifferential (g i) u := by
          exact
            (toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le
              (g i)
              (h_problem.g_proper i)
              (u - yiNext)
              u).2 hsupport_shift
        have hstrong :
            InnerProductSpace.toDualMap ℝ E (-yiNext) ∈ strongDualSubdifferential (g i) u := by
          simpa [sub_eq_add_neg] using hstrong_raw
        simpa using (mem_strongDualSubdifferential.mp hstrong)
      have hyi_eff :
          yiNext ∈ effective_domain (fun z : E ↦ ((g i)∗) (-z)) := by
        -- A subgradient witness at the active proximal point places `-yiNext` in the conjugate
        -- domain.
        simpa [conjugate_function_primal_apply] using
          mem_effective_domain_conjugate_function_of_mem_subdifferential
            (g i)
            (h_problem.g_proper i)
            hsub
      have hsame : yNext i = yiNext := by
        -- The selected coordinate is exactly the updated active block.
        have hsame' := congrArg (fun y : Fin p → E ↦ y i) hyupdate
        simpa [block_coordinate_update_apply_same] using hsame'.symm
      simpa [hsame] using hyi_eff
    · have hrest : yNext j = v j := by
        -- All inactive coordinates remain unchanged by the block update.
        have hrest' := congrArg (fun y : Fin p → E ↦ y j) hyupdate
        have hupdatej : block_coordinate_update v i (yiNext - v i) j = v j := by
          simp [block_coordinate_update_apply_ne, hji]
        exact hrest'.symm.trans hupdatej
      simpa [hrest] using
        block_dual_term_mem_effective_domain_of_mem_finite_domain
          f
          g
          h_problem.toIsProperExtendedRealFunction
          h_problem.g_proper
          hv
          j
  -- Reassemble the coordinatewise conjugate-domain invariant into finiteness of the full dual
  -- value.
  exact
    dual_value_mem_finite_domain_of_coordinatewise_dual_term
      σ
      f
      g
      h_problem
      hcoords

end
