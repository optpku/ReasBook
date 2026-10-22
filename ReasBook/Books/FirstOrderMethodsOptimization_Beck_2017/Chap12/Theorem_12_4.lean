/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient
open InnerProductSpace (toDualMap)

universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V)

-- Local declaration justification (source-local notation): the Chapter 12 split dual terms and
-- objective appear in every theorem statement in this file, and the notation only abbreviates
-- existing canonical owners instead of introducing a parallel public API.
local notation "F" => fun z : V ↦ dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ V z)
local notation "G" => fun z : V ↦ dual_based_proximal_gradient_dual_G_term g (toDualMap ℝ V z)
local notation "q" => dual_based_proximal_gradient_lagrange_dual_objective_primal f g A
local notation "qOpt" => dual_based_proximal_gradient_lagrange_dual_problem_value f g A

/- Theorem 12.4 is `bridge/view` in the Chapter 12 dual proximal-gradient API.

Domain sampling against the surrounding project identifies:
- `is_dual_based_proximal_gradient_dual_trajectory` from Algorithm 12.1 as the owner of the dual
  iterates;
- `dual_based_proximal_gradient_lagrange_dual_objective_primal` and
  `dual_based_proximal_gradient_lagrange_dual_problem_value` from Definition 12.4 as the owners of
  `q` and `qOpt`; and
- `dual_based_proximal_gradient_dual_F_term` and `dual_based_proximal_gradient_dual_G_term` from
  Definition 12.5 as the source-facing owners of the split dual terms, viewed on the primal
  dual-variable space through `toDualMap`;
- `proximal_gradient_convex_objective_gap_le` from Theorem 10.21 as the generic upstream
  `O(1 / k)` proximal-gradient objective-gap theorem.

The source theorem is therefore best kept as the Chapter 12 specialization of that generic owner,
stated directly on the canonical dual-trajectory owner and the canonical dual objective/value
owners, reusing the chapter’s canonical `F`/`G` split-term surface instead of duplicating it with
anonymous lambdas. Its primitive data are only the regularity hypotheses needed to regard the
dual split terms as a Chapter 10 convex composite smooth minimization problem together with an
explicit optimal dual witness `hyStar`; the qualification and attainment package from
`IsDualBasedProximalGradientProblem` is derived API and does not belong in this rate statement. -/

-- Proof sketch: rewrite the Chapter 12 dual maximization objective as `q = -(F + G)`. The
-- `hf_strong` supplies the smooth term `F`, while `hg_proper` and `hg_convex`
-- supply the nonsmooth term `G`. Apply the generic constant-stepsize proximal-gradient
-- `O(1 / k)` objective-gap bound to the dual trajectory `htraj`, then translate the estimate back
-- to the Chapter 12 dual gap `qOpt - q(y^k)`.
/- Theorem 12.4: if the Chapter 12 dual split terms satisfy the primitive proper/convex
and strong-convexity hypotheses needed for the Chapter 10 convex proximal-gradient rate theorem,
then every positive dual proximal-gradient iterate satisfies
`qOpt - q(y^k) ≤ L ‖y^0 - y^*‖^2 / (2 k)` for any optimal dual solution `y^*`, where
`q(y) = -f*(Aᵀ y) - g*(-y)`. -/

/-- Helper for Theorem 12.4: the primal-space dual objective is the Chapter 12 dual owner
evaluated at the Riesz image `toDualMap ℝ V y`. -/
lemma primalDualObjective_eq_dualOwner
    (y : V) :
    q y =
      dual_based_proximal_gradient_lagrange_dual_objective f g A (toDualMap ℝ V y) := by
  -- Rewrite the source-facing primal formula through the canonical dual-space owner.
  calc
    q y =
        -dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ V y) -
          dual_based_proximal_gradient_dual_G_term g (toDualMap ℝ V y) := by
          rw [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply,
            ← dual_based_proximal_gradient_dual_F_primal_apply (f := f) (A := A) (y := y),
            ← dual_based_proximal_gradient_dual_G_primal_apply (g := g) (y := y)]
    _ =
        dual_based_proximal_gradient_lagrange_dual_objective
          f g A (toDualMap ℝ V y) := by
          rw [dual_based_proximal_gradient_lagrange_dual_objective_apply,
            dual_based_proximal_gradient_dual_F_term_apply,
            dual_based_proximal_gradient_dual_G_term_apply]

/-- Helper for Theorem 12.4: every primal-space dual value is bounded above by `qOpt`. -/
lemma dualObjective_le_dualProblemValue
    (y : V) :
    q y ≤ qOpt := by
  -- Compare `q y` with the defining supremum of the canonical dual owner.
  rw [dual_based_proximal_gradient_lagrange_dual_problem_value_eq_sSup]
  calc
    q y =
        dual_based_proximal_gradient_lagrange_dual_objective
          f g A (toDualMap ℝ V y) :=
      primalDualObjective_eq_dualOwner (f := f) (g := g) (A := A) y
    _ ≤
        sSup
          (Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A)) := by
          exact le_sSup ⟨toDualMap ℝ V y, rfl⟩

/-- Helper for Theorem 12.4: the Chapter 10 minimization surface `composite_model_objective F G`
is exactly the negated Chapter 12 dual objective `-q`. -/
lemma dualCompositeObjective_eq_negDualObjective
    (σ : PosReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g)
    (y : V) :
    composite_model_objective F G y = -q y := by
  have hF_ne_bot :
      dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ V y) ≠ ⊥ := by
    rw [dual_based_proximal_gradient_dual_F_primal_apply (f := f) (A := A) (y := y)]
    exact
      (dual_based_proximal_gradient_dual_F_primal_finite_valued
        (σ := σ)
        (f := f)
        (A := A)
        hf_proper
        hf_closed
        hf_strong
        y).1
  have hG_ne_bot :
      dual_based_proximal_gradient_dual_G_term g (toDualMap ℝ V y) ≠ ⊥ := by
    let hGproper :=
      dual_based_proximal_gradient_dual_G_primal_proper
        (g := g)
        hg_proper
        hg_convex
    rw [dual_based_proximal_gradient_dual_G_primal_apply (g := g) (y := y)]
    exact hGproper.ne_bot y
  -- The Chapter 12 bridge theorem already identifies the split sum with `-q`.
  calc
    composite_model_objective F G y =
        -dual_based_proximal_gradient_lagrange_dual_objective
          f g A (toDualMap ℝ V y) := by
          exact
            dual_based_proximal_gradient_dual_terms_sum_eq_neg_lagrange_dual_objective
              f
              g
              A
              (toDualMap ℝ V y)
              hF_ne_bot
              hG_ne_bot
    _ = -q y := by
          rw [← primalDualObjective_eq_dualOwner (f := f) (g := g) (A := A) y]

/-- Helper for Theorem 12.4: the source dual objective never attains `⊤`. -/
lemma dualObjective_ne_top
    (σ : PosReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g)
    (y : V) :
    q y ≠ ⊤ := by
  have hF_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ)
      (f := f)
      (A := A)
      hf_proper
      hf_closed
      hf_strong
      y
  let hGproper :=
    dual_based_proximal_gradient_dual_G_primal_proper
      (g := g)
      hg_proper
      hg_convex
  have hnegF_ne_top : -((f∗) (A.adjoint y)) ≠ ⊤ := by
    intro htop
    exact hF_finite.1 (by simpa using congrArg Neg.neg htop)
  have hnegG_ne_top : -((g∗) (-y)) ≠ ⊤ := by
    intro htop
    exact hGproper.ne_bot y (by simpa using congrArg Neg.neg htop)
  -- Rewrite `q y` as a sum of two non-`⊤` terms.
  rw [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply, sub_eq_add_neg]
  simpa using EReal.add_ne_top hnegF_ne_top hnegG_ne_top

/-- Helper for Theorem 12.4: some primal-space dual value avoids `⊥`. -/
lemma exists_dualObjective_ne_bot
    (σ : PosReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g) :
    ∃ y : V, q y ≠ ⊥ := by
  let hGproper :=
    dual_based_proximal_gradient_dual_G_primal_proper
      (g := g)
      hg_proper
      hg_convex
  rcases hGproper.effective_domain_nonempty with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have hF_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ)
      (f := f)
      (A := A)
      hf_proper
      hf_closed
      hf_strong
      y
  have hnegF_ne_bot : -((f∗) (A.adjoint y)) ≠ ⊥ := by
    intro hbot
    exact hF_finite.2.ne (by simpa using congrArg Neg.neg hbot)
  have hGy_ne_top : (g∗) (-y) ≠ ⊤ := by
    simpa [effective_domain] using (mem_effective_domain.mp hy).ne
  have hnegG_ne_bot : -((g∗) (-y)) ≠ ⊥ := by
    intro hbot
    exact hGy_ne_top (by simpa using congrArg Neg.neg hbot)
  -- A sum of two non-`⊥` summands stays above `⊥`.
  rw [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply, sub_eq_add_neg]
  exact EReal.add_ne_bot_iff.mpr ⟨hnegF_ne_bot, hnegG_ne_bot⟩

/-- Helper for Theorem 12.4: an optimal dual point minimizes the Chapter 10 minimization view
`composite_model_objective F G = -q`. -/
lemma optimalDualPoint_mem_unconstrainedSolutionsMinimizationView
    (σ : PosReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g)
    {yStar : V}
    (hyStar : q yStar = qOpt) :
    yStar ∈ unconstrained_problem_solutions (composite_model_objective F G) := by
  -- Rewrite the minimization surface to `-q` and use the global maximality encoded in `qOpt`.
  rw [mem_unconstrained_problem_solutions_iff_forall_le]
  intro yBar
  rw [dualCompositeObjective_eq_negDualObjective
      (f := f)
      (g := g)
      (A := A)
      σ
      hf_proper
      hf_closed
      hf_strong
      hg_proper
      hg_convex
      yStar,
    dualCompositeObjective_eq_negDualObjective
      (f := f)
      (g := g)
      (A := A)
      σ
      hf_proper
      hf_closed
      hf_strong
      hg_proper
      hg_convex
      yBar]
  have hq_le : q yBar ≤ qOpt :=
    dualObjective_le_dualProblemValue (f := f) (g := g) (A := A) yBar
  have hneg : -qOpt ≤ -q yBar := by
    simpa using (EReal.neg_le_neg_iff.mpr hq_le)
  simpa [hyStar] using hneg

/-- Helper for Theorem 12.4: the minimization view `composite_model_objective F G = -q`
satisfies the Chapter 10 convex-composite-smooth assumptions with smoothness constant `L`. -/
lemma dualMinimizationView_isConvexCompositeSmoothMinimizationProblem
    (σ : PosReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    {yStar : V}
    (hyStar : q yStar = qOpt) :
    IsConvexCompositeSmoothMinimizationProblem
      F
      G
      (unconstrained_problem_solutions (composite_model_objective F G))
      (-EReal.toReal qOpt)
      (PosReal.toNNReal (L : PosReal)) := by
  let hGproper :=
    dual_based_proximal_gradient_dual_G_primal_proper
      (g := g)
      hg_proper
      hg_convex
  have hF_eq : F = fun y : V ↦ (f∗) (A.adjoint y) := by
    funext y
    exact dual_based_proximal_gradient_dual_F_primal_apply (f := f) (A := A) y
  have hG_eq : G = fun y : V ↦ (g∗) (-y) := by
    funext y
    exact dual_based_proximal_gradient_dual_G_primal_apply (g := g) y
  have hF_ne_bot :
      ∀ y : V, F y ≠ ⊥ := by
    intro y
    rw [hF_eq]
    exact
      (dual_based_proximal_gradient_dual_F_primal_finite_valued
        (σ := σ)
        (f := f)
        (A := A)
        hf_proper
        hf_closed
        hf_strong
        y).1
  have hF_closed : LowerSemicontinuous F := by
    -- Closedness of `f∗` survives precomposition with the adjoint.
    rw [hF_eq]
    exact
      (conjugate_function_closed_and_convex f).1.comp
        A.adjoint.toContinuousLinearMap.continuous
  have hF_convex : is_convex_function F := by
    rw [hF_eq]
    exact dual_based_proximal_gradient_dual_F_primal_convex (f := f) (A := A)
  have hG_closed : LowerSemicontinuous G := by
    rw [hG_eq]
    exact
      (dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).1
  have hG_convex : is_convex_function G := by
    rw [hG_eq]
    exact
      (dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).2
  have hF_eff_univ : effective_domain F = Set.univ := by
    rw [hF_eq]
    ext y
    constructor
    · intro _
      simp
    · intro _
      exact
        mem_effective_domain.mpr
          (dual_based_proximal_gradient_dual_F_primal_finite_valued
            (σ := σ)
            (f := f)
            (A := A)
            hf_proper
            hf_closed
            hf_strong
            y).2
  have hF_smooth_base :
      is_l_smooth_on
        (fun y : V ↦ (F y).toReal)
        Set.univ
        (Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ)) := by
    rw [hF_eq]
    exact
      dual_based_proximal_gradient_dual_F_primal_is_l_smooth
        (σ := σ)
        (f := f)
        (A := A)
        hf_proper
        hf_closed
        hf_strong
  have hconst_le :
      (Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ) : NNReal) ≤
        PosReal.toNNReal (L : PosReal) := by
    apply NNReal.coe_le_coe.mpr
    calc
      (((Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ) : NNReal) : ℝ))
          =
            (‖A.toContinuousLinearMap‖ ^ (2 : ℕ)) / (σ : ℝ) := by
              have hσ_nonneg : 0 ≤ 1 / (σ : ℝ) := le_of_lt (one_div_pos.mpr σ.2)
              rw [NNReal.coe_mul, NNReal.coe_pow, Real.toNNReal_of_nonneg hσ_nonneg]
              simp
              ring
      _ =
            dual_based_proximal_gradient_dual_lipschitz_constant
              A.toContinuousLinearMap σ := by
              rw [dual_based_proximal_gradient_dual_lipschitz_constant_eq]
      _ ≤ (L : ℝ) :=
            DualBasedProximalGradientDualStepsizeParameter.lower_bound L
      _ = (((PosReal.toNNReal (L : PosReal) : NNReal) : ℝ)) := by
            simp [PosReal.coe_toNNReal]
  have hF_smooth :
      is_l_smooth_on
        (fun y : V ↦ (F y).toReal)
        Set.univ
        (PosReal.toNNReal (L : PosReal)) := by
    exact Example_10_44.is_l_smooth_on_mono hF_smooth_base hconst_le
  have hqOpt_ne_top : qOpt ≠ ⊤ := by
    rw [← hyStar]
    exact
      dualObjective_ne_top
        (f := f)
        (g := g)
        (A := A)
        σ
        hf_proper
        hf_closed
        hf_strong
        hg_proper
        hg_convex
        yStar
  have hqOpt_ne_bot : qOpt ≠ ⊥ := by
    rcases
        exists_dualObjective_ne_bot
          (f := f)
          (g := g)
          (A := A)
          σ
          hf_proper
          hf_closed
          hf_strong
          hg_proper
          hg_convex with
      ⟨y0, hy0⟩
    have hy0_le : q y0 ≤ qOpt :=
      dualObjective_le_dualProblemValue (f := f) (g := g) (A := A) y0
    intro hqOpt_bot
    rw [hqOpt_bot] at hy0_le
    have hy0_bot : q y0 ≤ ⊥ := hy0_le
    exact hy0 (le_bot_iff.mp hy0_bot)
  have hneg_qOpt_coe :
      (((-EReal.toReal qOpt : ℝ)) : EReal) = -qOpt := by
    -- Coerce the finite optimal value to `ℝ`, then negate the equality.
    simpa using congrArg Neg.neg (EReal.coe_toReal hqOpt_ne_top hqOpt_ne_bot)
  refine
    { f_ne_bot := hF_ne_bot
      g_proper := by
        rw [hG_eq]
        exact hGproper
      f_closed := hF_closed
      g_closed := hG_closed
      f_convex := hF_convex
      g_convex := hG_convex
      g_effective_domain_subset_interior_f_effective_domain := ?_
      f_toReal_smooth_on_interior_effective_domain := ?_
      optimal_set_eq := rfl
      optimal_set_nonempty := ?_
      optimal_value_isGLB := ?_ }
  · intro y hy
    -- The smooth term is finite everywhere, so its interior effective domain is `Set.univ`.
    rw [hF_eff_univ]
    simp
  · -- Promote the canonical smoothness constant to the actual stepsize parameter `L`.
    rw [hF_eff_univ]
    simpa using hF_smooth
  · refine ⟨yStar, ?_⟩
    exact
      optimalDualPoint_mem_unconstrainedSolutionsMinimizationView
        (f := f)
        (g := g)
        (A := A)
        σ
        hf_proper
        hf_closed
        hf_strong
        hg_proper
        hg_convex
        hyStar
  · constructor
    · rintro _ ⟨yBar, rfl⟩
      -- Lower bounds on `-q` come from upper bounds on `q`.
      calc
        (((-EReal.toReal qOpt : ℝ)) : EReal) = -qOpt := hneg_qOpt_coe
        _ ≤ -q yBar := by
              simpa using
                (EReal.neg_le_neg_iff.mpr
                  (dualObjective_le_dualProblemValue (f := f) (g := g) (A := A) yBar))
        _ = composite_model_objective F G yBar := by
              rw [dualCompositeObjective_eq_negDualObjective
                (f := f)
                (g := g)
                (A := A)
                σ
                hf_proper
                hf_closed
                hf_strong
                hg_proper
                hg_convex
                yBar]
    · intro b hb
      have hyStar_lb : b ≤ composite_model_objective F G yStar := hb ⟨yStar, rfl⟩
      -- Evaluating the lower bound at an optimal point recovers exactly `-qOpt`.
      calc
        b ≤ composite_model_objective F G yStar := hyStar_lb
        _ = -q yStar := by
              rw [dualCompositeObjective_eq_negDualObjective
                (f := f)
                (g := g)
                (A := A)
                σ
                hf_proper
                hf_closed
                hf_strong
                hg_proper
                hg_convex
                yStar]
        _ = -qOpt := by rw [hyStar]
        _ = (((-EReal.toReal qOpt : ℝ)) : EReal) := hneg_qOpt_coe.symm

/-- Theorem 12.4: if the Chapter 12 dual split terms satisfy the primitive proper/convex
and strong-convexity hypotheses needed for the Chapter 10 convex proximal-gradient rate theorem,
then every positive dual proximal-gradient iterate satisfies
`qOpt - q(y^k) ≤ L ‖y^0 - y^*‖^2 / (2 k)` for any optimal dual solution `y^*`, where
`q(y) = -f*(Aᵀ y) - g*(-y)`.
-/
theorem dual_based_proximal_gradient_dual_objective_gap_le
    (σ : PosReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (y : ℕ → V) (y0 yStar : V)
    (htraj : is_dual_based_proximal_gradient_dual_trajectory F G L y y0)
    (hyStar : q yStar = qOpt)
    (k : ℕ) (hk : 1 ≤ k) :
    qOpt - q (y k) ≤
      (((L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / (2 * (k : ℝ)) : ℝ) : EReal) := by
  let hproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)) :=
    dualMinimizationView_isConvexCompositeSmoothMinimizationProblem
      (f := f)
      (g := g)
      (A := A)
      σ
      hf_proper
      hf_closed
      hf_strong
      hg_proper
      hg_convex
      L
      hyStar
  have htrajPG :
      is_proximal_gradient_trajectory F G y (fun _ ↦ (L : PosReal)) :=
    htraj.toIsProximalGradientTrajectory
  have hyStarMin :
      yStar ∈ unconstrained_problem_solutions (composite_model_objective F G) :=
    optimalDualPoint_mem_unconstrainedSolutionsMinimizationView
      (f := f)
      (g := g)
      (A := A)
      σ
      hf_proper
      hf_closed
      hf_strong
      hg_proper
      hg_convex
      hyStar
  have hrule :
      hproblem.SourceSublinearRateStepsizeRule y (fun _ ↦ (L : PosReal)) htrajPG 1 := by
    -- Route correction: apply Chapter 10 with the surrogate smoothness constant `Lf = L`.
    exact Or.inl ⟨rfl, fun _ ↦ rfl⟩
  have hqOpt_ne_top : qOpt ≠ ⊤ := by
    rw [← hyStar]
    exact
      dualObjective_ne_top
        (f := f)
        (g := g)
        (A := A)
        σ
        hf_proper
        hf_closed
        hf_strong
        hg_proper
        hg_convex
        yStar
  have hqOpt_ne_bot : qOpt ≠ ⊥ := by
    rcases
        exists_dualObjective_ne_bot
          (f := f)
          (g := g)
          (A := A)
          σ
          hf_proper
          hf_closed
          hf_strong
          hg_proper
          hg_convex with
      ⟨yBar, hyBar⟩
    have hyBar_le : q yBar ≤ qOpt :=
      dualObjective_le_dualProblemValue (f := f) (g := g) (A := A) yBar
    intro hqOpt_bot
    rw [hqOpt_bot] at hyBar_le
    have hyBar_bot : q yBar ≤ ⊥ := hyBar_le
    exact hyBar (le_bot_iff.mp hyBar_bot)
  have hneg_qOpt_coe :
      (((-EReal.toReal qOpt : ℝ)) : EReal) = -qOpt := by
    -- Coerce the finite optimal value to `ℝ`, then negate on both sides.
    simpa using congrArg Neg.neg (EReal.coe_toReal hqOpt_ne_top hqOpt_ne_bot)
  have hrate :
      composite_model_objective F G (y k) - (((-EReal.toReal qOpt : ℝ)) : EReal) ≤
        (((1 * ((PosReal.toNNReal (L : PosReal) : NNReal) : ℝ) * ‖y 0 - yStar‖ ^ (2 : ℕ) /
            (2 * (k : ℝ)) : ℝ)) : EReal) := by
    -- Apply the generic Chapter 10 `O(1 / k)` estimate on the minimization view `-q`.
    simpa using
      proximal_gradient_convex_objective_gap_le
        (hproblem := hproblem)
        (htraj := htrajPG)
        (hrule := hrule)
        (hxStar := hyStarMin)
        k
        hk
  -- Rewrite the Chapter 10 minimization gap back to the source dual gap.
  have hleft :
      qOpt - q (y k) =
        composite_model_objective F G (y k) - (((-EReal.toReal qOpt : ℝ)) : EReal) := by
    rw [dualCompositeObjective_eq_negDualObjective
        (f := f)
        (g := g)
        (A := A)
        σ
        hf_proper
        hf_closed
        hf_strong
        hg_proper
        hg_convex
        (y k),
      hneg_qOpt_coe]
    simp [sub_eq_add_neg, add_comm]
  rw [hleft]
  simpa [htraj.zero_eq, PosReal.coe_toNNReal, one_mul] using hrate

end
