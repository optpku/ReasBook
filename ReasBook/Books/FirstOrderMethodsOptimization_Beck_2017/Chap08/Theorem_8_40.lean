/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.HalfSquaredDiameterBound
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_27
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_39
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Baire.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ}
variable {fi : Fin m → E → EReal} {C XStar : Set E} {fOpt Θ : ℝ}
variable [h_problem : IsConstrainedConvexProblem (finite_sum_objective fi) C XStar fOpt]
variable (h_incremental : IncrementalProjectedSubgradientAssumptions fi C)
variable (g : ℕ → C → Fin m → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  incremental_projected_subgradient_method
    C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex t g x0 k

local notation "x[" k "," i "]" =>
  incremental_projected_subgradient_inner_iterate
    C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex t g k x[k] i

include h_problem h_incremental

omit [CompleteSpace E] h_incremental in
/-- Helper for Theorem 8.40: every feasible point has aggregate objective gap at least `0`. -/
private lemma feasibleFiniteSumObjectiveGap_nonneg
    {y : E} (hy : y ∈ C) :
    0 ≤ ((finite_sum_objective fi) y).toReal - fOpt := by
  have hyImage : (finite_sum_objective fi) y ∈ (finite_sum_objective fi) '' C := by
    exact ⟨y, hy, rfl⟩
  have hlower : (fOpt : EReal) ≤ (finite_sum_objective fi) y :=
    h_problem.optimal_value_isGLB.1 hyImage
  have hyDom : y ∈ effective_domain (finite_sum_objective fi) := by
    -- Feasibility puts `y` inside the finite-valued domain of the aggregate objective.
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hy)
  have hyTop : (finite_sum_objective fi) y ≠ ⊤ := ne_of_lt hyDom
  have hyBot : (finite_sum_objective fi) y ≠ ⊥ := h_problem.ne_bot y
  have hvalue_eq :
      ((((finite_sum_objective fi) y).toReal : ℝ) : EReal) = (finite_sum_objective fi) y := by
    -- Feasible aggregate values are finite, so coercing back from `toReal` recovers them.
    exact EReal.coe_toReal hyTop hyBot
  have hreal : fOpt ≤ ((finite_sum_objective fi) y).toReal := by
    exact EReal.coe_le_coe_iff.mp (hlower.trans_eq hvalue_eq.symm)
  exact sub_nonneg.mpr hreal

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] h_problem h_incremental in
/-- Helper for Theorem 8.40: every nonempty interval sum of positive stepsizes is strictly
positive. -/
private lemma positiveStepsizeIntervalSum_pos
    (h_stepsize_pos : ∀ n, 0 < t n) (a q : ℕ) :
    0 < Finset.sum (Finset.Icc a (a + q)) (fun n ↦ t n) := by
  -- The left endpoint `a` already contributes a positive summand to the interval sum.
  have hmem : a ∈ Finset.Icc a (a + q) := by
    simp
  have hle :
      t a ≤ Finset.sum (Finset.Icc a (a + q)) (fun n ↦ t n) := by
    simpa using
      (Finset.single_le_sum (fun n _ ↦ le_of_lt (h_stepsize_pos n)) hmem)
  exact lt_of_lt_of_le (h_stepsize_pos a) hle

/-- Helper for Theorem 8.40: the stage-point secant inequality yields an `EReal` comparison
between the inner-stage and outer-iterate component values with the drift term isolated on the
left-hand side. -/
private lemma innerStageComponentValue_subDrift_le_outerIterateValueEReal
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (k : ℕ) {i : ℕ} (hi : i < m) :
    fi ⟨i, hi⟩ (x[k, i] : E) +
        (((-(h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖) : ℝ)) : EReal) ≤
      fi ⟨i, hi⟩ (x[k] : E) := by
  let ii : Fin m := ⟨i, hi⟩
  let xki : C := x[k, i]
  have hxki_int : (xki : E) ∈ interior (effective_domain (fi ii)) := by
    -- The stage-point secant inequality applies because every inner iterate stays feasible.
    exact componentInteriorEffectiveDomain_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) xki.property ii
  have hxk_dom : (x[k] : E) ∈ effective_domain (fi ii) := by
    -- The comparison outer iterate is feasible as well, so its component value is finite.
    exact componentEffectiveDomain_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) (x[k]).property ii
  have hsecant :
      fi ii (x[k] : E) ≥
        fi ii (xki : E) +
          directional_derivative (fi ii) (xki : E) ((x[k] : E) - (xki : E)) := by
    -- Route correction: work at the current inner stage and use the convex secant inequality
    -- directly, instead of rebuilding an outer-iterate subgradient.
    exact value_ge_value_add_directional_derivative_of_mem_effective_domain
      (fi ii) (xki : E) (x[k] : E) (h_incremental.convex ii)
      (fun z ↦ (h_incremental.proper ii).ne_bot z) hxki_int hxk_dom
  have hdir :
      (((-(h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖) : ℝ)) : EReal) ≤
        directional_derivative (fi ii) (xki : E) ((x[k] : E) - (xki : E)) := by
    -- The selected stage subgradient bounds the directional derivative from below by `-L‖d‖`.
    simpa [ii, xki, norm_sub_rev] using
      (selectedStageDirectionalDerivative_ge_negMulNorm
        (h_problem := h_problem) (h_incremental := h_incremental)
        (g := g) (t := t) (x0 := x0) h_subgrad (k := k) (i := i) hi)
  -- Add the directional-derivative lower bound to the stage value, then compare against the
  -- secant upper support bound at the outer iterate.
  exact le_trans (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hdir (fi ii (xki : E)))
    (by simpa [ge_iff_le, ii, xki] using hsecant)

/-- Helper for Theorem 8.40: the stage-component gap controls the outer-iterate component gap up
to the Lipschitz drift term. -/
private lemma componentToReal_sub_le_mul_dist_of_lipschitzOnFeasible
    (k : ℕ) {i : ℕ} (hi : i < m)
    (hLip :
      LipschitzOnWith (Real.toNNReal h_incremental.L)
        (fun z ↦ (fi ⟨i, hi⟩ z).toReal) C) :
    (fi ⟨i, hi⟩ x[k]).toReal - (fi ⟨i, hi⟩ x[k, i]).toReal ≤
      h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
  have habs :
      |(fi ⟨i, hi⟩ x[k]).toReal - (fi ⟨i, hi⟩ x[k, i]).toReal| ≤
        (Real.toNNReal h_incremental.L : ℝ) * dist (x[k] : E) (x[k, i] : E) := by
    -- The feasible-set Lipschitz estimate controls the outer/stage component-value difference.
    exact abs_toReal_sub_le_mul_dist_of_lipschitzOnWith
      (f := fi ⟨i, hi⟩) hLip (x[k, i]).property (x[k]).property
  have hle :
      (fi ⟨i, hi⟩ x[k]).toReal - (fi ⟨i, hi⟩ x[k, i]).toReal ≤
        |(fi ⟨i, hi⟩ x[k]).toReal - (fi ⟨i, hi⟩ x[k, i]).toReal| :=
    le_abs_self _
  -- Rewrite the metric estimate into the norm form used in the stage-gap arithmetic.
  exact le_trans hle (by
    simpa [Real.toNNReal_of_nonneg h_incremental.L_pos.le, dist_eq_norm, norm_sub_rev] using
      habs)

/-- Helper for Theorem 8.40: the stage-component gap controls the outer-iterate component gap up
to the Lipschitz drift term. -/
private lemma componentGapCompareToOuterIterate_of_lipschitzOnFeasible
    (k : ℕ) {i : ℕ} (hi : i < m) {xStar : E}
    (hLip :
      LipschitzOnWith (Real.toNNReal h_incremental.L)
        (fun z ↦ (fi ⟨i, hi⟩ z).toReal) C) :
    (fi ⟨i, hi⟩ x[k, i]).toReal - (fi ⟨i, hi⟩ xStar).toReal ≥
      (fi ⟨i, hi⟩ x[k]).toReal - (fi ⟨i, hi⟩ xStar).toReal -
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
  have hvalueDiff :
      (fi ⟨i, hi⟩ x[k]).toReal - (fi ⟨i, hi⟩ x[k, i]).toReal ≤
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
    -- Reuse the direct outer/stage value-difference bound supplied by feasible-set Lipschitzness.
    exact componentToReal_sub_le_mul_dist_of_lipschitzOnFeasible
      (h_problem := h_problem) (h_incremental := h_incremental)
      (g := g) (t := t) (x0 := x0) (k := k) (i := i) hi hLip
  -- Keep the comparison point `xStar` fixed and isolate the controllable Lipschitz drift.
  linarith

/-- Helper for Theorem 8.40: the `EReal` stage-vs-outer comparison from the secant inequality can
be pushed down to the real-valued component objectives at feasible points. -/
private lemma innerStageComponentValue_subDrift_le_outerIterateValue_toReal
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (k : ℕ) {i : ℕ} (hi : i < m) :
    (fi ⟨i, hi⟩ (x[k, i] : E)).toReal -
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ ≤
      (fi ⟨i, hi⟩ (x[k] : E)).toReal := by
  let ii : Fin m := ⟨i, hi⟩
  let drift : ℝ := h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖
  have hxki_ne_top : fi ii (x[k, i] : E) ≠ ⊤ := by
    -- The current inner-stage point stays feasible, so its component value is finite above.
    exact componentValue_neTop_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) (x[k, i]).property ii
  have hxki_ne_bot : fi ii (x[k, i] : E) ≠ ⊥ := by
    -- Properness rules out `⊥` for every component value.
    exact (h_incremental.proper ii).ne_bot (x[k, i] : E)
  have hxk_ne_top : fi ii (x[k] : E) ≠ ⊤ := by
    -- The outer iterate is feasible as well, so its component value is finite above.
    exact componentValue_neTop_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) (x[k]).property ii
  have hleft_ne_bot :
      fi ii (x[k, i] : E) + (((-drift : ℝ)) : EReal) ≠ ⊥ := by
    -- Adding a finite real drift term preserves the non-`⊥` stage value.
    simpa [EReal.add_ne_bot_iff] using
      (show fi ii (x[k, i] : E) ≠ ⊥ ∧ (((-drift : ℝ)) : EReal) ≠ ⊥ from
        ⟨hxki_ne_bot, EReal.coe_ne_bot _⟩)
  have hcompareReal :
      (fi ii (x[k, i] : E) + (((-drift : ℝ)) : EReal)).toReal ≤
        (fi ii (x[k] : E)).toReal := by
    -- Route correction: convert the already proved `EReal` secant comparison directly to `ℝ`.
    exact EReal.toReal_le_toReal
      (innerStageComponentValue_subDrift_le_outerIterateValueEReal
        (h_problem := h_problem) (h_incremental := h_incremental)
        (g := g) (t := t) (x0 := x0) h_subgrad (k := k) (i := i) hi)
      hleft_ne_bot
      hxk_ne_top
  have hleft_toReal :
      (fi ii (x[k, i] : E) + (((-drift : ℝ)) : EReal)).toReal =
        (fi ii (x[k, i] : E)).toReal - drift := by
    -- The left-hand side is a sum of finite terms, so `toReal` distributes over it.
    have hneg_drift_toReal : (((( -drift : ℝ)) : EReal)).toReal = -drift := by
      simp
    rw [EReal.toReal_add hxki_ne_top hxki_ne_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    rw [hneg_drift_toReal]
    ring
  rw [hleft_toReal] at hcompareReal
  simpa [ii, drift] using hcompareReal

/-- Helper for Theorem 8.40: the stage-component gap controls the outer-iterate component gap up
once a strong-dual subgradient is available at the outer iterate. -/
private lemma componentGapCompareToOuterIterate_of_outerStrongSubgradient
    (k : ℕ) {i : ℕ} (hi : i < m) {xStar : E}
    {ζ : StrongDual ℝ E}
    (hζ : ζ ∈ strongDualSubdifferential (fi ⟨i, hi⟩) (x[k] : E)) :
    (fi ⟨i, hi⟩ x[k, i]).toReal - (fi ⟨i, hi⟩ xStar).toReal ≥
      (fi ⟨i, hi⟩ x[k]).toReal - (fi ⟨i, hi⟩ xStar).toReal -
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
  let ii : Fin m := ⟨i, hi⟩
  have hxk_int : (x[k] : E) ∈ interior (effective_domain (fi ii)) := by
    -- The outer iterate is feasible, so the component admits the owner subgradient inequality.
    exact componentInteriorEffectiveDomain_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) (x[k]).property ii
  have hxk_dom : (x[k] : E) ∈ effective_domain (fi ii) := interior_subset hxk_int
  have hxki_dom : (x[k, i] : E) ∈ effective_domain (fi ii) := by
    -- The current inner-stage point is feasible as well, so its component value is finite.
    exact componentEffectiveDomain_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) (x[k, i]).property ii
  have hζ_owner :
      ((ζ : StrongDual ℝ E) : Module.Dual ℝ E) ∈ subdifferential (fi ii) (x[k] : E) := by
    -- Read the outer-point strong-dual witness back through the owner subdifferential predicate.
    simpa [mem_strongDualSubdifferential] using hζ
  have hsub :
      ((ζ : StrongDual ℝ E) : Module.Dual ℝ E) ((x[k, i] : E) - (x[k] : E)) ≤
        (fi ii (x[k, i] : E)).toReal - (fi ii (x[k] : E)).toReal := by
    -- Evaluate the outer-point subgradient inequality at the inner-stage comparison point.
    exact subgradient_eval_le_toReal_sub (fi ii) (x[k] : E) (x[k, i] : E)
      (fun z hz ↦ (h_incremental.proper ii).ne_bot z) hxk_dom hxki_dom hζ_owner
  have hpair_abs :
      |ζ (((x[k, i] : E) - (x[k] : E)))| ≤
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
    calc
      |ζ (((x[k, i] : E) - (x[k] : E)))| =
          ‖ζ (((x[k, i] : E) - (x[k] : E)))‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖ζ‖ * ‖((x[k, i] : E) - (x[k] : E))‖ := by
          simpa using (ContinuousLinearMap.le_opNorm ζ ((x[k, i] : E) - (x[k] : E)))
      _ ≤ h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
          gcongr
          exact h_incremental.norm_le (x := (x[k] : E)) (g := ζ) (x[k]).property hζ
  have hpair_lower :
      -(h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖) ≤
        ζ (((x[k, i] : E) - (x[k] : E))) := by
    -- The operator-norm bound gives the needed lower control on the chosen pairing.
    linarith [neg_abs_le (ζ (((x[k, i] : E) - (x[k] : E)))), hpair_abs]
  have hvalueDiff :
      (fi ii (x[k] : E)).toReal - (fi ii (x[k, i] : E)).toReal ≤
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
    -- Combine the outer-point subgradient inequality with the norm control on its pairing.
    have htmp :
        -(h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖) ≤
          (fi ii (x[k, i] : E)).toReal - (fi ii (x[k] : E)).toReal :=
      le_trans hpair_lower hsub
    linarith
  -- Freeze the comparison point `xStar` and rewrite the value difference into the gap form.
  linarith

/-- Helper for Theorem 8.40: once an outer-iterate strong-dual subgradient is available, the
non-finite-dimensional component-gap comparison reduces to the existing outer-subgradient lemma. -/
private lemma componentGapCompareToOuterIterateNoFD_of_outerStrongSubgradientExists
    (k : ℕ) {i : ℕ} (hi : i < m) {xStar : E}
    (hexists :
      ∃ ζ : StrongDual ℝ E,
        ζ ∈ strongDualSubdifferential (fi ⟨i, hi⟩) (x[k] : E)) :
    (fi ⟨i, hi⟩ x[k, i]).toReal - (fi ⟨i, hi⟩ xStar).toReal ≥
      (fi ⟨i, hi⟩ x[k]).toReal - (fi ⟨i, hi⟩ xStar).toReal -
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
  rcases hexists with ⟨ζ, hζ⟩
  -- Once the outer witness exists, the reverse comparison is exactly the established bridge.
  exact componentGapCompareToOuterIterate_of_outerStrongSubgradient
    (h_problem := h_problem) (h_incremental := h_incremental)
    (g := g) (t := t) (x0 := x0) (k := k) (i := i) hi (xStar := xStar) hζ

omit [CompleteSpace E] h_problem h_incremental in
/-- Helper for Theorem 8.40: a proper convex extended-real function has an algebraic subgradient
at every interior effective-domain point, even without a finite-dimensional hypothesis. -/
private lemma subdifferentialNonempty_ofInteriorProperConvex
    {f : E → EReal} [IsProperExtendedRealFunction f] {x : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f)) :
    Set.Nonempty (subdifferential f x) := by
  by_cases hE : Subsingleton E
  · -- In the degenerate one-point space, the zero functional satisfies the subgradient inequality.
    refine ⟨0, ?_⟩
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
    refine ⟨interior_subset hx, ?_⟩
    intro y hy
    have hyx : y = x := Subsingleton.elim _ _
    subst hyx
    simp
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    obtain ⟨d, hd⟩ : ∃ d : E, d ≠ (0 : E) := exists_ne (0 : E)
    rcases existsDominatedLinearFunctional_eqDirectionalDerivative
        (f := f) (x := x) (d := d) hconvex hx hd with
      ⟨ζ, hζ_dom, -⟩
    -- The dominated Hahn-Banach witness is already an algebraic subgradient at `x`.
    exact ⟨ζ, dominatedLinearFunctional_memSubdifferential hconvex hx hζ_dom⟩

/-- Helper for Theorem 8.40: feasibility gives an algebraic subgradient for the current component
objective at the outer iterate `x[k]`. -/
private lemma componentOuterSubgradientExists_ofFeasible
    (k : ℕ) {i : ℕ} (hi : i < m) :
    ∃ ζ : Module.Dual ℝ E,
      ζ ∈ subdifferential (fi ⟨i, hi⟩) (x[k] : E) := by
  let ii : Fin m := ⟨i, hi⟩
  letI : IsProperExtendedRealFunction (fi ii) := h_incremental.proper ii
  have hxk_int : (x[k] : E) ∈ interior (effective_domain (fi ii)) := by
    -- Feasibility provides the interior-domain hypothesis needed by the algebraic owner theorem.
    exact componentInteriorEffectiveDomain_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) (x[k]).property ii
  -- Reuse the dimension-free Chapter 3 dominated-functional route before asking for continuity.
  simpa [ii] using
    subdifferentialNonempty_ofInteriorProperConvex
      (f := fi ii) (x := (x[k] : E)) (h_incremental.convex ii) hxk_int

omit h_problem h_incremental in
/-- Helper for Theorem 8.40: a proper closed convex extended-real-valued function admits a
continuous-dual subgradient at every interior effective-domain point. -/
private lemma strongDualSubdifferentialNonempty_ofInteriorProperClosedConvex
    {f : E → EReal} [IsProperExtendedRealFunction f] {x : E}
    (h_closed : LowerSemicontinuous f) (h_convex : is_convex_function f)
    (hx : x ∈ interior (effective_domain f)) :
    ∃ ζ : StrongDual ℝ E, ζ ∈ strongDualSubdifferential f x := by
  let s : Set E := effective_domain f
  let A : Set (E × ℝ) := {p : E × ℝ | f p.1 ≤ p.2}
  have hx_dom : x ∈ s := interior_subset hx
  have hfx_ne_top : f x ≠ ⊤ := ne_of_lt hx_dom
  have hfx_ne_bot : f x ≠ ⊥ := IsProperExtendedRealFunction.ne_bot x
  have hsublevel_closed : ∀ n : ℕ, IsClosed {y : E | f y ≤ (n : ℝ)} := by
    intro n
    simpa using h_closed.isClosed_real_sublevelSet (n : ℝ)
  have hA_convex : Convex ℝ A := by
    simpa [A] using (is_convex_function_iff_convex_real_epigraph f).mp h_convex
  have hA_closed : IsClosed A := by
    simpa [A] using h_closed.isClosed_real_epigraph
  have hA_int : (interior A).Nonempty := by
    rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx) with ⟨ε, hε_pos, hε_subset⟩
    let B : Set E := Metric.ball x ε
    have hB_open : IsOpen B := Metric.isOpen_ball
    have hB_nonempty : B.Nonempty := ⟨x, by simpa [B, Metric.mem_ball] using hε_pos⟩
    let F : ℕ → Set B := fun n ↦ ((↑) : B → E) ⁻¹' {y : E | f y ≤ (n : ℝ)}
    have hF_closed : ∀ n : ℕ, IsClosed (F n) := by
      intro n
      exact (hsublevel_closed n).preimage continuous_subtype_val
    have hF_cover : ⋃ n, F n = Set.univ := by
      ext u
      constructor
      · intro _
        simp
      · intro _
        obtain ⟨n, hn⟩ := exists_nat_ge ((f u).toReal)
        have hu_dom : (u : E) ∈ s := by
          exact interior_subset (hε_subset u.property)
        have hfu : f u ≤ (n : ℝ) := by
          rw [← EReal.coe_toReal (ne_of_lt hu_dom) (IsProperExtendedRealFunction.ne_bot (f := f) u)]
          exact_mod_cast hn
        exact Set.mem_iUnion.2 ⟨n, hfu⟩
    letI : Nonempty B := hB_nonempty.to_subtype
    letI : BaireSpace B := hB_open.baireSpace
    obtain ⟨n, hn_int⟩ := nonempty_interior_of_iUnion_of_closed hF_closed hF_cover
    rcases hn_int with ⟨z, hz_int⟩
    obtain ⟨ρ₁, hρ₁_pos, hρ₁_ball⟩ := Metric.mem_nhds_iff.1 (hB_open.mem_nhds z.property)
    obtain ⟨ρ₂, hρ₂_pos, hρ₂_ball⟩ := Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hz_int)
    let ρ : ℝ := min ρ₁ ρ₂
    have hρ_pos : 0 < ρ := lt_min hρ₁_pos hρ₂_pos
    have hball_sublevel :
        Metric.ball (z : E) ρ ⊆ {y : E | f y ≤ (n : ℝ)} := by
      intro y hy
      have hy_lt : dist y (z : E) < ρ := by
        simpa [Metric.mem_ball] using hy
      have hyB : y ∈ B := by
        exact hρ₁_ball (by
          simpa [Metric.mem_ball] using lt_of_lt_of_le hy_lt (min_le_left _ _))
      have hy_subtype : (⟨y, hyB⟩ : B) ∈ Metric.ball z ρ₂ := by
        simpa [Metric.mem_ball] using lt_of_lt_of_le hy_lt (min_le_right _ _)
      have hyFn : (⟨y, hyB⟩ : B) ∈ F n := interior_subset (hρ₂_ball hy_subtype)
      exact hyFn
    let O : Set (E × ℝ) := Metric.ball (z : E) ρ ×ˢ Set.Ioi (n : ℝ)
    have hO_open : IsOpen O := Metric.isOpen_ball.prod isOpen_Ioi
    have hO_subset : O ⊆ A := by
      intro p hp
      rcases hp with ⟨hp₁, hp₂⟩
      have hp₂' : (n : ℝ) ≤ p.2 := le_of_lt hp₂
      exact le_trans
        (show f p.1 ≤ (n : ℝ) from hball_sublevel hp₁)
        (by exact_mod_cast hp₂')
    refine ⟨((z : E), (n : ℝ) + 1), ?_⟩
    refine interior_maximal hO_subset hO_open ?_
    exact ⟨by simpa [Metric.mem_ball] using hρ_pos, by simp⟩
  have hpoint_not_int : ((x, (f x).toReal) : E × ℝ) ∉ interior A := by
    intro hxA
    rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hxA) with ⟨ε, hε_pos, hball⟩
    have hfst : x ∈ Metric.ball x ε := by
      simpa [Metric.mem_ball] using hε_pos
    have hsnd : (f x).toReal - ε / 2 ∈ Metric.ball (f x).toReal ε := by
      have hhalf : ε / 2 < ε := by
        linarith
      have habs : |((f x).toReal - ε / 2) - (f x).toReal| = ε / 2 := by
        have hcalc : ((f x).toReal - ε / 2) - (f x).toReal = -(ε / 2) := by
          ring
        rw [hcalc, abs_neg, abs_of_nonneg (by positivity)]
      have hhalf' : |ε| / 2 < ε := by
        simpa [abs_of_pos hε_pos] using hhalf
      simpa [Metric.mem_ball, Real.dist_eq, habs] using hhalf'
    have hdown_prod :
        ((x, (f x).toReal - ε / 2) : E × ℝ) ∈
          Metric.ball x ε ×ˢ Metric.ball (f x).toReal ε := by
      exact ⟨hfst, hsnd⟩
    have hdown_ball :
        ((x, (f x).toReal - ε / 2) : E × ℝ) ∈ Metric.ball ((x, (f x).toReal) : E × ℝ) ε := by
      simpa [ball_prod_same] using hdown_prod
    have hdown_mem : ((x, (f x).toReal - ε / 2) : E × ℝ) ∈ A := hball hdown_ball
    have hdown_lt :
        (((f x).toReal - ε / 2 : ℝ) : EReal) < f x := by
      rw [← EReal.coe_toReal hfx_ne_top hfx_ne_bot]
      exact_mod_cast sub_lt_self ((f x).toReal) (half_pos hε_pos)
    exact (not_le_of_gt hdown_lt) hdown_mem
  obtain ⟨L, hLne, hLsup⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hA_convex hpoint_not_int hA_int
  let a : ℝ := L ((0 : E), (1 : ℝ))
  let horiz : StrongDual ℝ E := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hdecomp (y : E) (r : ℝ) :
      L (y, r) = horiz y + r * a := by
    calc
      L (y, r) = L ((y, (0 : ℝ)) + ((0 : E), r)) := by simp
      _ = L (y, (0 : ℝ)) + L ((0 : E), r) := by rw [map_add]
      _ = horiz y + r * a := by
        rw [show ((0 : E), r) = r • ((0 : E), (1 : ℝ)) by simp, map_smul]
        simp [horiz, a, smul_eq_mul]
  have ha_nonpos : a ≤ 0 := by
    have hxup : ((x, (f x).toReal + 1) : E × ℝ) ∈ A := by
      change f x ≤ (((f x).toReal + 1 : ℝ) : EReal)
      rw [← EReal.coe_toReal hfx_ne_top hfx_ne_bot]
      exact_mod_cast le_add_of_nonneg_right zero_le_one
    have hstep := hLsup ((x, (f x).toReal + 1) : E × ℝ) hxup
    rw [hdecomp x ((f x).toReal + 1), hdecomp x (f x).toReal] at hstep
    linarith
  have ha_ne : a ≠ 0 := by
    intro ha_zero
    have hhoriz_zero : ∀ v : E, horiz v = 0 := by
      intro v
      rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx) with ⟨ε, hε_pos, hε_subset⟩
      let t : ℝ := min (ε / (‖v‖ + 1)) 1
      have ht_pos : 0 < t := by
        dsimp [t]
        refine lt_min ?_ zero_lt_one
        positivity
      have ht_nonneg : 0 ≤ t := ht_pos.le
      have hle : t ≤ ε / (‖v‖ + 1) := by
        dsimp [t]
        exact min_le_left _ _
      have hscaled : t * (‖v‖ + 1) ≤ ε := by
        have hden : 0 < ‖v‖ + 1 := by
          positivity
        have hmul := mul_le_mul_of_nonneg_right hle hden.le
        calc
          t * (‖v‖ + 1) ≤ (ε / (‖v‖ + 1)) * (‖v‖ + 1) := hmul
          _ = ε := by
            field_simp [hden.ne']
      have hnorm_lt : ‖t • v‖ < ε := by
        have hlt_aux : t * ‖v‖ < t * (‖v‖ + 1) := by
          nlinarith [ht_pos]
        have htv : t * ‖v‖ < ε := lt_of_lt_of_le hlt_aux hscaled
        simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg] using htv
      have hplus_mem : x + t • v ∈ s := by
        apply interior_subset
        apply hε_subset
        simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc] using hnorm_lt
      have hminus_mem : x - t • v ∈ s := by
        apply interior_subset
        apply hε_subset
        simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, sub_eq_add_neg, norm_neg]
          using hnorm_lt
      have hplus :=
        hLsup ((x + t • v, (f (x + t • v)).toReal) : E × ℝ) (by
          change f (x + t • v) ≤ (((f (x + t • v)).toReal : ℝ) : EReal)
          exact EReal.le_coe_toReal (ne_of_lt hplus_mem))
      have hminus :=
        hLsup ((x - t • v, (f (x - t • v)).toReal) : E × ℝ) (by
          change f (x - t • v) ≤ (((f (x - t • v)).toReal : ℝ) : EReal)
          exact EReal.le_coe_toReal (ne_of_lt hminus_mem))
      rw [hdecomp (x + t • v) (f (x + t • v)).toReal,
        hdecomp x (f x).toReal, ha_zero] at hplus
      rw [hdecomp (x - t • v) (f (x - t • v)).toReal,
        hdecomp x (f x).toReal, ha_zero] at hminus
      have hpos : t * horiz v ≤ 0 := by
        have hpos' : horiz x + t * horiz v ≤ horiz x := by
          simpa [horiz, map_add, map_smul, smul_eq_mul, add_comm, add_left_comm, add_assoc]
            using hplus
        linarith
      have hneg : (-t) * horiz v ≤ 0 := by
        have hneg' : horiz x + horiz (-(t • v)) ≤ horiz x := by
          simpa [horiz, sub_eq_add_neg, map_add, add_comm, add_left_comm, add_assoc] using hminus
        rw [show -(t • v) = (-t) • v by simp, map_smul, smul_eq_mul] at hneg'
        linarith
      have hv_nonpos : horiz v ≤ 0 := by
        nlinarith [hpos, ht_pos]
      have hv_nonneg : 0 ≤ horiz v := by
        nlinarith [hneg, ht_pos]
      exact le_antisymm hv_nonpos hv_nonneg
    have hLzero : L = 0 := by
      apply ContinuousLinearMap.ext
      intro q
      rcases q with ⟨v, r⟩
      simp [hdecomp, ha_zero, hhoriz_zero v]
    exact hLne hLzero
  have ha : a < 0 := lt_of_le_of_ne ha_nonpos ha_ne
  let g : StrongDual ℝ E := ((-a)⁻¹) • horiz
  refine ⟨g, ?_⟩
  rw [mem_strongDualSubdifferential, mem_subdifferential]
  rw [is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hx_dom, ?_⟩
  intro y hy
  have hsupp : L (y, (f y).toReal) ≤ L (x, (f x).toReal) := by
    exact hLsup ((y, (f y).toReal) : E × ℝ) (by
      change f y ≤ (((f y).toReal : ℝ) : EReal)
      exact EReal.le_coe_toReal (ne_of_lt hy))
  have hsupp' :
      horiz y + (f y).toReal * a ≤ horiz x + (f x).toReal * a := by
    simpa [hdecomp] using hsupp
  have hhoriz :
      horiz (y - x) ≤ (-a) * ((f y).toReal - (f x).toReal) := by
    have hyx : horiz y = horiz (y - x) + horiz x := by
      calc
        horiz y = horiz ((y - x) + x) := by simp
        _ = horiz (y - x) + horiz x := by rw [map_add]
    rw [hyx] at hsupp'
    linarith
  have hg_real : (f x).toReal + g (y - x) ≤ (f y).toReal := by
    have hvalue :
        g (y - x) ≤ (f y).toReal - (f x).toReal := by
      have hg_apply : g (y - x) = horiz (y - x) / (-a) := by
        rw [show g (y - x) = ((-a)⁻¹ * horiz (y - x)) by
          simp [g, horiz, smul_eq_mul]]
        rw [div_eq_mul_inv, mul_comm]
      rw [hg_apply]
      exact (div_le_iff₀ (neg_pos.mpr ha)).2 (by simpa [mul_comm] using hhoriz)
    linarith
  have hfy_ne_top : f y ≠ ⊤ := ne_of_lt hy
  have hfy_ne_bot : f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot y
  have hfx_eq : f x = (((f x).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hfx_ne_top hfx_ne_bot).symm
  have hfy_eq : f y = (((f y).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hfy_ne_top hfy_ne_bot).symm
  have hxy_ereal' :
      (((f x).toReal : ℝ) : EReal) + (g (y - x) : EReal) ≤ (((f y).toReal : ℝ) : EReal) := by
    exact_mod_cast hg_real
  calc
    f x + (g (y - x) : EReal) =
        (((f x).toReal : ℝ) : EReal) + (g (y - x) : EReal) := by
      rw [hfx_eq, EReal.toReal_coe]
    _ ≤ (((f y).toReal : ℝ) : EReal) := hxy_ereal'
    _ = f y := hfy_eq.symm

/-- Helper for Theorem 8.40: at a feasible outer iterate, the missing step is the existence of a
strong-dual subgradient for the current component objective at `x[k]`. -/
private lemma componentOuterStrongSubgradientExists_ofFeasible
    (k : ℕ) {i : ℕ} (hi : i < m) :
    ∃ ζ : StrongDual ℝ E,
      ζ ∈ strongDualSubdifferential (fi ⟨i, hi⟩) (x[k] : E) := by
  let ii : Fin m := ⟨i, hi⟩
  letI : IsProperExtendedRealFunction (fi ii) := h_incremental.proper ii
  have hxk_int : (x[k] : E) ∈ interior (effective_domain (fi ii)) := by
    -- The outer iterate is feasible, so the component objective is finite on a whole
    -- neighborhood of `x[k]`.
    exact componentInteriorEffectiveDomain_of_feasible
      (h_problem := h_problem) (h_incremental := h_incremental) (x[k]).property ii
  simpa [ii] using
    strongDualSubdifferentialNonempty_ofInteriorProperClosedConvex
      (f := fi ii) (x := (x[k] : E))
      (h_closed := h_incremental.closed ii)
      (h_convex := h_incremental.convex ii)
      hxk_int

/-- Helper for Theorem 8.40: the stage-component gap controls the outer-iterate component gap up
to the Lipschitz drift term. -/
private lemma componentGapCompareToOuterIterateNoFD
    (k : ℕ) {i : ℕ} (hi : i < m) {xStar : E} :
    (fi ⟨i, hi⟩ x[k, i]).toReal - (fi ⟨i, hi⟩ xStar).toReal ≥
      (fi ⟨i, hi⟩ x[k]).toReal - (fi ⟨i, hi⟩ xStar).toReal -
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
  have houterStrong :=
    componentOuterStrongSubgradientExists_ofFeasible
      (h_problem := h_problem) (h_incremental := h_incremental)
      (g := g) (t := t) (x0 := x0)
      (k := k) (i := i) hi
  -- Route correction: the real blocker is outer-point strong-dual existence, not a global
  -- feasible-set Lipschitz estimate.
  exact componentGapCompareToOuterIterateNoFD_of_outerStrongSubgradientExists
    (h_problem := h_problem) (h_incremental := h_incremental)
    (g := g) (t := t) (x0 := x0) (k := k) (i := i) hi (xStar := xStar) houterStrong

/-- Helper for Theorem 8.40: the outer iterate's component value is controlled by the
corresponding inner-stage value plus the stage drift term. -/
private lemma outerIterateComponentValue_le_innerStageValue_addDrift
    (k : ℕ) {i : ℕ} (hi : i < m) :
      (fi ⟨i, hi⟩ x[k]).toReal ≤
      (fi ⟨i, hi⟩ x[k, i]).toReal +
        h_incremental.L * ‖((x[k, i] : E) - (x[k] : E))‖ := by
  have hcompare :=
    componentGapCompareToOuterIterateNoFD
      (h_problem := h_problem)
      (h_incremental := h_incremental)
      (g := g) (t := t) (x0 := x0)
      (k := k) (i := i) hi (xStar := (x[k] : E))
  -- Freeze the comparison point at the outer iterate and rearrange the resulting drift bound.
  linarith

/-- Helper for Theorem 8.40: the summed inner-stage gaps dominate the outer objective gap up to
the index-weighted drift remainder. -/
private lemma incrementalStageGapSum_ge_outerObjectiveGap_minusIndexDrift
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (h_stepsize_pos : ∀ n, 0 < t n)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum Finset.univ (fun i : Fin m ↦
      ((fi i x[k, i.1]).toReal - (fi i xStar).toReal)) ≥
      (((finite_sum_objective fi) x[k]).toReal - fOpt) -
        (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) * t k * h_incremental.L ^ (2 : ℕ) := by
  have hxStar_data : xStar ∈ C ∧ IsMinOn (finite_sum_objective fi) C xStar := by
    -- Optimal-set membership provides the feasible comparison point for the aggregate rewrites.
    simpa [h_problem.optimal_set_eq] using hxStar
  have hpoint :
      ∀ i : Fin m,
        (fi i x[k]).toReal - (fi i xStar).toReal ≤
          ((fi i x[k, i.1]).toReal - (fi i xStar).toReal) +
            (i : ℝ) * t k * h_incremental.L ^ (2 : ℕ) := by
    intro i
    have hcomp :=
      outerIterateComponentValue_le_innerStageValue_addDrift
        (h_problem := h_problem) (h_incremental := h_incremental)
        (g := g) (t := t) (x0 := x0) (k := k) (i := i.1) i.2
    have hgap :
        (fi i x[k]).toReal - (fi i xStar).toReal ≤
          ((fi i x[k, i.1]).toReal + h_incremental.L * ‖((x[k, i.1] : E) - (x[k] : E))‖) -
            (fi i xStar).toReal := by
      exact sub_le_sub_right hcomp (fi i xStar).toReal
    have hdist :=
      incrementalInnerStage_distBase_le
        (h_problem := h_problem) (h_incremental := h_incremental)
        (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_pos
        (k := k) (i := i.1) (Nat.le_of_lt i.2)
    have hdrift :
        h_incremental.L * ‖((x[k, i.1] : E) - (x[k] : E))‖ ≤
          (i : ℝ) * t k * h_incremental.L ^ (2 : ℕ) := by
      -- The accumulated inner-stage displacement is at most `i * t_k * L`.
      nlinarith [hdist, h_stepsize_pos k, h_incremental.L_pos]
    linarith
  have hsumPoint :
      Finset.sum Finset.univ (fun i : Fin m ↦ ((fi i x[k]).toReal - (fi i xStar).toReal)) ≤
        Finset.sum Finset.univ (fun i : Fin m ↦
          (((fi i x[k, i.1]).toReal - (fi i xStar).toReal) +
            (i : ℝ) * t k * h_incremental.L ^ (2 : ℕ))) := by
    -- Sum the componentwise reverse comparison after inserting the controlled drift term.
    exact Finset.sum_le_sum (fun i _ ↦ hpoint i)
  have houterEq :
      Finset.sum Finset.univ (fun i : Fin m ↦ ((fi i x[k]).toReal - (fi i xStar).toReal)) =
        ((finite_sum_objective fi) x[k]).toReal - fOpt := by
    have hxStarSum :
        Finset.sum Finset.univ (fun i : Fin m ↦ (fi i xStar).toReal) = fOpt := by
      calc
        Finset.sum Finset.univ (fun i : Fin m ↦ (fi i xStar).toReal) =
            ((finite_sum_objective fi) xStar).toReal := by
              symm
              exact finiteSumObjective_toReal_eq_sum_componentToReal
                (h_problem := h_problem) (h_incremental := h_incremental)
                (x := xStar) hxStar_data.1
        _ = fOpt := optimal_point_toReal_eq_fOpt h_problem hxStar
    -- Collapse the outer-iterate component sum and the optimal-point component sum.
    rw [Finset.sum_sub_distrib,
      finiteSumObjective_toReal_eq_sum_componentToReal
        (h_problem := h_problem) (h_incremental := h_incremental)
        (x := (x[k] : E)) (x[k]).property,
      hxStarSum]
  have hdriftSum :
      Finset.sum Finset.univ (fun i : Fin m ↦ (i : ℝ) * t k * h_incremental.L ^ (2 : ℕ)) =
        (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) * t k * h_incremental.L ^ (2 : ℕ) := by
    -- Pull the common `t_k L^2` factor out of the finite index sum.
    calc
      Finset.sum Finset.univ (fun i : Fin m ↦ (i : ℝ) * t k * h_incremental.L ^ (2 : ℕ)) =
          Finset.sum Finset.univ (fun i : Fin m ↦ (i : ℝ) * (t k * h_incremental.L ^ (2 : ℕ))) := by
            simp [mul_assoc]
      _ = (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) * (t k * h_incremental.L ^ (2 : ℕ)) := by
            simpa using
              (Finset.sum_mul (s := Finset.univ)
                (f := fun i : Fin m ↦ (i : ℝ)) (a := t k * h_incremental.L ^ (2 : ℕ))).symm
      _ = (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) * t k * h_incremental.L ^ (2 : ℕ) := by
            ring
  rw [houterEq, Finset.sum_add_distrib, hdriftSum] at hsumPoint
  linarith

/-- Helper for Theorem 8.40: each outer incremental step satisfies the same fundamental
inequality as Lemma 8.39, proved here without the finite-dimensional detour. -/
private lemma incrementalOuterStepFundamentalInequality
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (h_stepsize_pos : ∀ n, 0 < t n)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖x[k + 1] - xStar‖ ^ (2 : ℕ) ≤
      ‖x[k] - xStar‖ ^ (2 : ℕ) -
        2 * t k * (((finite_sum_objective fi) x[k]).toReal - fOpt) +
          (t k) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ) := by
  have hxStar_data : xStar ∈ C ∧ IsMinOn (finite_sum_objective fi) C xStar := by
    -- Optimal-set membership provides the feasible comparison point used throughout the proof.
    simpa [h_problem.optimal_set_eq] using hxStar
  have hcum :
      ∀ {j : ℕ}, j ≤ m →
        ‖x[k, j] - xStar‖ ^ (2 : ℕ) ≤
          ‖x[k] - xStar‖ ^ (2 : ℕ) -
            2 * t k *
              Finset.sum (Finset.range j) (fun r ↦
                if hr : r < m then
                  (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
                else 0) +
              (t k) ^ (2 : ℕ) * (j : ℝ) * h_incremental.L ^ (2 : ℕ) := by
    intro j hj
    induction j with
    | zero =>
        -- At stage `0` no inner update has occurred, so the cumulative bound is exact.
        rw [incremental_projected_subgradient_method_inner_zero]
        simp
    | succ j ih =>
        have hj_lt : j < m := Nat.lt_of_succ_le hj
        have hstep :=
          incrementalInnerStage_sqdistStep
            (h_problem := h_problem) (h_incremental := h_incremental)
            (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_pos
            (k := k) (i := j) hj_lt (xStar := xStar) hxStar_data.1
        have hprev := ih (Nat.le_of_lt hj_lt)
        have hsum :
            Finset.sum (Finset.range (j + 1)) (fun r ↦
                if hr : r < m then
                  (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
                else 0) =
              Finset.sum (Finset.range j) (fun r ↦
                  if hr : r < m then
                    (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
                  else 0) +
                ((fi ⟨j, hj_lt⟩ x[k, j]).toReal - (fi ⟨j, hj_lt⟩ xStar).toReal) := by
          -- The next cumulative sum appends exactly the current component gap.
          rw [Finset.sum_range_succ]
          simp [hj_lt]
        calc
          ‖x[k, j + 1] - xStar‖ ^ (2 : ℕ) ≤
              ‖x[k, j] - xStar‖ ^ (2 : ℕ) -
                2 * t k * ((fi ⟨j, hj_lt⟩ x[k, j]).toReal - (fi ⟨j, hj_lt⟩ xStar).toReal) +
                  (t k) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ) := hstep
          _ ≤ ‖x[k] - xStar‖ ^ (2 : ℕ) -
                2 * t k *
                  (Finset.sum (Finset.range j) (fun r ↦
                      if hr : r < m then
                        (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
                      else 0) +
                    ((fi ⟨j, hj_lt⟩ x[k, j]).toReal - (fi ⟨j, hj_lt⟩ xStar).toReal)) +
                  ((t k) ^ (2 : ℕ) * (j : ℝ) * h_incremental.L ^ (2 : ℕ) +
                    (t k) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) := by
              nlinarith [hprev]
          _ = ‖x[k] - xStar‖ ^ (2 : ℕ) -
                2 * t k *
                  Finset.sum (Finset.range (j + 1)) (fun r ↦
                    if hr : r < m then
                      (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
                    else 0) +
                  (t k) ^ (2 : ℕ) * ((j + 1 : ℕ) : ℝ) * h_incremental.L ^ (2 : ℕ) := by
              rw [hsum, Nat.cast_add, Nat.cast_one]
              ring
  have hcum_m :
      ‖x[k + 1] - xStar‖ ^ (2 : ℕ) ≤
          ‖x[k] - xStar‖ ^ (2 : ℕ) -
          2 * t k *
            Finset.sum (Finset.range m) (fun r ↦
              if hr : r < m then
                (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
              else 0) +
            (t k) ^ (2 : ℕ) * (m : ℝ) * h_incremental.L ^ (2 : ℕ) := by
    -- The outer iterate `x[k + 1]` is the final inner stage `x[k,m]`.
    simpa [incremental_projected_subgradient_method_succ
      C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex
      t g x0 k] using
      (hcum (j := m) le_rfl)
  have hstageSumEq :
      Finset.sum (Finset.range m) (fun r ↦
          if hr : r < m then
            (fi ⟨r, hr⟩ x[k, r]).toReal - (fi ⟨r, hr⟩ xStar).toReal
          else 0) =
        Finset.sum Finset.univ
          (fun i : Fin m ↦ ((fi i x[k, i.1]).toReal - (fi i xStar).toReal)) := by
    -- Reindex the range sum by `Fin m` so the aggregate-value identities apply directly.
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp
  have hgapSum :=
    incrementalStageGapSum_ge_outerObjectiveGap_minusIndexDrift
      (h_problem := h_problem) (h_incremental := h_incremental)
      (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_pos hxStar k
  have hindexSum :
      (2 : ℝ) * (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) + m = (m : ℝ) ^ (2 : ℕ) := by
    -- The textbook coefficient identity `2 * ∑_{i=0}^{m-1} i + m = m^2` closes the error term.
    have hdoubleNat : 2 * Finset.sum (Finset.range m) (fun i ↦ i) = m * (m - 1) := by
      calc
        2 * Finset.sum (Finset.range m) (fun i ↦ i) = 2 * (m * (m - 1) / 2) := by
          rw [Finset.sum_range_id]
        _ = m * (m - 1) := by
          rw [← Nat.mul_div_assoc 2 (Nat.even_mul_pred_self m).two_dvd]
          simp
    have hsumCast :
        Finset.sum (Finset.range m) (fun i ↦ (i : ℝ)) =
          ((Finset.sum (Finset.range m) fun i ↦ i : ℕ) : ℝ) := by
      norm_num
    have hindexRange :
        (2 : ℝ) * Finset.sum (Finset.range m) (fun i ↦ (i : ℝ)) + m = (m : ℝ) ^ (2 : ℕ) := by
      have hdoubleRange :
          (2 : ℝ) * Finset.sum (Finset.range m) (fun i ↦ (i : ℝ)) =
            ((m * (m - 1) : ℕ) : ℝ) := by
        rw [hsumCast]
        exact_mod_cast hdoubleNat
      calc
        (2 : ℝ) * Finset.sum (Finset.range m) (fun i ↦ (i : ℝ)) + m =
            ((m * (m - 1) : ℕ) : ℝ) + m := by
              rw [hdoubleRange]
        _ = (m : ℝ) ^ (2 : ℕ) := by
              cases m with
              | zero =>
                  norm_num
              | succ n =>
                  simp [Nat.cast_add, Nat.cast_one]
                  ring
    simpa [Fin.sum_univ_eq_sum_range] using hindexRange
  calc
    ‖x[k + 1] - xStar‖ ^ (2 : ℕ) ≤
        ‖x[k] - xStar‖ ^ (2 : ℕ) -
          2 * t k * (((finite_sum_objective fi) x[k]).toReal - fOpt) +
            (t k) ^ (2 : ℕ) *
              (((2 : ℝ) * (Finset.sum Finset.univ fun i : Fin m ↦ (i : ℝ)) + m) *
                h_incremental.L ^ (2 : ℕ)) := by
      -- Combine the cumulative descent estimate with the aggregate stage-gap lower bound.
      rw [hstageSumEq] at hcum_m
      nlinarith [hcum_m, hgapSum, h_stepsize_pos k, h_incremental.L_pos]
    _ = ‖x[k] - xStar‖ ^ (2 : ℕ) -
          2 * t k * (((finite_sum_objective fi) x[k]).toReal - fOpt) +
            (t k) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ) := by
      rw [hindexSum]
      ring

/-- Helper for Theorem 8.40: summing Lemma 8.39 over the interval `a, ..., a + q` yields the
telescoping weighted-gap estimate with the explicit quadratic remainder. -/
private lemma incrementalWeightedObjectiveGapIntervalWithRemainder_le
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (h_stepsize_pos : ∀ n, 0 < t n)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (a q : ℕ) :
    Finset.sum (Finset.Icc a (a + q))
        (fun n ↦ t n * (((finite_sum_objective fi) x[n]).toReal - fOpt)) +
        (1 / 2 : ℝ) * ‖x[a + q + 1] - xStar‖ ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * ‖x[a] - xStar‖ ^ (2 : ℕ) +
        (1 / 2 : ℝ) *
          Finset.sum (Finset.Icc a (a + q))
            (fun n ↦ (t n) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) := by
  induction q with
  | zero =>
      have hstep :=
        incrementalOuterStepFundamentalInequality
          (h_problem := h_problem) (h_incremental := h_incremental)
          (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_pos hxStar a
      have hbase :
          t a * (((finite_sum_objective fi) x[a]).toReal - fOpt) +
              (1 / 2 : ℝ) * ‖x[a + 1] - xStar‖ ^ (2 : ℕ) ≤
            (1 / 2 : ℝ) * ‖x[a] - xStar‖ ^ (2 : ℕ) +
              (1 / 2 : ℝ) *
                ((t a) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) := by
        -- Halving the one-step inequality puts it into the textbook weighted-gap form.
        nlinarith
      simpa using hbase
  | succ q ih =>
      have hstep :=
        incrementalOuterStepFundamentalInequality
          (h_problem := h_problem) (h_incremental := h_incremental)
          (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_pos hxStar (a + q + 1)
      have hstep' :
          t (a + q + 1) * (((finite_sum_objective fi) x[a + q + 1]).toReal - fOpt) +
              (1 / 2 : ℝ) * ‖x[a + q + 2] - xStar‖ ^ (2 : ℕ) ≤
            (1 / 2 : ℝ) * ‖x[a + q + 1] - xStar‖ ^ (2 : ℕ) +
              (1 / 2 : ℝ) *
                ((t (a + q + 1)) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) := by
        -- The next single step contributes one more weighted gap term and one more quadratic
        -- remainder term.
        nlinarith
      have hIcc :
          Finset.Icc a (a + q + 1) = insert (a + q + 1) (Finset.Icc a (a + q)) := by
        ext n
        simp [Finset.mem_Icc]
        omega
      calc
        Finset.sum (Finset.Icc a (a + q + 1))
            (fun n ↦ t n * (((finite_sum_objective fi) x[n]).toReal - fOpt)) +
            (1 / 2 : ℝ) * ‖x[a + q + 2] - xStar‖ ^ (2 : ℕ)
            =
          Finset.sum (Finset.Icc a (a + q))
              (fun n ↦ t n * (((finite_sum_objective fi) x[n]).toReal - fOpt)) +
            (t (a + q + 1) * (((finite_sum_objective fi) x[a + q + 1]).toReal - fOpt) +
              (1 / 2 : ℝ) * ‖x[a + q + 2] - xStar‖ ^ (2 : ℕ)) := by
              rw [hIcc, Finset.sum_insert]
              · ring
              · simp
        _ ≤ (1 / 2 : ℝ) * ‖x[a] - xStar‖ ^ (2 : ℕ) +
            ((1 / 2 : ℝ) *
                Finset.sum (Finset.Icc a (a + q))
                  (fun n ↦ (t n) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) +
              (1 / 2 : ℝ) *
                ((t (a + q + 1)) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) *
                  h_incremental.L ^ (2 : ℕ))) := by
              nlinarith [ih, hstep']
        _ =
          (1 / 2 : ℝ) * ‖x[a] - xStar‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              Finset.sum (Finset.Icc a (a + q + 1))
                (fun n ↦ (t n) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) := by
              rw [hIcc, Finset.sum_insert]
              · ring
              · simp

/-- Helper for Theorem 8.40: the running-best objective gap on any interval is bounded by the
textbook ratio involving the interval sums of `t n` and `t n ^ 2`. -/
private lemma incrementalBestValueGap_leIntervalRatioBound
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (h_stepsize_pos : ∀ n, 0 < t n)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (a q : ℕ) :
    best_achieved_function_value
        (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
        (fun n ↦ x[n]) (a + q) - fOpt ≤
      (((1 / 2 : ℝ) * ‖x[a] - xStar‖ ^ (2 : ℕ)) /
          Finset.sum (Finset.Icc a (a + q)) (fun n ↦ t n)) +
        ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) *
          (Finset.sum (Finset.Icc a (a + q)) (fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.Icc a (a + q)) (fun n ↦ t n))) := by
  let interval : Finset ℕ := Finset.Icc a (a + q)
  let S : ℝ := Finset.sum interval (fun n ↦ t n)
  let bestGap : ℝ :=
    best_achieved_function_value
      (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
      (fun n ↦ x[n]) (a + q) - fOpt
  have hS_pos : 0 < S := by
    -- The interval denominator is strictly positive because every stepsize is positive.
    simpa [S, interval] using
      positiveStepsizeIntervalSum_pos
        (t := t) h_stepsize_pos a q
  have hS_best :
      Finset.sum interval (fun n ↦ t n * bestGap) = S * bestGap := by
    symm
    dsimp [S, interval]
    exact Finset.sum_mul _ _ _
  have hbest_sum_le :
      S * bestGap ≤
        Finset.sum interval (fun n ↦ t n * (((finite_sum_objective fi) x[n]).toReal - fOpt)) := by
    -- Compare the running best with each objective value in the interval and sum the inequalities.
    rw [← hS_best]
    refine Finset.sum_le_sum ?_
    intro n hn
    have hn_range : n ∈ Finset.range (a + q + 1) := by
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
    have hbest_le :
        best_achieved_function_value
            (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
            (fun j ↦ x[j]) (a + q) ≤
          ((finite_sum_objective fi) x[n]).toReal :=
      best_achieved_function_value_le_objective_value
        (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
        (fun j ↦ x[j]) (a + q) n hn_range
    exact
      mul_le_mul_of_nonneg_left
        (sub_le_sub_right hbest_le fOpt)
        (le_of_lt (h_stepsize_pos n))
  have hweighted :=
    incrementalWeightedObjectiveGapIntervalWithRemainder_le
      (h_problem := h_problem) (h_incremental := h_incremental)
      (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_pos hxStar a q
  have hrest_nonneg :
      0 ≤ (1 / 2 : ℝ) * ‖x[a + q + 1] - xStar‖ ^ (2 : ℕ) := by
    positivity
  have hmain :
      S * bestGap ≤
        (1 / 2 : ℝ) * ‖x[a] - xStar‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            Finset.sum interval
              (fun n ↦ (t n) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) := by
    -- Drop the nonnegative terminal remainder after comparing the running best with the interval.
    nlinarith [hbest_sum_le, hweighted, hrest_nonneg]
  have hquad_eq :
      (1 / 2 : ℝ) *
          Finset.sum interval
            (fun n ↦ (t n) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) =
        ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) *
          Finset.sum interval (fun n ↦ (t n) ^ (2 : ℕ))) := by
    -- Pull the constant quadratic coefficient out of the interval sum.
    calc
      (1 / 2 : ℝ) *
          Finset.sum interval
            (fun n ↦ (t n) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ))
          =
        (1 / 2 : ℝ) *
          Finset.sum interval
            (fun n ↦ ((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) * (t n) ^ (2 : ℕ)) := by
            refine congrArg ((1 / 2 : ℝ) * ·) ?_
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ = (1 / 2 : ℝ) *
            (((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) *
              Finset.sum interval (fun n ↦ (t n) ^ (2 : ℕ))) := by
            rw [← Finset.mul_sum]
      _ =
        ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) *
          Finset.sum interval (fun n ↦ (t n) ^ (2 : ℕ))) := by
            ring
  have hdiv :
      bestGap ≤
        (((1 / 2 : ℝ) * ‖x[a] - xStar‖ ^ (2 : ℕ) +
            ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) *
              Finset.sum interval (fun n ↦ (t n) ^ (2 : ℕ)))) / S) := by
    rw [le_div_iff₀ hS_pos]
    have hmain' := hmain
    rw [hquad_eq] at hmain'
    simpa [bestGap, S, interval, mul_comm, mul_left_comm, mul_assoc] using hmain'
  calc
    best_achieved_function_value
        (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
        (fun n ↦ x[n]) (a + q) - fOpt = bestGap := by
      rfl
    _ ≤
        (((1 / 2 : ℝ) * ‖x[a] - xStar‖ ^ (2 : ℕ) +
            ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) *
              Finset.sum interval (fun n ↦ (t n) ^ (2 : ℕ)))) / S) := hdiv
    _ =
        (((1 / 2 : ℝ) * ‖x[a] - xStar‖ ^ (2 : ℕ)) / S) +
          ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) *
            (Finset.sum interval (fun n ↦ (t n) ^ (2 : ℕ)) / S)) := by
            field_simp [hS_pos.ne']
    _ =
        (((1 / 2 : ℝ) * ‖x[a] - xStar‖ ^ (2 : ℕ)) /
            Finset.sum (Finset.Icc a (a + q)) (fun n ↦ t n)) +
          ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) *
            (Finset.sum (Finset.Icc a (a + q)) (fun n ↦ (t n) ^ (2 : ℕ)) /
              Finset.sum (Finset.Icc a (a + q)) (fun n ↦ t n))) := by
            simp [S, interval]

omit h_incremental in
/-- Helper for Theorem 8.40: the running-best aggregate objective gap is always nonnegative. -/
private lemma incrementalBestAchievedObjectiveGap_nonneg
    (k : ℕ) :
    0 ≤
      best_achieved_function_value
          (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
          (fun n ↦ x[n]) k - fOpt := by
  have hbest_lower :
      fOpt ≤
        best_achieved_function_value
          (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
          (fun n ↦ x[n]) k := by
    unfold best_achieved_function_value
    apply Finset.le_min'
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
    simpa using
      feasibleFiniteSumObjectiveGap_nonneg
        (h_problem := h_problem)
        (fi := fi) (C := C) (fOpt := fOpt) (y := (x[n] : E)) (x[n]).property
  linarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] h_problem h_incremental in
/-- Helper for Theorem 8.40: if `∑ t_n^2 / ∑ t_n → 0` and all stepsizes are positive, then the
prefix sums `∑ t_n` diverge to `+∞`. -/
private lemma stepsizePrefixSum_tendsto_atTop_of_ratio_tendsto_zero
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦ Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
      Filter.atTop Filter.atTop := by
  let S : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n)
  let Q : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))
  have hS_pos : ∀ k, 0 < S k := by
    intro k
    -- Every prefix sum contains the positive summand `t 0`.
    have hmem : 0 ∈ Finset.range (k + 1) := by
      simp
    have hle :
        t 0 ≤ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := by
      simpa [S] using
        (Finset.single_le_sum (fun n _ ↦ le_of_lt (h_stepsize_pos n)) hmem)
    exact lt_of_lt_of_le (h_stepsize_pos 0) hle
  have hS_mono : Monotone S := by
    -- Each next prefix sum adds the nonnegative summand `t (k + 1)`.
    refine monotone_nat_of_le_succ ?_
    intro k
    have hsucc : S (k + 1) = S k + t (k + 1) := by
      simp [S, Finset.sum_range_succ]
    calc
      S k ≤ S k + t (k + 1) := by
        exact le_add_of_nonneg_right (le_of_lt (h_stepsize_pos (k + 1)))
      _ = S (k + 1) := hsucc.symm
  refine Filter.tendsto_atTop.2 ?_
  intro b
  by_cases hb : b < S 0
  · exact
      (Filter.eventually_ge_atTop 0).mono fun n hn ↦
        le_trans (le_of_lt hb) (hS_mono hn)
  · have hS0_le_b : S 0 ≤ b := le_of_not_gt hb
    have hexists : ∃ N, b ≤ S N := by
      by_contra hbounded
      have hbounded' : ∀ k, ¬ b ≤ S k := by
        intro k hk
        exact hbounded ⟨k, hk⟩
      have hbound : ∀ k, S k ≤ b := by
        intro k
        exact le_of_not_ge (hbounded' k)
      have hb_pos : 0 < b := lt_of_lt_of_le (hS_pos 0) hS0_le_b
      let c : ℝ := (t 0) ^ (2 : ℕ) / b
      have hc_pos : 0 < c := by
        dsimp [c]
        have ht_sq_pos : 0 < (t 0) ^ (2 : ℕ) := by
          simpa [pow_two] using sq_pos_of_pos (h_stepsize_pos 0)
        exact div_pos ht_sq_pos hb_pos
      have hratio_lower : ∀ k, c ≤ Q k / S k := by
        intro k
        have hQ_lower :
            (t 0) ^ (2 : ℕ) ≤ Q k := by
          have hmem : 0 ∈ Finset.range (k + 1) := by
            simp
          simpa [Q] using
            (Finset.single_le_sum (fun n _ ↦ sq_nonneg (t n)) hmem)
        have hQ_nonneg : 0 ≤ Q k := by
          simpa [Q] using Finset.sum_nonneg (fun n _ ↦ sq_nonneg (t n))
        calc
          c = (t 0) ^ (2 : ℕ) / b := by
            rfl
          _ ≤ Q k / b := by
            exact (div_le_div_iff_of_pos_right hb_pos).2 hQ_lower
          _ ≤ Q k / S k := by
            exact div_le_div_of_nonneg_left hQ_nonneg (hS_pos k) (hbound k)
      have hc_le_zero : c ≤ 0 := by
        have hratio' :
            Filter.Tendsto (fun k ↦ Q k / S k) Filter.atTop (nhds 0) := by
          simpa [S, Q] using h_ratio
        exact
          le_of_tendsto_of_tendsto tendsto_const_nhds hratio'
            (Filter.Eventually.of_forall hratio_lower)
      exact (not_le_of_gt hc_pos) hc_le_zero
    rcases hexists with ⟨N, hN⟩
    exact (Filter.eventually_ge_atTop N).mono fun n hn ↦ le_trans hN (hS_mono hn)

-- Proof sketch: apply Lemma 8.39 to an arbitrary optimal point `xStar ∈ XStar`, sum the
-- fundamental inequality from `0` through `k`, and use the defining minimality of
-- `best_achieved_function_value` to obtain the standard estimate
-- `(f_best^k - fOpt) ≤ (‖x0 - xStar‖² + L² m² ∑_{n ≤ k} t_n²) / (2 ∑_{n ≤ k} t_n)`. The ratio
-- hypothesis forces the error term to vanish, while positivity of the stepsizes makes the
-- denominator diverge.
/-- Companion theorem for Theorem 8.40: clause (a) in gap form. Under Assumptions 8.7 and 8.38,
if the incremental projected subgradient method uses positive stepsizes and the ratio
`(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n)` tends to `0`, then the best objective gap attained by the
first `k + 1` iterates converges to `0`. -/
theorem incremental_projected_subgradient_best_value_gap_tendsto_zero_of_stepsize_ratio
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦
        best_achieved_function_value
            (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
            (fun n ↦ x[n]) k -
          fOpt)
      Filter.atTop (nhds 0) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  let S : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n)
  let Q : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))
  let bestGap : ℕ → ℝ :=
    fun k ↦
      best_achieved_function_value
          (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
          (fun n ↦ x[n]) k - fOpt
  have hS_atTop :
      Filter.Tendsto S Filter.atTop Filter.atTop :=
    stepsizePrefixSum_tendsto_atTop_of_ratio_tendsto_zero
      (t := t) h_stepsize_pos h_ratio
  have hbest_nonneg : ∀ k, 0 ≤ bestGap k := by
    intro k
    -- Every feasible iterate has aggregate value at least `fOpt`, so the running best gap is
    -- nonnegative.
    simpa [bestGap] using
      incrementalBestAchievedObjectiveGap_nonneg
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) k
  have hfirst_tendsto :
      Filter.Tendsto
        (fun k ↦ ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ)) / S k)
        Filter.atTop (nhds 0) :=
    hS_atTop.const_div_atTop ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ))
  have hsecond_tendsto :
      Filter.Tendsto
        (fun k ↦ (((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) * (Q k / S k))
        Filter.atTop (nhds 0) := by
    have hratio' : Filter.Tendsto (fun k ↦ Q k / S k) Filter.atTop (nhds 0) := by
      simpa [Q, S] using h_ratio
    simpa using
      hratio'.const_mul ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2))
  have hupper_tendsto :
      Filter.Tendsto
        (fun k ↦
          (((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ)) / S k) +
            ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) * (Q k / S k)))
        Filter.atTop (nhds 0) := by
    simpa using hfirst_tendsto.add hsecond_tendsto
  have hIcc_zero : ∀ k : ℕ, Finset.Icc 0 k = Finset.range (k + 1) := by
    intro k
    ext n
    constructor
    · intro hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
    · intro hn
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, Nat.le_of_lt_succ (Finset.mem_range.mp hn)⟩
  refine squeeze_zero hbest_nonneg ?_ hupper_tendsto
  intro k
  simpa [bestGap, S, Q, hIcc_zero, incremental_projected_subgradient_method_zero]
    using
      incrementalBestValueGap_leIntervalRatioBound
        (h_problem := h_problem) (h_incremental := h_incremental)
        (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_pos hxStar 0 k

/-- Theorem 8.40 (1): clause (a). Under Assumptions 8.7 and 8.38, if the incremental projected
subgradient method uses positive stepsizes and the ratio
`(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n)` tends to `0`, then the best objective value attained by the
first `k + 1` iterates converges to the optimal value `fOpt`. -/
theorem incremental_projected_subgradient_best_value_tendsto_of_stepsize_ratio
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦
        best_achieved_function_value
            (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
            (fun n ↦ x[n]) k)
      Filter.atTop (nhds fOpt) := by
  -- Add back the constant `fOpt` to the already proved gap convergence statement.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (incremental_projected_subgradient_best_value_gap_tendsto_zero_of_stepsize_ratio
      (h_problem := h_problem) (h_incremental := h_incremental)
      (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_pos h_ratio).const_add fOpt

-- Proof sketch: sum the inequality from Lemma 8.39 over the tail indices `⌊k / 2⌋, …, k`,
-- control the telescoping distance term by the half-squared-diameter bound `Θ`, substitute the
-- explicit stepsize `t_n = √Θ / (L m √(n + 1))`, and then apply Lemma 8.27 (2) with `D = 2`.
/-- Theorem 8.40 (2): clause (b). If `Θ` bounds the half squared diameter of the feasible set `C`
and the incremental projected subgradient method uses the stepsizes
`t_k = √Θ / (L m √(k + 1))`, where `L = h_incremental.L`, then for every `k ≥ 2` the best
objective gap satisfies
`f_best^k - fOpt ≤ 2 (2 + log 3) m L √Θ / √(k + 2)`. The compactness hypothesis from the prose is
omitted because the explicit bound `Θ` is the actual datum used in the estimate. -/
theorem incremental_projected_subgradient_best_value_gap_le_of_half_squared_diameter_stepsize
    (hm : 0 < m)
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) x[k,i])
    (hΘ : C.HasHalfSquaredDiameterBound Θ)
    (h_stepsize :
      ∀ n,
        t n = Real.sqrt Θ /
          (h_incremental.L * (m : ℝ) * Real.sqrt ((n : ℝ) + 1)))
    {k : ℕ} (hk : 2 ≤ k) :
    best_achieved_function_value
        (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
        (fun n ↦ x[n]) k -
      fOpt ≤
      (2 * (2 + Real.log 3)) * (m : ℝ) * h_incremental.L * Real.sqrt Θ /
        Real.sqrt ((k : ℝ) + 2) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  have hxStar_data : xStar ∈ C ∧ IsMinOn (finite_sum_objective fi) C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxStarC : xStar ∈ C := hxStar_data.1
  have hΘ_nonneg : 0 ≤ Θ := by
    have hself := hΘ.bound x0.property x0.property
    nlinarith [hself]
  let tail : Finset ℕ := Finset.Icc (k / 2) k
  let bestGap : ℝ :=
    best_achieved_function_value
        (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
        (fun n ↦ x[n]) k - fOpt
  have hbest_nonneg : 0 ≤ bestGap := by
    -- The running best remains above `fOpt` along the whole trajectory.
    simpa [bestGap] using
      incrementalBestAchievedObjectiveGap_nonneg
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) k
  by_cases hTheta_zero : Θ = 0
  · have hdist0 : (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) ≤ 0 := by
      simpa [hTheta_zero] using hΘ.bound x0.property hxStarC
    have hnorm0 : ‖(x0 : E) - xStar‖ = 0 := by
      nlinarith [hdist0, sq_nonneg ‖(x0 : E) - xStar‖]
    have hx0_eq : (x0 : E) = xStar := sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
    have hbest_le_opt :
        best_achieved_function_value
            (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
            (fun n ↦ x[n]) k ≤ fOpt := by
      -- The initial iterate already equals an optimal point.
      calc
        best_achieved_function_value
            (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
            (fun n ↦ x[n]) k ≤
          ((finite_sum_objective fi) x[0]).toReal := by
            exact
              best_achieved_function_value_le_objective_value
                (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
                (fun n ↦ x[n]) k 0 (by simp)
        _ = ((finite_sum_objective fi) (x0 : E)).toReal := by
            rw [incremental_projected_subgradient_method_zero]
        _ = ((finite_sum_objective fi) xStar).toReal := by rw [hx0_eq]
        _ = fOpt := optimal_point_toReal_eq_fOpt h_problem hxStar
    have hright_zero :
        (2 * (2 + Real.log 3)) * (m : ℝ) * h_incremental.L * Real.sqrt Θ /
          Real.sqrt ((k : ℝ) + 2) = 0 := by
      simp [hTheta_zero]
    rw [hright_zero]
    dsimp [bestGap] at hbest_nonneg ⊢
    linarith
  · have hTheta_pos : 0 < Θ := by
      exact lt_of_le_of_ne hΘ_nonneg (by simpa [eq_comm] using hTheta_zero)
    have hm_real_pos : 0 < (m : ℝ) := by
      exact_mod_cast hm
    have hLm_pos : 0 < h_incremental.L * (m : ℝ) := by
      exact mul_pos h_incremental.L_pos hm_real_pos
    have hsqrtTheta_pos : 0 < Real.sqrt Θ := by
      exact Real.sqrt_pos.2 hTheta_pos
    have h_stepsize_pos : ∀ n, 0 < t n := by
      intro n
      rw [h_stepsize]
      exact div_pos hsqrtTheta_pos (mul_pos hLm_pos (Real.sqrt_pos.2 (by positivity)))
    have htail_pos :
        0 < Finset.sum tail (fun n ↦ t n) := by
      -- The explicit stepsize is positive on every tail index.
      simpa [tail, Nat.add_sub_of_le (Nat.div_le_self k 2)] using
        positiveStepsizeIntervalSum_pos
          (t := t) h_stepsize_pos (k / 2) (k - k / 2)
    have hinv_pos : 0 < inverseSqrtHalfTailSum k := by
      have hden :=
        sqrt_div_four_le_inverseSqrtHalfTailSum k
      exact lt_of_lt_of_le (by positivity : 0 < Real.sqrt ((k : ℝ) + 2) / 4) hden
    have hratio :
        bestGap ≤
          (((1 / 2 : ℝ) * ‖x[k / 2] - xStar‖ ^ (2 : ℕ)) /
              Finset.sum tail (fun n ↦ t n)) +
            ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) *
              (Finset.sum tail (fun n ↦ (t n) ^ (2 : ℕ)) /
                Finset.sum tail (fun n ↦ t n))) := by
      -- Specialize the interval ratio bound to the textbook half-tail `⌊k/2⌋, …, k`.
      simpa [bestGap, tail, Nat.add_sub_of_le (Nat.div_le_self k 2)] using
        incrementalBestValueGap_leIntervalRatioBound
          (h_problem := h_problem) (h_incremental := h_incremental)
          (g := g) (t := t) (x0 := x0)
          h_subgrad h_stepsize_pos hxStar (k / 2) (k - k / 2)
    have hstart_le :
        (1 / 2 : ℝ) * ‖x[k / 2] - xStar‖ ^ (2 : ℕ) ≤ Θ := by
      -- The half-squared-diameter bound controls the tail starting point.
      exact hΘ.bound (x[k / 2]).property hxStarC
    have htail_eq :
        Finset.sum tail (fun n ↦ t n) =
          (Real.sqrt Θ / (h_incremental.L * (m : ℝ))) * inverseSqrtHalfTailSum k := by
      -- Rewrite the explicit half-tail stepsize sum into the named inverse-sqrt tail sum.
      calc
        Finset.sum tail (fun n ↦ t n) =
            Finset.sum tail
              (fun n ↦ (Real.sqrt Θ / (h_incremental.L * (m : ℝ))) *
                (1 / Real.sqrt ((n : ℝ) + 1))) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              rw [h_stepsize]
              field_simp [hLm_pos.ne', show Real.sqrt ((n : ℝ) + 1) ≠ 0 by positivity]
        _ = (Real.sqrt Θ / (h_incremental.L * (m : ℝ))) *
              Finset.sum tail (fun n ↦ 1 / Real.sqrt ((n : ℝ) + 1)) := by
              rw [Finset.mul_sum]
        _ = (Real.sqrt Θ / (h_incremental.L * (m : ℝ))) * inverseSqrtHalfTailSum k := by
              rw [inverseSqrtHalfTailSum]
    have hsqtail_eq :
        Finset.sum tail (fun n ↦ (t n) ^ (2 : ℕ)) =
          (Θ / (h_incremental.L * (m : ℝ)) ^ (2 : ℕ)) * harmonicHalfTailSum k := by
      -- Rewrite the squared explicit stepsizes into the named harmonic half-tail sum.
      calc
        Finset.sum tail (fun n ↦ (t n) ^ (2 : ℕ)) =
            Finset.sum tail
              (fun n ↦ (Θ / (h_incremental.L * (m : ℝ)) ^ (2 : ℕ)) *
                (1 / ((n : ℝ) + 1))) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              rw [h_stepsize]
              field_simp [pow_two, hLm_pos.ne', show ((n : ℝ) + 1) ≠ 0 by positivity,
                show Real.sqrt ((n : ℝ) + 1) ≠ 0 by positivity, Real.sq_sqrt hΘ_nonneg]
              rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)]
              rw [Real.sq_sqrt hΘ_nonneg]
              ring
        _ = (Θ / (h_incremental.L * (m : ℝ)) ^ (2 : ℕ)) *
              Finset.sum tail (fun n ↦ 1 / ((n : ℝ) + 1)) := by
              rw [Finset.mul_sum]
        _ = (Θ / (h_incremental.L * (m : ℝ)) ^ (2 : ℕ)) * harmonicHalfTailSum k := by
              rw [harmonicHalfTailSum]
    have hfirst_le :
        (((1 / 2 : ℝ) * ‖x[k / 2] - xStar‖ ^ (2 : ℕ)) /
            Finset.sum tail (fun n ↦ t n)) ≤
          (h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2) *
            (2 / inverseSqrtHalfTailSum k) := by
      have hbound :
          (((1 / 2 : ℝ) * ‖x[k / 2] - xStar‖ ^ (2 : ℕ)) /
              Finset.sum tail (fun n ↦ t n)) ≤
            Θ / Finset.sum tail (fun n ↦ t n) := by
        exact div_le_div_of_nonneg_right hstart_le htail_pos.le
      refine hbound.trans ?_
      rw [htail_eq]
      field_simp [hLm_pos.ne', hsqrtTheta_pos.ne', hinv_pos.ne']
      rw [Real.sq_sqrt hΘ_nonneg]
    have hsecond_eq :
        ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) *
            (Finset.sum tail (fun n ↦ (t n) ^ (2 : ℕ)) /
              Finset.sum tail (fun n ↦ t n))) =
          (h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2) *
            (harmonicHalfTailSum k / inverseSqrtHalfTailSum k) := by
      -- The quadratic ratio simplifies to the harmonic half-tail ratio after substituting the
      -- explicit stepsize formula.
      rw [hsqtail_eq, htail_eq]
      field_simp [pow_two, hLm_pos.ne', hsqrtTheta_pos.ne', hinv_pos.ne']
      rw [Real.sq_sqrt hΘ_nonneg]
      ring
    have hmain_ratio :
        bestGap ≤
          (h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2) *
            ((2 + harmonicHalfTailSum k) / inverseSqrtHalfTailSum k) := by
      have hfactor_nonneg :
          0 ≤ h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2 := by
        positivity
      calc
        bestGap ≤
            (((1 / 2 : ℝ) * ‖x[k / 2] - xStar‖ ^ (2 : ℕ)) /
                Finset.sum tail (fun n ↦ t n)) +
              ((((m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ)) / 2) *
                (Finset.sum tail (fun n ↦ (t n) ^ (2 : ℕ)) /
                  Finset.sum tail (fun n ↦ t n))) := hratio
        _ ≤
            (h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2) *
                (2 / inverseSqrtHalfTailSum k) +
              (h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2) *
                (harmonicHalfTailSum k / inverseSqrtHalfTailSum k) := by
              rw [hsecond_eq]
              exact add_le_add hfirst_le le_rfl
        _ =
            (h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2) *
              ((2 + harmonicHalfTailSum k) / inverseSqrtHalfTailSum k) := by
              field_simp [hinv_pos.ne']
    have htail_ratio :=
      harmonic_half_tail_ratio_le_log_three_bound 2 (by positivity : 0 ≤ (2 : ℝ)) k
    have hfactor_nonneg :
        0 ≤ h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2 := by
      positivity
    have hfinal :
        (h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2) *
            ((2 + harmonicHalfTailSum k) / inverseSqrtHalfTailSum k) ≤
          (h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2) *
            ((4 * (2 + Real.log 3)) / Real.sqrt ((k : ℝ) + 2)) := by
      exact mul_le_mul_of_nonneg_left htail_ratio hfactor_nonneg
    calc
      best_achieved_function_value
          (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
          (fun n ↦ x[n]) k - fOpt = bestGap := by
        rfl
      _ ≤
          (h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2) *
            ((2 + harmonicHalfTailSum k) / inverseSqrtHalfTailSum k) := hmain_ratio
      _ ≤
          (h_incremental.L * (m : ℝ) * Real.sqrt Θ / 2) *
            ((4 * (2 + Real.log 3)) / Real.sqrt ((k : ℝ) + 2)) := hfinal
      _ =
          (2 * (2 + Real.log 3)) * (m : ℝ) * h_incremental.L * Real.sqrt Θ /
            Real.sqrt ((k : ℝ) + 2) := by
          field_simp [show Real.sqrt ((k : ℝ) + 2) ≠ 0 by positivity]
          ring

end
