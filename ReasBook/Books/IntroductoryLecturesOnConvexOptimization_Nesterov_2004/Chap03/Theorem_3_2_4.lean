/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_34
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_46
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

namespace MultipleConstraintFirstOrderProblem

private def subgradientNormFamily
    (problem : MultipleConstraintFirstOrderProblem E m) : Fin (m + 1) → E → ℝ :=
  Fin.cases
    (fun y ↦ ‖problem.oracle.subgradient y‖)
    (fun j y ↦ ‖(problem.constraintOracle j).subgradient y‖)

/-- The canonical finite-family maximum of the objective-subgradient norm together with all
constraint-subgradient norms at `x`. -/
def subgradientNormMaximum
    (problem : MultipleConstraintFirstOrderProblem E m) (x : E) : ℝ :=
  maxTypeObjective (subgradientNormFamily problem) x

/-- Each sampled objective-subgradient norm is bounded by the problem-level maximum
`subgradientNormMaximum`. -/
theorem objectiveSubgradientNorm_le_subgradientNormMaximum
    (problem : MultipleConstraintFirstOrderProblem E m) (x : E) :
    ‖problem.oracle.subgradient x‖ ≤ problem.subgradientNormMaximum x := by
  rw [subgradientNormMaximum, maxTypeObjective_apply]
  simpa using
    (Finset.le_sup'
      (fun i : Fin (m + 1) ↦ subgradientNormFamily problem i x)
      (Finset.mem_univ 0))

/-- Each sampled constraint-subgradient norm is bounded by the problem-level maximum
`subgradientNormMaximum`. -/
theorem constraintSubgradientNorm_le_subgradientNormMaximum
    (problem : MultipleConstraintFirstOrderProblem E m) (x : E) (j : Fin m) :
    ‖(problem.constraintOracle j).subgradient x‖ ≤ problem.subgradientNormMaximum x := by
  rw [subgradientNormMaximum, maxTypeObjective_apply]
  simpa using
    (Finset.le_sup'
      (fun i : Fin (m + 1) ↦ subgradientNormFamily problem i x)
      (Finset.mem_univ (Fin.succ j)))

end MultipleConstraintFirstOrderProblem

namespace ApproximateLagrangeMultiplierSwitchingMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E m}

open scoped ApproximateLagrangeMultiplierSwitchingNotation

local notation "lagrangianProblem" => problem.toLagrangianProblem
local notation "lagrangianFeasibleSet" => problem.toLagrangianProblem.feasibleSet

/- Theorem 3.2.4 lies in the chapter's approximate-Lagrange-multiplier switching-method domain.

Sampled owner-style declarations:
- `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintIndices`
- `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintCount`
- `ApproximateLagrangeMultiplierSwitchingMethod.primalDualGapQuantity`
- `MultipleConstraintFirstOrderProblem.subgradientNormMaximum`
- `maxTypeObjective` in `Chap02/Lemma_2_18`
- mathlib `Finset.sup'` on finite sampled scalar families

Best owner abstraction:
- a run `method : ApproximateLagrangeMultiplierSwitchingMethod problem`
- the project finite-family maximum owner `maxTypeObjective`

Primitive data:
- the switching-method run `method`
- the radius `R`, the stage `t`, the bounded-feasible-set hypothesis, and the
  large-iteration hypothesis

Derived API:
- the residual maximum `maxTypeObjective problem.constraints (method k)`, given directly by the
  Chapter 2 finite-family maximum owner
- the problem-owned norm envelope
  `problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum`
- the sampled norm bound `M[method](t)`, owned by `sampleMaxSubgradientNorm` and derived as the
  finite operational maximum of that owner quantity along the sampled iterates `k = 0, ..., t`
- the source gap estimate written directly for the owner
  `primalDualGapQuantity`

Source/core/bridge triage:
- source-facing: the textbook residual bound, the positivity of `N(t)`, and the
  gap estimate for `δ_t` in the source regime `S_t > 0`
- core/canonical: `inactiveConstraintCount`, `normalizingFactor`,
  `approximateDualMultiplier`, `primalDualGapQuantity`, the finite-family maximum owner
  `maxTypeObjective`, and the finite-fold owner `Finset.sup'`
- bridge/view: the direct `Fin m` specialization `maxTypeObjective problem.constraints (method k)`

The old file duplicated the run data and left `δ_t` as arbitrary primitive data.
This refinement keeps the source-facing quantities, but derives them from the chapter owner run,
the chapter's canonical finite-family maximum surface for the constraint residual, the canonical
finite-fold sampled maximum for the textbook bound `M[method](t)`, and the existing gap owner
`primalDualGapQuantity`. -/

/-- Helper for Theorem 3.2.4: every selected-constraint branch decreases the squared distance to
any feasible comparison point by at least `h²`. -/
lemma selectedConstraintStep_sqDistDrop_ge_hSq
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem)
    (hh : 0 < method.h)
    (xStar : problem.feasibleSet)
    (hxStar_feas : ∀ j : Fin m, problem.constraints j xStar ≤ 0)
    {k : ℕ} {j : Fin m}
    (hsel : method.selectedIndexAt k = some j) :
    ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      ‖method k - xStar‖ ^ (2 : ℕ) - method.h ^ (2 : ℕ) := by
  let g := (problem.constraintOracle j).subgradient (method k)
  let β := problem.constraints j (method k)
  -- Convert the selected branch into the active-set threshold inequality at stage `k`.
  have hactive : j ∈ method.activeSet k := by
    simpa [hsel] using method.selectedIndexAt_spec k
  have hthreshold : method.h * ‖g‖ < β := by
    simpa [ApproximateLagrangeMultiplierSwitchingMethod.activeSet,
      ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet, g, β] using hactive
  -- Compare the violated constraint value at `method k` with the feasible comparison point.
  have hgap_val :
      problem.constraints j (method k) - problem.constraints j xStar ≤
        inner ℝ g (method k - xStar) := by
    simpa [g] using
      MultipleConstraintFirstOrderProblem.value_gap_le_inner_subgradient
        (oracle := problem.constraintOracle j) (x := method k) (y := xStar)
  have hgap : β ≤ inner ℝ g (method k - xStar) := by
    linarith [hgap_val, hxStar_feas j]
  have hg_ne : g ≠ 0 := by
    intro hg0
    have hβ_pos : 0 < β := by
      have hmul_nonneg : 0 ≤ method.h * ‖g‖ := by positivity
      exact lt_of_le_of_lt hmul_nonneg hthreshold
    rw [hg0, inner_zero_left] at hgap
    linarith
  have hβ_nonneg : 0 ≤ β := by
    have hmul_nonneg : 0 ≤ method.h * ‖g‖ := by positivity
    exact le_of_lt (lt_of_le_of_lt hmul_nonneg hthreshold)
  -- First control the explicit correction step before projecting back to `Q`.
  have hdrop_explicit :
      ‖(method k - (problem.constraintOracle j).correctionStepsize (method k) • g) - xStar‖ ^
          (2 : ℕ) ≤
        ‖method k - xStar‖ ^ (2 : ℕ) - β ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := by
    simpa [g, β, FirstOrderOracle.correctionStepsize] using
      MultipleConstraintFirstOrderProblem.sqDistDrop_of_gap_le_inner
        (x := method k) (xStar := (xStar : E)) (g := g) (β := β) hβ_nonneg hg_ne hgap
  -- Then use projection nonexpansiveness because `xStar` already lies in the feasible set.
  have hxStar_proj : IsProjectionPointOn problem.feasibleSet (xStar : E) (xStar : E) := by
    refine ⟨xStar.2, ?_⟩
    simp [Metric.infDist_zero_of_mem xStar.2]
  have hproj_sq :
      ‖problem.projection
          (method k - (problem.constraintOracle j).correctionStepsize (method k) • g) -
            xStar‖ ^ (2 : ℕ) ≤
        ‖(method k - (problem.constraintOracle j).correctionStepsize (method k) • g) - xStar‖ ^
          (2 : ℕ) := by
    have hproj_dist :
        dist
            (problem.projection
              (method k - (problem.constraintOracle j).correctionStepsize (method k) • g))
            xStar ≤
          dist (method k - (problem.constraintOracle j).correctionStepsize (method k) • g) xStar :=
      (problem.toFirstOrderConvexMinimizationProblem.projection_spec
        (method k - (problem.constraintOracle j).correctionStepsize (method k) • g)).dist_le_dist
        problem.feasibleSet_convex hxStar_proj
    have hproj_norm :
        ‖problem.projection
            (method k - (problem.constraintOracle j).correctionStepsize (method k) • g) -
              xStar‖ ≤
          ‖(method k - (problem.constraintOracle j).correctionStepsize (method k) • g) -
              xStar‖ := by
      simpa [dist_eq_norm] using hproj_dist
    exact
      (sq_le_sq₀
        (norm_nonneg
          (problem.projection
            (method k - (problem.constraintOracle j).correctionStepsize (method k) • g) - xStar))
        (norm_nonneg
          ((method k - (problem.constraintOracle j).correctionStepsize (method k) • g) - xStar))).2
        hproj_norm
  have hnorm_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg_ne
  have hfrac_ge_hSq : method.h ^ (2 : ℕ) ≤ β ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := by
    have hmul_nonneg : 0 ≤ method.h * ‖g‖ := by positivity
    have hsq : (method.h * ‖g‖) ^ (2 : ℕ) ≤ β ^ (2 : ℕ) := by
      exact (sq_le_sq₀ hmul_nonneg hβ_nonneg).2 (le_of_lt hthreshold)
    have hmul :
        method.h ^ (2 : ℕ) * ‖g‖ ^ (2 : ℕ) ≤ β ^ (2 : ℕ) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    exact (_root_.le_div_iff₀ (show 0 < ‖g‖ ^ (2 : ℕ) by positivity)).2 hmul
  -- Assemble the projected-step estimate with the explicit drop.
  calc
    ‖method (k + 1) - xStar‖ ^ (2 : ℕ) =
        ‖problem.projection
            (method k - (problem.constraintOracle j).correctionStepsize (method k) • g) -
          xStar‖ ^ (2 : ℕ) := by
          rw [method.iterates_succ, method.nextIterate_eq_constraint hsel]
    _ ≤
        ‖(method k - (problem.constraintOracle j).correctionStepsize (method k) • g) - xStar‖ ^
          (2 : ℕ) := hproj_sq
    _ ≤ ‖method k - xStar‖ ^ (2 : ℕ) - β ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := hdrop_explicit
    _ ≤ ‖method k - xStar‖ ^ (2 : ℕ) - method.h ^ (2 : ℕ) := by
      have hsub :
          ‖method k - xStar‖ ^ (2 : ℕ) - β ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) ≤
            ‖method k - xStar‖ ^ (2 : ℕ) - method.h ^ (2 : ℕ) := by
        linarith
      exact hsub

/-- Companion bridge for Theorem 3.2.4: if `0 < h`, the feasible set is contained in the ball
`‖x - x₀‖ ≤ R`, the constraint-feasible set is nonempty, and `t > R² / h²`, then the number
`N(t)` of objective-step indices among `{0, ..., t}` is positive. -/
theorem positive_inactiveConstraintCount_of_large_iteration_count
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (hfeasible : Set.Nonempty lagrangianFeasibleSet)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    0 < N[method](t) := by
  obtain ⟨xStar, hxStar_feasSet⟩ := hfeasible
  have hxStar_feas : ∀ j : Fin m, problem.constraints j xStar ≤ 0 := by
    simpa using (problem.toLagrangianProblem.mem_feasibleSet_iff (x := xStar)).1 hxStar_feasSet
  -- Assume `N(t) = 0`; then every stage `k ≤ t` is a selected-constraint correction step.
  by_contra hN
  have hN0 : N[method](t) = 0 := Nat.eq_zero_of_not_pos hN
  have hA0empty : A₀[method](t) = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [inactiveConstraintCount] using hN0
  have hselected_drop :
      ∀ n : ℕ, n ≤ t →
        ‖method (n + 1) - xStar‖ ^ (2 : ℕ) ≤
          ‖method n - xStar‖ ^ (2 : ℕ) - method.h ^ (2 : ℕ) := by
    intro n hn
    let k : Fin (t + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
    have hk_not_mem : k ∉ A₀[method](t) := by
      simp [hA0empty]
    have hactive_nonempty : method.activeSet n ≠ ∅ := by
      intro hactive
      exact hk_not_mem ((mem_inactiveConstraintIndices_iff method t).2 hactive)
    have hsel_ne_none : method.selectedIndexAt n ≠ none := by
      intro hsel_none
      have hactive : method.activeSet n = ∅ := by
        simpa [hsel_none] using method.selectedIndexAt_spec n
      exact hactive_nonempty hactive
    rcases Option.ne_none_iff_exists'.1 hsel_ne_none with ⟨j, hsel⟩
    -- Apply the one-step `h²` drop on the selected branch chosen at stage `n`.
    simpa using
      method.selectedConstraintStep_sqDistDrop_ge_hSq hh xStar hxStar_feas hsel
  -- Telescope the uniform `h²` drop along the whole prefix `0, ..., t`.
  have hprefix :
      ∀ n : ℕ, n ≤ t + 1 →
        ‖method n - xStar‖ ^ (2 : ℕ) ≤
          ‖method 0 - xStar‖ ^ (2 : ℕ) - (n : ℝ) * method.h ^ (2 : ℕ) := by
    intro n hn
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hn_le_t : n ≤ t := Nat.le_of_succ_le_succ hn
        have hn_le_tsucc : n ≤ t + 1 := Nat.le_trans (Nat.le_succ n) hn
        have hprev := ih hn_le_tsucc
        have hstep := hselected_drop n hn_le_t
        have htmp :
            ‖method n - xStar‖ ^ (2 : ℕ) - method.h ^ (2 : ℕ) ≤
              (‖method 0 - xStar‖ ^ (2 : ℕ) - (n : ℝ) * method.h ^ (2 : ℕ)) -
                method.h ^ (2 : ℕ) := by
          exact sub_le_sub_right hprev (method.h ^ (2 : ℕ))
        calc
          ‖method (n + 1) - xStar‖ ^ (2 : ℕ)
              ≤ ‖method n - xStar‖ ^ (2 : ℕ) - method.h ^ (2 : ℕ) := hstep
          _ ≤
              (‖method 0 - xStar‖ ^ (2 : ℕ) - (n : ℝ) * method.h ^ (2 : ℕ)) -
                method.h ^ (2 : ℕ) := htmp
          _ = ‖method 0 - xStar‖ ^ (2 : ℕ) - ((n + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ) := by
                rw [Nat.cast_add, Nat.cast_one]
                ring
  have hinitial_dist :
      ‖method 0 - xStar‖ ≤ R := by
    simpa [method.iterates_zero_eq_x0, norm_sub_rev] using hQ_bounded xStar xStar.2
  have hinitial_sq :
      ‖method 0 - xStar‖ ^ (2 : ℕ) ≤ (R : ℝ) ^ (2 : ℕ) := by
    have hR_nonneg : 0 ≤ (R : ℝ) := by exact_mod_cast R.2
    have hsq :=
      mul_le_mul hinitial_dist hinitial_dist (norm_nonneg (method 0 - xStar)) hR_nonneg
    simpa [pow_two] using hsq
  have hR_sq_lt :
      (R : ℝ) ^ (2 : ℕ) < (t : ℝ) * method.h ^ (2 : ℕ) := by
    exact (_root_.div_lt_iff₀ (show 0 < method.h ^ (2 : ℕ) by positivity)).1 ht
  have hR_sq_lt_succ :
      (R : ℝ) ^ (2 : ℕ) < ((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ) := by
    have hhSq_pos : 0 < method.h ^ (2 : ℕ) := by positivity
    calc
      (R : ℝ) ^ (2 : ℕ) < (t : ℝ) * method.h ^ (2 : ℕ) := hR_sq_lt
      _ < ((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ) := by
        have htlt : (t : ℝ) < ((t + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.lt_succ_self t
        exact mul_lt_mul_of_pos_right htlt hhSq_pos
  have hfinal_bound :
      ‖method (t + 1) - xStar‖ ^ (2 : ℕ) ≤
        ‖method 0 - xStar‖ ^ (2 : ℕ) - ((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ) :=
    hprefix (t + 1) le_rfl
  have hfinal_neg :
      ‖method (t + 1) - xStar‖ ^ (2 : ℕ) < 0 := by
    have hupper :
        ‖method 0 - xStar‖ ^ (2 : ℕ) - ((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ) < 0 := by
      have hstrict :
          ‖method 0 - xStar‖ ^ (2 : ℕ) < ((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ) :=
        lt_of_le_of_lt hinitial_sq hR_sq_lt_succ
      exact sub_neg.mpr hstrict
    exact lt_of_le_of_lt hfinal_bound hupper
  have hfinal_nonneg : 0 ≤ ‖method (t + 1) - xStar‖ ^ (2 : ℕ) := by
    positivity
  exact (not_lt_of_ge hfinal_nonneg hfinal_neg).elim

section ConstraintMaxima

/-- The sampled norm bound
`M = max_{0 ≤ k ≤ t} max {‖g(x_k)‖, ‖g₁(x_k)‖, ..., ‖g_m(x_k)‖}`. -/
def sampleMaxSubgradientNorm
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun k : Fin (t + 1) ↦
    problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method k)

/- Source-facing Lean notation for the textbook sampled norm bound `M`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "M[" method:arg "](" t:arg ")" =>
  sampleMaxSubgradientNorm method t

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

private theorem stageMax_le_sampleMaxSubgradientNorm
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) {t : ℕ} (k : Fin (t + 1)) :
    problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method k) ≤
      M[method](t) := by
  unfold sampleMaxSubgradientNorm
  exact
    Finset.le_sup'
      (fun i : Fin (t + 1) ↦
        problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method i))
      (Finset.mem_univ k)

/-- Companion bridge for the textbook residual estimate: every objective-step iterate up to time
`t` satisfies the componentwise bound `f_j(x_k) ≤ M h` for each constraint index `j`, where
`0 < h` and `M = M[method](t)`. -/
-- Proof sketch: on indices in `A₀(t)`, the switching active set is empty, so each constraint
-- value is bounded by the corresponding threshold `h ‖g_j(x_k)‖`. The sampled norm bound
-- `M[method](t)` dominates the owner quantity
-- `problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method k)` at every
-- sampled stage up to time `t`, hence every sampled constraint-subgradient norm, so the desired
-- inequality follows for each fixed `j`.
theorem constraintMaximumAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hh : 0 < method.h)
    {k : Fin (t + 1)} (hk : k ∈ A₀[method](t)) (j : Fin m) :
    problem.constraints j (method k) ≤ M[method](t) * method.h := by
  have hactive : method.activeSet k = ∅ :=
    (mem_inactiveConstraintIndices_iff method t).1 hk
  have hconstraint :
      problem.constraints j (method k) ≤
        method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ := by
    exact le_of_not_gt fun hj ↦ by
      have hj_mem : j ∈ method.activeSet k := by
        simp [ApproximateLagrangeMultiplierSwitchingMethod.activeSet,
          ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet, hj]
      simp [hactive] at hj_mem
  have hnorm :
      ‖(problem.constraintOracle j).subgradient (method k)‖ ≤
        M[method](t) :=
    le_trans
      (MultipleConstraintFirstOrderProblem.constraintSubgradientNorm_le_subgradientNormMaximum
        problem.toMultipleConstraintFirstOrderProblem (method k) j)
      (stageMax_le_sampleMaxSubgradientNorm method k)
  calc
    problem.constraints j (method k)
      ≤ method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ := hconstraint
    _ ≤ method.h * M[method](t) :=
      mul_le_mul_of_nonneg_left hnorm hh.le
    _ = M[method](t) * method.h := by rw [mul_comm]

/-- Every objective-step iterate up to time `t` satisfies the textbook residual-maximum bound
`max_{1 ≤ j ≤ m} f_j(x_k) ≤ M h`, written through the chapter owner
`maxTypeObjective problem.constraints (method k)`, where `0 < h` and `M = M[method](t)`. -/
theorem maxConstraintValueAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices
    [NeZero m]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hh : 0 < method.h)
    {k : Fin (t + 1)} (hk : k ∈ A₀[method](t)) :
    maxTypeObjective problem.constraints (method k) ≤
      M[method](t) * method.h := by
  exact
    (maxTypeObjective_le_iff problem.constraints (method k)
      (M[method](t) * method.h)).2
      (fun j ↦
        constraintMaximumAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices
          method t hh hk j)

/-- In the large-iteration regime, the textbook denominator regime needed by Definition 3.45 is
available: the objective and selected-constraint ratios are genuine, `h > 0`, and `N(t) > 0`. -/
theorem hasApproximateDualMultiplierDenominators_of_large_iteration_count
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hobjective : method.HasObjectiveDenominators t)
    (hselected : method.HasSelectedConstraintDenominators t)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (hfeasible : Set.Nonempty lagrangianFeasibleSet)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    method.HasApproximateDualMultiplierDenominators t := by
  refine ⟨hobjective, hselected, hh, ?_⟩
  exact
    method.positive_inactiveConstraintCount_of_large_iteration_count
      R t hh hQ_bounded hfeasible ht

/-- Helper for Theorem 3.2.4: the fixed-`λ_t` Lagrangian slice is supported by the objective
subgradient together with the multiplier-weighted constraint subgradients. -/
private def lagrangianSliceSubgradient
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t) (x : E) : E :=
  problem.oracle.subgradient x +
    ∑ j : Fin m, (λ[method](t; hdenom) j) • (problem.constraintOracle j).subgradient x

/-- Helper for Theorem 3.2.4: every comparison point in `Q` satisfies the affine-support
inequality for the fixed-`λ_t` Lagrangian slice. -/
lemma lagrangianValueGap_le_inner_lagrangianSliceSubgradient
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    {k : ℕ} (x : problem.feasibleSet) :
    problem.toLagrangianProblem.lagrangian
        ⟨method k, method.iterates_mem k⟩ (λ[method](t; hdenom)) -
      problem.toLagrangianProblem.lagrangian x (λ[method](t; hdenom)) ≤
        inner ℝ (lagrangianSliceSubgradient method t hdenom (method k)) (method k - x) := by
  let lam := λ[method](t; hdenom)
  -- Control the objective term by the objective oracle subgradient at the sampled iterate.
  have hobjective :
      problem.objective (method k) - problem.objective x ≤
        inner ℝ (problem.oracle.subgradient (method k)) (method k - x) := by
    simpa using
      MultipleConstraintFirstOrderProblem.value_gap_le_inner_subgradient
        (oracle := problem.oracle) (x := method k) (y := x)
  -- Control each constraint slice by its own oracle subgradient and multiply by `λ_t^(j) ≥ 0`.
  have hconstraint :
      ∀ j : Fin m,
        lam j * (problem.constraints j (method k) - problem.constraints j x) ≤
          lam j * inner ℝ ((problem.constraintOracle j).subgradient (method k)) (method k - x) := by
    intro j
    exact
      mul_le_mul_of_nonneg_left
        (MultipleConstraintFirstOrderProblem.value_gap_le_inner_subgradient
          (oracle := problem.constraintOracle j) (x := method k) (y := x))
        (method.approximateDualMultiplier_nonneg t hdenom j)
  have hconstraints :
      ∑ j : Fin m, lam j * (problem.constraints j (method k) - problem.constraints j x) ≤
        ∑ j : Fin m,
          lam j * inner ℝ ((problem.constraintOracle j).subgradient (method k)) (method k - x) := by
    -- Sum the coordinatewise constraint bounds after fixing the sampled stage `k`.
    exact Finset.sum_le_sum fun j _ ↦ hconstraint j
  -- Rewrite the Lagrangian gap as the objective gap plus the weighted constraint gaps.
  have hlagrangian :
      problem.toLagrangianProblem.lagrangian ⟨method k, method.iterates_mem k⟩ lam -
        problem.toLagrangianProblem.lagrangian x lam =
          (problem.objective (method k) - problem.objective x) +
            ∑ j : Fin m, lam j * (problem.constraints j (method k) - problem.constraints j x) := by
    rw [LagrangianProblem.lagrangian_eq_objective_add_sum,
      LagrangianProblem.lagrangian_eq_objective_add_sum]
    simp only [ProjectedMultipleConstraintFirstOrderProblem.toLagrangianProblem]
    calc
      problem.objective (method k) + ∑ j : Fin m, lam j * problem.constraints j (method k) -
          (problem.objective x + ∑ j : Fin m, lam j * problem.constraints j x) =
        problem.objective (method k) + ∑ j : Fin m, lam j * problem.constraints j (method k) -
          problem.objective x - ∑ j : Fin m, lam j * problem.constraints j x := by
          ring
      _ =
        (problem.objective (method k) - problem.objective x) +
          ((∑ j : Fin m, lam j * problem.constraints j (method k)) -
            ∑ j : Fin m, lam j * problem.constraints j x) := by
          ring
      _ = (problem.objective (method k) - problem.objective x) +
          ∑ j : Fin m,
            (lam j * problem.constraints j (method k) - lam j * problem.constraints j x) := by
            rw [Finset.sum_sub_distrib]
      _ = (problem.objective (method k) - problem.objective x) +
          ∑ j : Fin m, lam j * (problem.constraints j (method k) - problem.constraints j x) := by
            simp [mul_sub]
  -- Collect the objective and constraint support terms into one inner product.
  have hinner :
      inner ℝ (problem.oracle.subgradient (method k)) (method k - x) +
          ∑ j : Fin m,
            lam j *
              inner ℝ ((problem.constraintOracle j).subgradient (method k)) (method k - x) =
        inner ℝ (lagrangianSliceSubgradient method t hdenom (method k)) (method k - x) := by
    calc
      inner ℝ (problem.oracle.subgradient (method k)) (method k - x) +
          ∑ j : Fin m,
            lam j * inner ℝ ((problem.constraintOracle j).subgradient (method k)) (method k - x) =
          inner ℝ (problem.oracle.subgradient (method k)) (method k - x) +
          ∑ j : Fin m,
              inner ℝ
                (lam j • (problem.constraintOracle j).subgradient (method k))
                (method k - x) := by
        simp [inner_smul_left]
      _ =
          inner ℝ (problem.oracle.subgradient (method k)) (method k - x) +
            inner ℝ
              (∑ j : Fin m, lam j • (problem.constraintOracle j).subgradient (method k))
              (method k - x) := by
        rw [sum_inner]
      _ = inner ℝ (lagrangianSliceSubgradient method t hdenom (method k)) (method k - x) := by
        rw [lagrangianSliceSubgradient, inner_add_left]
  calc
    problem.toLagrangianProblem.lagrangian ⟨method k, method.iterates_mem k⟩ lam -
        problem.toLagrangianProblem.lagrangian x lam =
          (problem.objective (method k) - problem.objective x) +
            ∑ j : Fin m, lam j * (problem.constraints j (method k) - problem.constraints j x) :=
      hlagrangian
    _ ≤
        inner ℝ (problem.oracle.subgradient (method k)) (method k - x) +
          ∑ j : Fin m,
            lam j *
              inner ℝ ((problem.constraintOracle j).subgradient (method k)) (method k - x) := by
      exact add_le_add hobjective hconstraints
    _ = inner ℝ (lagrangianSliceSubgradient method t hdenom (method k)) (method k - x) := hinner

/-- Helper for Theorem 3.2.4: the unconstrained constant problem on `Q` has optimal value equal
to that constant. -/
private theorem unconstrainedConstantOptimalValue_eq
    (c : ℝ) :
    (SetConstrainedMinimizationProblem.unconstrained
      (fun _ : problem.feasibleSet ↦ c)).optimalValue = (c : EReal) := by
  obtain ⟨x, hx⟩ := problem.feasibleSet_nonempty
  let xQ : problem.feasibleSet := ⟨x, hx⟩
  let constProblem : SetConstrainedMinimizationProblem problem.feasibleSet :=
    SetConstrainedMinimizationProblem.unconstrained fun _ : problem.feasibleSet ↦ c
  -- Evaluate the constant unconstrained problem at one point of `Q`.
  refine constProblem.optimalValue_eq_of_isMinOn (x := xQ) ?_ ?_
  · simp [constProblem, xQ]
  · intro y hy
    simp [constProblem]

/-- Helper for Theorem 3.2.4: a pointwise lower bound for the fixed-`λ_t` Lagrangian on `Q`
immediately bounds the source gap quantity `δ_t`. -/
lemma primalDualGapQuantity_le_of_pointwiseLagrangianLowerBound
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    {B : ℝ}
    (hpointwise :
      ∀ x : problem.feasibleSet,
        ((A₀[method](t)).centerMass
            (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
            (fun k ↦ problem.objective (method k)) : ℝ) - B ≤
          problem.toLagrangianProblem.lagrangian x (λ[method](t; hdenom))) :
    δ[method](t; hdenom) ≤ (B : EReal) := by
  let avgObj : ℝ :=
    ((A₀[method](t)).centerMass
      (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
      (fun k ↦ problem.objective (method k)) : ℝ)
  let constProblem : SetConstrainedMinimizationProblem problem.feasibleSet :=
    SetConstrainedMinimizationProblem.unconstrained fun _ : problem.feasibleSet ↦ avgObj
  let lagProblem : SetConstrainedMinimizationProblem problem.feasibleSet :=
    SetConstrainedMinimizationProblem.unconstrained
      (fun x : problem.feasibleSet ↦
        problem.toLagrangianProblem.lagrangian x (λ[method](t; hdenom)))
  have hconst :
      constProblem.optimalValue = (avgObj : EReal) := by
    -- Collapse the left-hand optimal value because the source primal term is constant on `Q`.
    simpa [constProblem, avgObj] using
      (unconstrainedConstantOptimalValue_eq (problem := problem) avgObj)
  have hopt :
      constProblem.optimalValue - B ≤ lagProblem.optimalValue := by
    -- Compare the constant problem with the fixed-`λ_t` Lagrangian problem pointwise on `Q`.
    refine
      SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le
        constProblem lagProblem rfl ?_
    intro x hx
    simpa [constProblem, lagProblem, avgObj] using hpointwise x
  have hlower :
      ((avgObj : EReal) - (B : EReal)) ≤
        problem.toLagrangianProblem.dualFunction (λ[method](t; hdenom)) := by
    -- Rewrite both optimal values to the Chapter 1 owner `dualFunction`.
    simpa [hconst, lagProblem, LagrangianProblem.dualFunction]
      using hopt
  have hgap :
      (avgObj : EReal) ≤
        problem.toLagrangianProblem.dualFunction (λ[method](t; hdenom)) + (B : EReal) := by
    -- Add back the finite scalar `B` on both sides of the lower bound.
    have htmp :
        ((avgObj : EReal) - (B : EReal)) + (B : EReal) ≤
          problem.toLagrangianProblem.dualFunction (λ[method](t; hdenom)) + (B : EReal) :=
      add_le_add_left hlower (B : EReal)
    calc
      (avgObj : EReal) = ((avgObj : EReal) - (B : EReal)) + (B : EReal) := by
        simpa using (EReal.sub_add_cancel (a := (avgObj : EReal)) (b := B)).symm
      _ ≤ problem.toLagrangianProblem.dualFunction (λ[method](t; hdenom)) + (B : EReal) := htmp
  -- Finish by unfolding `δ_t` and reading the previous inequality as a subtraction bound.
  rw [primalDualGapQuantity]
  change (avgObj : EReal) -
      problem.toLagrangianProblem.dualFunction (λ[method](t; hdenom)) ≤ (B : EReal)
  exact EReal.sub_le_of_le_add' hgap

/-- Helper for Theorem 3.2.4: the inactive objective weights normalized by `S_t` add up to `1`.
-/
lemma inactiveObjectiveWeights_sum_one
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    Finset.sum (A₀[method](t))
      (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) = 1 := by
  have hS_pos :
      0 < S[method](t; hdenom.objective) :=
    method.inverseSubgradientNormSum_pos_of_inactiveConstraintCount_pos
      t hdenom.objective hdenom.inactiveConstraintCount_pos
  have hS_eq :
      Finset.sum (A₀[method](t)) (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹) =
        S[method](t; hdenom.objective) := by
    -- Rewrite the subtype sum in `S_t` back to the surface sum on `A₀(t)`.
    rw [ApproximateLagrangeMultiplierSwitchingMethod.inverseSubgradientNormSum]
    rw [← Finset.sum_attach
      (s := A₀[method](t))
      (f := fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)]
    refine Finset.sum_congr rfl ?_
    intro k hk
    change ‖method.objectiveSubgradient k.1‖⁻¹ =
      ↑((Units.mk0 ‖method.objectiveSubgradient k.1‖
        (norm_ne_zero_iff.mpr (hdenom.objective k.2)))⁻¹ : ℝˣ)
    simp [Units.val_mk0]
  -- Rewrite the normalized weights as one common denominator and cancel with `S_t`.
  calc
    Finset.sum (A₀[method](t))
        (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) =
        (Finset.sum (A₀[method](t)) fun k ↦ ‖method.objectiveSubgradient k‖⁻¹) /
          S[method](t; hdenom.objective) := by
          rw [Finset.sum_div]
    _ = S[method](t; hdenom.objective) / S[method](t; hdenom.objective) := by
          rw [hS_eq]
    _ = 1 := by
          field_simp [ne_of_gt hS_pos]

/-- Helper for Theorem 3.2.4: each normalized inactive objective weight is nonnegative. -/
lemma inactiveObjectiveWeight_nonneg
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    {k : Fin (t + 1)} (hk : k ∈ A₀[method](t)) :
    0 ≤ ‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective) := by
  have hinv_pos :
      0 < ‖method.objectiveSubgradient k‖⁻¹ :=
    method.inv_norm_objectiveSubgradient_pos k (hdenom.objective hk)
  have hS_pos :
      0 < S[method](t; hdenom.objective) :=
    method.inverseSubgradientNormSum_pos_of_inactiveConstraintCount_pos
      t hdenom.objective hdenom.inactiveConstraintCount_pos
  -- Both the reciprocal norm and the normalizing sum are positive on `A₀(t)`.
  exact div_nonneg hinv_pos.le hS_pos.le

/-- Helper for Theorem 3.2.4: the Definition 3.46 primal average rewrites to the explicit
normalized finite sum on `A₀(t)`. -/
lemma inactiveObjectiveAverage_eq_weightedSum
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    ((A₀[method](t)).centerMass
        (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
        (fun k ↦ problem.objective (method k)) : ℝ) =
      Finset.sum (A₀[method](t))
        (fun k ↦
        (‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
          problem.objective (method k)) := by
  have hS_pos :
      0 < S[method](t; hdenom.objective) :=
    method.inverseSubgradientNormSum_pos_of_inactiveConstraintCount_pos
      t hdenom.objective hdenom.inactiveConstraintCount_pos
  have hS_eq :
      Finset.sum (A₀[method](t)) (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹) =
        S[method](t; hdenom.objective) := by
    -- Rewrite the subtype sum in `S_t` back to the surface sum on `A₀(t)`.
    rw [ApproximateLagrangeMultiplierSwitchingMethod.inverseSubgradientNormSum]
    rw [← Finset.sum_attach
      (s := A₀[method](t))
      (f := fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)]
    refine Finset.sum_congr rfl ?_
    intro k hk
    change ‖method.objectiveSubgradient k.1‖⁻¹ =
      ↑((Units.mk0 ‖method.objectiveSubgradient k.1‖
        (norm_ne_zero_iff.mpr (hdenom.objective k.2)))⁻¹ : ℝˣ)
    simp [Units.val_mk0]
  -- Expand the center of mass and push the common factor `S_t⁻¹` through the finite sum.
  calc
    ((A₀[method](t)).centerMass
        (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
        (fun k ↦ problem.objective (method k)) : ℝ) =
      (S[method](t; hdenom.objective))⁻¹ *
        Finset.sum (A₀[method](t))
          (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹ * problem.objective (method k)) := by
        simp [Finset.centerMass, hS_eq, smul_eq_mul]
    _ = Finset.sum (A₀[method](t))
          (fun k ↦
            ((‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
              problem.objective (method k))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [div_eq_mul_inv]
        ring

/-- Helper for Theorem 3.2.4: every objective-branch contribution is controlled by the
corresponding squared-distance drop plus the `h² / 2` remainder from the normalized step. -/
lemma inactiveObjectiveGapTerm_le_halfSqDistDiff_add_halfHSq
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    (x : problem.feasibleSet)
    {k : Fin (t + 1)} (hk : k ∈ A₀[method](t)) :
    (method.h / ‖method.objectiveSubgradient k‖) *
        (problem.objective (method k) - problem.objective x) ≤
      (‖method k - x‖ ^ (2 : ℕ) - ‖method (k + 1) - x‖ ^ (2 : ℕ) +
        method.h ^ (2 : ℕ)) / 2 := by
  let g := method.objectiveSubgradient k
  have hg_ne : g ≠ 0 := hdenom.objective hk
  have hsel : method.selectedIndexAt k = none := by
    -- On `A₀(t)`, the switching active set is empty, so the objective branch is chosen.
    have hactive : method.activeSet k = ∅ :=
      (mem_inactiveConstraintIndices_iff method t).1 hk
    cases hsel' : method.selectedIndexAt k with
    | none =>
        rfl
    | some j =>
        have hj : j ∈ method.activeSet k := by
          simpa [hsel'] using method.selectedIndexAt_spec k
        simp [hactive] at hj
  have hgap :
      problem.objective (method k) - problem.objective x ≤
        inner ℝ g (method k - x) := by
    -- The objective oracle gives the affine support inequality at the sampled iterate.
    simpa [g] using
      MultipleConstraintFirstOrderProblem.value_gap_le_inner_subgradient
        (oracle := problem.oracle) (x := method k) (y := x)
  let y : E := method k - method.h • NormedSpace.normalize g
  have hpre_sq :
      ‖method (k + 1) - x‖ ^ (2 : ℕ) ≤ ‖y - x‖ ^ (2 : ℕ) := by
    -- Projection back to `Q` cannot increase the distance to the feasible comparison point `x`.
    have hx_proj : IsProjectionPointOn problem.feasibleSet (x : E) (x : E) := by
      refine ⟨x.2, ?_⟩
      simp [Metric.infDist_zero_of_mem x.2]
    have hproj_dist :
        dist
            (problem.projection y)
            x ≤
          dist y x :=
      (problem.toFirstOrderConvexMinimizationProblem.projection_spec y).dist_le_dist
        problem.feasibleSet_convex hx_proj
    have hproj_norm :
        ‖problem.projection y - x‖ ≤ ‖y - x‖ := by
      simpa [dist_eq_norm] using hproj_dist
    have hproj_sq :
        ‖problem.projection y - x‖ ^ (2 : ℕ) ≤ ‖y - x‖ ^ (2 : ℕ) := by
      exact
        (sq_le_sq₀
          (norm_nonneg (problem.projection y - x))
          (norm_nonneg (y - x))).2 hproj_norm
    simpa [y, method.iterates_succ, method.nextIterate_eq_objective hsel,
      ProjectedMultipleConstraintFirstOrderProblem.normalizedSubgradientStep,
      FirstOrderConvexMinimizationProblem.normalizedSubgradientStep] using hproj_sq
  have hscaled :
      (method.h / ‖g‖) * (problem.objective (method k) - problem.objective x) ≤
        method.h * inner ℝ (NormedSpace.normalize g) (method k - x) := by
    -- Scale the oracle inequality by `h / ‖g‖` and rewrite the right-hand side through
    -- the normalized subgradient direction.
    have hnorm_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg_ne
    have hcoef_nonneg : 0 ≤ method.h / ‖g‖ := by
      exact div_nonneg hdenom.h_pos.le hnorm_pos.le
    calc
      (method.h / ‖g‖) * (problem.objective (method k) - problem.objective x)
          ≤ (method.h / ‖g‖) * inner ℝ g (method k - x) :=
        mul_le_mul_of_nonneg_left hgap hcoef_nonneg
      _ = method.h * inner ℝ (NormedSpace.normalize g) (method k - x) := by
        calc
          (method.h / ‖g‖) * inner ℝ g (method k - x) =
              method.h * (‖g‖⁻¹ * inner ℝ g (method k - x)) := by
                rw [div_eq_mul_inv]
                ring
          _ = method.h * inner ℝ (NormedSpace.normalize g) (method k - x) := by
                simp [NormedSpace.normalize, real_inner_smul_left]
  have hnorm_normalize :
      ‖NormedSpace.normalize g‖ = 1 := by
    rw [NormedSpace.norm_normalize hg_ne]
  have hpre_expand :
      ‖y - x‖ ^ (2 : ℕ) =
        ‖method k - x‖ ^ (2 : ℕ) -
          2 * method.h * inner ℝ (NormedSpace.normalize g) (method k - x) +
            method.h ^ (2 : ℕ) := by
    -- Expand the explicit pre-projection objective step before comparing it with the oracle gap.
    calc
      ‖y - x‖ ^ (2 : ℕ) =
          ‖(method k - x) - method.h • NormedSpace.normalize g‖ ^ (2 : ℕ) := by
            simp [y, sub_eq_add_neg, add_left_comm, add_comm]
      _ = ‖method k - x‖ ^ (2 : ℕ) -
            2 * inner ℝ (method k - x) (method.h • NormedSpace.normalize g) +
              ‖method.h • NormedSpace.normalize g‖ ^ (2 : ℕ) := by
            rw [norm_sub_sq_real]
      _ = ‖method k - x‖ ^ (2 : ℕ) -
            2 * method.h * inner ℝ (NormedSpace.normalize g) (method k - x) +
              ‖method.h • NormedSpace.normalize g‖ ^ (2 : ℕ) := by
            rw [real_inner_smul_right, real_inner_comm]
            ring
      _ = ‖method k - x‖ ^ (2 : ℕ) -
            2 * method.h * inner ℝ (NormedSpace.normalize g) (method k - x) +
              method.h ^ (2 : ℕ) := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdenom.h_pos.le, hnorm_normalize]
            ring
  have hbound :
      ‖method (k + 1) - x‖ ^ (2 : ℕ) ≤
        ‖method k - x‖ ^ (2 : ℕ) -
          2 * ((method.h / ‖g‖) * (problem.objective (method k) - problem.objective x)) +
            method.h ^ (2 : ℕ) := by
    -- Replace the normalized-direction inner product by the scaled objective gap.
    calc
      ‖method (k + 1) - x‖ ^ (2 : ℕ) ≤ ‖y - x‖ ^ (2 : ℕ) := hpre_sq
      _ = ‖method k - x‖ ^ (2 : ℕ) -
            2 * method.h * inner ℝ (NormedSpace.normalize g) (method k - x) +
              method.h ^ (2 : ℕ) := hpre_expand
      _ ≤ ‖method k - x‖ ^ (2 : ℕ) -
            2 * ((method.h / ‖g‖) * (problem.objective (method k) - problem.objective x)) +
              method.h ^ (2 : ℕ) := by
            nlinarith [hscaled]
  linarith

/-- Helper for Theorem 3.2.4: every selected-constraint contribution is controlled by the
corresponding squared-distance drop together with the active-set bonus `-h² / 2`. -/
lemma selectedConstraintGapTerm_le_halfSqDistDiff_sub_halfHSq
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    (x : problem.feasibleSet)
    {j : Fin m} {k : Fin (t + 1)} (hk : k ∈ A[method](t, j)) :
    -(problem.constraintOracle j).correctionStepsize (method k) * problem.constraints j x ≤
      (‖method k - x‖ ^ (2 : ℕ) - ‖method (k + 1) - x‖ ^ (2 : ℕ) -
        method.h ^ (2 : ℕ)) / 2 := by
  let g := (problem.constraintOracle j).subgradient (method k)
  let β := problem.constraints j (method k)
  let η := (problem.constraintOracle j).correctionStepsize (method k)
  have hsel : method.selectedIndexAt k = some j :=
    (mem_selectedConstraintIndices_iff method t j).1 hk
  have hg_ne : g ≠ 0 := hdenom.selected hk
  have hη_nonneg : 0 ≤ η :=
    method.correctionStepsize_nonneg_of_mem_selectedConstraintIndices t hk hdenom.h_pos
  have hactive : j ∈ method.activeSet k := by
    simpa [hsel] using method.selectedIndexAt_spec k
  have hthreshold : method.h * ‖g‖ < β := by
    simpa [ApproximateLagrangeMultiplierSwitchingMethod.activeSet,
      ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet, g, β] using hactive
  have hgap :
      β - problem.constraints j x ≤ inner ℝ g (method k - x) := by
    -- Compare the violated constraint value with the arbitrary comparison point `x`.
    simpa [g, β] using
      MultipleConstraintFirstOrderProblem.value_gap_le_inner_subgradient
        (oracle := problem.constraintOracle j) (x := method k) (y := x)
  let y : E := method k - η • g
  have hpre_sq :
      ‖method (k + 1) - x‖ ^ (2 : ℕ) ≤ ‖y - x‖ ^ (2 : ℕ) := by
    -- Projection back to `Q` cannot increase the distance to the feasible comparison point `x`.
    have hx_proj : IsProjectionPointOn problem.feasibleSet (x : E) (x : E) := by
      refine ⟨x.2, ?_⟩
      simp [Metric.infDist_zero_of_mem x.2]
    have hproj_dist :
        dist (problem.projection y) x ≤ dist y x :=
      (problem.toFirstOrderConvexMinimizationProblem.projection_spec y).dist_le_dist
        problem.feasibleSet_convex hx_proj
    have hproj_norm :
        ‖problem.projection y - x‖ ≤ ‖y - x‖ := by
      simpa [dist_eq_norm] using hproj_dist
    have hproj_sq :
        ‖problem.projection y - x‖ ^ (2 : ℕ) ≤ ‖y - x‖ ^ (2 : ℕ) := by
      exact
        (sq_le_sq₀
          (norm_nonneg (problem.projection y - x))
          (norm_nonneg (y - x))).2 hproj_norm
    simpa [y, method.iterates_succ, method.nextIterate_eq_constraint hsel] using hproj_sq
  have hη_eq : η = β / ‖g‖ ^ (2 : ℕ) := by
    change (problem.constraintOracle j).correctionStepsize (method k) =
      problem.constraints j (method k) /
        ‖(problem.constraintOracle j).subgradient (method k)‖ ^ (2 : ℕ)
    simp [FirstOrderOracle.correctionStepsize]
  have hβ_nonneg : 0 ≤ β := by
    have hmul_nonneg : 0 ≤ method.h * ‖g‖ :=
      mul_nonneg hdenom.h_pos.le (norm_nonneg g)
    exact le_of_lt (lt_of_le_of_lt hmul_nonneg hthreshold)
  have hηβ_eq :
      η * β = β ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := by
    rw [hη_eq]
    ring_nf
  have hnorm_term :
      ‖η • g‖ ^ (2 : ℕ) = η * β := by
    rw [hηβ_eq, hη_eq, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg]
    · field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hg_ne)]
    · positivity
  have hpre_expand :
      ‖y - x‖ ^ (2 : ℕ) =
        ‖method k - x‖ ^ (2 : ℕ) -
          2 * η * inner ℝ g (method k - x) +
            η * β := by
    -- Expand the explicit correction step before using the affine-support inequality.
    calc
      ‖y - x‖ ^ (2 : ℕ) = ‖(method k - x) - η • g‖ ^ (2 : ℕ) := by
        simp [y, sub_eq_add_neg, add_assoc, add_comm]
      _ = ‖method k - x‖ ^ (2 : ℕ) -
            2 * inner ℝ (method k - x) (η • g) + ‖η • g‖ ^ (2 : ℕ) := by
        rw [norm_sub_sq_real]
      _ = ‖method k - x‖ ^ (2 : ℕ) -
            2 * η * inner ℝ g (method k - x) + ‖η • g‖ ^ (2 : ℕ) := by
        rw [real_inner_smul_right, real_inner_comm]
        ring
      _ = ‖method k - x‖ ^ (2 : ℕ) -
            2 * η * inner ℝ g (method k - x) + η * β := by
        rw [hnorm_term]
  have hscaled :
      η * (β - problem.constraints j x) ≤ η * inner ℝ g (method k - x) :=
    mul_le_mul_of_nonneg_left hgap hη_nonneg
  have hbonus :
      method.h ^ (2 : ℕ) ≤ η * β := by
    have hsq : (method.h * ‖g‖) ^ (2 : ℕ) ≤ β ^ (2 : ℕ) := by
      exact
        (sq_le_sq₀
          (mul_nonneg hdenom.h_pos.le (norm_nonneg g))
          hβ_nonneg).2 (le_of_lt hthreshold)
    calc
      method.h ^ (2 : ℕ) ≤ β ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := by
        have hmul :
            method.h ^ (2 : ℕ) * ‖g‖ ^ (2 : ℕ) ≤ β ^ (2 : ℕ) := by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
        exact (_root_.le_div_iff₀ (show 0 < ‖g‖ ^ (2 : ℕ) by positivity)).2 hmul
      _ = η * β := by rw [hηβ_eq]
  have hbound :
      ‖method (k + 1) - x‖ ^ (2 : ℕ) ≤
        ‖method k - x‖ ^ (2 : ℕ) -
          method.h ^ (2 : ℕ) +
            2 * η * problem.constraints j x := by
    -- Spend the affine-support inequality and then the active-set threshold bonus `h²`.
    calc
      ‖method (k + 1) - x‖ ^ (2 : ℕ) ≤ ‖y - x‖ ^ (2 : ℕ) := hpre_sq
      _ = ‖method k - x‖ ^ (2 : ℕ) -
            2 * η * inner ℝ g (method k - x) + η * β := hpre_expand
      _ ≤ ‖method k - x‖ ^ (2 : ℕ) -
            2 * η * (β - problem.constraints j x) + η * β := by
            nlinarith [hscaled]
      _ = ‖method k - x‖ ^ (2 : ℕ) - η * β + 2 * η * problem.constraints j x := by
            ring
      _ ≤ ‖method k - x‖ ^ (2 : ℕ) -
            method.h ^ (2 : ℕ) + 2 * η * problem.constraints j x := by
            linarith
  linarith

/-- Helper for Theorem 3.2.4: the scalar term `N(t) h²` is bounded by the normalizing factor
times the sampled subgradient envelope `M[method](t) * h`. -/
lemma inactiveConstraintCount_mul_hSq_le_sigma_mul_sampleMaxSubgradientNorm_mul_h
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    ((N[method](t) : ℝ) * method.h ^ (2 : ℕ)) ≤
      σ[method](t; hdenom.objective) * (M[method](t) * method.h) := by
  have hS_eq :
      Finset.sum (A₀[method](t)) (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹) =
        S[method](t; hdenom.objective) := by
    -- Rewrite the attached-definition of `S_t` to the surface sum over `A₀(t)`.
    rw [ApproximateLagrangeMultiplierSwitchingMethod.inverseSubgradientNormSum]
    rw [← Finset.sum_attach
      (s := A₀[method](t))
      (f := fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)]
    refine Finset.sum_congr rfl ?_
    intro k hk
    change ‖method.objectiveSubgradient k.1‖⁻¹ =
      ↑((Units.mk0 ‖method.objectiveSubgradient k.1‖
        (norm_ne_zero_iff.mpr (hdenom.objective k.2)))⁻¹ : ℝˣ)
    simp [Units.val_mk0]
  have hcount_le :
      (N[method](t) : ℝ) ≤ M[method](t) * S[method](t; hdenom.objective) := by
    -- Each inactive index contributes `1 ≤ M[method](t) / ‖g(x_k)‖`.
    calc
      (N[method](t) : ℝ) = Finset.sum (A₀[method](t)) (fun _ ↦ (1 : ℝ)) := by
        simp [inactiveConstraintCount]
      _ ≤ Finset.sum (A₀[method](t))
            (fun k ↦ M[method](t) * ‖method.objectiveSubgradient k‖⁻¹) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hk_norm :
              ‖method.objectiveSubgradient k‖ ≤ M[method](t) := by
            have hk_stage :
                ‖method.objectiveSubgradient k‖ ≤
                  problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum
                    (method k) :=
              MultipleConstraintFirstOrderProblem.objectiveSubgradientNorm_le_subgradientNormMaximum
                problem.toMultipleConstraintFirstOrderProblem
                  (method k)
            exact le_trans hk_stage (stageMax_le_sampleMaxSubgradientNorm method k)
          have hg_ne : method.objectiveSubgradient k ≠ 0 := hdenom.objective hk
          have hone :
              (1 : ℝ) = ‖method.objectiveSubgradient k‖ * ‖method.objectiveSubgradient k‖⁻¹ := by
            field_simp [norm_ne_zero_iff.mpr hg_ne]
          calc
            (1 : ℝ) = ‖method.objectiveSubgradient k‖ * ‖method.objectiveSubgradient k‖⁻¹ := hone
            _ ≤ M[method](t) * ‖method.objectiveSubgradient k‖⁻¹ := by
              exact mul_le_mul_of_nonneg_right hk_norm (by positivity)
      _ = M[method](t) * Finset.sum (A₀[method](t))
            (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹) := by
          rw [Finset.mul_sum]
      _ = M[method](t) * S[method](t; hdenom.objective) := by rw [hS_eq]
  -- Multiply the count bound by `h²` and rewrite `σ_t = h S_t`.
  calc
    ((N[method](t) : ℝ) * method.h ^ (2 : ℕ)) ≤
        (M[method](t) * S[method](t; hdenom.objective)) * method.h ^ (2 : ℕ) := by
          gcongr
    _ = σ[method](t; hdenom.objective) * (M[method](t) * method.h) := by
          rw [ApproximateLagrangeMultiplierSwitchingMethod.normalizingFactor]
          ring

/-- Helper for Theorem 3.2.4: summing over `A₀(t)` is the same as summing over the stages where
`selectedIndexAt k = none`. -/
lemma sumInactiveConstraintIndices_eq_sum_objectiveStages
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    {α : Type*} [AddCommMonoid α] (F : Fin (t + 1) → α) :
    Finset.sum (A₀[method](t)) F =
      Finset.sum
        (Finset.univ.filter (fun k : Fin (t + 1) ↦ method.selectedIndexAt k = none)) F := by
  classical
  have hindices :
      A₀[method](t) =
        Finset.univ.filter (fun k : Fin (t + 1) ↦ method.selectedIndexAt k = none) := by
    apply Finset.ext
    intro k
    constructor
    · intro hk
      have hactive : method.activeSet k = ∅ :=
        (mem_inactiveConstraintIndices_iff method t).1 hk
      have hsel : method.selectedIndexAt k = none := by
        cases hcase : method.selectedIndexAt k with
        | none =>
            rfl
        | some j =>
            have hj : j ∈ method.activeSet k := by
              simpa [hcase] using method.selectedIndexAt_spec k
            simp [hactive] at hj
      simp [hsel]
    · intro hk
      have hsel : method.selectedIndexAt k = none := by
        simpa using hk
      have hactive : method.activeSet k = ∅ := by
        simpa [hsel] using method.selectedIndexAt_spec k
      exact (mem_inactiveConstraintIndices_iff method t).2 hactive
  rw [hindices]

/-- Helper for Theorem 3.2.4: summing over the families `A_j(t)` is the same as summing over the
stages where `selectedIndexAt k ≠ none`. -/
lemma sumSelectedConstraintIndices_eq_sum_selectedStages
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    {α : Type*} [AddCommMonoid α] (F : Fin (t + 1) → α) :
    (∑ j : Fin m, Finset.sum (A[method](t, j)) F) =
      Finset.sum
        (Finset.univ.filter (fun k : Fin (t + 1) ↦ method.selectedIndexAt k ≠ none)) F := by
  classical
  calc
    (∑ j : Fin m, Finset.sum (A[method](t, j)) F) =
        ∑ j : Fin m, Finset.sum Finset.univ
          (fun k : Fin (t + 1) ↦ if method.selectedIndexAt k = some j then F k else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [ApproximateLagrangeMultiplierSwitchingMethod.selectedConstraintIndices,
            Finset.sum_filter]
    _ = Finset.sum Finset.univ
          (fun k : Fin (t + 1) ↦ ∑ j : Fin m,
            if method.selectedIndexAt k = some j then F k else 0) := by
          rw [Finset.sum_comm]
    _ = Finset.sum Finset.univ
          (fun k : Fin (t + 1) ↦ if method.selectedIndexAt k = none then 0 else F k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          cases hsel : method.selectedIndexAt k with
          | none =>
              simp
          | some j =>
              simp
    _ = Finset.sum
          (Finset.univ.filter (fun k : Fin (t + 1) ↦ method.selectedIndexAt k ≠ none)) F := by
          simp [Finset.sum_filter]

/-- Helper for Theorem 3.2.4: the objective stages and the selected-constraint stages partition
`{0, ..., t}`. -/
lemma sumInactiveAndSelectedConstraintIndices_eq_sum_univ
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    {α : Type*} [AddCommMonoid α] (F : Fin (t + 1) → α) :
    Finset.sum (A₀[method](t)) F + ∑ j : Fin m, Finset.sum (A[method](t, j)) F =
      ∑ k : Fin (t + 1), F k := by
  classical
  rw [method.sumInactiveConstraintIndices_eq_sum_objectiveStages,
    method.sumSelectedConstraintIndices_eq_sum_selectedStages]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases hsel : method.selectedIndexAt k = none
  · simp [hsel]
  · simp [hsel]

/-- Helper for Theorem 3.2.4: the selected-constraint families together contain exactly the
complement of `A₀(t)` inside `{0, ..., t}`. -/
lemma selectedConstraintIndices_card_sum_eq_total_sub_inactiveConstraintCount
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) :
    (∑ j : Fin m, ((A[method](t, j)).card : ℝ)) =
      (t + 1 : ℝ) - N[method](t) := by
  -- Specialize the stage partition to the constant function `1` to count both sides.
  have hpartition :
      (N[method](t) : ℝ) + ∑ j : Fin m, ((A[method](t, j)).card : ℝ) = (t + 1 : ℝ) := by
    simpa [inactiveConstraintCount] using
      (method.sumInactiveAndSelectedConstraintIndices_eq_sum_univ
        (t := t) (F := fun _ ↦ (1 : ℝ)))
  -- Rearranging the partition count isolates the selected-stage contribution.
  linarith

/-- Helper for Theorem 3.2.4: multiplying the Definition 3.46 primal average by `σ_t` rewrites
it as the explicit inactive-stage objective-gap sum. -/
lemma sigmaMul_objectiveAverageSub_eq_sumInactiveObjectiveGaps
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    (x : problem.feasibleSet) :
    σ[method](t; hdenom.objective) *
      ((((A₀[method](t)).centerMass
          (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
          (fun k ↦ problem.objective (method k)) : ℝ) - problem.objective x)) =
      Finset.sum (A₀[method](t)) (fun k ↦
        (method.h / ‖method.objectiveSubgradient k‖) *
          (problem.objective (method k) - problem.objective x)) := by
  have hS_pos :
      0 < S[method](t; hdenom.objective) :=
    method.inverseSubgradientNormSum_pos_of_inactiveConstraintCount_pos
      t hdenom.objective hdenom.inactiveConstraintCount_pos
  have hweightedAverage :
      ((A₀[method](t)).centerMass
          (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
          (fun k ↦ problem.objective (method k)) : ℝ) =
        Finset.sum (A₀[method](t))
          (fun k ↦
            (‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
              problem.objective (method k)) :=
    method.inactiveObjectiveAverage_eq_weightedSum t hdenom
  have hconstantAsWeightedSum :
      problem.objective x =
        Finset.sum (A₀[method](t))
          (fun k ↦
            (‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
              problem.objective x) := by
    -- Rewrite the constant objective value using that the normalized inactive weights sum to `1`.
    calc
      problem.objective x =
          (Finset.sum (A₀[method](t))
              (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective))) *
            problem.objective x := by
              rw [method.inactiveObjectiveWeights_sum_one t hdenom, one_mul]
      _ =
          Finset.sum (A₀[method](t))
            (fun k ↦
              (‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
                problem.objective x) := by
              rw [Finset.sum_mul]
  -- Route correction: normalize the primal average once via Definition 3.46, then cancel the
  -- common `S_t` factor termwise instead of re-expanding `centerMass` inside the aggregate proof.
  calc
    σ[method](t; hdenom.objective) *
        ((((A₀[method](t)).centerMass
            (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
            (fun k ↦ problem.objective (method k)) : ℝ) - problem.objective x)) =
      (method.h * S[method](t; hdenom.objective)) *
        (Finset.sum (A₀[method](t))
            (fun k ↦
              (‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
                problem.objective (method k)) -
          problem.objective x) := by
          rw [ApproximateLagrangeMultiplierSwitchingMethod.normalizingFactor, hweightedAverage]
    _ =
      (method.h * S[method](t; hdenom.objective)) *
        (Finset.sum (A₀[method](t))
            (fun k ↦
              (‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
                problem.objective (method k)) -
          Finset.sum (A₀[method](t))
            (fun k ↦
                (‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
                problem.objective x)) := by
          have hsub :
              Finset.sum (A₀[method](t))
                  (fun k ↦
                    (‖method.objectiveSubgradient k‖⁻¹ /
                        S[method](t; hdenom.objective)) *
                      problem.objective (method k)) -
                problem.objective x =
              Finset.sum (A₀[method](t))
                  (fun k ↦
                    (‖method.objectiveSubgradient k‖⁻¹ /
                        S[method](t; hdenom.objective)) *
                      problem.objective (method k)) -
                Finset.sum (A₀[method](t))
                  (fun k ↦
                    (‖method.objectiveSubgradient k‖⁻¹ /
                        S[method](t; hdenom.objective)) *
                      problem.objective x) := by
            linarith [hconstantAsWeightedSum]
          rw [hsub]
    _ =
      (method.h * S[method](t; hdenom.objective)) *
        Finset.sum (A₀[method](t)) (fun k ↦
          ((‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
              problem.objective (method k)) -
            ((‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
              problem.objective x)) := by
          rw [← Finset.sum_sub_distrib]
    _ =
      Finset.sum (A₀[method](t)) (fun k ↦
        (method.h * S[method](t; hdenom.objective)) *
          (((‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
              problem.objective (method k)) -
            ((‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
              problem.objective x))) := by
          rw [Finset.mul_sum]
    _ =
      Finset.sum (A₀[method](t)) (fun k ↦
        (method.h * S[method](t; hdenom.objective)) *
          ((‖method.objectiveSubgradient k‖⁻¹ / S[method](t; hdenom.objective)) *
            (problem.objective (method k) - problem.objective x))) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ =
      Finset.sum (A₀[method](t)) (fun k ↦
        (method.h / ‖method.objectiveSubgradient k‖) *
          (problem.objective (method k) - problem.objective x)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hk_norm_ne : ‖method.objectiveSubgradient k‖ ≠ 0 :=
            norm_ne_zero_iff.mpr (hdenom.objective hk)
          field_simp [ne_of_gt hS_pos, hk_norm_ne]

/-- Helper for Theorem 3.2.4: multiplying the penalty term by `σ_t` rewrites it as the explicit
double sum of selected correction penalties. -/
lemma sigmaMul_constraintPenalty_eq_sumSelectedCorrectionPenalties
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    (x : problem.feasibleSet) :
    σ[method](t; hdenom.objective) *
      (∑ j : Fin m, (λ[method](t; hdenom) j) * problem.constraints j x) =
      ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
        (problem.constraintOracle j).correctionStepsize (method k) * problem.constraints j x) := by
  -- Rewrite each coordinate of `λ_t`, then cancel the common factor `σ_t`.
  calc
    σ[method](t; hdenom.objective) *
        (∑ j : Fin m, (λ[method](t; hdenom) j) * problem.constraints j x) =
      ∑ j : Fin m,
        σ[method](t; hdenom.objective) *
          ((λ[method](t; hdenom) j) * problem.constraints j x) := by
        rw [Finset.mul_sum]
    _ =
      ∑ j : Fin m,
        ((Finset.sum (A[method](t, j)).attach
            (fun k ↦ (problem.constraintOracle j).correctionStepsize (method k.1))) *
          problem.constraints j x) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [method.approximateDualMultiplier_apply]
        have hcancel :
            σ[method](t; hdenom.objective) *
                (((Finset.sum (A[method](t, j)).attach
                    (fun k ↦ (problem.constraintOracle j).correctionStepsize (method k.1))) /
                  σ[method](t; hdenom.objective)) *
                problem.constraints j x) =
              (Finset.sum (A[method](t, j)).attach
                  (fun k ↦ (problem.constraintOracle j).correctionStepsize (method k.1))) *
                problem.constraints j x := by
          field_simp [hdenom.normalizingFactor_ne_zero]
        exact hcancel
    _ =
      ∑ j : Fin m,
        Finset.sum (A[method](t, j)).attach
          (fun k ↦
            (problem.constraintOracle j).correctionStepsize (method k.1) *
              problem.constraints j x) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [Finset.sum_mul]
    _ =
      ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
        (problem.constraintOracle j).correctionStepsize (method k) * problem.constraints j x) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [← Finset.sum_attach
          (s := A[method](t, j))
          (f := fun k ↦
            (problem.constraintOracle j).correctionStepsize (method k) *
              problem.constraints j x)]

/-- Helper for Theorem 3.2.4: the full prefix sum of half squared-distance drops telescopes to
the endpoint difference. -/
private lemma sumSqDistDropHalf_eq_endpointDiffHalf
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (x : problem.feasibleSet) :
    (∑ k : Fin (t + 1),
        (‖method k - x‖ ^ (2 : ℕ) - ‖method (k + 1) - x‖ ^ (2 : ℕ)) / 2) =
      (‖method 0 - x‖ ^ (2 : ℕ) - ‖method (t + 1) - x‖ ^ (2 : ℕ)) / 2 := by
  -- Rewrite the `Fin`-indexed prefix as a `range` sum and telescope the adjacent differences.
  calc
    (∑ k : Fin (t + 1),
        (‖method k - x‖ ^ (2 : ℕ) - ‖method (k + 1) - x‖ ^ (2 : ℕ)) / 2) =
      Finset.sum (Finset.range (t + 1))
        (fun k ↦ (‖method k - x‖ ^ (2 : ℕ) - ‖method (k + 1) - x‖ ^ (2 : ℕ)) / 2) := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun k : ℕ ↦
                (‖method k - x‖ ^ (2 : ℕ) - ‖method (k + 1) - x‖ ^ (2 : ℕ)) / 2)
              (t + 1))
    _ =
      (Finset.sum (Finset.range (t + 1))
        (fun k ↦ (‖method k - x‖ ^ (2 : ℕ) - ‖method (k + 1) - x‖ ^ (2 : ℕ)))) / 2 := by
          rw [Finset.sum_div]
    _ =
      (‖method 0 - x‖ ^ (2 : ℕ) - ‖method (t + 1) - x‖ ^ (2 : ℕ)) / 2 := by
          rw [Finset.sum_range_sub' (fun k ↦ ‖method k - x‖ ^ (2 : ℕ)) (t + 1)]

/-- Helper for Theorem 3.2.4: the telescoped squared-distance drop is controlled by the large
iteration budget `((t + 1) : ℝ) * h² / 2`. -/
private lemma endpointSqDistDropHalf_le_iterationBudgetHalf
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ))
    (x : problem.feasibleSet) :
    (‖method 0 - x‖ ^ (2 : ℕ) - ‖method (t + 1) - x‖ ^ (2 : ℕ)) / 2 ≤
      (((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ)) / 2 := by
  have hinitial_dist : ‖method 0 - x‖ ≤ R := by
    -- The bounded feasible set controls the initial squared-distance term.
    simpa [method.iterates_zero_eq_x0, norm_sub_rev] using hQ_bounded x x.2
  have hinitial_sq : ‖method 0 - x‖ ^ (2 : ℕ) ≤ (R : ℝ) ^ (2 : ℕ) := by
    have hR_nonneg : 0 ≤ (R : ℝ) := by
      exact_mod_cast R.2
    have hsq :=
      mul_le_mul hinitial_dist hinitial_dist (norm_nonneg (method 0 - x)) hR_nonneg
    simpa [pow_two] using hsq
  have hR_sq_lt :
      (R : ℝ) ^ (2 : ℕ) < (t : ℝ) * method.h ^ (2 : ℕ) := by
    exact (_root_.div_lt_iff₀ (show 0 < method.h ^ (2 : ℕ) by positivity)).1 ht
  have hR_sq_lt_succ :
      (R : ℝ) ^ (2 : ℕ) < ((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ) := by
    have hhSq_pos : 0 < method.h ^ (2 : ℕ) := by
      positivity
    calc
      (R : ℝ) ^ (2 : ℕ) < (t : ℝ) * method.h ^ (2 : ℕ) := hR_sq_lt
      _ < ((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ) := by
          have htlt : (t : ℝ) < ((t + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.lt_succ_self t
          exact mul_lt_mul_of_pos_right htlt hhSq_pos
  have hterminal_nonneg : 0 ≤ ‖method (t + 1) - x‖ ^ (2 : ℕ) := by
    positivity
  -- Discard the nonnegative terminal distance term and spend the large-iteration budget bound.
  have hmain :
      (‖method 0 - x‖ ^ (2 : ℕ) - ‖method (t + 1) - x‖ ^ (2 : ℕ)) / 2 <
        (((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ)) / 2 := by
    nlinarith [hinitial_sq, hR_sq_lt_succ, hterminal_nonneg]
  exact hmain.le

/-- Helper for Theorem 3.2.4: the Definition 3.45 and 3.46 aggregate terms combine to give the
real-valued estimate `σ_t * (avgObj - lagrangian x λ_t) ≤ N(t) * h²`. -/
lemma sigmaMul_primalAverageSubLagrangian_le_inactiveConstraintCount_mul_hSq
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    (hh : 0 < method.h)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ))
    (x : problem.feasibleSet) :
    σ[method](t; hdenom.objective) *
      ((((A₀[method](t)).centerMass
          (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
          (fun k ↦ problem.objective (method k)) : ℝ) -
        problem.toLagrangianProblem.lagrangian x (λ[method](t; hdenom)))) ≤
      ((N[method](t) : ℝ) * method.h ^ (2 : ℕ)) := by
  let avgObj : ℝ :=
    ((A₀[method](t)).centerMass
      (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
      (fun k ↦ problem.objective (method k)) : ℝ)
  let lam := λ[method](t; hdenom)
  let D : ℕ → ℝ := fun k ↦ ‖method k - x‖ ^ (2 : ℕ)
  let diffHalf : Fin (t + 1) → ℝ := fun k ↦ (D k - D (k + 1)) / 2
  let halfHSq : ℝ := method.h ^ (2 : ℕ) / 2
  have hlagrangian :
      problem.toLagrangianProblem.lagrangian x lam =
        problem.objective x + ∑ j : Fin m, lam j * problem.constraints j x := by
    -- Expand the fixed-`λ_t` Lagrangian slice into the objective term plus the penalty sum.
    rw [LagrangianProblem.lagrangian_eq_objective_add_sum]
    simp [ProjectedMultipleConstraintFirstOrderProblem.toLagrangianProblem]
  have hsigma_split :
      σ[method](t; hdenom.objective) * (avgObj - problem.toLagrangianProblem.lagrangian x lam) =
        σ[method](t; hdenom.objective) * (avgObj - problem.objective x) -
          σ[method](t; hdenom.objective) *
            (∑ j : Fin m, lam j * problem.constraints j x) := by
    -- Separate the `σ_t`-scaled primal-average gap from the `σ_t`-scaled penalty term.
    rw [hlagrangian]
    ring
  have hobjective_bound :
      Finset.sum (A₀[method](t)) (fun k ↦
        (method.h / ‖method.objectiveSubgradient k‖) *
          (problem.objective (method k) - problem.objective x)) ≤
        Finset.sum (A₀[method](t)) (fun k ↦
          (D k - D (k + 1) + method.h ^ (2 : ℕ)) / 2) := by
    -- Sum the objective-branch one-step bounds over the inactive stages `A₀(t)`.
    exact Finset.sum_le_sum fun k hk ↦
      method.inactiveObjectiveGapTerm_le_halfSqDistDiff_add_halfHSq
        (t := t) (hdenom := hdenom) (x := x) hk
  have hselected_bound :
      - (∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
          (problem.constraintOracle j).correctionStepsize (method k) *
            problem.constraints j x)) ≤
        ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
          (D k - D (k + 1) - method.h ^ (2 : ℕ)) / 2) := by
    -- Rewrite the outer minus sign as a pointwise negation before summing the selected
    -- one-step bounds.
    have hselected_bound' :
        ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
            (-(problem.constraintOracle j).correctionStepsize (method k)) *
              problem.constraints j x) ≤
          ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
            (D k - D (k + 1) - method.h ^ (2 : ℕ)) / 2) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact Finset.sum_le_sum fun k hk ↦ by
        simpa [D] using
          (method.selectedConstraintGapTerm_le_halfSqDistDiff_sub_halfHSq
            (t := t) (hdenom := hdenom) (x := x) (j := j) hk)
    simpa [Finset.sum_neg_distrib, neg_mul]
      using hselected_bound'
  have hpartition_diff :
      Finset.sum (A₀[method](t)) diffHalf + ∑ j : Fin m, Finset.sum (A[method](t, j)) diffHalf =
        ∑ k : Fin (t + 1), diffHalf k := by
    -- Use the stage partition only on the pure distance-drop term.
    simpa [diffHalf] using
      (method.sumInactiveAndSelectedConstraintIndices_eq_sum_univ (t := t) (F := diffHalf))
  have hobjective_split :
      Finset.sum (A₀[method](t)) (fun k ↦
          (D k - D (k + 1) + method.h ^ (2 : ℕ)) / 2) =
        Finset.sum (A₀[method](t)) diffHalf + (N[method](t) : ℝ) * halfHSq := by
    -- Separate the distance-drop contribution from the constant `h² / 2` term on `A₀(t)`.
    calc
      Finset.sum (A₀[method](t)) (fun k ↦
          (D k - D (k + 1) + method.h ^ (2 : ℕ)) / 2) =
        Finset.sum (A₀[method](t)) (fun k ↦ diffHalf k + halfHSq) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [diffHalf, halfHSq]
          ring
      _ =
        Finset.sum (A₀[method](t)) diffHalf + Finset.sum (A₀[method](t)) (fun _ ↦ halfHSq) := by
          rw [Finset.sum_add_distrib]
      _ = Finset.sum (A₀[method](t)) diffHalf + (N[method](t) : ℝ) * halfHSq := by
          simp [inactiveConstraintCount, Finset.sum_const, nsmul_eq_mul]
  have hselected_split :
      ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
          (D k - D (k + 1) - method.h ^ (2 : ℕ)) / 2) =
        (∑ j : Fin m, Finset.sum (A[method](t, j)) diffHalf) -
          (∑ j : Fin m, ((A[method](t, j)).card : ℝ)) * halfHSq := by
    -- Separate the selected-stage distance drops from the constant `-h² / 2` term.
    calc
      ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
          (D k - D (k + 1) - method.h ^ (2 : ℕ)) / 2) =
        ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦ diffHalf k - halfHSq) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [diffHalf, halfHSq]
          ring
      _ =
        ∑ j : Fin m,
          (Finset.sum (A[method](t, j)) diffHalf -
            ((A[method](t, j)).card : ℝ) * halfHSq) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      _ =
        (∑ j : Fin m, Finset.sum (A[method](t, j)) diffHalf) -
          (∑ j : Fin m, ((A[method](t, j)).card : ℝ)) * halfHSq := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
  have hdiff_budget :
      (∑ k : Fin (t + 1), diffHalf k) ≤ (((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ)) / 2 := by
    -- Telescope the full-prefix distance drops and then spend the large-iteration budget.
    calc
      (∑ k : Fin (t + 1), diffHalf k) =
          (‖method 0 - x‖ ^ (2 : ℕ) - ‖method (t + 1) - x‖ ^ (2 : ℕ)) / 2 := by
            simpa [diffHalf, D] using
              (method.sumSqDistDropHalf_eq_endpointDiffHalf (t := t) (x := x))
      _ ≤ (((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ)) / 2 := by
            exact method.endpointSqDistDropHalf_le_iterationBudgetHalf
              (R := R) (t := t) hh hQ_bounded ht x
  have hassembled :
      Finset.sum (A₀[method](t)) (fun k ↦
          (D k - D (k + 1) + method.h ^ (2 : ℕ)) / 2) +
        ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
          (D k - D (k + 1) - method.h ^ (2 : ℕ)) / 2) ≤
        ((N[method](t) : ℝ) * method.h ^ (2 : ℕ)) := by
    -- After telescoping the distance drops, only the scalar `±h² / 2` bookkeeping remains.
    let selectedCount : ℝ := ∑ j : Fin m, ((A[method](t, j)).card : ℝ)
    have hpartition_le :
        Finset.sum (A₀[method](t)) diffHalf + ∑ j : Fin m, Finset.sum (A[method](t, j)) diffHalf ≤
          (((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ)) / 2 := by
      rw [hpartition_diff]
      exact hdiff_budget
    have hselected_card :
        selectedCount = (t + 1 : ℝ) - N[method](t) := by
      dsimp [selectedCount]
      exact
      method.selectedConstraintIndices_card_sum_eq_total_sub_inactiveConstraintCount (t := t)
    have hcoeff :
        (((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ)) / 2 +
            ((N[method](t) : ℝ) * (method.h ^ (2 : ℕ) / 2) -
              selectedCount * (method.h ^ (2 : ℕ) / 2)) =
          ((N[method](t) : ℝ) * method.h ^ (2 : ℕ)) := by
      rw [hselected_card, Nat.cast_add, Nat.cast_one]
      ring
    rw [hobjective_split, hselected_split]
    calc
      Finset.sum (A₀[method](t)) diffHalf + (N[method](t) : ℝ) * (method.h ^ (2 : ℕ) / 2) +
          (∑ j : Fin m, Finset.sum (A[method](t, j)) diffHalf -
            selectedCount * (method.h ^ (2 : ℕ) / 2)) =
        (Finset.sum (A₀[method](t)) diffHalf +
            ∑ j : Fin m, Finset.sum (A[method](t, j)) diffHalf) +
          ((N[method](t) : ℝ) * (method.h ^ (2 : ℕ) / 2) -
            selectedCount * (method.h ^ (2 : ℕ) / 2)) := by
            ring
      _ ≤
        (((t + 1 : ℕ) : ℝ) * method.h ^ (2 : ℕ)) / 2 +
          ((N[method](t) : ℝ) * (method.h ^ (2 : ℕ) / 2) -
            selectedCount * (method.h ^ (2 : ℕ) / 2)) := by
            simpa [add_assoc, add_comm, add_left_comm] using
              add_le_add_right hpartition_le
                ((N[method](t) : ℝ) * (method.h ^ (2 : ℕ) / 2) -
                  selectedCount * (method.h ^ (2 : ℕ) / 2))
      _ = ((N[method](t) : ℝ) * method.h ^ (2 : ℕ)) := hcoeff
  -- Route correction: consume the packaged sigma-normalization lemmas and the packaged
  -- one-step bounds, then use the partition/telescope helpers only on the distance-drop terms.
  calc
    σ[method](t; hdenom.objective) * (avgObj - problem.toLagrangianProblem.lagrangian x lam) =
        σ[method](t; hdenom.objective) * (avgObj - problem.objective x) -
          σ[method](t; hdenom.objective) *
            (∑ j : Fin m, lam j * problem.constraints j x) := hsigma_split
    _ ≤
        Finset.sum (A₀[method](t)) (fun k ↦
            (D k - D (k + 1) + method.h ^ (2 : ℕ)) / 2) +
          ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
            (D k - D (k + 1) - method.h ^ (2 : ℕ)) / 2) := by
          have hmain :
              Finset.sum (A₀[method](t)) (fun k ↦
                  (method.h / ‖method.objectiveSubgradient k‖) *
                    (problem.objective (method k) - problem.objective x)) -
                ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
                  (problem.constraintOracle j).correctionStepsize (method k) *
                    problem.constraints j x) ≤
                Finset.sum (A₀[method](t)) (fun k ↦
                    (D k - D (k + 1) + method.h ^ (2 : ℕ)) / 2) +
                  ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
                    (D k - D (k + 1) - method.h ^ (2 : ℕ)) / 2) := by
            have hadd := add_le_add hobjective_bound hselected_bound
            simpa [sub_eq_add_neg] using hadd
          calc
            σ[method](t; hdenom.objective) * (avgObj - problem.objective x) -
                σ[method](t; hdenom.objective) *
                  (∑ j : Fin m, lam j * problem.constraints j x) =
              Finset.sum (A₀[method](t)) (fun k ↦
                  (method.h / ‖method.objectiveSubgradient k‖) *
                    (problem.objective (method k) - problem.objective x)) -
                ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
                  (problem.constraintOracle j).correctionStepsize (method k) *
                    problem.constraints j x) := by
                    rw [method.sigmaMul_objectiveAverageSub_eq_sumInactiveObjectiveGaps
                      (t := t) (hdenom := hdenom) (x := x),
                      method.sigmaMul_constraintPenalty_eq_sumSelectedCorrectionPenalties
                        (t := t) (hdenom := hdenom) (x := x)]
            _ ≤
              Finset.sum (A₀[method](t)) (fun k ↦
                  (D k - D (k + 1) + method.h ^ (2 : ℕ)) / 2) +
                ∑ j : Fin m, Finset.sum (A[method](t, j)) (fun k ↦
                  (D k - D (k + 1) - method.h ^ (2 : ℕ)) / 2) := hmain
    _ ≤ ((N[method](t) : ℝ) * method.h ^ (2 : ℕ)) := hassembled

/-- Theorem 3.2.4: under the large-iteration hypothesis, the Definition 3.46 primal average is
pointwise bounded below by the fixed-`λ_t` Lagrangian up to the error `M h`. -/
lemma pointwiseLagrangianLowerBound_of_large_iteration_count
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    (hh : 0 < method.h)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ))
    (x : problem.feasibleSet) :
    (((A₀[method](t)).centerMass
        (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
        (fun k ↦ problem.objective (method k)) : ℝ) - M[method](t) * method.h) ≤
      problem.toLagrangianProblem.lagrangian x (λ[method](t; hdenom)) := by
  let avgObj : ℝ :=
    ((A₀[method](t)).centerMass
      (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
      (fun k ↦ problem.objective (method k)) : ℝ)
  let lam := λ[method](t; hdenom)
  have hsigma_pos : 0 < σ[method](t; hdenom.objective) :=
    hdenom.normalizingFactor_pos
  have hscaled :
      σ[method](t; hdenom.objective) * (avgObj - problem.toLagrangianProblem.lagrangian x lam) ≤
        σ[method](t; hdenom.objective) * (M[method](t) * method.h) := by
    -- Compare the aggregate `σ_t` bound with the sampled subgradient envelope bound.
    exact le_trans
      (method.sigmaMul_primalAverageSubLagrangian_le_inactiveConstraintCount_mul_hSq
        (R := R) (t := t) (hdenom := hdenom) hh hQ_bounded ht x)
      (method.inactiveConstraintCount_mul_hSq_le_sigma_mul_sampleMaxSubgradientNorm_mul_h
        (t := t) (hdenom := hdenom))
  -- Descale by the positive factor `σ_t` to recover the pointwise Lagrangian lower bound.
  have hdescaled :
      avgObj - problem.toLagrangianProblem.lagrangian x lam ≤ M[method](t) * method.h := by
    exact le_of_mul_le_mul_left hscaled hsigma_pos
  linarith

/-- Companion bridge for Theorem 3.2.4: in the large-iteration regime, the textbook gap
quantity `δ_t` is bounded above by `M h`, where `0 < h` and `M = M[method](t)`. The source
denominator regime needed for `δ_t` is assembled from the objective and selected-constraint
nonvanishing hypotheses together with the earlier positivity theorem for `N(t)`. -/
-- Proof sketch: combine the telescoping estimate `(3.2.36)` with the source positivity gate
-- `0 < S[method](t; hobjective)`, obtained from the earlier positivity theorem for `N(t)`,
-- hence `0 < σ[method](t; hobjective)`. After inserting `t > R² / h²`, divide by `σ_t`
-- to obtain `δ_t ≤ M h`.
theorem delta_le_sampleMaxSubgradientNorm_mul_h_of_large_iteration_count
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hobjective : method.HasObjectiveDenominators t)
    (hselected : method.HasSelectedConstraintDenominators t)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (hfeasible : Set.Nonempty lagrangianFeasibleSet)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    δ[method](t;
        (method.hasApproximateDualMultiplierDenominators_of_large_iteration_count
          R t hh hobjective hselected hQ_bounded hfeasible ht)) ≤
      (M[method](t) * method.h : EReal) := by
  let hdenom :=
    method.hasApproximateDualMultiplierDenominators_of_large_iteration_count
      R t hh hobjective hselected hQ_bounded hfeasible ht
  -- Route correction: the closing `EReal` step is now isolated in
  -- `primalDualGapQuantity_le_of_pointwiseLagrangianLowerBound`.
  -- Only the global pointwise lower bound on `Q` remains to be proved.
  refine
    (method.primalDualGapQuantity_le_of_pointwiseLagrangianLowerBound
      t hdenom ?_)
  intro x
  -- The real-valued aggregate bridge is now packaged separately, so the `EReal` closing step is
  -- just an application of the pointwise lower bound on the fixed-`λ_t` Lagrangian slice.
  exact
    method.pointwiseLagrangianLowerBound_of_large_iteration_count
      R t hdenom hh hQ_bounded ht x

/-- First consequence of Theorem 3.2.4: if `0 < h`, the feasible set is contained in the ball
`‖x - x₀‖ ≤ R`, the constraint-feasible set is nonempty, and `t > R² / h²`, then `N(t) > 0`. -/
theorem large_iteration_count_positive_inactiveConstraintCount
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (hfeasible : Set.Nonempty lagrangianFeasibleSet)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    0 < N[method](t) := by
  -- This public theorem is the source-facing wrapper around the companion bridge above.
  exact
    method.positive_inactiveConstraintCount_of_large_iteration_count
      R t hh hQ_bounded hfeasible ht

/-- Second consequence of Theorem 3.2.4: under the same large-iteration hypotheses, every
objective-step iterate `x_k` with `k ∈ A₀(t)` satisfies
`maxTypeObjective problem.constraints (method k) ≤ M[method](t) * method.h`. -/
theorem large_iteration_count_maxConstraintValueAt_le_sampleMaxSubgradientNorm_mul_h
    [CompleteSpace E] [NeZero m]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (hfeasible : Set.Nonempty lagrangianFeasibleSet)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ))
    {k : Fin (t + 1)} (hk : k ∈ A₀[method](t)) :
    maxTypeObjective problem.constraints (method k) ≤ M[method](t) * method.h := by
  let _ := hQ_bounded
  let _ := hfeasible
  let _ := ht
  -- This source-facing theorem is exactly the previously proved inactive-index residual bound.
  exact
    method.maxConstraintValueAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices
      t hh hk

/-- Third consequence of Theorem 3.2.4: under the same large-iteration hypotheses and the
denominator hypotheses needed to form the textbook multiplier `λ_t`, the canonical gap quantity
`δ_t` satisfies `δ_t ≤ M[method](t) * method.h`. -/
theorem large_iteration_count_delta_le_sampleMaxSubgradientNorm_mul_h
    [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hobjective : method.HasObjectiveDenominators t)
    (hselected : method.HasSelectedConstraintDenominators t)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (hfeasible : Set.Nonempty lagrangianFeasibleSet)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    δ[method](t;
        (method.hasApproximateDualMultiplierDenominators_of_large_iteration_count
          R t hh hobjective hselected hQ_bounded hfeasible ht)) ≤
      (M[method](t) * method.h : EReal) := by
  -- This public theorem is the source-facing wrapper around the companion `δ_t` estimate.
  exact
    method.delta_le_sampleMaxSubgradientNorm_mul_h_of_large_iteration_count
      R t hh hobjective hselected hQ_bounded hfeasible ht

end ConstraintMaxima

end ApproximateLagrangeMultiplierSwitchingMethod

end
