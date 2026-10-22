/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_extra_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Deriv

noncomputable section

section Chapter08Theorem8218

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin n)

-- Domain-style sampling:
-- * primary domain: convex constrained optimization and KKT sufficiency
-- * sampled owner declarations:
--   `ConstrainedOptimizationProblem.IsKKTPoint`
--   `ConstrainedOptimizationProblem.HasConstraintGradientsAt`
--   `IsMinOn`
--   `ConstrainedOptimizationProblem.IsConvexProgramming`
--   `ConstrainedOptimizationProblem.IsGlobalMinimizer`
-- * source/core/bridge triage:
--   `source-facing`: the global-minimizer conclusion for constrained problems
--   `core/canonical`: the KKT owner `problem.IsKKTPoint`, the convex-programming owner
--     `problem.IsConvexProgramming`, and the minimizer owner `IsMinOn`
--   `bridge/view`: `problem.IsGlobalMinimizer xStar`, which packages feasibility together with
--     the core `IsMinOn` conclusion
-- * primitive data: the constrained problem, the candidate point, the multiplier vector, and
--   the smoothness data at `xStar`
-- * derived API: the `IsMinOn` conclusion and its constrained-global-minimizer bridge

namespace ConstrainedOptimizationProblem

/-- Helper for Chapter08 Theorem 8.2.18: the convex-feasible-set part of convex programming keeps
the whole unit-interval segment between feasible points inside `problem.feasibleSet`. -/
lemma lineMap_mem_feasibleSet_of_mem
    {problem : ConstrainedOptimizationProblem n m E I} {xStar x : Point}
    (h_convex : problem.IsConvexProgramming) (hxStar : xStar ∈ problem) (hx : x ∈ problem)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (k := ℝ) xStar x t ∈ problem.feasibleSet := by
  -- Rewrite the affine segment point as a convex combination and use convexity of the feasible
  -- set packaged inside `problem.IsConvexProgramming`.
  rw [AffineMap.lineMap_apply_module]
  refine h_convex.1 ?_ ?_ (sub_nonneg.2 ht.2) ht.1 ?_
  · simpa [problem.feasibleSet_eq_setOf_mem] using hxStar
  · simpa [problem.feasibleSet_eq_setOf_mem] using hx
  · linarith

/-- Helper for Chapter08 Theorem 8.2.18: along a feasible segment, convexity of the objective
forces the directional derivative at `xStar` to lie below the endpoint slope. -/
lemma objective_fderiv_le_sub_of_isConvexProgramming
    {problem : ConstrainedOptimizationProblem n m E I} {xStar x : Point}
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_convex : problem.IsConvexProgramming) (hxStar : xStar ∈ problem) (hx : x ∈ problem) :
    fderiv ℝ problem.objective xStar (x - xStar) ≤
      problem.objective x - problem.objective xStar := by
  let g : ℝ → ℝ := problem.objective ∘ (AffineMap.lineMap (k := ℝ) xStar x : ℝ → Point)
  let T : Set ℝ := (AffineMap.lineMap (k := ℝ) xStar x : ℝ → Point) ⁻¹' problem.feasibleSet
  have hgconv : ConvexOn ℝ T g := by
    -- Restrict the convex objective to the affine line through `xStar` and `x`.
    simpa [g, T, Function.comp] using
      h_convex.comp_affineMap (AffineMap.lineMap (k := ℝ) xStar x)
  have h0 : (0 : ℝ) ∈ T := by
    simpa [T, problem.feasibleSet_eq_setOf_mem, AffineMap.lineMap_apply_zero] using hxStar
  have h1 : (1 : ℝ) ∈ T := by
    simpa [T, problem.feasibleSet_eq_setOf_mem, AffineMap.lineMap_apply_one] using hx
  have hderiv_g :
      HasDerivAt g (fderiv ℝ problem.objective xStar (x - xStar)) 0 := by
    -- The derivative of the line restriction is the objective directional derivative.
    simpa [g, Function.comp] using
      (h_objective.hasFDerivAt.comp_hasDerivAt_of_eq
        (hf := AffineMap.hasDerivAt_lineMap (a := xStar) (b := x) (x := 0))
        (hy := (AffineMap.lineMap_apply_zero xStar x).symm))
  have hslope :=
    hgconv.deriv_le_slope h0 h1 zero_lt_one hderiv_g.differentiableAt
  rw [hderiv_g.deriv] at hslope
  simpa [g, slope_def_field] using hslope

/-- Helper for Chapter08 Theorem 8.2.18: differentiating a constraint along the line from
`xStar` to `x` produces the Chapter 8 linearized-constraint pairing. -/
lemma hasDerivAt_constraint_lineMap
    {problem : ConstrainedOptimizationProblem n m E I} {xStar x : Point}
    (h_constraints : problem.HasConstraintGradientsAt xStar) (i : Fin m) :
    HasDerivAt
      (problem.constraint i ∘ (AffineMap.lineMap (k := ℝ) xStar x : ℝ → Point))
      (problem.linearizedConstraintPairing xStar (x - xStar) i) 0 := by
  -- Chain the constraint derivative at `xStar` with the derivative of the affine segment map.
  simpa [ConstrainedOptimizationProblem.linearizedConstraintPairing, Function.comp] using
    ((h_constraints i).hasFDerivAt.comp_hasDerivAt_of_eq
      (hf := AffineMap.hasDerivAt_lineMap (a := xStar) (b := x) (x := 0))
      (hy := (AffineMap.lineMap_apply_zero xStar x).symm))

/-- Helper for Chapter08 Theorem 8.2.18: equality constraints vanish identically on a feasible
segment, so their linearized pairings are zero. -/
lemma linearizedConstraintPairing_eq_zero_of_eqIndex_of_feasible
    {problem : ConstrainedOptimizationProblem n m E I} {xStar x : Point}
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_convex : problem.IsConvexProgramming) (hxStar : xStar ∈ problem) (hx : x ∈ problem)
    {i : Fin m} (hi : i ∈ problem.eqIndices) :
    problem.linearizedConstraintPairing xStar (x - xStar) i = 0 := by
  let g : ℝ → ℝ := problem.constraint i ∘ (AffineMap.lineMap (k := ℝ) xStar x : ℝ → Point)
  have hderiv_g :
      HasDerivAt g (problem.linearizedConstraintPairing xStar (x - xStar) i) 0 :=
    hasDerivAt_constraint_lineMap h_constraints i
  have hlt_one : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
    (eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds
  have hmem :
      problem.linearizedConstraintPairing xStar (x - xStar) i ∈ ({0} : Set ℝ) := by
    refine isClosed_singleton.mem_of_tendsto hderiv_g.tendsto_slope_zero_right ?_
    filter_upwards [self_mem_nhdsWithin, hlt_one] with t ht0 ht1
    have hline :
        AffineMap.lineMap (k := ℝ) xStar x t ∈ problem.feasibleSet :=
      lineMap_mem_feasibleSet_of_mem h_convex hxStar hx ⟨le_of_lt ht0, ht1.le⟩
    have hg_t : g t = 0 := by
      exact (problem.mem_feasibleSet_iff _).1 hline |>.1 i hi
    have hg0 : g 0 = 0 := by
      have hxStarFeasible : xStar ∈ problem.feasibleSet := by
        simpa [problem.feasibleSet_eq_setOf_mem] using hxStar
      simpa [g, Function.comp, AffineMap.lineMap_apply_zero] using
        (problem.mem_feasibleSet_iff _).1 hxStarFeasible |>.1 i hi
    have hslope_zero : t⁻¹ * (g (0 + t) - g 0) = 0 := by
      rw [zero_add, hg_t, hg0]
      ring
    simpa [Set.mem_singleton_iff] using hslope_zero
  simpa using hmem

/-- Helper for Chapter08 Theorem 8.2.18: an active inequality constraint is nonnegative on the
whole feasible segment and vanishes at `xStar`, so its linearized pairing is nonnegative. -/
lemma linearizedConstraintPairing_nonneg_of_activeIneq_of_feasible
    {problem : ConstrainedOptimizationProblem n m E I} {xStar x : Point}
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_convex : problem.IsConvexProgramming) (hxStar : xStar ∈ problem) (hx : x ∈ problem)
    {i : Fin m} (hi : i ∈ problem.ineqIndices) (hactive : problem.constraint i xStar = 0) :
    0 ≤ problem.linearizedConstraintPairing xStar (x - xStar) i := by
  let g : ℝ → ℝ := problem.constraint i ∘ (AffineMap.lineMap (k := ℝ) xStar x : ℝ → Point)
  have hderiv_g :
      HasDerivAt g (problem.linearizedConstraintPairing xStar (x - xStar) i) 0 :=
    hasDerivAt_constraint_lineMap h_constraints i
  have hlt_one : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
    (eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds
  have hmem :
      problem.linearizedConstraintPairing xStar (x - xStar) i ∈ Set.Ici 0 := by
    refine isClosed_Ici.mem_of_tendsto hderiv_g.tendsto_slope_zero_right ?_
    filter_upwards [self_mem_nhdsWithin, hlt_one] with t ht0 ht1
    have hline :
        AffineMap.lineMap (k := ℝ) xStar x t ∈ problem.feasibleSet :=
      lineMap_mem_feasibleSet_of_mem h_convex hxStar hx ⟨le_of_lt ht0, ht1.le⟩
    have hg_t_nonneg : 0 ≤ g t := by
      exact (problem.mem_feasibleSet_iff _).1 hline |>.2 i hi
    have hg0 : g 0 = 0 := by
      simpa [g, Function.comp, AffineMap.lineMap_apply_zero] using hactive
    have hslope_nonneg : 0 ≤ t⁻¹ * (g (0 + t) - g 0) := by
      rw [zero_add, hg0]
      exact mul_nonneg (inv_nonneg.mpr ht0.le) (by simpa using hg_t_nonneg)
    simpa [Set.mem_Ici, g, Function.comp] using hslope_nonneg
  simpa using hmem

/-- Helper for Chapter08 Theorem 8.2.18: KKT stationarity rewrites the objective directional
derivative as the multiplier-weighted sum of linearized constraint pairings. -/
lemma stationarity_pairing_eq_weighted_constraint_sum
    {problem : ConstrainedOptimizationProblem n m E I} {xStar d : Point}
    {lamStar : Fin m → ℝ} (h_kkt : problem.IsKKTPoint xStar lamStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar) :
    fderiv ℝ problem.objective xStar d =
      ∑ i : Fin m, lamStar i * problem.linearizedConstraintPairing xStar d i := by
  have hgrad_obj :
      gradient problem.euclideanObjective (WithLp.toLp 2 xStar) =
        ∑ i : Fin m, lamStar i •
          gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) := by
    -- Expand KKT stationarity through the Chapter 8 gradient identity.
    have hstationary := h_kkt.stationarity
    rw [problem.gradient_euclideanLagrangian_eq_objective_sub_sum
      xStar lamStar h_objective h_constraints, sub_eq_zero] at hstationary
    exact hstationary
  have hinner_sum :
      inner ℝ (WithLp.toLp 2 d)
          (∑ i : Fin m, lamStar i •
            gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar)) =
        ∑ i : Fin m, lamStar i * problem.linearizedConstraintPairing xStar d i := by
    rw [inner_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [real_inner_smul_right,
      problem.linearizedConstraintPairing_eq_inner_euclideanConstraintGradient xStar d i]
  calc
    fderiv ℝ problem.objective xStar d
        = fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) := by
            symm
            exact problem.euclideanObjective_fderiv_eq xStar d
    _ = inner ℝ (WithLp.toLp 2 d)
          (gradient problem.euclideanObjective (WithLp.toLp 2 xStar)) := by
            simpa using
              (inner_gradient_right (𝕜 := ℝ) (f := problem.euclideanObjective)
                (x := WithLp.toLp 2 d) (y := WithLp.toLp 2 xStar)).symm
    _ = inner ℝ (WithLp.toLp 2 d)
          (∑ i : Fin m, lamStar i •
            gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar)) := by
            rw [hgrad_obj]
    _ = ∑ i : Fin m, lamStar i * problem.linearizedConstraintPairing xStar d i := hinner_sum

/-- Helper for Chapter08 Theorem 8.2.18: the multiplier-weighted sum of linearized constraint
pairings is nonnegative for every feasible comparison point. -/
lemma weighted_constraint_pairing_nonneg_of_feasible
    {problem : ConstrainedOptimizationProblem n m E I} {xStar x : Point}
    {lamStar : Fin m → ℝ} (h_kkt : problem.IsKKTPoint xStar lamStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_convex : problem.IsConvexProgramming) (hx : x ∈ problem) :
    0 ≤ ∑ i : Fin m, lamStar i * problem.linearizedConstraintPairing xStar (x - xStar) i := by
  classical
  -- Split the finite sum into equality, active-inequality, and inactive-inequality cases.
  refine Finset.sum_nonneg fun i hi ↦ ?_
  by_cases hiEq : i ∈ problem.eqIndices
  · rw [linearizedConstraintPairing_eq_zero_of_eqIndex_of_feasible
      h_constraints h_convex h_kkt.feasible hx hiEq]
    simp
  · have hiUnion : i ∈ problem.eqIndices ∪ problem.ineqIndices := by
      simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
        using (show i ∈ E ∪ I from by
          rw [problem.eqIndices_union_ineqIndices]
          exact Set.mem_univ i)
    have hiIneq : i ∈ problem.ineqIndices := hiUnion.elim (fun hi' ↦ False.elim (hiEq hi')) id
    by_cases hactive : problem.constraint i xStar = 0
    · exact mul_nonneg (h_kkt.dualFeasible i hiIneq)
        (linearizedConstraintPairing_nonneg_of_activeIneq_of_feasible
          h_constraints h_convex h_kkt.feasible hx hiIneq hactive)
    · have hlam_zero : lamStar i = 0 := by
        exact (mul_eq_zero.mp (h_kkt.complementarySlackness i hiIneq)).resolve_right hactive
      simp [hlam_zero]

/-- Companion core statement for Chapter08 Theorem 8.2.18: under the Chapter 8 differentiability
setup, if `problem` is a convex programming problem and `(xStar, lamStar)` is a KKT pair for
`problem`, then `xStar` minimizes `problem.objective` on `problem.feasibleSet`. -/
theorem IsKKTPoint.isMinOn_of_isConvexProgramming
    {problem : ConstrainedOptimizationProblem n m E I} {xStar : Point} {lamStar : Fin m → ℝ}
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_convex : problem.IsConvexProgramming) :
    IsMinOn problem.objective problem.feasibleSet xStar := by
  -- Compare `xStar` with an arbitrary feasible point by the textbook convex-support and KKT
  -- sign argument along the feasible segment from `xStar` to that point.
  rw [isMinOn_iff]
  intro x hx
  have hsupport :
      fderiv ℝ problem.objective xStar (x - xStar) ≤
        problem.objective x - problem.objective xStar :=
    objective_fderiv_le_sub_of_isConvexProgramming
      h_objective h_convex h_kkt.feasible hx
  have hstationary :
      fderiv ℝ problem.objective xStar (x - xStar) =
        ∑ i : Fin m, lamStar i * problem.linearizedConstraintPairing xStar (x - xStar) i :=
    stationarity_pairing_eq_weighted_constraint_sum h_kkt h_objective h_constraints
  have hweighted :
      0 ≤ ∑ i : Fin m, lamStar i * problem.linearizedConstraintPairing xStar (x - xStar) i :=
    weighted_constraint_pairing_nonneg_of_feasible h_kkt h_constraints h_convex hx
  linarith

/-- Under the hypotheses of Theorem 8.2.18, the objective value at `xStar` is bounded above by
the objective value at every feasible point of `problem`. -/
theorem IsKKTPoint.objective_le_of_isConvexProgramming
    {problem : ConstrainedOptimizationProblem n m E I} {xStar x : Point}
    {lamStar : Fin m → ℝ} (h_kkt : problem.IsKKTPoint xStar lamStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_convex : problem.IsConvexProgramming)
    (hx : x ∈ problem) :
    problem.objective xStar ≤ problem.objective x :=
  (isMinOn_iff.mp <|
      h_kkt.isMinOn_of_isConvexProgramming h_objective h_constraints h_convex) x hx

/-- Chapter08 Theorem 8.2.18: under the Chapter 8 differentiability setup, if `problem` is a
convex programming problem and `(xStar, lamStar)` is a KKT pair for `problem`, then `xStar` is a
global minimizer of `problem` on its feasible set. -/
theorem IsKKTPoint.isGlobalMinimizer_of_isConvexProgramming
    {problem : ConstrainedOptimizationProblem n m E I} {xStar : Point} {lamStar : Fin m → ℝ}
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_convex : problem.IsConvexProgramming) :
    problem.IsGlobalMinimizer xStar :=
  ⟨h_kkt.feasible, h_kkt.isMinOn_of_isConvexProgramming h_objective h_constraints h_convex⟩

end ConstrainedOptimizationProblem

end Chapter08Theorem8218
