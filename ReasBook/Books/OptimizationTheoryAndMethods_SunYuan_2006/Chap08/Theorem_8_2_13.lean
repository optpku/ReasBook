/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Assumption_8_2_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7

noncomputable section

open scoped BigOperators

section Chapter08Theorem8213

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin n)

-- Domain-style sampling:
-- * source-facing theorem: KKT-multiplier existence under the Chapter 8 regularity condition
--   `(8.2.42)`, which is weaker than the full constraint qualification from Theorem 8.2.7
-- * reused Chapter 8 owners:
--   `problem.regularityAssumptionAt` from `Assumption_8_2_extra_4`
--   `problem.HasConstraintGradientsAt` from `Definition_8_2_2`
--   `problem.IsKKTPoint` from `Theorem_8_2_7`
-- * companion API added here:
--   `problem.linearizedDescentDirections_eq_empty_of_regularityAssumptionAt`
--   isolates the source-semantic consequence of the weaker regularity assumption before the KKT
--   packaging step
-- * owner choice: this file is theorem-only, so it should reuse the chapter owners rather than
--   rebuilding a second constrained-problem/KKT API

namespace ConstrainedOptimizationProblem

/-- Helper for Chapter08 Theorem 8.2.13: a feasible local minimizer admits no positive tangent
direction whose Euclidean transport is a strict descent direction of the transported objective.
-/
theorem tangent_descent_preimage_eq_empty_of_isLocalMinOn
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar) :
    posTangentConeAt problem.feasibleSet xStar ∩
        ((WithLp.toLp 2) ⁻¹'
          descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) =
      (∅ : Set Point) := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro d hd
  -- Local minimality forces the feasible directional derivative to be nonnegative on the
  -- positive tangent cone.
  have hnonneg_within :
      0 ≤ fderivWithin ℝ problem.objective problem.feasibleSet xStar d :=
    h_localMin.fderivWithin_nonneg hd.1
  have hd_real : d ∈ tangentConeAt ℝ problem.feasibleSet xStar :=
    tangentConeAt_mono_field hd.1
  have hderiv_eq :
      fderiv ℝ problem.objective xStar d =
        fderivWithin ℝ problem.objective problem.feasibleSet xStar d := by
    simpa using
      (h_objective.hasFDerivAt.hasFDerivWithinAt).unique_on
        (h_objective.differentiableWithinAt.hasFDerivWithinAt) hd_real
  have hnonneg :
      0 ≤ fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) := by
    have hnonneg_objective : 0 ≤ fderiv ℝ problem.objective xStar d := by
      rw [hderiv_eq]
      exact hnonneg_within
    simpa [problem.euclideanObjective_fderiv_eq xStar d] using hnonneg_objective
  -- A descent direction makes the same directional derivative strictly negative.
  have hdesc :
      fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) < 0 := by
    calc
      fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) (WithLp.toLp 2 d)
          = inner ℝ (WithLp.toLp 2 d)
              (gradient problem.euclideanObjective (WithLp.toLp 2 xStar)) := by
                exact
                  (inner_gradient_right (𝕜 := ℝ) (f := problem.euclideanObjective)
                    (x := WithLp.toLp 2 d) (y := WithLp.toLp 2 xStar)).symm
      _ < 0 := (mem_descentDirections_iff problem.euclideanObjective (WithLp.toLp 2 xStar)
        (WithLp.toLp 2 d)).1 hd.2
  exact not_lt_of_ge hnonneg hdesc

/-- Under a constrained local minimum and the Chapter 8 regularity assumption `(8.2.42)`, the
linearized feasible directions at `xStar` that are descent directions of the Euclidean objective
transport form the empty set. This is the source-semantic intermediate consequence used before
packaging the conclusion as a KKT multiplier statement. -/
theorem linearizedDescentDirections_eq_empty_of_regularityAssumptionAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_regularity : problem.regularityAssumptionAt xStar) :
    problem.linearizedFeasibleDirectionSet xStar ∩
        ((WithLp.toLp 2) ⁻¹'
          descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) =
      (∅ : Set Point) := by
  -- First exclude descent directions on the tangent cone by the local-minimum argument.
  have h_no_tangent :
      posTangentConeAt problem.feasibleSet xStar ∩
          ((WithLp.toLp 2) ⁻¹'
            descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) =
        (∅ : Set Point) :=
    problem.tangent_descent_preimage_eq_empty_of_isLocalMinOn xStar h_localMin h_objective
  -- Then use the regularity assumption `(8.2.42)` to replace the tangent-descent set by the
  -- linearized-descent set.
  rw [← h_regularity]
  exact h_no_tangent

/-- Helper for Chapter08 Theorem 8.2.13: emptiness of the linearized descent set translates into
the Euclidean gradient-system emptiness required by the Farkas multiplier lemma. -/
theorem euclidean_linearized_descent_system_eq_empty_of_linearizedDescentDirections_eq_empty
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_empty_linearized :
      problem.linearizedFeasibleDirectionSet xStar ∩
          ((WithLp.toLp 2) ⁻¹'
            descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) =
        (∅ : Set Point)) :
    descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar) ∩
        {u |
          (∀ i ∈ problem.eqIndices,
            inner ℝ u (gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar)) = 0) ∧
          ∀ i ∈ problem.activeIneqIndexSet xStar,
            0 ≤ inner ℝ u (gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar))} =
      (∅ : Set EPoint) := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro u hu
  let d : Point := u.ofLp
  have hu_toLp : WithLp.toLp 2 d = u := by
    rfl
  have hd_linearized : d ∈ problem.linearizedFeasibleDirectionSet xStar := by
    -- Rewrite the Euclidean gradient side conditions back into the source linearized-feasibility
    -- conditions for the transported direction `d`.
    rw [problem.mem_linearizedFeasibleDirectionSet_iff_explicit]
    refine ⟨hxStar, h_constraints.hasActiveConstraintGradientsAt, ?_, ?_⟩
    · intro i hi
      rw [problem.linearizedConstraintPairing_eq_inner_euclideanConstraintGradient xStar d i,
        hu_toLp]
      exact hu.2.1 i hi
    · intro i hi
      rw [problem.linearizedConstraintPairing_eq_inner_euclideanConstraintGradient xStar d i,
        hu_toLp]
      exact hu.2.2 i hi
  have hd_preimage :
      d ∈ ((WithLp.toLp 2) ⁻¹'
        descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) := by
    change WithLp.toLp 2 d ∈ descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)
    simpa [d] using hu.1
  -- The transported direction would lie in the forbidden linearized-descent intersection.
  have hd_empty : d ∈ (∅ : Set Point) := by
    rw [← h_empty_linearized]
    exact ⟨hd_linearized, hd_preimage⟩
  simp at hd_empty

end ConstrainedOptimizationProblem

/-- Chapter08 Theorem 8.2.13: under the standing differentiability setup of the Chapter 8 KKT
theorem, if `xStar` is a feasible local minimizer of `problem` and the regularity assumption
`problem.regularityAssumptionAt xStar` from `(8.2.42)` holds, then there exists a multiplier
vector `lamStar` such that `(xStar, lamStar)` satisfies the KKT conditions for `problem`. -/
theorem exists_isKKTPoint_of_isLocalMinOn_of_regularityAssumptionAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_regularity : problem.regularityAssumptionAt xStar) :
    ∃ lamStar : Fin m → ℝ, problem.IsKKTPoint xStar lamStar := by
  classical
  let xStarE : EPoint := WithLp.toLp 2 xStar
  let gradC : Fin m → EPoint := fun i ↦ gradient (problem.euclideanConstraint i) xStarE
  have h_no_linearized_descent :
      problem.linearizedFeasibleDirectionSet xStar ∩
        ((WithLp.toLp 2) ⁻¹'
            descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) =
        (∅ : Set Point) :=
    problem.linearizedDescentDirections_eq_empty_of_regularityAssumptionAt
      xStar h_localMin h_objective h_regularity
  have hobjectiveE : DifferentiableAt ℝ problem.euclideanObjective xStarE := by
    -- The objective differentiability hypothesis transports to the Euclidean model.
    exact (problem.differentiableAt_euclideanObjective_iff xStar).2 h_objective
  have hdisjEqActive :
      Disjoint problem.eqIndices (problem.activeIneqIndexSet xStar) := by
    rw [Set.disjoint_left]
    intro i hi_eq hi_active
    exact
      Set.disjoint_left.mp
          (by
            simpa
              [ConstrainedOptimizationProblem.eqIndices,
                ConstrainedOptimizationProblem.ineqIndices]
              using problem.eqIndices_disjoint_ineqIndices)
          hi_eq ((problem.mem_activeIneqIndexSet_iff xStar i).1 hi_active).1
  have hdisjEqIneq :
      Disjoint problem.eqIndices problem.ineqIndices := by
    simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
      using problem.eqIndices_disjoint_ineqIndices
  have hEmpty :
      descentDirections problem.euclideanObjective xStarE ∩
          {u |
            (∀ i ∈ problem.eqIndices, inner ℝ u (gradC i) = 0) ∧
              ∀ i ∈ problem.activeIneqIndexSet xStar, 0 ≤ inner ℝ u (gradC i)} =
        (∅ : Set EPoint) := by
    -- Translate the source linearized-descent emptiness into the Euclidean system used by the
    -- Farkas multiplier lemma.
    simpa [xStarE, gradC] using
      problem.euclidean_linearized_descent_system_eq_empty_of_linearizedDescentDirections_eq_empty
        xStar hxStar h_constraints h_no_linearized_descent
  obtain ⟨lam, hlam_nonneg, hgrad_repr⟩ :=
    (descentDirections_inter_constraintGradientSystem_eq_empty_iff_exists_multiplier
      (X := EPoint) (ι := Fin m)
      problem.eqIndices (problem.activeIneqIndexSet xStar) hdisjEqActive
      problem.euclideanObjective xStarE (gradient problem.euclideanObjective xStarE) gradC
      hobjectiveE.hasGradientAt).1 hEmpty
  let lamStar : Fin m → ℝ :=
    fun i ↦ if i ∈ problem.activeConstraintIndexSet xStar then lam i else 0
  have hgrad_repr_full :
      gradient problem.euclideanObjective xStarE = ∑ i : Fin m, lamStar i • gradC i := by
    -- Move the subtype-indexed Farkas representation to the full active-constraint owner and
    -- then zero-extend it over `Fin m`.
    let _ : Fintype ↑problem.eqIndices := Fintype.ofFinite ↑problem.eqIndices
    let _ : Fintype ↑(problem.activeIneqIndexSet xStar) :=
      Fintype.ofFinite ↑(problem.activeIneqIndexSet xStar)
    have heq_sum :
        (∑ i : problem.eqIndices, lam i • gradC i) =
          Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.eqIndices)
            (fun i ↦ lam i • gradC i) := by
      calc
        (∑ i : problem.eqIndices, lam i • gradC i)
            = Finset.sum
                ((Finset.univ : Finset problem.eqIndices).map
                  (Function.Embedding.subtype (fun i : Fin m => i ∈ problem.eqIndices)))
                (fun i ↦ lam i • gradC i) := by
                  simp [Finset.sum_map]
        _ = Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.eqIndices)
              (fun i ↦ lam i • gradC i) := by
                rw [Finset.univ_map_subtype]
    have hactive_sum :
        (∑ i : problem.activeIneqIndexSet xStar, lam i • gradC i) =
          Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.activeIneqIndexSet xStar)
            (fun i ↦ lam i • gradC i) := by
      calc
        (∑ i : problem.activeIneqIndexSet xStar, lam i • gradC i)
            = Finset.sum
                ((Finset.univ : Finset (problem.activeIneqIndexSet xStar)).map
                  (Function.Embedding.subtype
                    (fun i : Fin m => i ∈ problem.activeIneqIndexSet xStar)))
                (fun i ↦ lam i • gradC i) := by
                  simp [Finset.sum_map]
        _ = Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.activeIneqIndexSet xStar)
              (fun i ↦ lam i • gradC i) := by
                rw [Finset.univ_map_subtype]
    have hzero_extend :
        ∑ i : Fin m, (if i ∈ problem.activeConstraintIndexSet xStar then lam i else 0) • gradC i =
          (∑ i : Fin m, if i ∈ problem.eqIndices then lam i • gradC i else 0) +
            ∑ i : Fin m,
              if i ∈ problem.activeIneqIndexSet xStar then lam i • gradC i else 0 :=
      ConstrainedOptimizationProblem.zero_extended_active_constraint_multiplier_sum_eq_eq_add_active
        (problem := problem) (xStar := xStar) (lam := lam) (V := EPoint) gradC
    calc
      gradient problem.euclideanObjective xStarE
          = (∑ i : problem.eqIndices, lam i • gradC i) +
              ∑ i : problem.activeIneqIndexSet xStar, lam i • gradC i := hgrad_repr
      _ = Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.eqIndices)
            (fun i ↦ lam i • gradC i) +
          Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.activeIneqIndexSet xStar)
            (fun i ↦ lam i • gradC i) := by
            rw [heq_sum, hactive_sum]
      _ = (∑ i : Fin m, if i ∈ problem.eqIndices then lam i • gradC i else 0) +
            ∑ i : Fin m,
              if i ∈ problem.activeIneqIndexSet xStar then lam i • gradC i else 0 := by
            simp [Finset.sum_filter]
      _ = ∑ i : Fin m, lamStar i • gradC i := by
            symm
            simpa [lamStar] using hzero_extend
  have hnot_activeConstraint_of_not_activeIneq :
      ∀ ⦃i : Fin m⦄, i ∈ problem.ineqIndices →
        i ∉ problem.activeIneqIndexSet xStar →
          i ∉ problem.activeConstraintIndexSet xStar := by
    intro i hi_ineq hi_not_active hi_constraint
    rw [problem.activeConstraintIndexSet_def] at hi_constraint
    rcases hi_constraint with hi_eq | hi_active
    · exact Set.disjoint_left.mp hdisjEqIneq hi_eq hi_ineq
    · exact hi_not_active hi_active
  refine ⟨lamStar, ?_⟩
  refine
    { feasible := hxStar
      dualFeasible := ?_
      stationarity := ?_
      complementarySlackness := ?_ }
  · intro i hi_ineq
    by_cases hi_active : i ∈ problem.activeIneqIndexSet xStar
    · have hi_constraint : i ∈ problem.activeConstraintIndexSet xStar := by
        rw [problem.activeConstraintIndexSet_def]
        exact Or.inr hi_active
      -- Active inequalities inherit the Farkas nonnegativity directly.
      simpa [lamStar, hi_constraint] using hlam_nonneg i hi_active
    · have hi_not_constraint :
          i ∉ problem.activeConstraintIndexSet xStar :=
        hnot_activeConstraint_of_not_activeIneq hi_ineq hi_active
      -- Inactive inequalities get multiplier `0` after zero-extension.
      simp [lamStar, hi_not_constraint]
  · -- The Euclidean Lagrangian gradient vanishes because the multiplier sum matches the objective
    -- gradient returned by the Farkas lemma.
    rw [problem.gradient_euclideanLagrangian_eq_objective_sub_sum xStar lamStar
      h_objective h_constraints]
    rw [hgrad_repr_full]
    simp [gradC, xStarE]
  · intro i hi_ineq
    by_cases hi_active : i ∈ problem.activeIneqIndexSet xStar
    · have hi_constraint : i ∈ problem.activeConstraintIndexSet xStar := by
        rw [problem.activeConstraintIndexSet_def]
        exact Or.inr hi_active
      have hi_zero : problem.constraint i xStar = 0 :=
        (problem.mem_activeIneqIndexSet_iff xStar i).1 hi_active |>.2
      -- Active inequalities vanish at the feasible point, so complementary slackness is
      -- immediate.
      simp [lamStar, hi_constraint, hi_zero]
    · have hi_not_constraint :
          i ∉ problem.activeConstraintIndexSet xStar :=
        hnot_activeConstraint_of_not_activeIneq hi_ineq hi_active
      -- Inactive inequalities again carry multiplier `0`.
      simp [lamStar, hi_not_constraint]

end Chapter08Theorem8213
