/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_3

noncomputable section

/- Chapter08 Lemma 8.2.4 (1): exact recall of the existing source-facing theorem
`feasibleDirections_subset_tangentConeAt`. -/
#check feasibleDirections_subset_tangentConeAt

section Chapter08Lemma824

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

open ConstrainedOptimizationProblem

/-- Helper for Chapter08 Lemma 8.2.4: a source feasible direction yields the constant sequential
feasible-direction witnesses required for membership in the canonical positive tangent cone. -/
theorem IsFeasibleDirectionAt.mem_posTangentConeAt
    {X : Set Point} {xStar d : Point}
    (h : IsFeasibleDirectionAt X xStar d) :
    d ∈ posTangentConeAt X xStar := by
  rcases h.small_segment_mem with ⟨δ, hδ, hsmall_segment_mem⟩
  -- Route correction: follow the textbook constant-sequence proof in the positive tangent cone
  -- owner, rather than packaging the weaker `tangentConeAt ℝ` inclusion.
  refine (mem_posTangentConeAt_iff_exists_seq_pos).2 ?_
  refine ⟨fun _ ↦ d, fun k ↦ δ * (1 / ((k : ℝ) + 1)), ?_, ?_, ?_, ?_⟩
  · -- The source proof uses strictly positive step sizes shrinking to zero.
    intro k
    positivity
  · -- Each scaled point stays on the same feasible ray segment from the source definition.
    intro k
    have hk_inv_le : 1 / ((k : ℝ) + 1) ≤ 1 := by
      have hk_one_le : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast Nat.zero_le k
        linarith
      simpa using
        (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by positivity) hk_one_le)
    have hk_mem : δ * (1 / ((k : ℝ) + 1)) ∈ Set.Icc (0 : ℝ) δ := by
      constructor
      · positivity
      · have hmul_le := mul_le_mul_of_nonneg_left hk_inv_le hδ.le
        simpa using hmul_le
    exact hsmall_segment_mem _ hk_mem
  · -- The direction sequence is constant, so it converges to `d`.
    simp
  · -- The positive step sizes converge to zero by scaling the standard reciprocal sequence.
    simpa [mul_comm] using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ δ) Filter.atTop (nhds δ)).mul
        tendsto_one_div_add_atTop_nhds_zero_nat)

/-- Helper for Chapter08 Lemma 8.2.4: every feasible direction is a sequential feasible direction
in the chapter's `posTangentConeAt` owner language. -/
theorem feasibleDirections_subset_posTangentConeAt
    (xStar : Point) (X : Set Point) :
    feasibleDirections xStar X ⊆ posTangentConeAt X xStar := by
  -- Rewrite set membership to the source predicate, then apply the constant-sequence bridge.
  intro d hd
  exact ((mem_feasibleDirections_iff xStar d X).1 hd).mem_posTangentConeAt

/-- Chapter08 Lemma 8.2.4 (2): if every active constraint function of `problem` is differentiable
at `xStar`, then every sequential feasible direction of `problem.feasibleSet` at `xStar` is a
linearized feasible direction at `xStar`. This is the source-facing bridge from the canonical
positive tangent cone `posTangentConeAt problem.feasibleSet xStar` to the chapter owner
`problem.linearizedFeasibleDirectionSet xStar`. -/
theorem sequentialFeasibleDirections_subset_linearizedFeasibleDirectionSet
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_constraints : problem.HasActiveConstraintGradientsAt xStar) :
    posTangentConeAt problem.feasibleSet xStar ⊆
      problem.linearizedFeasibleDirectionSet xStar := by
  intro d hd
  have hd_real : d ∈ tangentConeAt ℝ problem.feasibleSet xStar :=
    tangentConeAt_mono_field hd
  change problem.IsLinearizedFeasibleDirectionAt xStar d
  refine
    { feasiblePoint := hxStar
      hasActiveConstraintGradientsAt := h_constraints
      eq_pairing_eq_zero := ?_
      activeIneq_pairing_nonneg := ?_ }
  · intro i hi_eq
    have hi_active :
        i ∈ problem.activeConstraintIndexSet xStar :=
      (problem.mem_activeConstraintIndexSet_iff xStar i).2 (Or.inl hi_eq)
    have hx_eq : problem.constraint i xStar = 0 :=
      (problem.mem_iff xStar).1 hxStar |>.1 i hi_eq
    have hzero_eq :
        Set.EqOn (problem.constraint i) (fun _ : Point ↦ (0 : ℝ)) problem.feasibleSet := by
      intro x hx
      exact (problem.mem_iff x).1 hx |>.1 i hi_eq
    have hzero_within :
        HasFDerivWithinAt (problem.constraint i) (0 : Point →L[ℝ] ℝ)
          problem.feasibleSet xStar :=
      (hasFDerivWithinAt_const (0 : ℝ) xStar problem.feasibleSet).congr hzero_eq hx_eq
    have hi_diff : DifferentiableAt ℝ (problem.constraint i) xStar :=
      h_constraints i hi_active
    have hderiv_zero :
        fderiv ℝ (problem.constraint i) xStar d = 0 := by
      have hzero_eval :
          (0 : Point →L[ℝ] ℝ) d =
            (fderiv ℝ (problem.constraint i) xStar : Point →L[ℝ] ℝ) d :=
        hzero_within.unique_on (hi_diff.hasFDerivAt.hasFDerivWithinAt) hd_real
      simpa using hzero_eval.symm
    simpa [problem.linearizedConstraintPairing_eq xStar d i] using hderiv_zero
  · intro i hi_active
    have hi_active' := (problem.mem_activeIneqIndexSet_iff xStar i).1 hi_active
    have hi_constraint :
        i ∈ problem.activeConstraintIndexSet xStar :=
      (problem.mem_activeConstraintIndexSet_iff xStar i).2 (Or.inr hi_active')
    have hi_ineq : i ∈ problem.ineqIndices := hi_active'.1
    have hi_zero : problem.constraint i xStar = 0 := hi_active'.2
    have hle :
        (fun _ : Point ↦ (0 : ℝ)) ≤ᶠ[nhdsWithin xStar problem.feasibleSet]
          problem.constraint i := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (problem.mem_iff x).1 hx |>.2 i hi_ineq
    have hconst : IsLocalMinOn (fun _ : Point ↦ (0 : ℝ)) problem.feasibleSet xStar :=
      isLocalMinOn_const
    have hlocalMin : IsLocalMinOn (problem.constraint i) problem.feasibleSet xStar :=
      hle.isLocalMinOn hi_zero.symm hconst
    have hnonneg_within :
        0 ≤ fderivWithin ℝ (problem.constraint i) problem.feasibleSet xStar d :=
      hlocalMin.fderivWithin_nonneg hd
    have hi_diff : DifferentiableAt ℝ (problem.constraint i) xStar :=
      h_constraints i hi_constraint
    have hderiv_eq :
        fderiv ℝ (problem.constraint i) xStar d =
          fderivWithin ℝ (problem.constraint i) problem.feasibleSet xStar d :=
      by
        simpa using
          (hi_diff.hasFDerivAt.hasFDerivWithinAt).unique_on
            (hi_diff.differentiableWithinAt.hasFDerivWithinAt) hd_real
    rw [problem.linearizedConstraintPairing_eq xStar d i, hderiv_eq]
    exact hnonneg_within

/-- Helper for Chapter08 Lemma 8.2.4: differentiability of every constraint upgrades the existing
active-constraint bridge from sequential feasible directions to linearized feasible directions. -/
theorem hasConstraintGradients_subset_linearizedFeasibleDirectionSet
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_constraints : problem.HasConstraintGradientsAt xStar) :
    posTangentConeAt problem.feasibleSet xStar ⊆
      problem.linearizedFeasibleDirectionSet xStar := by
  -- Convert the textbook hypothesis to the active-constraint differentiability owner used above.
  exact sequentialFeasibleDirections_subset_linearizedFeasibleDirectionSet
    problem xStar hxStar h_constraints.hasActiveConstraintGradientsAt

/-- Chapter08 Lemma 8.2.4: if all constraint functions of `problem` are differentiable at
`xStar`, then feasible directions are sequential feasible directions and sequential feasible
directions are linearized feasible directions. -/
theorem feasibleDirections_subset_sequentialFeasibleDirections_subset_linearizedFeasibleDirectionSet
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_constraints : problem.HasConstraintGradientsAt xStar) :
    feasibleDirections xStar problem.feasibleSet ⊆ posTangentConeAt problem.feasibleSet xStar ∧
      posTangentConeAt problem.feasibleSet xStar ⊆
        problem.linearizedFeasibleDirectionSet xStar := by
  constructor
  · -- The source feasible-ray definition already gives the textbook sequential witnesses.
    exact feasibleDirections_subset_posTangentConeAt xStar problem.feasibleSet
  · -- The second inclusion is the chapter's existing linearization bridge.
    exact hasConstraintGradients_subset_linearizedFeasibleDirectionSet
      problem xStar hxStar h_constraints

end Chapter08Lemma824
