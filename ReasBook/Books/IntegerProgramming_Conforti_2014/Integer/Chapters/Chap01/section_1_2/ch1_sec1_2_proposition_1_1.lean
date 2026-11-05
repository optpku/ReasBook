/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_definition_1_7.Optimality

public section

open scoped IntegerVectorNotation MixedIntegerNotation

section Proposition11

variable {m n p : ℕ}

/-- Companion to Proposition 1.1 (1). Every MILP-feasible point has objective value at most the
objective value attained by an LP-relaxation-optimal point. -/
theorem objectiveValue_le_of_mem_feasibleSet_of_isLpRelaxationOptimalSolution
    (P : MixedIntegerLinearProgram m n p)
    {xy xy0 : MixedRealPoint n p}
    (hxy_feasible : xy ∈ P.feasibleSet)
    (h_lp_opt : P.isLpRelaxationOptimalSolution xy0) :
    P.objectiveValue xy ≤ P.objectiveValue xy0 := by
  exact h_lp_opt.objectiveIsGreatest.2
    ⟨xy, P.feasibleSet_subset_lpRelaxation hxy_feasible, rfl⟩

/-- Proposition 1.1 (1) [Relation between MILP and its LP relaxation]. For a mixed-integer linear
program `P`, the optimal MILP value does not exceed the optimal LP-relaxation value. -/
theorem milpValue_le_lpRelaxationValue
    (P : MixedIntegerLinearProgram m n p)
    {zStar z0 : ℝ}
    (h_milp_opt : IsGreatest P.objectiveValues zStar)
    (h_lp_opt : IsGreatest P.lpRelaxationObjectiveValues z0) :
    zStar ≤ z0 := by
  rcases h_milp_opt.1 with ⟨xy, hxy_feasible, rfl⟩
  exact h_lp_opt.2 ⟨xy, P.feasibleSet_subset_lpRelaxation hxy_feasible, rfl⟩

/-- Helper for Proposition 1.1: an LP-relaxation-feasible point with integral `x`-coordinates is
MILP-feasible. -/
lemma mem_feasibleSet_of_mem_lpRelaxation_of_integral
    (P : MixedIntegerLinearProgram m n p)
    (x0 : Fin n → ℝ)
    (y0 : Fin p → ℝ)
    (h_lp_feasible : (x0, y0) ∈ P.lpRelaxation)
    (hx0_integral : x0 ∈ ℤ^n) :
    (x0, y0) ∈ P.feasibleSet := by
  -- Unpack the LP-relaxation constraints so the only new ingredient is integrality of `x0`.
  rcases (P.mem_lpRelaxation_iff (x0, y0)).mp h_lp_feasible with
    ⟨hineq, hx0_nonneg, hy0_nonneg⟩
  -- Convert the integral `x`-block into mixed-lattice membership for `(x0, y0)`.
  have h_mixed_integer : (x0, y0) ∈ (ℤ^n×ℝ^p) := by
    exact (mem_mixed_integer_lattice_iff).2 hx0_integral
  -- Repackage the LP constraints together with lattice membership into MILP feasibility.
  exact (P.mem_feasibleSet_iff_mem_mixed_integer_lattice (x0, y0)).2
    ⟨hineq, hx0_nonneg, hy0_nonneg, h_mixed_integer⟩

/-- Helper for Proposition 1.1: LP-relaxation optimality on a point already known to be
MILP-feasible transports to greatestness on `P.objectiveValues`. -/
lemma objectiveIsGreatest_of_mem_feasibleSet_of_isLpRelaxationOptimalSolution
    (P : MixedIntegerLinearProgram m n p)
    {xy0 : MixedRealPoint n p}
    (hxy0_feasible : xy0 ∈ P.feasibleSet)
    (h_lp_opt : P.isLpRelaxationOptimalSolution xy0) :
    IsGreatest P.objectiveValues (P.objectiveValue xy0) := by
  refine ⟨?_, ?_⟩
  · -- Record that the candidate objective value is attained on the smaller MILP feasible set.
    exact ⟨xy0, hxy0_feasible, rfl⟩
  · -- Compare against any MILP-feasible objective value by viewing its witness in the LP relaxation.
    rintro z ⟨xy, hxy_feasible, rfl⟩
    exact h_lp_opt.objectiveIsGreatest.2
      ⟨xy, P.feasibleSet_subset_lpRelaxation hxy_feasible, rfl⟩

/-- Proposition 1.1 (2) companion. If `(x0, y0)` is LP-relaxation-optimal for `P`, and
`x0 ∈ ℤ^n`, then `(x0, y0)` is MILP-feasible for `P`. -/
theorem milpFeasible_of_integralLpOpt
    (P : MixedIntegerLinearProgram m n p)
    (x0 : Fin n → ℝ)
    (y0 : Fin p → ℝ)
    (h_lp_opt : P.isLpRelaxationOptimalSolution (x0, y0))
    (hx0_integral : x0 ∈ ℤ^n) :
    (x0, y0) ∈ P.feasibleSet := by
  -- Route correction: prove LP-to-MILP feasibility directly, then package optimality separately.
  exact mem_feasibleSet_of_mem_lpRelaxation_of_integral
    P x0 y0 h_lp_opt.mem_lpRelaxation hx0_integral

/-- Proposition 1.1 (2) [Relation between MILP and its LP relaxation]. If `(x0, y0)` is
LP-relaxation-optimal for `P`, and `x0 ∈ ℤ^n`, then `(x0, y0)` is MILP-optimal for `P`. -/
theorem milpOptimal_of_integralLpOpt
    (P : MixedIntegerLinearProgram m n p)
    (x0 : Fin n → ℝ)
    (y0 : Fin p → ℝ)
    (h_lp_opt : P.isLpRelaxationOptimalSolution (x0, y0))
    (hx0_integral : x0 ∈ ℤ^n) :
    P.isOptimalSolution (x0, y0) := by
  -- First transport LP feasibility to MILP feasibility using the integrality hypothesis.
  have h_milp_feasible : (x0, y0) ∈ P.feasibleSet :=
    milpFeasible_of_integralLpOpt P x0 y0 h_lp_opt hx0_integral
  -- Then transport greatestness from the LP-relaxation objective set to the MILP objective set.
  exact ⟨h_milp_feasible,
    objectiveIsGreatest_of_mem_feasibleSet_of_isLpRelaxationOptimalSolution
      P h_milp_feasible h_lp_opt⟩

/-- Proposition 1.1 (2) [Relation between MILP and its LP relaxation]. If `(x0, y0)` is
LP-relaxation-optimal for `P`, and `x0 ∈ ℤ^n`, then `(x0, y0)` is MILP-feasible and the optimal
MILP value agrees with the LP-relaxation objective value attained there. -/
theorem milpFeasible_and_milpValue_eq_of_integralLpOpt
    (P : MixedIntegerLinearProgram m n p)
    (x0 : Fin n → ℝ)
    (y0 : Fin p → ℝ)
    {zStar : ℝ}
    (h_milp_opt : IsGreatest P.objectiveValues zStar)
    (h_lp_opt : P.isLpRelaxationOptimalSolution (x0, y0))
    (hx0_integral : x0 ∈ ℤ^n) :
    (x0, y0) ∈ P.feasibleSet ∧
      zStar = P.objectiveValue (x0, y0) := by
  -- Reuse the direct feasibility bridge instead of re-extracting it from packaged optimality.
  have h_milp_feasible : (x0, y0) ∈ P.feasibleSet :=
    milpFeasible_of_integralLpOpt P x0 y0 h_lp_opt hx0_integral
  -- Transport LP-relaxation greatestness to the MILP objective-value set at the same point.
  have h_integral_greatest : IsGreatest P.objectiveValues (P.objectiveValue (x0, y0)) :=
    objectiveIsGreatest_of_mem_feasibleSet_of_isLpRelaxationOptimalSolution
      P h_milp_feasible h_lp_opt
  -- Compare the two greatest objective values by membership in the common MILP objective set.
  have hzStar_le : zStar ≤ P.objectiveValue (x0, y0) :=
    h_integral_greatest.2 h_milp_opt.1
  have hz0_mem : P.objectiveValue (x0, y0) ∈ P.objectiveValues :=
    ⟨(x0, y0), h_milp_feasible, rfl⟩
  have hz0_le : P.objectiveValue (x0, y0) ≤ zStar :=
    h_milp_opt.2 hz0_mem
  exact ⟨h_milp_feasible, le_antisymm hzStar_le hz0_le⟩

/-- Proposition 1.1 (2) companion. Under the same hypotheses, the MILP optimum agrees with the
LP-relaxation objective value attained at `(x0, y0)`. -/
theorem milpValue_eq_lpRelaxationValue_of_integralLpOpt
    (P : MixedIntegerLinearProgram m n p)
    (x0 : Fin n → ℝ)
    (y0 : Fin p → ℝ)
    {zStar : ℝ}
    (h_milp_opt : IsGreatest P.objectiveValues zStar)
    (h_lp_opt : P.isLpRelaxationOptimalSolution (x0, y0))
    (hx0_integral : x0 ∈ ℤ^n) :
    zStar = P.objectiveValue (x0, y0) :=
  (milpFeasible_and_milpValue_eq_of_integralLpOpt
    P x0 y0 h_milp_opt h_lp_opt hx0_integral).2

end Proposition11

end
