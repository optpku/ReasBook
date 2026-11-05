/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_exercise_9_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix
open scoped SplitHullNotation

-- Domain-style sampling for this refine pass:
-- * primary domain: split disjunctions and split-cut LP bounds over polyhedral relaxations
-- * sampled owner abstractions:
--   - Chapter 3 `primal_objective_values`
--   - Chapter 9 `linear_objective_values`
--   - Chapter 9 `linear_objective_lp_value`
--   - Chapter 9 `coordinate_branch_lp_value`
--   - Chapter 5 `split_branch_lower`
--   - Chapter 5 `split_branch_upper`
--   - Chapter 5 split-hull notation `P^(π, π₀)` and `split_strip`
--   - Chapter 5 `is_valid_inequality`
--   - Chapter 9 `IsNodeOptimalPoint`
-- * best owner abstraction:
--   - the project style takes the set of attained objective values as primitive, with
--     `linear_objective_value` as the real-valued source-facing optimum surface and
--     `linear_objective_lp_value` available when infeasibility must be recorded explicitly
-- * source/core/bridge triage:
--   - the exercise gap statements and named values `z⁻`, `z⁺`, `ẑ`, `z*` remain source-facing,
--     paired with explicit optimal-point witnesses when finite LP optima are required
--   - split branches, split-hull notation, split-strip membership, `is_valid_inequality`, and the
--     imported generic linear-objective-value owner form the core/canonical layer
--   - the exercise-specific value names are thin bridge/view aliases to that owner
-- * primitive data: `P`, `c`, `(π, π0)`, `xBar`, and `(α, β)`
-- * derived API: optimal values on branches/cuts and the gap configuration predicate

section Exercise917

variable {p : ℕ}

/-- The source-facing value `z⁻` attached to `(LP⁻)`, expressed on the real-valued
`linear_objective_value` surface. Later statements pair this with an optimal-point witness when
they need `z⁻` to be a genuine attained LP optimum. -/
noncomputable abbrev exercise_9_17_lp_minus_value
    (P : Set (Fin p → ℝ))
    (c : Fin p → ℝ)
    (π : Fin p → ℤ)
    (π0 : ℤ) : ℝ :=
  linear_objective_value (split_branch_lower P π π0) c

/-- The source-facing value `z⁺` attached to `(LP⁺)`, again on the real-valued
`linear_objective_value` surface and intended to be used together with an optimal-point witness
when an attained optimum is required. -/
noncomputable abbrev exercise_9_17_lp_plus_value
    (P : Set (Fin p → ℝ))
    (c : Fin p → ℝ)
    (π : Fin p → ℤ)
    (π0 : ℤ) : ℝ :=
  linear_objective_value (split_branch_upper P π π0) c

/-- A split cut from the chosen disjunction is a valid inequality for the split hull that cuts off
the current LP optimum `xBar`. -/
def exercise_9_17_is_split_cut_from_disjunction
    (P : Set (Fin p → ℝ))
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xBar : Fin p → ℝ)
    (α : Fin p → ℝ)
    (β : ℝ) : Prop :=
  is_valid_inequality (P^(π, π0)) α β ∧
    β < α ⬝ᵥ xBar

/-- `exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β` unfolds to the conjunction that
`α x ≤ β` is valid for the split hull `P^(π, π₀)` and cuts off `xBar`. -/
theorem exercise_9_17_is_split_cut_from_disjunction_iff
    (P : Set (Fin p → ℝ))
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xBar : Fin p → ℝ)
    (α : Fin p → ℝ)
    (β : ℝ) :
    exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β ↔
      is_valid_inequality (P^(π, π0)) α β ∧
        β < α ⬝ᵥ xBar :=
  Iff.rfl

/-- A split cut from the chosen disjunction is valid on the split hull `P^(π, π₀)`. -/
theorem exercise_9_17_is_split_cut_from_disjunction.valid
    {P : Set (Fin p → ℝ)}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    {xBar : Fin p → ℝ}
    {α : Fin p → ℝ}
    {β : ℝ}
    (hcut : exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β) :
    is_valid_inequality (P^(π, π0)) α β :=
  hcut.1

/-- A split cut from the chosen disjunction strictly cuts off the current LP optimum `xBar`. -/
theorem exercise_9_17_is_split_cut_from_disjunction.cuts_off
    {P : Set (Fin p → ℝ)}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    {xBar : Fin p → ℝ}
    {α : Fin p → ℝ}
    {β : ℝ}
    (hcut : exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β) :
    β < α ⬝ᵥ xBar :=
  hcut.2

/-- A split cut from the chosen disjunction excludes `xBar` from the split hull `P^(π, π₀)`. -/
theorem exercise_9_17_is_split_cut_from_disjunction.not_mem_split_hull
    {P : Set (Fin p → ℝ)}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    {xBar : Fin p → ℝ}
    {α : Fin p → ℝ}
    {β : ℝ}
    (hcut : exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β) :
    xBar ∉ P^(π, π0) := by
  intro hxBar
  rcases hcut with ⟨hvalid, hlt⟩
  rw [is_valid_inequality_iff] at hvalid
  exact not_le_of_gt hlt (hvalid hxBar)

/-- The source-facing value `ẑ` obtained by adding the split cut `α x ≤ β` to the LP relaxation
`P`, expressed on the real-valued `linear_objective_value` surface. -/
noncomputable abbrev exercise_9_17_split_cut_value
    (P : Set (Fin p → ℝ))
    (c : Fin p → ℝ)
    (α : Fin p → ℝ)
    (β : ℝ) : ℝ :=
  linear_objective_value (P ∩ {x : Fin p → ℝ | α ⬝ᵥ x ≤ β}) c

/-- The value `z*` obtained by adding all split inequalities from the chosen disjunction, that is,
the real-valued objective value over `P^(π, π₀)`. -/
noncomputable abbrev exercise_9_17_all_split_inequalities_value
    (P : Set (Fin p → ℝ))
    (c : Fin p → ℝ)
    (π : Fin p → ℤ)
    (π0 : ℤ) : ℝ :=
  linear_objective_value (P^(π, π0)) c

/-- A gap configuration consists of a polyhedral LP relaxation with an optimal solution crossing
the chosen split disjunction, together with a split cut from that disjunction. -/
def exercise_9_17_gap_configuration
    (P : Set (Fin p → ℝ))
    (c xBar : Fin p → ℝ)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (α : Fin p → ℝ)
    (β : ℝ) : Prop :=
  is_polyhedron P ∧
    IsNodeOptimalPoint P c xBar ∧
      xBar ∈ split_strip π π0 ∧
        exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β

/-- `exercise_9_17_gap_configuration` records polyhedrality of `P`, optimality of `xBar` for the
LP objective, membership of `xBar` in the split strip, and the chosen split cut. -/
theorem exercise_9_17_gap_configuration_iff
    (P : Set (Fin p → ℝ))
    (c xBar : Fin p → ℝ)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (α : Fin p → ℝ)
    (β : ℝ) :
    exercise_9_17_gap_configuration P c xBar π π0 α β ↔
      is_polyhedron P ∧
        IsNodeOptimalPoint P c xBar ∧
          xBar ∈ split_strip π π0 ∧
            exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β :=
  Iff.rfl

/-- In a gap configuration, the LP relaxation `P` is a polyhedron. -/
theorem exercise_9_17_gap_configuration.is_polyhedron
    {P : Set (Fin p → ℝ)}
    {c xBar : Fin p → ℝ}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    {α : Fin p → ℝ}
    {β : ℝ}
    (hgap : exercise_9_17_gap_configuration P c xBar π π0 α β) :
    is_polyhedron P :=
  hgap.1

/-- In a gap configuration, the LP relaxation `P` is convex. -/
theorem exercise_9_17_gap_configuration.convex
    {P : Set (Fin p → ℝ)}
    {c xBar : Fin p → ℝ}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    {α : Fin p → ℝ}
    {β : ℝ}
    (hgap : exercise_9_17_gap_configuration P c xBar π π0 α β) :
    Convex ℝ P :=
  convex_of_is_polyhedron hgap.is_polyhedron

/-- In a gap configuration, `xBar` is an optimal solution of the LP relaxation over `P`. -/
theorem exercise_9_17_gap_configuration.isNodeOptimalPoint
    {P : Set (Fin p → ℝ)}
    {c xBar : Fin p → ℝ}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    {α : Fin p → ℝ}
    {β : ℝ}
    (hgap : exercise_9_17_gap_configuration P c xBar π π0 α β) :
    IsNodeOptimalPoint P c xBar :=
  hgap.2.1

/-- In a gap configuration, `xBar` lies in the chosen split strip. -/
theorem exercise_9_17_gap_configuration.mem_split_strip
    {P : Set (Fin p → ℝ)}
    {c xBar : Fin p → ℝ}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    {α : Fin p → ℝ}
    {β : ℝ}
    (hgap : exercise_9_17_gap_configuration P c xBar π π0 α β) :
    xBar ∈ split_strip π π0 :=
  hgap.2.2.1

/-- In a gap configuration, `α x ≤ β` is a split cut from the chosen disjunction. -/
theorem exercise_9_17_gap_configuration.is_split_cut_from_disjunction
    {P : Set (Fin p → ℝ)}
    {c xBar : Fin p → ℝ}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    {α : Fin p → ℝ}
    {β : ℝ}
    (hgap : exercise_9_17_gap_configuration P c xBar π π0 α β) :
    exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β :=
  hgap.2.2.2

/-- In a gap configuration, the LP optimum `xBar` is excluded from the split hull `P^(π, π₀)`. -/
theorem exercise_9_17_gap_configuration.not_mem_split_hull
    {P : Set (Fin p → ℝ)}
    {c xBar : Fin p → ℝ}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    {α : Fin p → ℝ}
    {β : ℝ}
    (hgap : exercise_9_17_gap_configuration P c xBar π π0 α β) :
    xBar ∉ P^(π, π0) :=
  hgap.is_split_cut_from_disjunction.not_mem_split_hull

/-- Helper for Exercise 9.17: an attained node optimum rewrites the source-facing
`linear_objective_value` to the witness objective value. -/
lemma linearObjectiveValue_eq_of_isNodeOptimalPoint
    {P : Set (Fin p → ℝ)}
    {c x : Fin p → ℝ}
    (hx : IsNodeOptimalPoint P c x) :
    linear_objective_value P c = c ⬝ᵥ x := by
  -- The optimal witness gives a greatest attained objective value.
  have hgreatest : IsGreatest (linear_objective_values P c) (c ⬝ᵥ x) := by
    constructor
    · exact ⟨x, hx.mem, rfl⟩
    · intro y hy
      rcases hy with ⟨z, hzP, rfl⟩
      exact hx.objective_le hzP
  simpa [linear_objective_value] using hgreatest.csSup_eq

/-- Helper for Exercise 9.17: an inequality that is valid on both split branches is valid on the
split hull. -/
lemma splitHullValidInequality_of_branch_valid
    {P : Set (Fin p → ℝ)}
    {α : Fin p → ℝ}
    {β : ℝ}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    (hLower : is_valid_inequality (split_branch_lower P π π0) α β)
    (hUpper : is_valid_inequality (split_branch_upper P π π0) α β) :
    is_valid_inequality (P^(π, π0)) α β := by
  have hvalidUnion :
      is_valid_inequality
        (split_branch_lower P π π0 ∪ split_branch_upper P π π0)
        α β := by
    -- Check the two sides of the disjunction separately on the branch union.
    rw [is_valid_inequality_iff]
    intro x hx
    rcases hx with hx | hx
    · exact hLower hx
    · exact hUpper hx
  -- Transport branch-union validity across the `convexHull` owner of `P^(π, π₀)`.
  simpa [split_hull] using
    (is_valid_inequality_convexHull_iff
      (S := split_branch_lower P π π0 ∪ split_branch_upper P π π0)
      (α := α) (β := β)).2 hvalidUnion

/-- Helper for Exercise 9.17: every point of `P^(π, π₀)` has objective value at most the better
of the two branch optima. -/
lemma splitHullObjective_le_maxBranchObjectives
    {P : Set (Fin p → ℝ)}
    {c x xMinus xPlus : Fin p → ℝ}
    {π : Fin p → ℤ}
    {π0 : ℤ}
    (hMinusOpt : IsNodeOptimalPoint (split_branch_lower P π π0) c xMinus)
    (hPlusOpt : IsNodeOptimalPoint (split_branch_upper P π π0) c xPlus)
    (hx : x ∈ P^(π, π0)) :
    c ⬝ᵥ x ≤ max (c ⬝ᵥ xMinus) (c ⬝ᵥ xPlus) := by
  have hLower :
      is_valid_inequality
        (split_branch_lower P π π0)
        c
        (max (c ⬝ᵥ xMinus) (c ⬝ᵥ xPlus)) := by
    -- The lower branch optimum bounds every lower-branch objective value.
    rw [is_valid_inequality_iff]
    intro y hy
    exact le_trans (hMinusOpt.objective_le hy) (le_max_left _ _)
  have hUpper :
      is_valid_inequality
        (split_branch_upper P π π0)
        c
        (max (c ⬝ᵥ xMinus) (c ⬝ᵥ xPlus)) := by
    -- The upper branch optimum gives the symmetric bound on the upper branch.
    rw [is_valid_inequality_iff]
    intro y hy
    exact le_trans (hPlusOpt.objective_le hy) (le_max_right _ _)
  -- Route correction: transport the branchwise bound through the split-hull owner
  -- instead of unfolding `convexHull` directly inside the main theorem.
  exact splitHullValidInequality_of_branch_valid hLower hUpper hx

/-- Helper for Exercise 9.17: the objective vector `![0, 1]` reads off the second coordinate. -/
lemma objectiveSecondCoordinate_eq
    (x : Fin 2 → ℝ) :
    (![(0 : ℝ), 1] : Fin 2 → ℝ) ⬝ᵥ x = x 1 := by
  norm_num [dotProduct]

/-- Helper for Exercise 9.17: the split vector `![1, 0]` reads off the first coordinate. -/
lemma splitDotFirstCoordinate_eq
    (x : Fin 2 → ℝ) :
    split_dot (![(1 : ℤ), 0] : Fin 2 → ℤ) x = x 0 := by
  norm_num [split_dot, dotProduct]

/-- Helper for Exercise 9.17: the explicit left-gap polyhedron whose lower split branch collapses
to the origin while the split cut keeps the point `![1, T]`. -/
def leftGapExamplePolyhedron
    (T : ℝ) : Set (Fin 2 → ℝ) :=
  polyhedron_le_set
    !![(-1 : ℝ), 0;
      1, 0;
      0, -1;
      0, 1;
      -(2 * (T + 1)), 1;
      2, 1]
    ![(0 : ℝ), 1, 0, T + 1, 0, T + 2]

/-- Helper for Exercise 9.17: membership in the left-gap polyhedron is equivalent to the intended
scalar system of inequalities. -/
lemma memLeftGapExamplePolyhedron_iff
    (T : ℝ)
    (x : Fin 2 → ℝ) :
    x ∈ leftGapExamplePolyhedron T ↔
      0 ≤ x 0 ∧
        x 0 ≤ 1 ∧
        0 ≤ x 1 ∧
        x 1 ≤ T + 1 ∧
        x 1 ≤ 2 * (T + 1) * x 0 ∧
        x 1 ≤ T + 2 - 2 * x 0 := by
  rw [leftGapExamplePolyhedron, mem_polyhedron_le_set_iff]
  constructor
  · intro hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    have h3 := hx 3
    have h4 := hx 4
    have h5 := hx 5
    -- Rewrite the six matrix rows into the source-facing scalar inequalities.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hrow : -x 0 ≤ 0 := by
        simpa [Matrix.mulVec, dotProduct] using h0
      linarith
    · simpa [Matrix.mulVec, dotProduct] using h1
    · have hrow : -x 1 ≤ 0 := by
        simpa [Matrix.mulVec, dotProduct] using h2
      linarith
    · simpa [Matrix.mulVec, dotProduct] using h3
    · have hrow : -(2 * (T + 1)) * x 0 + x 1 ≤ 0 := by
        simpa [Matrix.mulVec, dotProduct] using h4
      linarith
    · have hrow : 2 * x 0 + x 1 ≤ T + 2 := by
        simpa [Matrix.mulVec, dotProduct] using h5
      linarith
  · rintro ⟨hx0_nonneg, hx0_le_one, hx1_nonneg, hx1_le_top, hx1_le_diag, hx1_le_side⟩
    -- Reassemble the matrix system from the normalized scalar inequalities.
    intro i
    fin_cases i
    · have hrow : -x 0 ≤ 0 := by
        linarith
      simpa [Matrix.mulVec, dotProduct] using hrow
    · simpa [Matrix.mulVec, dotProduct] using hx0_le_one
    · have hrow : -x 1 ≤ 0 := by
        linarith
      simpa [Matrix.mulVec, dotProduct] using hrow
    · simpa [Matrix.mulVec, dotProduct] using hx1_le_top
    · have hrow : -(2 * (T + 1)) * x 0 + x 1 ≤ 0 := by
        linarith
      simpa [Matrix.mulVec, dotProduct] using hrow
    · have hrow : 2 * x 0 + x 1 ≤ T + 2 := by
        linarith
      simpa [Matrix.mulVec, dotProduct] using hrow

/-- Helper for Exercise 9.17: the lower split branch of the left-gap example is the singleton
`![0, 0]`. -/
lemma leftGapLowerBranchCollapse
    {T : ℝ}
    {x : Fin 2 → ℝ}
    (hx : x ∈ split_branch_lower (leftGapExamplePolyhedron T) ![(1 : ℤ), 0] 0) :
    x = ![(0 : ℝ), 0] := by
  rcases (mem_split_branch_lower_iff).1 hx with ⟨hxP, hxLower⟩
  rcases (memLeftGapExamplePolyhedron_iff T x).1 hxP with
    ⟨hx0_nonneg, -, hx1_nonneg, -, hx1_le_diag, -⟩
  have hx0_le_zero : x 0 ≤ 0 := by
    simpa [splitDotFirstCoordinate_eq] using hxLower
  have hx0_eq : x 0 = 0 := by
    linarith
  have hx1_le_zero : x 1 ≤ 0 := by
    simpa [hx0_eq] using hx1_le_diag
  have hx1_eq : x 1 = 0 := by
    linarith
  -- Collapse the branch point coordinatewise.
  funext i
  fin_cases i
  · simp [hx0_eq]
  · simp [hx1_eq]

/-- Helper for Exercise 9.17: the explicit right-gap polyhedron whose upper split branch collapses
to `![1, 0]` while the mirrored split cut keeps the point `![0, T]`. -/
def rightGapExamplePolyhedron
    (T : ℝ) : Set (Fin 2 → ℝ) :=
  polyhedron_le_set
    !![(-1 : ℝ), 0;
      1, 0;
      0, -1;
      0, 1;
      -2, 1;
      2 * (T + 1), 1]
    ![(0 : ℝ), 1, 0, T + 1, T, 2 * (T + 1)]

/-- Helper for Exercise 9.17: membership in the right-gap polyhedron is equivalent to the
mirrored scalar system of inequalities. -/
lemma memRightGapExamplePolyhedron_iff
    (T : ℝ)
    (x : Fin 2 → ℝ) :
    x ∈ rightGapExamplePolyhedron T ↔
      0 ≤ x 0 ∧
        x 0 ≤ 1 ∧
        0 ≤ x 1 ∧
        x 1 ≤ T + 1 ∧
        x 1 ≤ T + 2 * x 0 ∧
        x 1 ≤ 2 * (T + 1) * (1 - x 0) := by
  rw [rightGapExamplePolyhedron, mem_polyhedron_le_set_iff]
  constructor
  · intro hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    have h3 := hx 3
    have h4 := hx 4
    have h5 := hx 5
    -- Rewrite the six matrix rows into the mirrored scalar inequalities.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hrow : -x 0 ≤ 0 := by
        simpa [Matrix.mulVec, dotProduct] using h0
      linarith
    · simpa [Matrix.mulVec, dotProduct] using h1
    · have hrow : -x 1 ≤ 0 := by
        simpa [Matrix.mulVec, dotProduct] using h2
      linarith
    · simpa [Matrix.mulVec, dotProduct] using h3
    · have hrow : -2 * x 0 + x 1 ≤ T := by
        simpa [Matrix.mulVec, dotProduct] using h4
      linarith
    · have hrow : 2 * (T + 1) * x 0 + x 1 ≤ 2 * (T + 1) := by
        simpa [Matrix.mulVec, dotProduct] using h5
      linarith
  · rintro ⟨hx0_nonneg, hx0_le_one, hx1_nonneg, hx1_le_top, hx1_le_diag, hx1_le_side⟩
    -- Reassemble the matrix system from the normalized scalar inequalities.
    intro i
    fin_cases i
    · have hrow : -x 0 ≤ 0 := by
        linarith
      simpa [Matrix.mulVec, dotProduct] using hrow
    · simpa [Matrix.mulVec, dotProduct] using hx0_le_one
    · have hrow : -x 1 ≤ 0 := by
        linarith
      simpa [Matrix.mulVec, dotProduct] using hrow
    · simpa [Matrix.mulVec, dotProduct] using hx1_le_top
    · have hrow : -2 * x 0 + x 1 ≤ T := by
        linarith
      simpa [Matrix.mulVec, dotProduct] using hrow
    · have hrow : 2 * (T + 1) * x 0 + x 1 ≤ 2 * (T + 1) := by
        linarith
      simpa [Matrix.mulVec, dotProduct] using hrow

/-- Helper for Exercise 9.17: the upper split branch of the right-gap example is the singleton
`![1, 0]`. -/
lemma rightGapUpperBranchCollapse
    {T : ℝ}
    {x : Fin 2 → ℝ}
    (hx : x ∈ split_branch_upper (rightGapExamplePolyhedron T) ![(1 : ℤ), 0] 0) :
    x = ![(1 : ℝ), 0] := by
  rcases (mem_split_branch_upper_iff).1 hx with ⟨hxP, hxUpper⟩
  rcases (memRightGapExamplePolyhedron_iff T x).1 hxP with
    ⟨-, hx0_le_one, hx1_nonneg, -, -, hx1_le_side⟩
  have hx0_ge_one : 1 ≤ x 0 := by
    simpa [splitDotFirstCoordinate_eq] using hxUpper
  have hx0_eq : x 0 = 1 := by
    linarith
  have hx1_le_zero : x 1 ≤ 0 := by
    simpa [hx0_eq] using hx1_le_side
  have hx1_eq : x 1 = 0 := by
    linarith
  -- Collapse the branch point coordinatewise.
  funext i
  fin_cases i
  · simp [hx0_eq]
  · simp [hx1_eq]

/-- Exercise 9.17 (3). Let `P` be a polyhedral LP relaxation with optimal solution `xBar`, and let
`(π, π₀)` be an integer split disjunction chosen so that `xBar` lies in the corresponding split
strip. Assume `(LP⁻)`, `(LP⁺)`, and the split-hull relaxation obtained by adding all split
inequalities from that disjunction each admit an optimal solution. Then the corresponding optimum
value `z*` equals `max(z⁻, z⁺)`. -/
theorem exercise_9_17_all_split_inequalities_value_eq_max_branch_value
    (P : Set (Fin p → ℝ))
    (c xBar : Fin p → ℝ)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (hP : is_polyhedron P)
    (hBarOpt : IsNodeOptimalPoint P c xBar)
    (hxBarStrip : xBar ∈ split_strip π π0)
    (h_minus_opt :
      ∃ xMinus : Fin p → ℝ, IsNodeOptimalPoint (split_branch_lower P π π0) c xMinus)
    (h_plus_opt :
      ∃ xPlus : Fin p → ℝ, IsNodeOptimalPoint (split_branch_upper P π π0) c xPlus)
    (h_star_opt :
      ∃ xStar : Fin p → ℝ, IsNodeOptimalPoint (P^(π, π0)) c xStar) :
    exercise_9_17_all_split_inequalities_value P c π π0 =
      max
        (exercise_9_17_lp_minus_value P c π π0)
        (exercise_9_17_lp_plus_value P c π π0) := by
  let _ := hP
  let _ := hBarOpt
  let _ := hxBarStrip
  obtain ⟨xMinus, hxMinus⟩ := h_minus_opt
  obtain ⟨xPlus, hxPlus⟩ := h_plus_opt
  obtain ⟨xStar, hxStar⟩ := h_star_opt
  have hMinusValue :
      exercise_9_17_lp_minus_value P c π π0 = c ⬝ᵥ xMinus := by
    -- Rewrite the lower-branch value to the chosen optimal witness.
    simpa [exercise_9_17_lp_minus_value] using
      linearObjectiveValue_eq_of_isNodeOptimalPoint hxMinus
  have hPlusValue :
      exercise_9_17_lp_plus_value P c π π0 = c ⬝ᵥ xPlus := by
    -- Rewrite the upper-branch value to the chosen optimal witness.
    simpa [exercise_9_17_lp_plus_value] using
      linearObjectiveValue_eq_of_isNodeOptimalPoint hxPlus
  have hStarValue :
      exercise_9_17_all_split_inequalities_value P c π π0 = c ⬝ᵥ xStar := by
    -- Rewrite the split-hull value to the split-hull optimal witness.
    simpa [exercise_9_17_all_split_inequalities_value] using
      linearObjectiveValue_eq_of_isNodeOptimalPoint hxStar
  have hxMinusHull : xMinus ∈ P^(π, π0) := by
    -- Each branch witness belongs to the convex hull defining the split hull.
    rw [split_hull]
    exact subset_convexHull ℝ
      (split_branch_lower P π π0 ∪ split_branch_upper P π π0)
      (Or.inl hxMinus.mem)
  have hxPlusHull : xPlus ∈ P^(π, π0) := by
    -- The upper-branch witness enters the same convex hull through the right summand.
    rw [split_hull]
    exact subset_convexHull ℝ
      (split_branch_lower P π π0 ∪ split_branch_upper P π π0)
      (Or.inr hxPlus.mem)
  have hStarLe :
      c ⬝ᵥ xStar ≤ max (c ⬝ᵥ xMinus) (c ⬝ᵥ xPlus) := by
    -- The split-hull objective is bounded above by the better branch optimum.
    exact splitHullObjective_le_maxBranchObjectives hxMinus hxPlus hxStar.mem
  have hMinusLeStar : c ⬝ᵥ xMinus ≤ c ⬝ᵥ xStar := by
    -- The split-hull optimum dominates every point already lying in the split hull.
    exact hxStar.objective_le hxMinusHull
  have hPlusLeStar : c ⬝ᵥ xPlus ≤ c ⬝ᵥ xStar := by
    exact hxStar.objective_le hxPlusHull
  calc
    exercise_9_17_all_split_inequalities_value P c π π0 = c ⬝ᵥ xStar := hStarValue
    _ = max (c ⬝ᵥ xMinus) (c ⬝ᵥ xPlus) := by
      apply le_antisymm
      · exact hStarLe
      · exact max_le hMinusLeStar hPlusLeStar
    _ = max
          (exercise_9_17_lp_minus_value P c π π0)
          (exercise_9_17_lp_plus_value P c π π0) := by
      rw [hMinusValue.symm, hPlusValue.symm]

/-- A left-branch gap construction for Exercise 9.17. For every target gap `M`, there exists a
polyhedral LP relaxation `P`
with optimal solution `xBar`, a split disjunction crossed by `xBar`, and a split cut from that
disjunction such that both `(LP⁻)` and the cut LP admit optimal solutions and their optimum values
satisfy `z⁻ + M ≤ ẑ`. -/
theorem exercise_9_17_arbitrarily_large_gap_to_lp_minus
    (M : ℝ) :
    ∃ (p : ℕ)
      (P : Set (Fin p → ℝ))
      (c xBar xMinus xHat : Fin p → ℝ)
      (π : Fin p → ℤ)
      (π0 : ℤ)
      (α : Fin p → ℝ)
      (β : ℝ)
      (_hP : is_polyhedron P)
      (_hBarOpt : IsNodeOptimalPoint P c xBar)
      (_hxBarStrip : xBar ∈ split_strip π π0)
      (_hcut : exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β)
      (_hMinusOpt : IsNodeOptimalPoint (split_branch_lower P π π0) c xMinus)
      (_hHatOpt : IsNodeOptimalPoint (P ∩ {x : Fin p → ℝ | α ⬝ᵥ x ≤ β}) c xHat),
      exercise_9_17_lp_minus_value P c π π0 + M ≤
        exercise_9_17_split_cut_value P c α β := by
  let T : ℝ := |M| + 1
  let P : Set (Fin 2 → ℝ) := leftGapExamplePolyhedron T
  let c : Fin 2 → ℝ := ![(0 : ℝ), 1]
  let xBar : Fin 2 → ℝ := ![((1 : ℝ) / 2), T + 1]
  let xMinus : Fin 2 → ℝ := ![(0 : ℝ), 0]
  let xHat : Fin 2 → ℝ := ![(1 : ℝ), T]
  let π : Fin 2 → ℤ := ![(1 : ℤ), 0]
  let π0 : ℤ := 0
  let α : Fin 2 → ℝ := ![-T, 1]
  let β : ℝ := 0
  have hT_nonneg : 0 ≤ T := by
    -- The gap parameter `T = |M| + 1` is nonnegative.
    dsimp [T]
    nlinarith [abs_nonneg M]
  have hM_le_T : M ≤ T := by
    -- `|M| + 1` dominates the prescribed target gap `M`.
    dsimp [T]
    nlinarith [le_abs_self M]
  have hP : is_polyhedron P := by
    -- The example is presented directly as a matrix polyhedron.
    dsimp [P, leftGapExamplePolyhedron]
    exact
      ⟨6,
        !![(-1 : ℝ), 0;
          1, 0;
          0, -1;
          0, 1;
          -(2 * (T + 1)), 1;
          2, 1],
        ![(0 : ℝ), 1, 0, T + 1, 0, T + 2],
        rfl⟩
  have hxBar_mem : xBar ∈ P := by
    -- Read feasibility of `xBar = ![1/2, T + 1]` from the normalized inequalities.
    dsimp [P, xBar]
    rw [memLeftGapExamplePolyhedron_iff]
    refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
    · have hrow : 0 ≤ T + 1 := by
        linarith
      simpa using hrow
    · simp
    · have hEq : T + 1 = 2 * (T + 1) * ((1 : ℝ) / 2) := by
        ring
      simpa [xBar] using hEq.le
    · have hrow : T + 1 ≤ T + 2 - (1 : ℝ) := by
        linarith
      simpa [xBar] using hrow
  have hBarOpt : IsNodeOptimalPoint P c xBar := by
    constructor
    · exact hxBar_mem
    · intro y hy
      have hyP : y ∈ leftGapExamplePolyhedron T := by
        simpa [P] using hy
      rcases (memLeftGapExamplePolyhedron_iff T y).1 hyP with
        ⟨-, -, -, hy1_le, -, -⟩
      -- The row `y₁ ≤ T + 1` already certifies optimality for the second-coordinate objective.
      calc
        c ⬝ᵥ y = y 1 := by
          simpa [c] using objectiveSecondCoordinate_eq y
        _ ≤ T + 1 := hy1_le
        _ = c ⬝ᵥ xBar := by
          dsimp [c, xBar]
          norm_num [dotProduct]
  have hxBarStrip : xBar ∈ split_strip π π0 := by
    -- The chosen LP optimum lies strictly between the two split hyperplanes.
    dsimp [xBar, π, π0]
    rw [mem_split_strip_iff]
    constructor <;> norm_num [splitDotFirstCoordinate_eq]
  have hxMinus_mem : xMinus ∈ split_branch_lower P π π0 := by
    -- The lower-branch witness is the origin.
    rw [mem_split_branch_lower_iff]
    constructor
    · dsimp [P, xMinus]
      rw [memLeftGapExamplePolyhedron_iff]
      refine ⟨by norm_num, by norm_num, by norm_num, ?_, by norm_num, ?_⟩
      · have hrow : 0 ≤ T + 1 := by
          linarith
        simpa using hrow
      · have hrow : 0 ≤ T + 2 := by
          linarith
        simpa using hrow
    · dsimp [xMinus, π, π0]
      norm_num [splitDotFirstCoordinate_eq]
  have hMinusOpt : IsNodeOptimalPoint (split_branch_lower P π π0) c xMinus := by
    constructor
    · exact hxMinus_mem
    · intro y hy
      have hyCollapse :
          y = xMinus := by
        have hyCollapse' :
            y = ![(0 : ℝ), 0] := by
          simpa [P, π, π0] using
            (leftGapLowerBranchCollapse
              (T := T)
              (x := y)
              (by simpa [P, π, π0] using hy))
        simpa [xMinus] using hyCollapse'
      -- The lower branch is a singleton, so every feasible objective equals the witness value.
      rw [hyCollapse]
  have hcutValidLower :
      is_valid_inequality (split_branch_lower P π π0) α β := by
    rw [is_valid_inequality_iff]
    intro y hy
    have hyCollapse :
        y = ![(0 : ℝ), 0] := by
      simpa [P, π, π0] using
        (leftGapLowerBranchCollapse
          (T := T)
          (x := y)
          (by simpa [P, π, π0] using hy))
    -- On the collapsed lower branch, the cut is tight at the origin.
    rw [hyCollapse]
    dsimp [α, β]
    norm_num [dotProduct]
  have hcutValidUpper :
      is_valid_inequality (split_branch_upper P π π0) α β := by
    rw [is_valid_inequality_iff]
    intro y hy
    rcases (mem_split_branch_upper_iff).1 hy with ⟨hyP, hyUpper⟩
    have hyP' : y ∈ leftGapExamplePolyhedron T := by
      simpa [P] using hyP
    rcases (memLeftGapExamplePolyhedron_iff T y).1 hyP' with
      ⟨-, hy0_le_one, -, -, -, hy1_le_side⟩
    have hy0_ge_one : 1 ≤ y 0 := by
      simpa [π, π0, splitDotFirstCoordinate_eq] using hyUpper
    have hy1_le_T : y 1 ≤ T := by
      linarith
    have hT_le_Tx0 : T ≤ T * y 0 := by
      nlinarith [hT_nonneg, hy0_ge_one]
    have hyCutScalar : -T * y 0 + y 1 ≤ 0 := by
      linarith
    -- The side branch inequality dominates the split cut once `x₀ ≥ 1`.
    simpa [α, β, dotProduct] using hyCutScalar
  have hcutValid : is_valid_inequality (P^(π, π0)) α β := by
    -- Transport the two branchwise validity checks to the split hull.
    exact splitHullValidInequality_of_branch_valid hcutValidLower hcutValidUpper
  have hcutOff : β < α ⬝ᵥ xBar := by
    -- The split cut excludes the fractional LP optimum.
    dsimp [β, α, xBar]
    norm_num [dotProduct]
    nlinarith [hT_nonneg]
  have hcut :
      exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β := by
    exact ⟨hcutValid, hcutOff⟩
  have hxHat_mem : xHat ∈ P ∩ {x : Fin 2 → ℝ | α ⬝ᵥ x ≤ β} := by
    constructor
    · dsimp [P, xHat]
      rw [memLeftGapExamplePolyhedron_iff]
      refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
      · exact hT_nonneg
      · have hrow : T ≤ T + 1 := by
          linarith
        exact hrow
      · norm_num
        nlinarith [hT_nonneg]
      · simp
    · dsimp [xHat, α, β]
      norm_num [dotProduct]
  have hHatOpt : IsNodeOptimalPoint (P ∩ {x : Fin 2 → ℝ | α ⬝ᵥ x ≤ β}) c xHat := by
    constructor
    · exact hxHat_mem
    · intro y hy
      rcases hy with ⟨hyP, hyCut⟩
      have hyP' : y ∈ leftGapExamplePolyhedron T := by
        simpa [P] using hyP
      rcases (memLeftGapExamplePolyhedron_iff T y).1 hyP' with
        ⟨-, hy0_le_one, -, -, -, -⟩
      have hyCutScalar : -T * y 0 + y 1 ≤ 0 := by
        simpa [α, β, dotProduct] using hyCut
      have hTy_le_T : T * y 0 ≤ T := by
        nlinarith [hT_nonneg, hy0_le_one]
      have hy1_le_T : y 1 ≤ T := by
        linarith
      -- The cut bounds the objective by `T`, attained at `xHat = ![1, T]`.
      calc
        c ⬝ᵥ y = y 1 := by
          simpa [c] using objectiveSecondCoordinate_eq y
        _ ≤ T := hy1_le_T
        _ = c ⬝ᵥ xHat := by
          dsimp [c, xHat]
          norm_num [dotProduct]
  have hMinusValue :
      exercise_9_17_lp_minus_value P c π π0 = c ⬝ᵥ xMinus := by
    -- Rewrite `z⁻` through the chosen lower-branch optimal witness.
    simpa [exercise_9_17_lp_minus_value] using
      linearObjectiveValue_eq_of_isNodeOptimalPoint hMinusOpt
  have hHatValue :
      exercise_9_17_split_cut_value P c α β = c ⬝ᵥ xHat := by
    -- Rewrite the cut-LP value through the chosen cut-feasible optimum.
    simpa [exercise_9_17_split_cut_value] using
      linearObjectiveValue_eq_of_isNodeOptimalPoint hHatOpt
  refine
    ⟨2, P, c, xBar, xMinus, xHat, π, π0, α, β, hP, hBarOpt, hxBarStrip, hcut,
      hMinusOpt, hHatOpt, ?_⟩
  -- The constructed witnesses realize a gap of at least `M`.
  calc
    exercise_9_17_lp_minus_value P c π π0 + M = c ⬝ᵥ xMinus + M := by
      rw [hMinusValue]
    _ = M := by
      dsimp [c, xMinus]
      norm_num [dotProduct]
    _ ≤ T := hM_le_T
    _ = c ⬝ᵥ xHat := by
      dsimp [c, xHat]
      norm_num [dotProduct]
    _ = exercise_9_17_split_cut_value P c α β := by
      rw [hHatValue.symm]

/-- A right-branch gap construction for Exercise 9.17. For every target gap `M`, there exists a
polyhedral LP relaxation `P`
with optimal solution `xBar`, a split disjunction crossed by `xBar`, and a split cut from that
disjunction such that both `(LP⁺)` and the cut LP admit optimal solutions and their optimum values
satisfy `z⁺ + M ≤ ẑ`. -/
theorem exercise_9_17_arbitrarily_large_gap_to_lp_plus
    (M : ℝ) :
    ∃ (p : ℕ)
      (P : Set (Fin p → ℝ))
      (c xBar xPlus xHat : Fin p → ℝ)
      (π : Fin p → ℤ)
      (π0 : ℤ)
      (α : Fin p → ℝ)
      (β : ℝ)
      (_hP : is_polyhedron P)
      (_hBarOpt : IsNodeOptimalPoint P c xBar)
      (_hxBarStrip : xBar ∈ split_strip π π0)
      (_hcut : exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β)
      (_hPlusOpt : IsNodeOptimalPoint (split_branch_upper P π π0) c xPlus)
      (_hHatOpt : IsNodeOptimalPoint (P ∩ {x : Fin p → ℝ | α ⬝ᵥ x ≤ β}) c xHat),
      exercise_9_17_lp_plus_value P c π π0 + M ≤
        exercise_9_17_split_cut_value P c α β := by
  let T : ℝ := |M| + 1
  let P : Set (Fin 2 → ℝ) := rightGapExamplePolyhedron T
  let c : Fin 2 → ℝ := ![(0 : ℝ), 1]
  let xBar : Fin 2 → ℝ := ![((1 : ℝ) / 2), T + 1]
  let xPlus : Fin 2 → ℝ := ![(1 : ℝ), 0]
  let xHat : Fin 2 → ℝ := ![(0 : ℝ), T]
  let π : Fin 2 → ℤ := ![(1 : ℤ), 0]
  let π0 : ℤ := 0
  let α : Fin 2 → ℝ := ![T, 1]
  let β : ℝ := T
  have hT_nonneg : 0 ≤ T := by
    -- The mirrored gap parameter is again `|M| + 1`.
    dsimp [T]
    nlinarith [abs_nonneg M]
  have hM_le_T : M ≤ T := by
    -- The chosen `T` still dominates the prescribed target gap.
    dsimp [T]
    nlinarith [le_abs_self M]
  have hP : is_polyhedron P := by
    -- The mirrored example is also presented as a matrix polyhedron.
    dsimp [P, rightGapExamplePolyhedron]
    exact
      ⟨6,
        !![(-1 : ℝ), 0;
          1, 0;
          0, -1;
          0, 1;
          -2, 1;
          2 * (T + 1), 1],
        ![(0 : ℝ), 1, 0, T + 1, T, 2 * (T + 1)],
        rfl⟩
  have hxBar_mem : xBar ∈ P := by
    -- Read feasibility of `xBar = ![1/2, T + 1]` from the mirrored inequalities.
    dsimp [P, xBar]
    rw [memRightGapExamplePolyhedron_iff]
    refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
    · have hrow : 0 ≤ T + 1 := by
        linarith
      simpa using hrow
    · simp
    · norm_num
    · norm_num
      nlinarith
  have hBarOpt : IsNodeOptimalPoint P c xBar := by
    constructor
    · exact hxBar_mem
    · intro y hy
      have hyP : y ∈ rightGapExamplePolyhedron T := by
        simpa [P] using hy
      rcases (memRightGapExamplePolyhedron_iff T y).1 hyP with
        ⟨-, -, -, hy1_le, -, -⟩
      -- The row `y₁ ≤ T + 1` gives the same parent optimum as in the left example.
      calc
        c ⬝ᵥ y = y 1 := by
          simpa [c] using objectiveSecondCoordinate_eq y
        _ ≤ T + 1 := hy1_le
        _ = c ⬝ᵥ xBar := by
          dsimp [c, xBar]
          norm_num [dotProduct]
  have hxBarStrip : xBar ∈ split_strip π π0 := by
    -- The mirrored parent optimum uses the same disjunction and split-strip point.
    dsimp [xBar, π, π0]
    rw [mem_split_strip_iff]
    constructor <;> norm_num [splitDotFirstCoordinate_eq]
  have hxPlus_mem : xPlus ∈ split_branch_upper P π π0 := by
    -- The upper-branch witness is the corner point `![1, 0]`.
    rw [mem_split_branch_upper_iff]
    constructor
    · dsimp [P, xPlus]
      rw [memRightGapExamplePolyhedron_iff]
      refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
      · have hrow : 0 ≤ T + 1 := by
          linarith
        simpa using hrow
      · have hrow : 0 ≤ T + 2 := by
          linarith
        simpa using hrow
      · simp
    · dsimp [xPlus, π, π0]
      norm_num [splitDotFirstCoordinate_eq]
  have hPlusOpt : IsNodeOptimalPoint (split_branch_upper P π π0) c xPlus := by
    constructor
    · exact hxPlus_mem
    · intro y hy
      have hyCollapse :
          y = xPlus := by
        have hyCollapse' :
            y = ![(1 : ℝ), 0] := by
          simpa [P, π, π0] using
            (rightGapUpperBranchCollapse
              (T := T)
              (x := y)
              (by simpa [P, π, π0] using hy))
        simpa [xPlus] using hyCollapse'
      -- The upper branch is a singleton, so every feasible objective equals the witness value.
      rw [hyCollapse]
  have hcutValidLower :
      is_valid_inequality (split_branch_lower P π π0) α β := by
    rw [is_valid_inequality_iff]
    intro y hy
    rcases (mem_split_branch_lower_iff).1 hy with ⟨hyP, hyLower⟩
    have hyP' : y ∈ rightGapExamplePolyhedron T := by
      simpa [P] using hyP
    rcases (memRightGapExamplePolyhedron_iff T y).1 hyP' with
      ⟨hy0_nonneg, -, -, -, hy1_le_diag, -⟩
    have hy0_le_zero : y 0 ≤ 0 := by
      simpa [π, π0, splitDotFirstCoordinate_eq] using hyLower
    have hy0_eq : y 0 = 0 := by
      linarith
    have hy1_le_T : y 1 ≤ T := by
      nlinarith [hy1_le_diag, hy0_eq]
    have hyCutScalar : T * y 0 + y 1 ≤ T := by
      nlinarith [hy1_le_T, hy0_eq]
    -- On the lower branch, `x₀ = 0`, so the mirrored cut reduces to `y₁ ≤ T`.
    simpa [α, β, dotProduct] using hyCutScalar
  have hcutValidUpper :
      is_valid_inequality (split_branch_upper P π π0) α β := by
    rw [is_valid_inequality_iff]
    intro y hy
    have hyCollapse :
        y = ![(1 : ℝ), 0] := by
      simpa [P, π, π0] using
        (rightGapUpperBranchCollapse
          (T := T)
          (x := y)
          (by simpa [P, π, π0] using hy))
    -- On the collapsed upper branch, the mirrored cut is tight at `![1, 0]`.
    rw [hyCollapse]
    dsimp [α, β]
    norm_num [dotProduct]
  have hcutValid : is_valid_inequality (P^(π, π0)) α β := by
    -- Transport the two branchwise validity checks to the split hull.
    exact splitHullValidInequality_of_branch_valid hcutValidLower hcutValidUpper
  have hcutOff : β < α ⬝ᵥ xBar := by
    -- The mirrored split cut also excludes the fractional LP optimum.
    dsimp [β, α, xBar]
    norm_num [dotProduct]
    nlinarith [hT_nonneg]
  have hcut :
      exercise_9_17_is_split_cut_from_disjunction P π π0 xBar α β := by
    exact ⟨hcutValid, hcutOff⟩
  have hxHat_mem : xHat ∈ P ∩ {x : Fin 2 → ℝ | α ⬝ᵥ x ≤ β} := by
    constructor
    · dsimp [P, xHat]
      rw [memRightGapExamplePolyhedron_iff]
      refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
      · exact hT_nonneg
      · simp
      · simp
      · have hrow : T ≤ 2 * (T + 1) := by
          nlinarith [hT_nonneg]
        simpa using hrow
    · dsimp [xHat, α, β]
      norm_num [dotProduct]
  have hHatOpt : IsNodeOptimalPoint (P ∩ {x : Fin 2 → ℝ | α ⬝ᵥ x ≤ β}) c xHat := by
    constructor
    · exact hxHat_mem
    · intro y hy
      rcases hy with ⟨hyP, hyCut⟩
      have hyP' : y ∈ rightGapExamplePolyhedron T := by
        simpa [P] using hyP
      rcases (memRightGapExamplePolyhedron_iff T y).1 hyP' with
        ⟨hy0_nonneg, -, -, - , -, -⟩
      have hyCutScalar : T * y 0 + y 1 ≤ T := by
        simpa [α, β, dotProduct] using hyCut
      have hy1_le_T : y 1 ≤ T := by
        nlinarith [hyCutScalar, hy0_nonneg, hT_nonneg]
      -- The mirrored cut bounds the objective by `T`, attained at `xHat = ![0, T]`.
      calc
        c ⬝ᵥ y = y 1 := by
          simpa [c] using objectiveSecondCoordinate_eq y
        _ ≤ T := hy1_le_T
        _ = c ⬝ᵥ xHat := by
          dsimp [c, xHat]
          norm_num [dotProduct]
  have hPlusValue :
      exercise_9_17_lp_plus_value P c π π0 = c ⬝ᵥ xPlus := by
    -- Rewrite `z⁺` through the chosen upper-branch optimal witness.
    simpa [exercise_9_17_lp_plus_value] using
      linearObjectiveValue_eq_of_isNodeOptimalPoint hPlusOpt
  have hHatValue :
      exercise_9_17_split_cut_value P c α β = c ⬝ᵥ xHat := by
    -- Rewrite the cut-LP value through the chosen cut-feasible optimum.
    simpa [exercise_9_17_split_cut_value] using
      linearObjectiveValue_eq_of_isNodeOptimalPoint hHatOpt
  refine
    ⟨2, P, c, xBar, xPlus, xHat, π, π0, α, β, hP, hBarOpt, hxBarStrip, hcut,
      hPlusOpt, hHatOpt, ?_⟩
  -- The constructed witnesses realize a mirrored gap of at least `M`.
  calc
    exercise_9_17_lp_plus_value P c π π0 + M = c ⬝ᵥ xPlus + M := by
      rw [hPlusValue]
    _ = M := by
      dsimp [c, xPlus]
      norm_num [dotProduct]
    _ ≤ T := hM_le_T
    _ = c ⬝ᵥ xHat := by
      dsimp [c, xHat]
      norm_num [dotProduct]
    _ = exercise_9_17_split_cut_value P c α β := by
      rw [hHatValue.symm]

end Exercise917
