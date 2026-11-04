/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.subgradient
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators Matrix
open WithLp

-- Semantic recall note:
-- * this file keeps its own Exercise 8.13 LP surface for the basic feasible-set and objective
--   owners so the argument does not depend on rebuilding Proposition 8.8
-- * the Chapter 8 projected-subgradient interface is reproduced locally over the canonical
--   `IsSubgradientAtOn` owner from `Integer.Chapters.Chap08.subgradient`
--   `IsSubgradientAtOn`, `ProjectionOnto`, and `IsProjectedSubgradientMethodSequence`
-- * semantic search confirmed that the canonical infeasibility-aware value layer is `WithBot`;
--   this source-facing part (4) therefore keeps the local `ℝ` owner and states explicit
--   nonemptiness hypotheses instead of changing owners mid-exercise
-- This file keeps the source-facing Exercise 8.13 value-function and dual-multiplier layer, then
-- bridges that source surface to the generic Chapter 8 projected-subgradient API.

noncomputable section

section Exercise813

variable {m n : ℕ}

/-- The set `S = {x ∈ [0,1]^n | ∑_j x_j ≥ 1}` appearing in Exercise 8.13. -/
def uncapacitated_facility_location_opening_domain : Set (Fin n → ℝ) :=
  {x | (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ 1 ≤ ∑ j, x j}

/-- Membership in `uncapacitated_facility_location_opening_domain` means precisely that every
coordinate lies in `[0,1]` and the coordinates sum to at least `1`. -/
theorem mem_uncapacitated_facility_location_opening_domain_iff
    {x : Fin n → ℝ} :
    x ∈ uncapacitated_facility_location_opening_domain ↔
      (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ 1 ≤ ∑ j, x j :=
  Iff.rfl

/-- The assignment vectors `y` feasible for a fixed opening vector `x`: each customer `i` is fully
assigned, the assignment variables are nonnegative, and they satisfy the linking bounds
`y_ij ≤ x_j`. -/
def uncapacitated_facility_location_assignment_feasible_set
    (x : Fin n → ℝ) : Set (Fin m → Fin n → ℝ) :=
  {y |
    (∀ i, ∑ j, y i j = 1) ∧
      (∀ i j, 0 ≤ y i j) ∧
      (∀ i j, y i j ≤ x j)}

/-- Membership in `uncapacitated_facility_location_assignment_feasible_set x` expands to the row
sum equations, nonnegativity, and linking inequalities `y_ij ≤ x_j`. -/
theorem mem_uncapacitated_facility_location_assignment_feasible_set_iff
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ} :
    y ∈ uncapacitated_facility_location_assignment_feasible_set x ↔
      (∀ i, ∑ j, y i j = 1) ∧
        (∀ i j, 0 ≤ y i j) ∧
        (∀ i j, y i j ≤ x j) :=
  Iff.rfl

/-- Helper for Exercise 8.13: the LP-relaxation feasible set consists of assignment equations,
nonnegativity, linking inequalities, and opening-vector box constraints. -/
def facilityLocationLpFeasibleSet : Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  {xy |
    (∀ i, ∑ j, xy.1 i j = 1) ∧
      (∀ i j, 0 ≤ xy.1 i j) ∧
      (∀ i j, xy.1 i j ≤ xy.2 j) ∧
      (∀ j, 0 ≤ xy.2 j) ∧
      (∀ j, xy.2 j ≤ 1)}

/-- Helper for Exercise 8.13: membership in `facilityLocationLpFeasibleSet` unfolds to the
assignment equations, nonnegativity, linking inequalities, and box constraints. -/
theorem mem_facilityLocationLpFeasibleSet_iff
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)} :
    xy ∈ facilityLocationLpFeasibleSet ↔
      (∀ i, ∑ j, xy.1 i j = 1) ∧
        (∀ i j, 0 ≤ xy.1 i j) ∧
        (∀ i j, xy.1 i j ≤ xy.2 j) ∧
        (∀ j, 0 ≤ xy.2 j) ∧
        (∀ j, xy.2 j ≤ 1) :=
  Iff.rfl

/-- Helper for Exercise 8.13: the LP objective is `∑_{i,j} c_ij y_ij - ∑_j f_j x_j` on a pair
`(y, x)`. -/
def facilityLocationObjective
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (∑ i, ∑ j, c i j * xy.1 i j) - ∑ j, f j * xy.2 j

/-- Helper for Exercise 8.13: evaluating `facilityLocationObjective` on `(y, x)` recovers the
displayed objective formula. -/
theorem facilityLocationObjective_mk
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (y : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) :
    facilityLocationObjective c f (y, x) =
      (∑ i, ∑ j, c i j * y i j) - ∑ j, f j * x j :=
  rfl

/-- The objective value `∑_{i,j} c_ij y_ij - ∑_j f_j x_j` for a fixed opening vector `x` and a
feasible assignment vector `y`. -/
abbrev uncapacitated_facility_location_opening_objective
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (x : Fin n → ℝ)
  (y : Fin m → Fin n → ℝ) : ℝ :=
  facilityLocationObjective c f (y, x)

/-- The value function `z(x)` from Exercise 8.13, defined as the supremum of the assignment
objective over the feasible assignment set attached to `x`. -/
def uncapacitated_facility_location_opening_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  sSup
    ((fun y : Fin m → Fin n → ℝ ↦
        uncapacitated_facility_location_opening_objective c f x y) ''
      uncapacitated_facility_location_assignment_feasible_set x)

/-- Unfolding `uncapacitated_facility_location_opening_value c f x` recovers the displayed
supremum formula for the value function `z(x)`. -/
theorem uncapacitated_facility_location_opening_value_eq_sSup
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (x : Fin n → ℝ) :
    uncapacitated_facility_location_opening_value c f x =
      sSup
        ((fun y : Fin m → Fin n → ℝ ↦
            uncapacitated_facility_location_opening_objective c f x y) ''
          uncapacitated_facility_location_assignment_feasible_set x) :=
  rfl

/-- A pair `(u,v)` is feasible for the dual linear program associated with `z(x)` when the
linking multipliers are nonnegative and the dual covering inequalities `v_i + u_ij ≥ c_ij` hold
for all customers `i` and facilities `j`. -/
def IsFeasibleFacilityLocationOpeningDualSolution
    (c : Fin m → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ)
    (v : Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ u i j) ∧
    (∀ i j, c i j ≤ v i + u i j)

/-- The dual objective corresponding to the value function `z(x)`: the affine function of `x`
obtained from a dual-feasible pair `(u,v)`. -/
def uncapacitated_facility_location_opening_dual_objective
    (f : Fin n → ℝ)
    (x : Fin n → ℝ)
    (u : Fin m → Fin n → ℝ)
    (v : Fin m → ℝ) : ℝ :=
  (∑ i, v i) + ∑ j, ((∑ i, u i j) - f j) * x j

/-- `IsOptimalFacilityLocationOpeningDualSolution c f x u v` means that `(u,v)` is feasible for
the dual of `z(x)` and minimizes the dual objective at the chosen opening vector `x`. -/
def IsOptimalFacilityLocationOpeningDualSolution
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (x : Fin n → ℝ)
    (u : Fin m → Fin n → ℝ)
    (v : Fin m → ℝ) : Prop :=
  IsFeasibleFacilityLocationOpeningDualSolution c u v ∧
    ∀ u' : Fin m → Fin n → ℝ, ∀ v' : Fin m → ℝ,
      IsFeasibleFacilityLocationOpeningDualSolution c u' v' →
        uncapacitated_facility_location_opening_dual_objective f x u v ≤
          uncapacitated_facility_location_opening_dual_objective f x u' v'

namespace IsOptimalFacilityLocationOpeningDualSolution

/-- An optimal opening-dual solution is, in particular, dual feasible. -/
theorem feasible
    {c : Fin m → Fin n → ℝ}
    {f : Fin n → ℝ}
    {x : Fin n → ℝ}
    {u : Fin m → Fin n → ℝ}
    {v : Fin m → ℝ}
    (huv : IsOptimalFacilityLocationOpeningDualSolution c f x u v) :
    IsFeasibleFacilityLocationOpeningDualSolution c u v :=
  huv.1

end IsOptimalFacilityLocationOpeningDualSolution

/-- In the source convention for maximizing a concave function on a domain `P`, `g` is a
subgradient of `φ` at `x` when the negated function `-φ` has the usual Chapter 8 subgradient
`-g` there with comparison points restricted to `P`. -/
abbrev IsConcaveSubgradientAt
    (φ : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    (x g : Fin n → ℝ) : Prop :=
  IsSubgradientAtOn (fun x' ↦ -φ x') P x (-g)

/-- The source-facing affine upper-bound inequality is the sign-convention specialization of
`IsSubgradientAtOn` on the comparison set `P`. -/
theorem isConcaveSubgradientAt_iff
    (φ : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    (x g : Fin n → ℝ) :
    IsConcaveSubgradientAt φ P x g ↔
      ∀ x' ∈ P, φ x' ≤ φ x + ∑ j, g j * (x' j - x j) := by
  -- Unfold the source-facing sign convention to the Chapter 8 affine lower-bound inequality.
  unfold IsConcaveSubgradientAt IsSubgradientAtOn
  constructor
  · intro h x' hx'
    let t : ℝ := ∑ j, g j * (x' j - x j)
    have hneg :
        (∑ j, (-g) j * (x' j - x j) : ℝ) = -t := by
      simp [t, Pi.neg_apply, Finset.sum_neg_distrib, mul_comm]
    have hraw := h x' hx'
    rw [hneg] at hraw
    change -φ x' ≥ -φ x - t at hraw
    have hupper : φ x' ≤ φ x + t := by
      linarith [hraw]
    simpa [t, add_comm, add_left_comm, add_assoc]
      using hupper
  · intro h x' hx'
    let t : ℝ := ∑ j, g j * (x' j - x j)
    have hx' := h x' hx'
    have hupper : φ x' ≤ φ x + t := by
      simpa [t] using hx'
    have hneg :
        (∑ j, (-g) j * (x' j - x j) : ℝ) = -t := by
      simp [t, Pi.neg_apply, Finset.sum_neg_distrib, mul_comm]
    have hraw' : φ x' + (-t) ≤ φ x := by
      linarith [hupper]
    rw [hneg]
    have hgoal : -φ x' ≥ -φ x + (-t) := by
      change -φ x' ≥ -φ x - t
      linarith [hupper]
    exact hgoal

/-- The dual multipliers induce the candidate subgradient whose `j`-th coordinate is
`∑_i u_ij - f_j`. -/
def facility_location_opening_dual_subgradient
    (f : Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j ↦ (∑ i, u i j) - f j

/-- Evaluating `facility_location_opening_dual_subgradient f u` at coordinate `j` gives the source
formula `∑_i u_ij - f_j`. -/
theorem facility_location_opening_dual_subgradient_apply
    (f : Fin n → ℝ)
    (u : Fin m → Fin n → ℝ)
    (j : Fin n) :
    facility_location_opening_dual_subgradient f u j = (∑ i, u i j) - f j :=
  rfl

/-- Helper for Exercise 8.13: every opening vector `x ∈ S` admits a normalized feasible
assignment obtained by distributing each customer's unit mass proportionally to the openings. -/
lemma openingAssignmentFeasible_nonempty
    {x : Fin n → ℝ}
    (hx : x ∈ uncapacitated_facility_location_opening_domain) :
    Set.Nonempty (uncapacitated_facility_location_assignment_feasible_set (m := m) x) := by
  rcases (mem_uncapacitated_facility_location_opening_domain_iff.mp hx) with ⟨hxbox, hsum⟩
  let total : ℝ := ∑ j, x j
  have htotal_pos : 0 < total := by
    -- The domain condition `1 ≤ ∑ j, x j` supplies a positive normalizing denominator.
    exact lt_of_lt_of_le zero_lt_one hsum
  have htotal_ne : total ≠ 0 := ne_of_gt htotal_pos
  refine ⟨fun _ j ↦ x j / total, ?_⟩
  rw [mem_uncapacitated_facility_location_assignment_feasible_set_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    -- The normalized row sums equal `1`.
    calc
      ∑ j, x j / total = (∑ j, x j) / total := by
        rw [Finset.sum_div]
      _ = 1 := by
        simp [total, htotal_ne]
  · intro i j
    -- Nonnegativity is inherited from the opening vector.
    exact div_nonneg (hxbox j).1 (le_of_lt htotal_pos)
  · intro i j
    -- Since `total ≥ 1`, dividing by `total` can only decrease the nonnegative coordinate `x j`.
    have hxj_nonneg : 0 ≤ x j := (hxbox j).1
    simpa [total] using div_le_self hxj_nonneg hsum

/-- Helper for Exercise 8.13: every feasible opening-objective value is bounded above by a crude
absolute-value constant depending only on `c` and `f`. -/
lemma openingObjective_le_absBound
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ uncapacitated_facility_location_opening_domain)
    {y : Fin m → Fin n → ℝ}
    (hy : y ∈ uncapacitated_facility_location_assignment_feasible_set x) :
    uncapacitated_facility_location_opening_objective c f x y ≤
      (∑ i, ∑ j, |c i j|) + ∑ j, |f j| := by
  rcases (mem_uncapacitated_facility_location_opening_domain_iff.mp hx) with ⟨hxbox, _⟩
  rcases (mem_uncapacitated_facility_location_assignment_feasible_set_iff.mp hy) with
    ⟨_, hyNonneg, hyLeX⟩
  have hyLeOne : ∀ i j, y i j ≤ 1 := by
    intro i j
    exact le_trans (hyLeX i j) (hxbox j).2
  have hassign :
      ∑ i, ∑ j, c i j * y i j ≤ ∑ i, ∑ j, |c i j| := by
    -- Each assignment term is controlled by the absolute value of its coefficient.
    refine Finset.sum_le_sum fun i _ ↦ ?_
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have hmul :
        |c i j * y i j| ≤ |c i j| := by
      calc
        |c i j * y i j| = |c i j| * |y i j| := by
          rw [abs_mul]
        _ = |c i j| * y i j := by
          rw [abs_of_nonneg (hyNonneg i j)]
        _ ≤ |c i j| * 1 := by
          gcongr
          exact hyLeOne i j
        _ = |c i j| := by ring
    exact le_trans (le_abs_self _) hmul
  have hcost :
      -∑ j, f j * x j ≤ ∑ j, |f j| := by
    -- The opening-cost correction is controlled termwise by `|f j|` because `0 ≤ x j ≤ 1`.
    calc
      -∑ j, f j * x j = ∑ j, -(f j * x j) := by
        rw [Finset.sum_neg_distrib]
      _ ≤ ∑ j, |f j| := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        have hmul :
            |f j * x j| ≤ |f j| := by
          calc
            |f j * x j| = |f j| * |x j| := by
              rw [abs_mul]
            _ = |f j| * x j := by
              rw [abs_of_nonneg (hxbox j).1]
            _ ≤ |f j| * 1 := by
              gcongr
              exact (hxbox j).2
            _ = |f j| := by ring
        exact le_trans (neg_le_abs _) hmul
  -- Combine the assignment and opening-cost bounds into the claimed objective bound.
  change facilityLocationObjective c f (y, x) ≤
    (∑ i, ∑ j, |c i j|) + ∑ j, |f j|
  rw [facilityLocationObjective_mk]
  calc
    (∑ i, ∑ j, c i j * y i j) - ∑ j, f j * x j
        = (∑ i, ∑ j, c i j * y i j) + (-∑ j, f j * x j) := by
            ring
    _ ≤ (∑ i, ∑ j, |c i j|) + ∑ j, |f j| := add_le_add hassign hcost

/-- Helper for Exercise 8.13: every LP-feasible pair with at least one customer has its opening
component in the source domain `S`. -/
lemma lpSecond_memOpeningDomain_of_memLpFeasible
    (hm : 0 < m)
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hxy : xy ∈ facilityLocationLpFeasibleSet) :
    xy.2 ∈ uncapacitated_facility_location_opening_domain := by
  rcases (mem_facilityLocationLpFeasibleSet_iff.mp hxy) with
    ⟨hrow, _, hyLeX, hxNonneg, hxLeOne⟩
  let i0 : Fin m := ⟨0, hm⟩
  have hsum_le : ∑ j, xy.1 i0 j ≤ ∑ j, xy.2 j := by
    exact Finset.sum_le_sum fun j _ ↦ hyLeX i0 j
  have hsum_ge_one : 1 ≤ ∑ j, xy.2 j := by
    -- The row-sum equality for any existing customer forces the opening vector into `S`.
    calc
      1 = ∑ j, xy.1 i0 j := by
        symm
        exact hrow i0
      _ ≤ ∑ j, xy.2 j := hsum_le
  exact (mem_uncapacitated_facility_location_opening_domain_iff.mpr
    ⟨fun j ↦ ⟨hxNonneg j, hxLeOne j⟩, hsum_ge_one⟩)

/-- Helper for Exercise 8.13: the opening domain `S` is convex, since the box constraints and the
lower bound on `∑ j, x j` are both preserved by convex combinations. -/
lemma openingDomain_convex :
    Convex ℝ (uncapacitated_facility_location_opening_domain (n := n)) := by
  intro x hx y hy a b ha hb hab
  rw [mem_uncapacitated_facility_location_opening_domain_iff] at hx hy
  rw [mem_uncapacitated_facility_location_opening_domain_iff]
  rcases hx with ⟨hxbox, hxsum⟩
  rcases hy with ⟨hybox, hysum⟩
  refine ⟨?_, ?_⟩
  · intro j
    rcases hxbox j with ⟨hxj0, hxj1⟩
    rcases hybox j with ⟨hyj0, hyj1⟩
    constructor
    · -- Each coordinate stays nonnegative under a nonnegative convex combination.
      change 0 ≤ a * x j + b * y j
      nlinarith
    · -- Each coordinate stays at most `1` for the same reason.
      change a * x j + b * y j ≤ 1
      nlinarith
  · -- The total opening mass stays at least `1`.
    have hsum_combo :
        ∑ j, (a • x + b • y) j = a * ∑ j, x j + b * ∑ j, y j := by
      simp [Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]
    rw [show (a • x + b • y) = fun j ↦ a * x j + b * y j by
      funext j
      simp [Pi.smul_apply]]
    calc
      1 = a * 1 + b * 1 := by nlinarith
      _ ≤ a * ∑ j, x j + b * ∑ j, y j := by
        gcongr
      _ = ∑ j, (a * x j + b * y j) := by
        simpa [Pi.smul_apply] using hsum_combo.symm

/-- Helper for Exercise 8.13: feasible assignments are closed under convex combinations when the
opening vectors are convex-combined in the same way. -/
lemma convexCombination_memOpeningAssignmentFeasibleSet
    {x₁ x₂ : Fin n → ℝ}
    {y₁ y₂ : Fin m → Fin n → ℝ}
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hab : a + b = 1)
    (hy₁ : y₁ ∈ uncapacitated_facility_location_assignment_feasible_set x₁)
    (hy₂ : y₂ ∈ uncapacitated_facility_location_assignment_feasible_set x₂) :
    (fun i j ↦ a * y₁ i j + b * y₂ i j) ∈
      uncapacitated_facility_location_assignment_feasible_set
        (fun j ↦ a * x₁ j + b * x₂ j) := by
  rw [mem_uncapacitated_facility_location_assignment_feasible_set_iff] at hy₁ hy₂ ⊢
  rcases hy₁ with ⟨hrow₁, hnonneg₁, hlink₁⟩
  rcases hy₂ with ⟨hrow₂, hnonneg₂, hlink₂⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    -- The row-sum equations are preserved by linearity.
    calc
      ∑ j, (a * y₁ i j + b * y₂ i j)
          = a * ∑ j, y₁ i j + b * ∑ j, y₂ i j := by
              simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = 1 := by rw [hrow₁ i, hrow₂ i]; nlinarith
  · intro i j
    -- Nonnegativity is preserved coordinatewise.
    nlinarith [hnonneg₁ i j, hnonneg₂ i j]
  · intro i j
    -- The linking inequalities are preserved coordinatewise.
    nlinarith [hlink₁ i j, hlink₂ i j]

/-- Helper for Exercise 8.13: the opening objective is affine in `(y, x)`, so evaluating it on a
common convex combination splits into the same convex combination of objective values. -/
lemma openingObjective_convexCombination
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (x₁ x₂ : Fin n → ℝ)
    (y₁ y₂ : Fin m → Fin n → ℝ)
    (a b : ℝ) :
    uncapacitated_facility_location_opening_objective c f
      (fun j ↦ a * x₁ j + b * x₂ j)
      (fun i j ↦ a * y₁ i j + b * y₂ i j) =
      a * uncapacitated_facility_location_opening_objective c f x₁ y₁ +
        b * uncapacitated_facility_location_opening_objective c f x₂ y₂ := by
  -- Expand the objective and distribute the sums across the convex combination.
  simp [uncapacitated_facility_location_opening_objective,
    facilityLocationObjective_mk, Finset.sum_add_distrib, Finset.mul_sum,
    mul_add, sub_eq_add_neg, mul_left_comm]
  ring

/-- Helper for Exercise 8.13: every dual-feasible pair `(u,v)` gives a global affine upper bound
on the opening value function at the chosen opening vector `x`. -/
lemma openingValue_le_dualObjective_of_feasibleDual
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ uncapacitated_facility_location_opening_domain)
    {u : Fin m → Fin n → ℝ}
    {v : Fin m → ℝ}
    (huv : IsFeasibleFacilityLocationOpeningDualSolution c u v) :
    uncapacitated_facility_location_opening_value c f x ≤
      uncapacitated_facility_location_opening_dual_objective f x u v := by
  rcases openingAssignmentFeasible_nonempty (m := m) hx with ⟨y₀, hy₀⟩
  let imageSet : Set ℝ :=
    ((fun y : Fin m → Fin n → ℝ ↦
        uncapacitated_facility_location_opening_objective c f x y) ''
      uncapacitated_facility_location_assignment_feasible_set x)
  have hImageNonempty : imageSet.Nonempty := by
    exact ⟨uncapacitated_facility_location_opening_objective c f x y₀, ⟨y₀, hy₀, rfl⟩⟩
  rw [uncapacitated_facility_location_opening_value_eq_sSup]
  refine csSup_le hImageNonempty ?_
  rintro _ ⟨y, hy, rfl⟩
  rcases huv with ⟨huNonneg, hcover⟩
  rcases (mem_uncapacitated_facility_location_assignment_feasible_set_iff.mp hy) with
    ⟨hrow, hyNonneg, hyLeX⟩
  have hcoeff :
      ∑ i, ∑ j, c i j * y i j ≤ ∑ i, ∑ j, (v i + u i j) * y i j := by
    refine Finset.sum_le_sum fun i _ ↦ ?_
    refine Finset.sum_le_sum fun j _ ↦ ?_
    exact mul_le_mul_of_nonneg_right (hcover i j) (hyNonneg i j)
  have hvRows :
      ∑ i, ∑ j, v i * y i j = ∑ i, v i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.mul_sum, hrow i]
    ring
  have huRows :
      ∑ i, ∑ j, u i j * y i j ≤ ∑ j, (∑ i, u i j) * x j := by
    calc
      ∑ i, ∑ j, u i j * y i j = ∑ j, ∑ i, u i j * y i j := by
        rw [Finset.sum_comm]
      _ ≤ ∑ j, ∑ i, u i j * x j := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact mul_le_mul_of_nonneg_left (hyLeX i j) (huNonneg i j)
      _ = ∑ j, (∑ i, u i j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [← Finset.sum_mul]
  have hsplit :
      ∑ i, ∑ j, (v i + u i j) * y i j =
        (∑ i, v i) + ∑ i, ∑ j, u i j * y i j := by
    calc
      ∑ i, ∑ j, (v i + u i j) * y i j
          = ∑ i, (∑ j, v i * y i j + ∑ j, u i j * y i j) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp_rw [add_mul]
              rw [Finset.sum_add_distrib]
      _ = (∑ i, ∑ j, v i * y i j) + ∑ i, ∑ j, u i j * y i j := by
            rw [Finset.sum_add_distrib]
      _ = (∑ i, v i) + ∑ i, ∑ j, u i j * y i j := by
            rw [hvRows]
  change facilityLocationObjective c f (y, x) ≤
    uncapacitated_facility_location_opening_dual_objective f x u v
  rw [facilityLocationObjective_mk]
  calc
    (∑ i, ∑ j, c i j * y i j) - ∑ j, f j * x j
        ≤ (∑ i, ∑ j, (v i + u i j) * y i j) - ∑ j, f j * x j := by
            exact sub_le_sub_right hcoeff _
    _ = (∑ i, v i) + ∑ i, ∑ j, u i j * y i j - ∑ j, f j * x j := by
          rw [hsplit]
    _ ≤ (∑ i, v i) + ∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j := by
          gcongr
    _ = uncapacitated_facility_location_opening_dual_objective f x u v := by
          have hassoc :
              (∑ i, v i) + ∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j =
                (∑ i, v i) + (∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j) := by
            ring
          have hsum :
              ∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j =
                ∑ j, (((∑ i, u i j) - f j) * x j) := by
            calc
              ∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j
                  = ∑ j, (∑ i, u i j) * x j + ∑ j, -(f j * x j) := by
                      rw [sub_eq_add_neg, Finset.sum_neg_distrib]
              _ = ∑ j, (((∑ i, u i j) * x j) + -(f j * x j)) := by
                    rw [← Finset.sum_add_distrib]
              _ = ∑ j, (((∑ i, u i j) - f j) * x j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    ring
          calc
            (∑ i, v i) + ∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j
                = (∑ i, v i) + (∑ j, (((∑ i, u i j) - f j) * x j)) := by
                    rw [hassoc, hsum]
            _ = uncapacitated_facility_location_opening_dual_objective f x u v := by
                  rfl

#exit

/-- Helper for Exercise 8.13: the row LP for a fixed customer uses two split row-sum
constraints, the linking inequalities `y_j ≤ x_j`, and the nonnegativity rows `-y_j ≤ 0`. -/
abbrev openingRowConstraint (n : ℕ) := (Fin 1 ⊕ Fin 1) ⊕ (Fin n ⊕ Fin n)

/-- Helper for Exercise 8.13: the generic LP owners use `Fin`-indexed rows, so the split row LP
is reindexed from its sum-type row set to `Fin ((1 + 1) + (n + n))`. -/
abbrev openingRowConstraintEquiv :
    openingRowConstraint n ≃ Fin ((1 + 1) + (n + n)) :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

/-- Helper for Exercise 8.13: the `∑_j y_j ≤ 1` row in the row LP. -/
def openingRowSumUpper : openingRowConstraint n :=
  Sum.inl (Sum.inl 0)

/-- Helper for Exercise 8.13: the `-∑_j y_j ≤ -1` row in the row LP. -/
def openingRowSumLower : openingRowConstraint n :=
  Sum.inl (Sum.inr 0)

/-- Helper for Exercise 8.13: the row `y_j ≤ x_j` attached to coordinate `j`. -/
def openingRowLink (j : Fin n) : openingRowConstraint n :=
  Sum.inr (Sum.inl j)

/-- Helper for Exercise 8.13: the row `-y_j ≤ 0` encoding nonnegativity of coordinate `j`. -/
def openingRowNonneg (j : Fin n) : openingRowConstraint n :=
  Sum.inr (Sum.inr j)

/-- Helper for Exercise 8.13: the coefficient matrix of the one-customer primal LP. -/
def openingRowPrimalMatrix :
    Matrix (openingRowConstraint n) (Fin n) ℝ :=
  fun row col ↦
    match row with
    | Sum.inl (Sum.inl _) => 1
    | Sum.inl (Sum.inr _) => -1
    | Sum.inr (Sum.inl j) => if j = col then 1 else 0
    | Sum.inr (Sum.inr j) => if j = col then -1 else 0

/-- Helper for Exercise 8.13: the right-hand side of the one-customer primal LP at opening vector
`x`. -/
def openingRowPrimalRhs
    (x : Fin n → ℝ) : openingRowConstraint n → ℝ :=
  fun row ↦
    match row with
    | Sum.inl (Sum.inl _) => 1
    | Sum.inl (Sum.inr _) => -1
    | Sum.inr (Sum.inl j) => x j
    | Sum.inr (Sum.inr _) => 0

/-- Helper for Exercise 8.13: the `Fin`-indexed row matrix used with the Chapter 3 LP owners. -/
def openingRowPrimalMatrixFin :
    Matrix (Fin ((1 + 1) + (n + n))) (Fin n) ℝ :=
  (openingRowPrimalMatrix (n := n)).submatrix openingRowConstraintEquiv.symm (Equiv.refl _)

/-- Helper for Exercise 8.13: the `Fin`-indexed right-hand side used with the Chapter 3 LP
owners. -/
def openingRowPrimalRhsFin
    (x : Fin n → ℝ) : Fin ((1 + 1) + (n + n)) → ℝ :=
  openingRowPrimalRhs (n := n) x ∘ openingRowConstraintEquiv.symm

/-- Helper for Exercise 8.13: a source-facing dual pair for one customer row consists of
nonnegative linking multipliers `u` and a free scalar `v` with `r_j ≤ v + u_j`. -/
def IsFeasibleOpeningRowDualSolution
    (r : Fin n → ℝ)
    (u : Fin n → ℝ)
    (v : ℝ) : Prop :=
  (∀ j, 0 ≤ u j) ∧
    (∀ j, r j ≤ v + u j)

/-- Helper for Exercise 8.13: the source row dual objective is `v + ∑_j u_j x_j`. -/
def openingRowDualObjective
    (x : Fin n → ℝ)
    (u : Fin n → ℝ)
    (v : ℝ) : ℝ :=
  v + ∑ j, u j * x j

/-- Helper for Exercise 8.13: split `v` into nonnegative parts to obtain a generic LP dual vector
for the row LP. -/
def openingRowLinearDualOfSource
    (r : Fin n → ℝ)
    (u : Fin n → ℝ)
    (v : ℝ) : openingRowConstraint n → ℝ :=
  fun row ↦
    match row with
    | Sum.inl (Sum.inl _) => max v 0
    | Sum.inl (Sum.inr _) => max (-v) 0
    | Sum.inr (Sum.inl j) => u j
    | Sum.inr (Sum.inr j) => v + u j - r j

/-- Helper for Exercise 8.13: the source row dual witness reindexed to the `Fin` row type used by
the generic LP owners. -/
def openingRowLinearDualOfSourceFin
    (r : Fin n → ℝ)
    (u : Fin n → ℝ)
    (v : ℝ) : Fin ((1 + 1) + (n + n)) → ℝ :=
  openingRowLinearDualOfSource (n := n) r u v ∘ openingRowConstraintEquiv.symm

/-- Helper for Exercise 8.13: recover the source row linking multipliers from a generic LP dual
vector. -/
def openingRowSourceDualUOfLinear
    (w : Fin ((1 + 1) + (n + n)) → ℝ) : Fin n → ℝ :=
  fun j ↦ w (openingRowConstraintEquiv (openingRowLink j))

/-- Helper for Exercise 8.13: recover the free source row scalar from the split row-sum
multipliers of a generic LP dual vector. -/
def openingRowSourceDualVOfLinear
    (w : Fin ((1 + 1) + (n + n)) → ℝ) : ℝ :=
  w (openingRowConstraintEquiv openingRowSumUpper) -
    w (openingRowConstraintEquiv openingRowSumLower)

/-- Helper for Exercise 8.13: `max v 0 - max (-v) 0 = v`, so the split row-sum multipliers really
encode the original unrestricted scalar `v`. -/
lemma max_sub_max_neg_eq_self
    (v : ℝ) :
    max v 0 - max (-v) 0 = v := by
  -- Check the sign of `v` and simplify the positive/negative parts casewise.
  by_cases hv : 0 ≤ v
  · rw [max_eq_left hv, max_eq_right (by linarith)]
    ring
  · have hv' : v ≤ 0 := le_of_not_ge hv
    rw [max_eq_right hv', max_eq_left (by linarith)]
    ring

-- Route correction: instead of asking `simp` to normalize the `openingRowConstraintEquiv`
-- transport inside large LP goals, record the four row evaluations and the one dual row formula
-- explicitly and reuse them everywhere below.

/-- Helper for Exercise 8.13: the transported row-sum upper constraint evaluates to `∑_j y_j`. -/
lemma openingRowPrimalMatrixFin_mulVec_sumUpper
    (y : Fin n → ℝ) :
    (openingRowPrimalMatrixFin (n := n) *ᵥ y)
        (openingRowConstraintEquiv (openingRowSumUpper (n := n))) =
      ∑ j, y j := by
  let Araw : Matrix (openingRowConstraint n) (Fin n) ℝ := openingRowPrimalMatrix (n := n)
  have hmul :=
    Matrix.submatrix_mulVec_equiv Araw y openingRowConstraintEquiv.symm (Equiv.refl _)
  have hEq :
      (openingRowPrimalMatrixFin (n := n) *ᵥ y)
          (openingRowConstraintEquiv (openingRowSumUpper (n := n))) =
        (Araw *ᵥ y) (openingRowSumUpper (n := n)) := by
    simpa [openingRowPrimalMatrixFin, Araw] using
      congrFun hmul (openingRowConstraintEquiv (openingRowSumUpper (n := n)))
  rw [hEq]
  -- The upper row contains only `1`s, so its matrix product is the row sum.
  simp [Araw, openingRowPrimalMatrix, Matrix.mulVec, dotProduct, openingRowSumUpper]

/-- Helper for Exercise 8.13: the transported row-sum lower constraint evaluates to `-∑_j y_j`.
-/
lemma openingRowPrimalMatrixFin_mulVec_sumLower
    (y : Fin n → ℝ) :
    (openingRowPrimalMatrixFin (n := n) *ᵥ y)
        (openingRowConstraintEquiv (openingRowSumLower (n := n))) =
      -∑ j, y j := by
  let Araw : Matrix (openingRowConstraint n) (Fin n) ℝ := openingRowPrimalMatrix (n := n)
  have hmul :=
    Matrix.submatrix_mulVec_equiv Araw y openingRowConstraintEquiv.symm (Equiv.refl _)
  have hEq :
      (openingRowPrimalMatrixFin (n := n) *ᵥ y)
          (openingRowConstraintEquiv (openingRowSumLower (n := n))) =
        (Araw *ᵥ y) (openingRowSumLower (n := n)) := by
    simpa [openingRowPrimalMatrixFin, Araw] using
      congrFun hmul (openingRowConstraintEquiv (openingRowSumLower (n := n)))
  rw [hEq]
  -- The lower row contains only `-1`s, so its matrix product is the negated row sum.
  simp [Araw, openingRowPrimalMatrix, Matrix.mulVec, dotProduct, openingRowSumLower]

/-- Helper for Exercise 8.13: the transported linking row for `j` evaluates to `y_j`. -/
lemma openingRowPrimalMatrixFin_mulVec_link
    (y : Fin n → ℝ)
    (j : Fin n) :
    (openingRowPrimalMatrixFin (n := n) *ᵥ y)
        (openingRowConstraintEquiv (openingRowLink (n := n) j)) =
      y j := by
  let Araw : Matrix (openingRowConstraint n) (Fin n) ℝ := openingRowPrimalMatrix (n := n)
  have hmul :=
    Matrix.submatrix_mulVec_equiv Araw y openingRowConstraintEquiv.symm (Equiv.refl _)
  have hEq :
      (openingRowPrimalMatrixFin (n := n) *ᵥ y)
          (openingRowConstraintEquiv (openingRowLink (n := n) j)) =
        (Araw *ᵥ y) (openingRowLink (n := n) j) := by
    simpa [openingRowPrimalMatrixFin, Araw] using
      congrFun hmul (openingRowConstraintEquiv (openingRowLink (n := n) j))
  rw [hEq]
  -- Only the `j`-th coordinate survives in the transported linking row.
  simp [Araw, openingRowPrimalMatrix, Matrix.mulVec, dotProduct, openingRowLink]

/-- Helper for Exercise 8.13: the transported nonnegativity row for `j` evaluates to `-y_j`. -/
lemma openingRowPrimalMatrixFin_mulVec_nonneg
    (y : Fin n → ℝ)
    (j : Fin n) :
    (openingRowPrimalMatrixFin (n := n) *ᵥ y)
        (openingRowConstraintEquiv (openingRowNonneg (n := n) j)) =
      -y j := by
  let Araw : Matrix (openingRowConstraint n) (Fin n) ℝ := openingRowPrimalMatrix (n := n)
  have hmul :=
    Matrix.submatrix_mulVec_equiv Araw y openingRowConstraintEquiv.symm (Equiv.refl _)
  have hEq :
      (openingRowPrimalMatrixFin (n := n) *ᵥ y)
          (openingRowConstraintEquiv (openingRowNonneg (n := n) j)) =
        (Araw *ᵥ y) (openingRowNonneg (n := n) j) := by
    simpa [openingRowPrimalMatrixFin, Araw] using
      congrFun hmul (openingRowConstraintEquiv (openingRowNonneg (n := n) j))
  rw [hEq]
  -- Only the `-y_j` entry survives in the transported nonnegativity row.
  simp [Araw, openingRowPrimalMatrix, Matrix.mulVec, dotProduct, openingRowNonneg]

/-- Helper for Exercise 8.13: the transported row-sum upper right-hand side is `1`. -/
lemma openingRowPrimalRhsFin_sumUpper
    (x : Fin n → ℝ) :
    openingRowPrimalRhsFin (n := n) x
      (openingRowConstraintEquiv (openingRowSumUpper (n := n))) = 1 := by
  simp [openingRowPrimalRhsFin, openingRowPrimalRhs, openingRowConstraintEquiv, openingRowSumUpper]

/-- Helper for Exercise 8.13: the transported row-sum lower right-hand side is `-1`. -/
lemma openingRowPrimalRhsFin_sumLower
    (x : Fin n → ℝ) :
    openingRowPrimalRhsFin (n := n) x
      (openingRowConstraintEquiv (openingRowSumLower (n := n))) = -1 := by
  simp [openingRowPrimalRhsFin, openingRowPrimalRhs, openingRowConstraintEquiv, openingRowSumLower]

/-- Helper for Exercise 8.13: the transported linking right-hand side at row `j` is `x_j`. -/
lemma openingRowPrimalRhsFin_link
    (x : Fin n → ℝ)
    (j : Fin n) :
    openingRowPrimalRhsFin (n := n) x
      (openingRowConstraintEquiv (openingRowLink (n := n) j)) = x j := by
  simp [openingRowPrimalRhsFin, openingRowPrimalRhs, openingRowConstraintEquiv, openingRowLink]

/-- Helper for Exercise 8.13: the transported nonnegativity right-hand side at row `j` is `0`. -/
lemma openingRowPrimalRhsFin_nonneg
    (x : Fin n → ℝ)
    (j : Fin n) :
    openingRowPrimalRhsFin (n := n) x
      (openingRowConstraintEquiv (openingRowNonneg (n := n) j)) = 0 := by
  simpa [openingRowPrimalRhsFin, openingRowPrimalRhs, openingRowNonneg] using
    congrArg (openingRowPrimalRhs (n := n) x)
      (openingRowConstraintEquiv.symm_apply_apply (openingRowNonneg (n := n) j))

/-- Helper for Exercise 8.13: evaluating the transported dual row equation at column `j` gives the
source expression `v⁺ - v⁻ + u_j - s_j`. -/
lemma openingRowPrimalMatrixFin_vecMul_link
    (w : Fin ((1 + 1) + (n + n)) → ℝ)
    (j : Fin n) :
    (w ᵥ* openingRowPrimalMatrixFin (n := n)) j =
      w (openingRowConstraintEquiv (openingRowSumUpper (n := n))) -
        w (openingRowConstraintEquiv (openingRowSumLower (n := n))) +
          w (openingRowConstraintEquiv (openingRowLink (n := n) j)) -
            w (openingRowConstraintEquiv (openingRowNonneg (n := n) j)) := by
  let Araw : Matrix (openingRowConstraint n) (Fin n) ℝ := openingRowPrimalMatrix (n := n)
  have hvec :=
    Matrix.submatrix_vecMul_equiv Araw w openingRowConstraintEquiv.symm (Equiv.refl _)
  have hEq :
      (w ᵥ* openingRowPrimalMatrixFin (n := n)) j =
        ((w ∘ openingRowConstraintEquiv) ᵥ* Araw) j := by
    simpa [openingRowPrimalMatrixFin, Araw] using congrFun hvec j
  rw [hEq, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Fintype.sum_sum_type]
  -- Split the transported row sum into the four native row blocks and collapse the selector rows.
  simp [Araw, openingRowPrimalMatrix, openingRowConstraintEquiv, openingRowSumUpper,
    openingRowSumLower, openingRowLink, openingRowNonneg]
  ring

/-- Helper for Exercise 8.13: the transported split upper multiplier recovers `max v 0`. -/
lemma openingRowLinearDualOfSourceFin_sumUpper
    (r : Fin n → ℝ)
    (u : Fin n → ℝ)
    (v : ℝ) :
    openingRowLinearDualOfSourceFin (n := n) r u v
      (openingRowConstraintEquiv (openingRowSumUpper (n := n))) = max v 0 := by
  simp [openingRowLinearDualOfSourceFin, openingRowLinearDualOfSource, openingRowConstraintEquiv,
    openingRowSumUpper]

/-- Helper for Exercise 8.13: the transported split lower multiplier recovers `max (-v) 0`. -/
lemma openingRowLinearDualOfSourceFin_sumLower
    (r : Fin n → ℝ)
    (u : Fin n → ℝ)
    (v : ℝ) :
    openingRowLinearDualOfSourceFin (n := n) r u v
      (openingRowConstraintEquiv (openingRowSumLower (n := n))) = max (-v) 0 := by
  simp [openingRowLinearDualOfSourceFin, openingRowLinearDualOfSource, openingRowConstraintEquiv,
    openingRowSumLower]

/-- Helper for Exercise 8.13: the transported linking multiplier at row `j` is `u_j`. -/
lemma openingRowLinearDualOfSourceFin_link
    (r : Fin n → ℝ)
    (u : Fin n → ℝ)
    (v : ℝ)
    (j : Fin n) :
    openingRowLinearDualOfSourceFin (n := n) r u v
      (openingRowConstraintEquiv (openingRowLink (n := n) j)) = u j := by
  simp [openingRowLinearDualOfSourceFin, openingRowLinearDualOfSource, openingRowConstraintEquiv,
    openingRowLink]

/-- Helper for Exercise 8.13: the transported slack multiplier at row `j` is `v + u_j - r_j`. -/
lemma openingRowLinearDualOfSourceFin_nonneg
    (r : Fin n → ℝ)
    (u : Fin n → ℝ)
    (v : ℝ)
    (j : Fin n) :
    openingRowLinearDualOfSourceFin (n := n) r u v
      (openingRowConstraintEquiv (openingRowNonneg (n := n) j)) = v + u j - r j := by
  simpa [openingRowLinearDualOfSourceFin, openingRowLinearDualOfSource, openingRowNonneg] using
    congrArg (openingRowLinearDualOfSource (n := n) r u v)
      (openingRowConstraintEquiv.symm_apply_apply (openingRowNonneg (n := n) j))

/-- Helper for Exercise 8.13: membership in the generic row primal region is exactly the source
row system `∑_j y_j = 1`, `0 ≤ y_j`, and `y_j ≤ x_j`. -/
lemma mem_openingRowPrimalFeasible_iff
    {x : Fin n → ℝ}
    {y : Fin n → ℝ} :
    y ∈ primal_feasible_region (openingRowPrimalMatrixFin (n := n)) (openingRowPrimalRhsFin x) ↔
      (∑ j, y j = 1) ∧
        (∀ j, 0 ≤ y j) ∧
        (∀ j, y j ≤ x j) := by
  rw [mem_primal_feasible_region_iff]
  constructor
  · intro hy
    refine ⟨?_, ?_, ?_⟩
    · have hUpper := hy (openingRowConstraintEquiv (openingRowSumUpper (n := n)))
      have hLower := hy (openingRowConstraintEquiv (openingRowSumLower (n := n)))
      rw [openingRowPrimalMatrixFin_mulVec_sumUpper] at hUpper
      rw [openingRowPrimalMatrixFin_mulVec_sumLower] at hLower
      rw [openingRowPrimalRhsFin_sumUpper] at hUpper
      rw [openingRowPrimalRhsFin_sumLower] at hLower
      -- The split `≤ 1` and `≥ 1` rows force the equality `∑_j y_j = 1`.
      linarith
    · intro j
      have hNonneg := hy (openingRowConstraintEquiv (openingRowNonneg (n := n) j))
      rw [openingRowPrimalMatrixFin_mulVec_nonneg] at hNonneg
      rw [openingRowPrimalRhsFin_nonneg] at hNonneg
      linarith
    · intro j
      have hLink := hy (openingRowConstraintEquiv (openingRowLink (n := n) j))
      rw [openingRowPrimalMatrixFin_mulVec_link] at hLink
      rw [openingRowPrimalRhsFin_link] at hLink
      exact hLink
  · rintro ⟨hSum, hNonneg, hLink⟩ row
    cases hsplit : openingRowConstraintEquiv.symm row with
      | inl s =>
          cases s with
          | inl u =>
              fin_cases u
              have hr : row = openingRowConstraintEquiv (openingRowSumUpper (n := n)) := by
                simpa [openingRowSumUpper, hsplit] using
                  (openingRowConstraintEquiv.apply_symm_apply row).symm
              rw [hr, openingRowPrimalMatrixFin_mulVec_sumUpper, openingRowPrimalRhsFin_sumUpper]
              exact le_of_eq hSum
          | inr u =>
              fin_cases u
              have hr : row = openingRowConstraintEquiv (openingRowSumLower (n := n)) := by
                simpa [openingRowSumLower, hsplit] using
                  (openingRowConstraintEquiv.apply_symm_apply row).symm
              rw [hr, openingRowPrimalMatrixFin_mulVec_sumLower, openingRowPrimalRhsFin_sumLower]
              have hLower : -(∑ j, y j) ≤ (-1 : ℝ) := by
                linarith [hSum]
              exact hLower
      | inr s =>
          cases s with
          | inl j =>
              have hr : row = openingRowConstraintEquiv (openingRowLink (n := n) j) := by
                simpa [openingRowLink, hsplit] using
                  (openingRowConstraintEquiv.apply_symm_apply row).symm
              rw [hr, openingRowPrimalMatrixFin_mulVec_link, openingRowPrimalRhsFin_link]
              exact hLink j
          | inr j =>
              have hr : row = openingRowConstraintEquiv (openingRowNonneg (n := n) j) := by
                simpa [openingRowNonneg, hsplit] using
                  (openingRowConstraintEquiv.apply_symm_apply row).symm
              rw [hr, openingRowPrimalMatrixFin_mulVec_nonneg, openingRowPrimalRhsFin_nonneg]
              have hNeg : -y j ≤ (0 : ℝ) := by
                linarith [hNonneg j]
              exact hNeg

/-- Helper for Exercise 8.13: any source-feasible row dual pair yields a generic LP dual witness
for the row LP. -/
lemma rowOpeningDualFeasible_toLinearDualFeasible
    (r : Fin n → ℝ)
    {u : Fin n → ℝ}
    {v : ℝ}
    (huv : IsFeasibleOpeningRowDualSolution r u v) :
    openingRowLinearDualOfSourceFin (n := n) r u v ∈
      dual_feasible_region (openingRowPrimalMatrixFin (n := n)) r := by
  rcases huv with ⟨huNonneg, hcover⟩
  rw [mem_dual_feasible_region_iff]
  refine ⟨?_, ?_⟩
  · ext j
    -- Evaluate the transported dual row equation at column `j` and collapse the split `v` parts.
    rw [openingRowPrimalMatrixFin_vecMul_link]
    rw [openingRowLinearDualOfSourceFin_sumUpper, openingRowLinearDualOfSourceFin_sumLower,
      openingRowLinearDualOfSourceFin_link, openingRowLinearDualOfSourceFin_nonneg]
    rw [max_sub_max_neg_eq_self]
    ring
  · intro row
    cases hsplit : openingRowConstraintEquiv.symm row with
      | inl s =>
          cases s with
          | inl u0 =>
              fin_cases u0
              -- The positive part `max v 0` is nonnegative.
              rw [show row = openingRowConstraintEquiv (openingRowSumUpper (n := n)) by
                    simpa [openingRowSumUpper, hsplit] using
                      (openingRowConstraintEquiv.apply_symm_apply row).symm]
              rw [openingRowLinearDualOfSourceFin_sumUpper]
              exact le_max_right v 0
          | inr u0 =>
              fin_cases u0
              -- The negative part `max (-v) 0` is also nonnegative.
              rw [show row = openingRowConstraintEquiv (openingRowSumLower (n := n)) by
                    simpa [openingRowSumLower, hsplit] using
                      (openingRowConstraintEquiv.apply_symm_apply row).symm]
              rw [openingRowLinearDualOfSourceFin_sumLower]
              exact le_max_right (-v) 0
      | inr s =>
          cases s with
          | inl j =>
              -- The transported linking block inherits nonnegativity from the
              -- source multiplier `u`.
              rw [show row = openingRowConstraintEquiv (openingRowLink (n := n) j) by
                    simpa [openingRowLink, hsplit] using
                      (openingRowConstraintEquiv.apply_symm_apply row).symm]
              rw [openingRowLinearDualOfSourceFin_link]
              exact huNonneg j
          | inr j =>
              -- The slack block is exactly `v + u_j - r_j`, which is
              -- nonnegative by row feasibility.
              have hslack : 0 ≤ v + u j - r j := by
                linarith [hcover j]
              rw [show row = openingRowConstraintEquiv (openingRowNonneg (n := n) j) by
                    simpa [openingRowNonneg, hsplit] using
                      (openingRowConstraintEquiv.apply_symm_apply row).symm]
              rw [openingRowLinearDualOfSourceFin_nonneg]
              exact hslack

/-- Helper for Exercise 8.13: the generic LP dual objective of the lifted row witness is exactly
the source row dual objective. -/
lemma openingRowLinearDualOfSource_objective
    {x : Fin n → ℝ}
    (r : Fin n → ℝ)
    (u : Fin n → ℝ)
    (v : ℝ) :
    (openingRowLinearDualOfSourceFin (n := n) r u v) ⬝ᵥ openingRowPrimalRhsFin x =
      openingRowDualObjective x u v := by
  rw [dotProduct]
  calc
    ∑ row : Fin ((1 + 1) + (n + n)),
        openingRowLinearDualOfSourceFin (n := n) r u v row * openingRowPrimalRhsFin x row
        =
          ∑ row : openingRowConstraint n,
            openingRowLinearDualOfSource (n := n) r u v row * openingRowPrimalRhs x row := by
              symm
              exact Fintype.sum_equiv openingRowConstraintEquiv _ _ fun row ↦ by
                simp [openingRowLinearDualOfSourceFin, openingRowPrimalRhsFin]
    _ = openingRowDualObjective x u v := by
      -- Reindex to the four native row blocks and simplify the split objective once.
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp [openingRowLinearDualOfSource, openingRowPrimalRhs, openingRowDualObjective]
      have hsplitV : max v 0 + -max (-v) 0 = v := by
        simpa [sub_eq_add_neg] using max_sub_max_neg_eq_self v
      rw [hsplitV]

/-- Helper for Exercise 8.13: every generic LP dual witness for the row LP transports back to a
source-feasible row pair. -/
lemma linearDualFeasible_toRowOpeningDualFeasible
    {r : Fin n → ℝ}
    {w : Fin ((1 + 1) + (n + n)) → ℝ}
    (hw : w ∈ dual_feasible_region (openingRowPrimalMatrixFin (n := n)) r) :
    IsFeasibleOpeningRowDualSolution r
      (openingRowSourceDualUOfLinear (n := n) w)
      (openingRowSourceDualVOfLinear (n := n) w) := by
  rcases (mem_dual_feasible_region_iff
      (openingRowPrimalMatrixFin (n := n)) r w).mp hw with ⟨hwEq, hwNonneg⟩
  refine ⟨?_, ?_⟩
  · intro j
    -- The recovered source multiplier is read directly from the transported linking block.
    simpa [openingRowSourceDualUOfLinear] using
      hwNonneg (openingRowConstraintEquiv (openingRowLink (n := n) j))
  · intro j
    have hEqj := congrFun hwEq j
    rw [openingRowPrimalMatrixFin_vecMul_link] at hEqj
    have hSlack :
        0 ≤ w (openingRowConstraintEquiv (openingRowNonneg (n := n) j)) := by
      exact hwNonneg (openingRowConstraintEquiv (openingRowNonneg (n := n) j))
    have hUpper :
        r j ≤
          w (openingRowConstraintEquiv (openingRowSumUpper (n := n))) -
            w (openingRowConstraintEquiv (openingRowSumLower (n := n))) +
              w (openingRowConstraintEquiv (openingRowLink (n := n) j)) := by
      linarith [hEqj, hSlack]
    -- The nonnegativity of the slack block converts the equality into the source inequality.
    simpa [openingRowSourceDualVOfLinear, openingRowSourceDualUOfLinear, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using hUpper

/-- Helper for Exercise 8.13: replacing one customer row changes the global dual objective by
replacing exactly that row's source contribution. -/
lemma openingDualObjective_updateRow
    (f : Fin n → ℝ)
    {x : Fin n → ℝ}
    (u : Fin m → Fin n → ℝ)
    (v : Fin m → ℝ)
    (i : Fin m)
    (uRow : Fin n → ℝ)
    (vRow : ℝ) :
    uncapacitated_facility_location_opening_dual_objective f x
      (Function.update u i uRow)
      (Function.update v i vRow) =
      uncapacitated_facility_location_opening_dual_objective f x u v -
        openingRowDualObjective x (fun j ↦ u i j) (v i) +
          openingRowDualObjective x uRow vRow := by
  let eraseRows : Finset (Fin m) := Finset.univ.erase i
  let eraseColumnSum : Fin n → ℝ := fun j ↦ eraseRows.sum (fun k ↦ u k j)
  have hVsplit :
      (∑ k : Fin m, v k) = eraseRows.sum (fun k ↦ v k) + v i := by
    dsimp [eraseRows]
    exact (Finset.sum_erase_add (s := Finset.univ) (f := fun k : Fin m ↦ v k)
      (Finset.mem_univ i)).symm
  have hVupdateErase :
      (∑ k : Fin m, Function.update v i vRow k) = eraseRows.sum (fun k ↦ v k) + vRow := by
    calc
      ∑ k : Fin m, Function.update v i vRow k =
          eraseRows.sum (fun k ↦ Function.update v i vRow k) + Function.update v i vRow i := by
            dsimp [eraseRows]
            exact (Finset.sum_erase_add (s := Finset.univ)
              (f := fun k : Fin m ↦ Function.update v i vRow k) (Finset.mem_univ i)).symm
      _ = eraseRows.sum (fun k ↦ v k) + vRow := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro k hk
              have hk' : k ∈ Finset.univ.erase i := by
                simpa [eraseRows] using hk
              have hkne : k ≠ i := (Finset.mem_erase.mp hk').1
              simp [Function.update, hkne]
            · simp [Function.update]
  have hVupdate :
      (∑ k : Fin m, Function.update v i vRow k) = ∑ k : Fin m, v k - v i + vRow := by
    calc
      (∑ k : Fin m, Function.update v i vRow k) = eraseRows.sum (fun k ↦ v k) + vRow :=
        hVupdateErase
      _ = ∑ k : Fin m, v k - v i + vRow := by
            linarith [hVsplit]
  have hUold :
      ∀ j : Fin n, (∑ k : Fin m, u k j) = eraseColumnSum j + u i j := by
    intro j
    dsimp [eraseColumnSum, eraseRows]
    exact (Finset.sum_erase_add (s := Finset.univ)
      (f := fun k : Fin m ↦ u k j) (Finset.mem_univ i)).symm
  have hUupdateErase :
      ∀ j : Fin n, (∑ k : Fin m, Function.update u i uRow k j) = eraseColumnSum j + uRow j := by
    intro j
    calc
      ∑ k : Fin m, Function.update u i uRow k j =
          eraseRows.sum (fun k ↦ Function.update u i uRow k j) +
            Function.update u i uRow i j := by
            dsimp [eraseRows]
            exact (Finset.sum_erase_add (s := Finset.univ)
              (f := fun k : Fin m ↦ Function.update u i uRow k j) (Finset.mem_univ i)).symm
      _ = eraseColumnSum j + uRow j := by
            dsimp [eraseColumnSum]
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro k hk
              have hk' : k ∈ Finset.univ.erase i := by
                simpa [eraseRows] using hk
              have hkne : k ≠ i := (Finset.mem_erase.mp hk').1
              simp [Function.update, hkne]
            · simp [Function.update]
  have hUupdate :
      ∀ j : Fin n, (∑ k : Fin m, Function.update u i uRow k j) =
        ∑ k : Fin m, u k j - u i j + uRow j := by
    intro j
    calc
      (∑ k : Fin m, Function.update u i uRow k j) = eraseColumnSum j + uRow j := hUupdateErase j
      _ = ∑ k : Fin m, u k j - u i j + uRow j := by
            linarith [hUold j]
  have hObjOld :
      ∑ j : Fin n, ((∑ k : Fin m, u k j) - f j) * x j =
        ∑ j : Fin n, ((eraseColumnSum j + u i j - f j) * x j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hUold j]
  have hObjUpdate :
      ∑ j : Fin n, ((∑ k : Fin m, Function.update u i uRow k j) - f j) * x j =
        ∑ j : Fin n, ((eraseColumnSum j + uRow j - f j) * x j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hUupdate j, hUold j]
    ring
  have hObjReplace :
      ∑ j : Fin n, ((eraseColumnSum j + uRow j - f j) * x j) =
        ∑ j : Fin n, ((eraseColumnSum j + u i j - f j) * x j) -
          ∑ j : Fin n, u i j * x j + ∑ j : Fin n, uRow j * x j := by
    have hNegSum :
        ∑ j : Fin n, -u i j * x j = -∑ j : Fin n, u i j * x j := by
      calc
        ∑ j : Fin n, -u i j * x j = ∑ j : Fin n, -(u i j * x j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
        _ = -∑ j : Fin n, u i j * x j := by
              rw [Finset.sum_neg_distrib]
    calc
      ∑ j : Fin n, ((eraseColumnSum j + uRow j - f j) * x j)
          =
            ∑ j : Fin n,
              (((eraseColumnSum j + u i j - f j) * x j) - u i j * x j + uRow j * x j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = ∑ j : Fin n, ((eraseColumnSum j + u i j - f j) * x j) +
            ∑ j : Fin n, (-u i j * x j + uRow j * x j) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = ∑ j : Fin n, ((eraseColumnSum j + u i j - f j) * x j) +
            (∑ j : Fin n, -u i j * x j + ∑ j : Fin n, uRow j * x j) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ j : Fin n, ((eraseColumnSum j + u i j - f j) * x j) -
            ∑ j : Fin n, u i j * x j + ∑ j : Fin n, uRow j * x j := by
              rw [hNegSum]
              ring
  unfold uncapacitated_facility_location_opening_dual_objective openingRowDualObjective
  rw [hVupdate, hObjUpdate, hObjOld, hObjReplace]
  -- After isolating the replaced row in the outer sum and column sums, the
  -- remainder is ring algebra.
  ring

/-- Helper for Exercise 8.13: the source row objective recovered from a generic LP dual witness
matches the generic LP dual objective. -/
lemma openingRowSourceDualOfLinear_objective
    {x : Fin n → ℝ}
    (w : Fin ((1 + 1) + (n + n)) → ℝ) :
    openingRowDualObjective x
      (openingRowSourceDualUOfLinear (n := n) w)
      (openingRowSourceDualVOfLinear (n := n) w) =
      w ⬝ᵥ openingRowPrimalRhsFin x := by
  simp only [openingRowDualObjective, openingRowSourceDualUOfLinear,
    openingRowSourceDualVOfLinear, dotProduct, Nat.reduceAdd]
  calc
    w (openingRowConstraintEquiv (openingRowSumUpper (n := n))) -
        w (openingRowConstraintEquiv (openingRowSumLower (n := n))) +
          ∑ j : Fin n, w (openingRowConstraintEquiv (openingRowLink (n := n) j)) * x j
        =
          ∑ row : openingRowConstraint n, w (openingRowConstraintEquiv row) *
            openingRowPrimalRhs x row := by
              rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
              simp [openingRowPrimalRhs, openingRowSumUpper, openingRowSumLower, openingRowLink]
              ring
    _ = ∑ row : Fin ((1 + 1) + (n + n)), w row * openingRowPrimalRhsFin x row := by
          exact Fintype.sum_equiv openingRowConstraintEquiv _ _ fun row ↦ by
            simp [openingRowPrimalRhsFin]

/-- Helper for Exercise 8.13: global optimality of `(u,v)` implies rowwise optimality when only
one customer row is replaced. -/
lemma rowDualOptimality_of_globalOpeningDualOptimality
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    {x : Fin n → ℝ}
    {u : Fin m → Fin n → ℝ}
    {v : Fin m → ℝ}
    (huv : IsOptimalFacilityLocationOpeningDualSolution c f x u v)
    (i : Fin m) :
    ∀ {uRow : Fin n → ℝ} {vRow : ℝ},
      IsFeasibleOpeningRowDualSolution (fun j ↦ c i j) uRow vRow →
        openingRowDualObjective x (fun j ↦ u i j) (v i) ≤
          openingRowDualObjective x uRow vRow := by
  intro uRow vRow hRowFeasible
  let u' : Fin m → Fin n → ℝ := Function.update u i uRow
  let v' : Fin m → ℝ := Function.update v i vRow
  have hfeasible' : IsFeasibleFacilityLocationOpeningDualSolution c u' v' := by
    refine ⟨?_, ?_⟩
    · intro i' j
      by_cases hi' : i' = i
      · subst hi'
        simpa [u', Function.update] using hRowFeasible.1 j
      · simpa [u', Function.update, hi'] using huv.feasible.1 i' j
    · intro i' j
      by_cases hi' : i' = i
      · subst hi'
        simpa [u', v', Function.update] using hRowFeasible.2 j
      · simpa [u', v', Function.update, hi'] using huv.feasible.2 i' j
  have hoptGlobal :
      uncapacitated_facility_location_opening_dual_objective f x u v ≤
        uncapacitated_facility_location_opening_dual_objective f x u' v' :=
    huv.2 u' v' hfeasible'
  have hold :
      uncapacitated_facility_location_opening_dual_objective f x u v =
        uncapacitated_facility_location_opening_dual_objective f x u v -
          openingRowDualObjective x (fun j ↦ u i j) (v i) +
            openingRowDualObjective x (fun j ↦ u i j) (v i) := by
    ring
  rw [openingDualObjective_updateRow (m := m) (n := n) f u v i uRow vRow] at hoptGlobal
  -- Replacing only row `i` turns global optimality into the desired rowwise optimality inequality.
  linarith [hold]

/-- Helper for Exercise 8.13: rowwise strong duality produces a feasible row assignment attaining
the value of any source-optimal row dual pair. -/
lemma exists_rowAssignment_eq_rowDualObjective_of_optimalDual
    {x : Fin n → ℝ}
    (hx : x ∈ uncapacitated_facility_location_opening_domain)
    (r : Fin n → ℝ)
    {u : Fin n → ℝ}
    {v : ℝ}
    (hOptimal :
      ∀ {uRow : Fin n → ℝ} {vRow : ℝ},
        IsFeasibleOpeningRowDualSolution r uRow vRow →
          openingRowDualObjective x u v ≤ openingRowDualObjective x uRow vRow)
    (hFeasible : IsFeasibleOpeningRowDualSolution r u v) :
    ∃ y : Fin n → ℝ,
      (∑ j, y j = 1) ∧
        (∀ j, 0 ≤ y j) ∧
        (∀ j, y j ≤ x j) ∧
        (∑ j, r j * y j = openingRowDualObjective x u v) := by
  have hPrimalNonempty :
      Set.Nonempty
        (primal_feasible_region (openingRowPrimalMatrixFin (n := n)) (openingRowPrimalRhsFin x)) :=
    by
      rcases openingAssignmentFeasible_nonempty (m := 1) hx with ⟨y0, hy0⟩
      rcases (mem_uncapacitated_facility_location_assignment_feasible_set_iff.mp hy0) with
        ⟨hrow0, hnonneg0, hlink0⟩
      refine ⟨fun j ↦ y0 0 j, ?_⟩
      rw [mem_openingRowPrimalFeasible_iff]
      exact ⟨hrow0 0, hnonneg0 0, hlink0 0⟩
  have hDualNonempty :
      Set.Nonempty
        (dual_feasible_region (openingRowPrimalMatrixFin (n := n)) r) := by
      exact ⟨openingRowLinearDualOfSourceFin (n := n) r u v,
        rowOpeningDualFeasible_toLinearDualFeasible (n := n) r hFeasible⟩
  rcases exists_optimal_primal_dual_pair
      (openingRowPrimalMatrixFin (n := n))
      (openingRowPrimalRhsFin x)
      r
      hPrimalNonempty
      hDualNonempty with
    ⟨yStar, hyStar, wStar, hwStar, hStrong, _, hLeast⟩
  have hRecoveredFeasible :
      IsFeasibleOpeningRowDualSolution r
        (openingRowSourceDualUOfLinear (n := n) wStar)
        (openingRowSourceDualVOfLinear (n := n) wStar) :=
    linearDualFeasible_toRowOpeningDualFeasible (n := n) hwStar
  have hUpper :
      openingRowDualObjective x u v ≤
        openingRowDualObjective x
          (openingRowSourceDualUOfLinear (n := n) wStar)
          (openingRowSourceDualVOfLinear (n := n) wStar) :=
    hOptimal hRecoveredFeasible
  have hLower :
      openingRowDualObjective x
          (openingRowSourceDualUOfLinear (n := n) wStar)
          (openingRowSourceDualVOfLinear (n := n) wStar) ≤
        openingRowDualObjective x u v := by
    have hwGiven :
        openingRowLinearDualOfSourceFin (n := n) r u v ∈
          dual_feasible_region (openingRowPrimalMatrixFin (n := n)) r :=
      rowOpeningDualFeasible_toLinearDualFeasible (n := n) r hFeasible
    have hLeastValue :
        wStar ⬝ᵥ openingRowPrimalRhsFin x ≤
          (openingRowLinearDualOfSourceFin (n := n) r u v) ⬝ᵥ openingRowPrimalRhsFin x :=
      hLeast.2 ⟨openingRowLinearDualOfSourceFin (n := n) r u v, hwGiven, rfl⟩
    calc
      openingRowDualObjective x
          (openingRowSourceDualUOfLinear (n := n) wStar)
          (openingRowSourceDualVOfLinear (n := n) wStar)
          = wStar ⬝ᵥ openingRowPrimalRhsFin x :=
            openingRowSourceDualOfLinear_objective (n := n) (x := x) wStar
      _ ≤ (openingRowLinearDualOfSourceFin (n := n) r u v) ⬝ᵥ openingRowPrimalRhsFin x :=
            hLeastValue
      _ = openingRowDualObjective x u v :=
            openingRowLinearDualOfSource_objective (n := n) (x := x) r u v
  have hDualEq :
      openingRowDualObjective x
          (openingRowSourceDualUOfLinear (n := n) wStar)
          (openingRowSourceDualVOfLinear (n := n) wStar) =
        openingRowDualObjective x u v :=
    le_antisymm hLower hUpper
  rcases (mem_openingRowPrimalFeasible_iff (n := n) (x := x) (y := yStar)).mp hyStar with
    ⟨hSumStar, hNonnegStar, hLinkStar⟩
  refine ⟨yStar, hSumStar, hNonnegStar, hLinkStar, ?_⟩
  calc
    ∑ j, r j * yStar j = wStar ⬝ᵥ openingRowPrimalRhsFin x := by
      simpa [dotProduct] using hStrong
    _ = openingRowDualObjective x
          (openingRowSourceDualUOfLinear (n := n) wStar)
          (openingRowSourceDualVOfLinear (n := n) wStar) := by
            symm
            exact openingRowSourceDualOfLinear_objective (n := n) (x := x) wStar
    _ = openingRowDualObjective x u v := hDualEq

/-- Helper for Exercise 8.13: if each customer row objective matches the corresponding row dual
value, then the assembled opening objective equals the global dual objective. -/
lemma openingObjective_eq_dualObjective_of_rowEqualities
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ}
    {u : Fin m → Fin n → ℝ}
    {v : Fin m → ℝ}
    (hrow :
      ∀ i, ∑ j, c i j * y i j = v i + ∑ j, u i j * x j) :
    uncapacitated_facility_location_opening_objective c f x y =
      uncapacitated_facility_location_opening_dual_objective f x u v := by
  have hrows :
      ∑ i, ∑ j, c i j * y i j = ∑ i, (v i + ∑ j, u i j * x j) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hrow i
  have huRows :
      ∑ i, ∑ j, u i j * x j = ∑ j, (∑ i, u i j) * x j := by
    calc
      ∑ i, ∑ j, u i j * x j = ∑ j, ∑ i, u i j * x j := by
        rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, u i j) * x j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [← Finset.sum_mul]
  change facilityLocationObjective c f (y, x) =
    uncapacitated_facility_location_opening_dual_objective f x u v
  rw [facilityLocationObjective_mk]
  calc
    (∑ i, ∑ j, c i j * y i j) - ∑ j, f j * x j
        = (∑ i, (v i + ∑ j, u i j * x j)) - ∑ j, f j * x j := by
            rw [hrows]
    _ = (∑ i, v i) + ∑ i, ∑ j, u i j * x j - ∑ j, f j * x j := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i, v i) + ∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j := by
          rw [huRows]
    _ = uncapacitated_facility_location_opening_dual_objective f x u v := by
          have hassoc :
              (∑ i, v i) + ∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j =
                (∑ i, v i) + (∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j) := by
            ring
          have hsum :
              ∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j =
                ∑ j, (((∑ i, u i j) - f j) * x j) := by
            calc
              ∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j
                  = ∑ j, (∑ i, u i j) * x j + ∑ j, -(f j * x j) := by
                      rw [sub_eq_add_neg, Finset.sum_neg_distrib]
              _ = ∑ j, (((∑ i, u i j) * x j) + -(f j * x j)) := by
                    rw [← Finset.sum_add_distrib]
              _ = ∑ j, (((∑ i, u i j) - f j) * x j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    ring
          calc
            (∑ i, v i) + ∑ j, (∑ i, u i j) * x j - ∑ j, f j * x j
                = (∑ i, v i) + ∑ j, (((∑ i, u i j) - f j) * x j) := by
                    rw [hassoc, hsum]
            _ = uncapacitated_facility_location_opening_dual_objective f x u v := by
                  rfl

/-- Helper for Exercise 8.13: at an opening vector `x ∈ S`, an optimal dual pair `(u,v)` must
attain the opening value, i.e. the source weak-duality upper bound is tight. -/
lemma openingValue_eq_dualObjective_of_optimalDualSolution
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ uncapacitated_facility_location_opening_domain)
    {u : Fin m → Fin n → ℝ}
    {v : Fin m → ℝ}
    (huv : IsOptimalFacilityLocationOpeningDualSolution c f x u v) :
    uncapacitated_facility_location_opening_value c f x =
      uncapacitated_facility_location_opening_dual_objective f x u v := by
  classical
  have hRowWitness :
      ∀ i : Fin m,
        ∃ yRow : Fin n → ℝ,
          (∑ j, yRow j = 1) ∧
            (∀ j, 0 ≤ yRow j) ∧
            (∀ j, yRow j ≤ x j) ∧
            (∑ j, c i j * yRow j =
              openingRowDualObjective x (fun j ↦ u i j) (v i)) := by
    intro i
    have hRowFeasible :
        IsFeasibleOpeningRowDualSolution (fun j ↦ c i j) (fun j ↦ u i j) (v i) := by
      exact ⟨fun j ↦ huv.feasible.1 i j, fun j ↦ huv.feasible.2 i j⟩
    have hRowOptimal :
        ∀ {uRow : Fin n → ℝ} {vRow : ℝ},
          IsFeasibleOpeningRowDualSolution (fun j ↦ c i j) uRow vRow →
            openingRowDualObjective x (fun j ↦ u i j) (v i) ≤
              openingRowDualObjective x uRow vRow :=
      rowDualOptimality_of_globalOpeningDualOptimality (m := m) (n := n) c f huv i
    exact exists_rowAssignment_eq_rowDualObjective_of_optimalDual
      (n := n) hx (fun j ↦ c i j) hRowOptimal hRowFeasible
  choose y hsum hnonneg hlink hrowEq using hRowWitness
  have hyFeasible : y ∈ uncapacitated_facility_location_assignment_feasible_set x := by
    rw [mem_uncapacitated_facility_location_assignment_feasible_set_iff]
    exact ⟨hsum, hnonneg, hlink⟩
  have hrowObjective :
      ∀ i, ∑ j, c i j * y i j = v i + ∑ j, u i j * x j := by
    intro i
    simpa [openingRowDualObjective] using hrowEq i
  let imageSet : Set ℝ :=
    ((fun y' : Fin m → Fin n → ℝ ↦
        uncapacitated_facility_location_opening_objective c f x y') ''
      uncapacitated_facility_location_assignment_feasible_set x)
  have hImageBdd : BddAbove imageSet := by
    refine ⟨(∑ i, ∑ j, |c i j|) + ∑ j, |f j|, ?_⟩
    rintro _ ⟨y', hy', rfl⟩
    exact openingObjective_le_absBound c f hx hy'
  have hLower :
      uncapacitated_facility_location_opening_dual_objective f x u v ≤
        uncapacitated_facility_location_opening_value c f x := by
    calc
      uncapacitated_facility_location_opening_dual_objective f x u v =
          uncapacitated_facility_location_opening_objective c f x y := by
            symm
            exact openingObjective_eq_dualObjective_of_rowEqualities c f hrowObjective
      _ ≤ uncapacitated_facility_location_opening_value c f x := by
            rw [uncapacitated_facility_location_opening_value_eq_sSup]
            exact le_csSup hImageBdd ⟨y, hyFeasible, rfl⟩
  exact le_antisymm
    (openingValue_le_dualObjective_of_feasibleDual c f hx huv.feasible)
    hLower

/-- Helper for Exercise 8.13: the generic LP dual objective of the lifted row witness is exactly
the source row dual objective. -/
lemma openingRowLinearDualOfSource_objective
    {x : Fin n → ℝ}
    (r : Fin n → ℝ)
    (u : Fin n → ℝ)
    (v : ℝ) :
    (openingRowLinearDualOfSourceFin (n := n) r u v) ⬝ᵥ openingRowPrimalRhsFin x =
      openingRowDualObjective x u v := by
  rw [dotProduct]
  calc
    ∑ row : Fin ((1 + 1) + (n + n)),
        openingRowLinearDualOfSourceFin (n := n) r u v row * openingRowPrimalRhsFin x row
        =
          ∑ row : openingRowConstraint n,
            openingRowLinearDualOfSource (n := n) r u v row * openingRowPrimalRhs x row := by
              symm
              exact Fintype.sum_equiv openingRowConstraintEquiv _ _ fun row ↦ by
                simp [openingRowLinearDualOfSourceFin, openingRowPrimalRhsFin]
    _ = openingRowDualObjective x u v := by
      -- Reindex to the four native row blocks and simplify the split objective once.
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp [openingRowLinearDualOfSource, openingRowPrimalRhs, openingRowDualObjective]
      have hsplitV : max v 0 + -max (-v) 0 = v := by
        simpa [sub_eq_add_neg] using max_sub_max_neg_eq_self v
      rw [hsplitV]

/-- Helper for Exercise 8.13: changing the opening vector from `x` to `x'` shifts the opening-dual
objective by the affine offset induced by `facility_location_opening_dual_subgradient f u`. -/
lemma openingDualObjective_eq_base_add_subgradientOffset
    (f : Fin n → ℝ)
    (x x' : Fin n → ℝ)
    (u : Fin m → Fin n → ℝ)
    (v : Fin m → ℝ) :
    uncapacitated_facility_location_opening_dual_objective f x' u v =
      uncapacitated_facility_location_opening_dual_objective f x u v +
        ∑ j, facility_location_opening_dual_subgradient f u j * (x' j - x j) := by
  let g : Fin n → ℝ := facility_location_opening_dual_subgradient f u
  have hsplit :
      ∑ j, g j * x' j = ∑ j, g j * x j + ∑ j, g j * (x' j - x j) := by
    -- Split each comparison-point term into the base-point contribution plus the affine offset.
    calc
      ∑ j, g j * x' j = ∑ j, (g j * x j + g j * (x' j - x j)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ = ∑ j, g j * x j + ∑ j, g j * (x' j - x j) := by
        rw [Finset.sum_add_distrib]
  -- Rewrite the dual objective once in terms of the subgradient coordinates and regroup.
  calc
    uncapacitated_facility_location_opening_dual_objective f x' u v =
        (∑ i, v i) + ∑ j, g j * x' j := by
          simp [uncapacitated_facility_location_opening_dual_objective, g,
            facility_location_opening_dual_subgradient_apply]
    _ = (∑ i, v i) + (∑ j, g j * x j + ∑ j, g j * (x' j - x j)) := by
          rw [hsplit]
    _ = ((∑ i, v i) + ∑ j, g j * x j) + ∑ j, g j * (x' j - x j) := by
          ring
    _ = uncapacitated_facility_location_opening_dual_objective f x u v +
          ∑ j, facility_location_opening_dual_subgradient f u j * (x' j - x j) := by
          simp [uncapacitated_facility_location_opening_dual_objective, g,
            facility_location_opening_dual_subgradient_apply]

/-- Helper for Exercise 8.13: if `(u,v)` is optimal at the base point `x`, then the comparison
dual objective at `x'` equals `z(x)` plus the same affine subgradient offset. -/
lemma openingDualObjective_eq_value_add_subgradientOffset_of_optimalDual
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ uncapacitated_facility_location_opening_domain)
    {u : Fin m → Fin n → ℝ}
    {v : Fin m → ℝ}
    (huv : IsOptimalFacilityLocationOpeningDualSolution c f x u v)
    (x' : Fin n → ℝ) :
    uncapacitated_facility_location_opening_dual_objective f x' u v =
      uncapacitated_facility_location_opening_value c f x +
        ∑ j, facility_location_opening_dual_subgradient f u j * (x' j - x j) := by
  -- Transport the affine rewrite through optimal-dual tightness at the base point.
  calc
    uncapacitated_facility_location_opening_dual_objective f x' u v =
        uncapacitated_facility_location_opening_dual_objective f x u v +
          ∑ j, facility_location_opening_dual_subgradient f u j * (x' j - x j) :=
      openingDualObjective_eq_base_add_subgradientOffset f x x' u v
    _ = uncapacitated_facility_location_opening_value c f x +
          ∑ j, facility_location_opening_dual_subgradient f u j * (x' j - x j) := by
            rw [← openingValue_eq_dualObjective_of_optimalDualSolution c f hx huv]

/-- Helper for Exercise 8.13: weak duality at a comparison point combined with optimal-dual
tightness at the base point yields the source affine subgradient inequality. -/
lemma openingValue_le_value_add_subgradient_of_optimalDual
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ uncapacitated_facility_location_opening_domain)
    {u : Fin m → Fin n → ℝ}
    {v : Fin m → ℝ}
    (huv : IsOptimalFacilityLocationOpeningDualSolution c f x u v)
    {x' : Fin n → ℝ}
    (hx' : x' ∈ uncapacitated_facility_location_opening_domain) :
    uncapacitated_facility_location_opening_value c f x' ≤
      uncapacitated_facility_location_opening_value c f x +
        ∑ j, facility_location_opening_dual_subgradient f u j * (x' j - x j) := by
  -- Compare `z(x')` to the feasible dual objective at `x'`, then rewrite that dual objective
  -- using the optimal-dual certificate at `x`.
  calc
    uncapacitated_facility_location_opening_value c f x' ≤
        uncapacitated_facility_location_opening_dual_objective f x' u v :=
      openingValue_le_dualObjective_of_feasibleDual c f hx' huv.feasible
    _ = uncapacitated_facility_location_opening_value c f x +
          ∑ j, facility_location_opening_dual_subgradient f u j * (x' j - x j) :=
      openingDualObjective_eq_value_add_subgradientOffset_of_optimalDual c f hx huv x'

/-- Exercise 8.13 (2). If `(u,v)` is an optimal dual solution for the value function at a point
`x ∈ S`, then the vector with coordinates `∑_i u_ij - f_j` is a subgradient of `z` at `x`. -/
theorem facility_location_opening_dual_subgradient_is_subgradient
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ uncapacitated_facility_location_opening_domain)
    {u : Fin m → Fin n → ℝ}
    {v : Fin m → ℝ}
    (huv : IsOptimalFacilityLocationOpeningDualSolution c f x u v) :
    IsConcaveSubgradientAt
      (uncapacitated_facility_location_opening_value c f)
      uncapacitated_facility_location_opening_domain
      x
      (facility_location_opening_dual_subgradient f u) := by
  -- Route correction: package the affine normalization into helper lemmas so the final theorem
  -- only invokes weak duality and the base-point optimal-dual identity.
  rw [isConcaveSubgradientAt_iff]
  intro x' hx'
  -- The standalone pointwise inequality is exactly the source-facing subgradient condition.
  exact openingValue_le_value_add_subgradient_of_optimalDual c f hx huv hx'

/-- Helper for Exercise 8.13: the Euclidean distance on `Fin n → ℝ`, realized through the
canonical `toLp 2` embedding into `EuclideanSpace ℝ (Fin n)`. -/
noncomputable abbrev euclideanDist
    (x y : Fin n → ℝ) : ℝ :=
  dist (toLp 2 x) (toLp 2 y)

/-- Helper for Exercise 8.13: a projection operator onto `P` together with the Euclidean distance
nonexpansiveness property used by projected subgradient steps. -/
structure ProjectionOnto (P : Set (Fin n → ℝ)) where
  toFun : (Fin n → ℝ) → (Fin n → ℝ)
  mapsTo : Set.MapsTo toFun Set.univ P
  dist_le : ∀ x y, y ∈ P → euclideanDist (toFun x) y ≤ euclideanDist x y

namespace ProjectionOnto

/-- Helper for Exercise 8.13: a projection operator onto `P` is used as a function on ambient
vectors. -/
instance (P : Set (Fin n → ℝ)) :
    CoeFun (ProjectionOnto P) (fun _ ↦ (Fin n → ℝ) → (Fin n → ℝ)) where
  coe proj := proj.toFun

end ProjectionOnto

/-- Helper for Exercise 8.13: one projected subgradient step from `x` with chosen subgradient
`s` and stepsize `α`. -/
def projected_subgradient_step
    {P : Set (Fin n → ℝ)}
    (proj : ProjectionOnto P)
    (x s : Fin n → ℝ)
    (α : ℝ) : Fin n → ℝ :=
  proj (fun i ↦ x i - α * s i)

/-- `x_next` is a Euclidean projection of `w` onto the opening domain `S` when it belongs to `S`
and minimizes the Chapter 8 Euclidean distance `euclideanDist` to `w` among all points of `S`. -/
def IsEuclideanProjectionOnFacilityLocationOpeningDomain
    (x_next w : Fin n → ℝ) : Prop :=
  x_next ∈ uncapacitated_facility_location_opening_domain ∧
    ∀ y : Fin n → ℝ, y ∈ uncapacitated_facility_location_opening_domain →
      euclideanDist w x_next ≤ euclideanDist w y

namespace IsEuclideanProjectionOnFacilityLocationOpeningDomain

/-- A Euclidean projection onto the opening domain lies in the opening domain. -/
theorem mem
    {x_next w : Fin n → ℝ}
    (hproj : IsEuclideanProjectionOnFacilityLocationOpeningDomain x_next w) :
    x_next ∈ uncapacitated_facility_location_opening_domain :=
  hproj.1

end IsEuclideanProjectionOnFacilityLocationOpeningDomain

/-- The projected subgradient target `x + α g` built from the dual subgradient
`g_j = ∑_i u_ij - f_j`. -/
def facility_location_opening_projected_subgradient_target
    (f : Fin n → ℝ)
    (x : Fin n → ℝ)
    (u : Fin m → Fin n → ℝ)
    (α : ℝ) : Fin n → ℝ :=
  fun j ↦ x j + α * facility_location_opening_dual_subgradient f u j

/-- Evaluating the projected-subgradient target at coordinate `j` expands to
`x_j + α (∑_i u_ij - f_j)`. -/
theorem facility_location_opening_projected_subgradient_target_apply
    (f : Fin n → ℝ)
    (x : Fin n → ℝ)
    (u : Fin m → Fin n → ℝ)
    (α : ℝ)
    (j : Fin n) :
    facility_location_opening_projected_subgradient_target f x u α j =
      x j + α * facility_location_opening_dual_subgradient f u j :=
  rfl

/-- Helper for Exercise 8.13: the generic projected subgradient method owner records an initial
point in `P` and the stagewise subgradient and projection update rules. -/
def IsProjectedSubgradientMethodSequence
    (g : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    (proj : ProjectionOnto P)
    (α : ℕ → ℝ)
    (x s : ℕ → Fin n → ℝ) : Prop :=
  x 0 ∈ P ∧
    ∀ t : ℕ,
      IsSubgradientAtOn g P (x t) (s t) ∧
        x (t + 1) = projected_subgradient_step proj (x t) (s t) (α t)

/-- Part (3) of Exercise 8.13. A projected subgradient-ascent sequence for `max_{x ∈ S} z(x)` is
given
by iterates `xᵗ ∈ S` together with dual-optimal multipliers `(uᵗ,vᵗ)` such that each next iterate
is a Euclidean projection onto `S` of `xᵗ + α_t gᵗ`, where
`gᵗ_j = ∑_i uᵗ_ij - f_j` is the subgradient from part `(2)`. -/
class IsFacilityLocationOpeningProjectedSubgradientAscentSequence
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (α : ℕ → ℝ)
    (x : ℕ → Fin n → ℝ)
    (u : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ) : Prop where
  /-- The initial iterate lies in the opening domain `S`. -/
  initial_mem : x 0 ∈ uncapacitated_facility_location_opening_domain
  /-- At each time `t`, the chosen dual multipliers are optimal for `xᵗ` and `xᵗ⁺¹` is the
  Euclidean projection of the projected-subgradient target back onto `S`. -/
  step :
    ∀ t : ℕ,
      IsOptimalFacilityLocationOpeningDualSolution c f (x t) (u t) (v t) ∧
        IsEuclideanProjectionOnFacilityLocationOpeningDomain
          (x (t + 1))
          (facility_location_opening_projected_subgradient_target f (x t) (u t) (α t))

/-- A projected subgradient-ascent sequence is a proposition, hence has the canonical
subsingleton instance expected for Prop-valued owner declarations. -/
instance instSubsingletonIsFacilityLocationOpeningProjectedSubgradientAscentSequence
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (α : ℕ → ℝ)
    (x : ℕ → Fin n → ℝ)
    (u : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ) :
    Subsingleton
      (IsFacilityLocationOpeningProjectedSubgradientAscentSequence c f α x u v) := by
  infer_instance

/-- Unfolding `IsFacilityLocationOpeningProjectedSubgradientAscentSequence` recovers the initial
feasibility condition together with the stagewise optimal-dual and projection clauses. -/
theorem isFacilityLocationOpeningProjectedSubgradientAscentSequence_iff
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (α : ℕ → ℝ)
    (x : ℕ → Fin n → ℝ)
    (u : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ) :
    IsFacilityLocationOpeningProjectedSubgradientAscentSequence c f α x u v ↔
      x 0 ∈ uncapacitated_facility_location_opening_domain ∧
        ∀ t : ℕ,
          IsOptimalFacilityLocationOpeningDualSolution c f (x t) (u t) (v t) ∧
            IsEuclideanProjectionOnFacilityLocationOpeningDomain
              (x (t + 1))
              (facility_location_opening_projected_subgradient_target f (x t) (u t) (α t)) := by
  constructor
  · intro hseq
    exact ⟨hseq.initial_mem, hseq.step⟩
  · rintro ⟨hinitial, hstep⟩
    exact ⟨hinitial, hstep⟩

namespace IsFacilityLocationOpeningProjectedSubgradientAscentSequence

/-- The initial iterate of a projected subgradient-ascent sequence lies in the opening domain. -/
theorem zero_mem
    {c : Fin m → Fin n → ℝ}
    {f : Fin n → ℝ}
    {α : ℕ → ℝ}
    {x : ℕ → Fin n → ℝ}
    {u : ℕ → Fin m → Fin n → ℝ}
    {v : ℕ → Fin m → ℝ}
    (hseq : IsFacilityLocationOpeningProjectedSubgradientAscentSequence c f α x u v) :
    x 0 ∈ uncapacitated_facility_location_opening_domain :=
  hseq.initial_mem

/-- At each stage, the chosen dual multipliers are optimal for the current iterate. -/
theorem isOptimalDualSolution
    {c : Fin m → Fin n → ℝ}
    {f : Fin n → ℝ}
    {α : ℕ → ℝ}
    {x : ℕ → Fin n → ℝ}
    {u : ℕ → Fin m → Fin n → ℝ}
    {v : ℕ → Fin m → ℝ}
    (hseq : IsFacilityLocationOpeningProjectedSubgradientAscentSequence c f α x u v)
    (t : ℕ) :
    IsOptimalFacilityLocationOpeningDualSolution c f (x t) (u t) (v t) :=
  (hseq.step t).1

/-- At each stage, the next iterate is a Euclidean projection of the projected-subgradient target
back onto the opening domain. -/
theorem isEuclideanProjection
    {c : Fin m → Fin n → ℝ}
    {f : Fin n → ℝ}
    {α : ℕ → ℝ}
    {x : ℕ → Fin n → ℝ}
    {u : ℕ → Fin m → Fin n → ℝ}
    {v : ℕ → Fin m → ℝ}
    (hseq : IsFacilityLocationOpeningProjectedSubgradientAscentSequence c f α x u v)
    (t : ℕ) :
    IsEuclideanProjectionOnFacilityLocationOpeningDomain
      (x (t + 1))
      (facility_location_opening_projected_subgradient_target f (x t) (u t) (α t)) :=
  (hseq.step t).2

/-- Every iterate after the initial point lies in the opening domain. -/
theorem succ_mem
    {c : Fin m → Fin n → ℝ}
    {f : Fin n → ℝ}
    {α : ℕ → ℝ}
    {x : ℕ → Fin n → ℝ}
    {u : ℕ → Fin m → Fin n → ℝ}
    {v : ℕ → Fin m → ℝ}
    (hseq : IsFacilityLocationOpeningProjectedSubgradientAscentSequence c f α x u v)
    (t : ℕ) :
    x (t + 1) ∈ uncapacitated_facility_location_opening_domain :=
  (hseq.isEuclideanProjection t).mem

/-- Every iterate of a projected subgradient-ascent sequence lies in the opening domain `S`. -/
theorem mem
    {c : Fin m → Fin n → ℝ}
    {f : Fin n → ℝ}
    {α : ℕ → ℝ}
    {x : ℕ → Fin n → ℝ}
    {u : ℕ → Fin m → Fin n → ℝ}
    {v : ℕ → Fin m → ℝ}
    (hseq : IsFacilityLocationOpeningProjectedSubgradientAscentSequence c f α x u v) :
    ∀ t : ℕ, x t ∈ uncapacitated_facility_location_opening_domain
  | 0 => hseq.zero_mem
  | t + 1 => hseq.succ_mem t

end IsFacilityLocationOpeningProjectedSubgradientAscentSequence

/-- Every step of a projected subgradient-ascent sequence for Exercise 8.13 uses the dual vector
`gᵗ_j = ∑_i uᵗ_ij - f_j`, which is a valid subgradient of `z` at the current iterate `xᵗ`. -/
theorem facility_location_opening_projected_subgradient_ascent_sequence_uses_subgradients
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (α : ℕ → ℝ)
    (x : ℕ → Fin n → ℝ)
    (u : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ)
    (hseq :
      IsFacilityLocationOpeningProjectedSubgradientAscentSequence c f α x u v) :
    ∀ t : ℕ,
      IsConcaveSubgradientAt
        (uncapacitated_facility_location_opening_value c f)
        uncapacitated_facility_location_opening_domain
        (x t)
        (facility_location_opening_dual_subgradient f (u t)) := by
  intro t
  -- Apply the source-facing subgradient theorem at the current iterate of the ascent sequence.
  exact facility_location_opening_dual_subgradient_is_subgradient c f
    (hseq.mem t) (hseq.isOptimalDualSolution t)

/-- Choosing an actual projection operator on `S` turns an Exercise 8.13 projected
subgradient-ascent sequence into an instance of the generic Chapter 8 projected subgradient method
for the convex function `x ↦ -z(x)`. -/
theorem facility_location_opening_sequence_toIsProjectedSubgradientMethodSequence
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (proj : ProjectionOnto uncapacitated_facility_location_opening_domain)
    (α : ℕ → ℝ)
    (x : ℕ → Fin n → ℝ)
    (u : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ)
    (hseq : IsFacilityLocationOpeningProjectedSubgradientAscentSequence c f α x u v)
    (hproj :
      ∀ t : ℕ,
        proj (facility_location_opening_projected_subgradient_target f (x t) (u t) (α t)) =
          x (t + 1)) :
    IsProjectedSubgradientMethodSequence
      (fun x' ↦ -(uncapacitated_facility_location_opening_value c f x'))
      uncapacitated_facility_location_opening_domain
      proj
      α
      x
      (fun t ↦ -facility_location_opening_dual_subgradient f (u t)) := by
  -- Translate the source-facing ascent sequence to the Chapter 8 projected-subgradient owner.
  refine ⟨hseq.zero_mem, ?_⟩
  intro t
  refine ⟨?_, ?_⟩
  · -- The ascent subgradient becomes a subgradient of the negated objective after sign conversion.
    exact facility_location_opening_projected_subgradient_ascent_sequence_uses_subgradients
      c f α x u v hseq t
  · -- The projected-subgradient update is exactly the source target after rewriting the sign.
    calc
      x (t + 1) =
          proj (facility_location_opening_projected_subgradient_target f (x t) (u t) (α t)) := by
        symm
        exact hproj t
      _ =
          projected_subgradient_step proj
            (x t)
            (-facility_location_opening_dual_subgradient f (u t))
            (α t) := by
              rw [projected_subgradient_step]
              congr 1
              funext j
              simp [facility_location_opening_projected_subgradient_target, sub_eq_add_neg]

/-- The outer maximization value `max_{x ∈ S} z(x)` from Exercise 8.13, recorded on the
source-facing `ℝ` layer as the supremum of `z(x)` over the opening domain `S`. -/
def uncapacitated_facility_location_opening_master_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) : ℝ :=
  sSup
    ((fun x : Fin n → ℝ ↦
        uncapacitated_facility_location_opening_value c f x) ''
      uncapacitated_facility_location_opening_domain)

/-- Unfolding `uncapacitated_facility_location_opening_master_value c f` recovers the supremum of
`z(x)` over the set `S`. -/
theorem uncapacitated_facility_location_opening_master_value_eq_sSup
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    uncapacitated_facility_location_opening_master_value c f =
      sSup
        ((fun x : Fin n → ℝ ↦
            uncapacitated_facility_location_opening_value c f x) ''
          uncapacitated_facility_location_opening_domain) :=
  rfl

/-- The LP-relaxation value `z_LP` from Proposition 8.8, recast on the source-facing `ℝ` layer
as the supremum of the linear objective over the LP-feasible set. -/
def uncapacitated_facility_location_lp_real_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) : ℝ :=
  sSup
    ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
        facilityLocationObjective c f xy) ''
      facilityLocationLpFeasibleSet)

/-- Unfolding `uncapacitated_facility_location_lp_real_value c f` recovers the source-facing
supremum formula for `z_LP`. -/
theorem uncapacitated_facility_location_lp_real_value_eq_sSup
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    uncapacitated_facility_location_lp_real_value c f =
      sSup
        ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
            facilityLocationObjective c f xy) ''
          facilityLocationLpFeasibleSet) :=
  rfl

/-- Part (4) of Exercise 8.13. When there is at least one customer and at least one facility, the
optimal
value of the outer maximization problem `max_{x ∈ S} z(x)` coincides with `z_LP`, the value of the
linear-programming relaxation of `(8.5)`. -/
theorem uncapacitated_facility_location_opening_master_value_eq_lp_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (hm : 0 < m)
    (hn : 0 < n) :
    uncapacitated_facility_location_opening_master_value c f =
      uncapacitated_facility_location_lp_real_value c f := by
  classical
  let x0 : Fin n → ℝ := fun j ↦ if j = ⟨0, hn⟩ then 1 else 0
  have hx0 : x0 ∈ uncapacitated_facility_location_opening_domain := by
    -- Open a single facility to witness that the master domain is nonempty.
    refine (mem_uncapacitated_facility_location_opening_domain_iff.mpr ?_)
    refine ⟨?_, ?_⟩
    · intro j
      by_cases hj : j = ⟨0, hn⟩
      · simp [x0, hj]
      · simp [x0, hj]
    · have hmem : (⟨0, hn⟩ : Fin n) ∈ Finset.univ := by simp
      calc
        1 = x0 ⟨0, hn⟩ := by simp [x0]
        _ ≤ ∑ j, x0 j := by
          exact Finset.single_le_sum
            (fun j _ ↦ by
              by_cases hj : j = ⟨0, hn⟩ <;> simp [x0, hj])
            hmem
  rcases openingAssignmentFeasible_nonempty (m := m) hx0 with ⟨y0, hy0⟩
  have hy0lp : (y0, x0) ∈ facilityLocationLpFeasibleSet := by
    -- Any feasible fiber point over `x0 ∈ S` is LP-feasible after restoring the box bounds on `x0`.
    rcases (mem_uncapacitated_facility_location_opening_domain_iff.mp hx0) with ⟨hxbox0, _⟩
    rcases (mem_uncapacitated_facility_location_assignment_feasible_set_iff.mp hy0) with
      ⟨hrow0, hyNonneg0, hyLeX0⟩
    rw [mem_facilityLocationLpFeasibleSet_iff]
    exact ⟨hrow0, hyNonneg0, hyLeX0, fun j ↦ (hxbox0 j).1, fun j ↦ (hxbox0 j).2⟩
  let masterImage : Set ℝ :=
    ((fun x : Fin n → ℝ ↦ uncapacitated_facility_location_opening_value c f x) ''
      uncapacitated_facility_location_opening_domain)
  let lpImage : Set ℝ :=
    ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
        facilityLocationObjective c f xy) ''
      facilityLocationLpFeasibleSet)
  have hLpImageNonempty : lpImage.Nonempty := by
    exact ⟨facilityLocationObjective c f (y0, x0), ⟨(y0, x0), hy0lp, rfl⟩⟩
  have hLpImageBdd : BddAbove lpImage := by
    refine ⟨(∑ i, ∑ j, |c i j|) + ∑ j, |f j|, ?_⟩
    rintro _ ⟨xy, hxy, rfl⟩
    have hxyDomain : xy.2 ∈ uncapacitated_facility_location_opening_domain :=
      lpSecond_memOpeningDomain_of_memLpFeasible hm hxy
    have hxyFiber : xy.1 ∈ uncapacitated_facility_location_assignment_feasible_set xy.2 := by
      rcases (mem_facilityLocationLpFeasibleSet_iff.mp hxy) with
        ⟨hrow, hyNonneg, hyLeX, _, _⟩
      exact (mem_uncapacitated_facility_location_assignment_feasible_set_iff.mpr
        ⟨hrow, hyNonneg, hyLeX⟩)
    simpa [lpImage] using openingObjective_le_absBound c f hxyDomain hxyFiber
  have hMasterImageNonempty : masterImage.Nonempty := by
    refine ⟨uncapacitated_facility_location_opening_value c f x0, ⟨x0, hx0, rfl⟩⟩
  have hMasterImageBdd : BddAbove masterImage := by
    refine ⟨(∑ i, ∑ j, |c i j|) + ∑ j, |f j|, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    change uncapacitated_facility_location_opening_value c f x ≤
      (∑ i, ∑ j, |c i j|) + ∑ j, |f j|
    have hFiberNonempty :
        (((fun y : Fin m → Fin n → ℝ ↦ uncapacitated_facility_location_opening_objective c f x y) ''
          uncapacitated_facility_location_assignment_feasible_set x)).Nonempty := by
      rcases openingAssignmentFeasible_nonempty (m := m) hx with ⟨y, hy⟩
      exact ⟨uncapacitated_facility_location_opening_objective c f x y, ⟨y, hy, rfl⟩⟩
    -- Bound each fiber supremum by the same global constant.
    rw [uncapacitated_facility_location_opening_value_eq_sSup]
    refine csSup_le hFiberNonempty ?_
    rintro _ ⟨y, hy, rfl⟩
    exact openingObjective_le_absBound c f hx hy
  rw [uncapacitated_facility_location_opening_master_value_eq_sSup,
    uncapacitated_facility_location_lp_real_value_eq_sSup]
  refine le_antisymm ?_ ?_
  · refine csSup_le hMasterImageNonempty ?_
    rintro _ ⟨x, hx, rfl⟩
    change uncapacitated_facility_location_opening_value c f x ≤ sSup lpImage
    rw [uncapacitated_facility_location_opening_value_eq_sSup]
    have hFiberNonempty :
        (((fun y : Fin m → Fin n → ℝ ↦ uncapacitated_facility_location_opening_objective c f x y) ''
          uncapacitated_facility_location_assignment_feasible_set x)).Nonempty := by
      rcases openingAssignmentFeasible_nonempty (m := m) hx with ⟨y, hy⟩
      exact ⟨uncapacitated_facility_location_opening_objective c f x y, ⟨y, hy, rfl⟩⟩
    refine csSup_le hFiberNonempty ?_
    rintro _ ⟨y, hy, rfl⟩
    -- Each feasible fiber point is already LP-feasible, so its value is bounded by `z_LP`.
    have hxy : (y, x) ∈ facilityLocationLpFeasibleSet := by
      rcases (mem_uncapacitated_facility_location_opening_domain_iff.mp hx) with ⟨hxbox, _⟩
      rcases (mem_uncapacitated_facility_location_assignment_feasible_set_iff.mp hy) with
        ⟨hrow, hyNonneg, hyLeX⟩
      rw [mem_facilityLocationLpFeasibleSet_iff]
      exact ⟨hrow, hyNonneg, hyLeX, fun j ↦ (hxbox j).1, fun j ↦ (hxbox j).2⟩
    exact le_csSup hLpImageBdd ⟨(y, x), hxy, rfl⟩
  · refine csSup_le hLpImageNonempty ?_
    rintro _ ⟨xy, hxy, rfl⟩
    have hxyDomain : xy.2 ∈ uncapacitated_facility_location_opening_domain :=
      lpSecond_memOpeningDomain_of_memLpFeasible hm hxy
    have hxyFiber : xy.1 ∈ uncapacitated_facility_location_assignment_feasible_set xy.2 := by
      rcases (mem_facilityLocationLpFeasibleSet_iff.mp hxy) with
        ⟨hrow, hyNonneg, hyLeX, _, _⟩
      exact (mem_uncapacitated_facility_location_assignment_feasible_set_iff.mpr
        ⟨hrow, hyNonneg, hyLeX⟩)
    have hValueLe :
        facilityLocationObjective c f xy ≤
          uncapacitated_facility_location_opening_value c f xy.2 := by
      rw [uncapacitated_facility_location_opening_value_eq_sSup]
      have hFiberBdd :
          BddAbove
            (((fun y : Fin m → Fin n → ℝ ↦
                uncapacitated_facility_location_opening_objective c f xy.2 y) ''
              uncapacitated_facility_location_assignment_feasible_set xy.2)) := by
        refine ⟨(∑ i, ∑ j, |c i j|) + ∑ j, |f j|, ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        exact openingObjective_le_absBound c f hxyDomain hy
      exact le_csSup hFiberBdd ⟨xy.1, hxyFiber, rfl⟩
    have hMasterLe :
        uncapacitated_facility_location_opening_value c f xy.2 ≤ sSup masterImage := by
      exact le_csSup hMasterImageBdd ⟨xy.2, hxyDomain, rfl⟩
    exact hValueLe.trans hMasterLe

end Exercise813
