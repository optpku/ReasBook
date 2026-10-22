/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_1_extra_1

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "ConstraintMatrix" => Matrix (Fin n) (Fin m) ℝ

-- Domain-style sampling:
-- * primary domain: linearly constrained feasible-direction search and its explicit dual
--   maximization problem in Euclidean space
-- * inspected owner declarations:
--   `OptimizationProblem` from Chapter 1,
--   `ConstrainedOptimizationProblem.IsDualSolution` from Chapter 8,
--   `QuadraticProgram.IsDualSolution` from Chapter 9,
--   and `IsFeasibleDescentDirection` from `Definition_11_1_extra_1`
-- * best owner abstraction: keep the source-facing feasible-set/objective data for the primal
--   direction search, and expose the dual directly by its multiplier feasible set and objective;
--   the Chapter 1 owner `OptimizationProblem` would add only a coordinate transport from
--   `EuclideanSpace ℝ (Fin m)` to `Fin m → ℝ`, so the dual optimality surface here should be the
--   canonical predicate `IsMaxOn` rather than a second local problem wrapper
-- * primitive data: the primal feasible set/objective and the dual feasible set/objective
-- * layer triage:
--   source-facing: `linearlyConstrainedDirectionSearchDualFeasibleSet` and
--     `linearlyConstrainedDirectionSearchDualObjective`
--   core/canonical: `ConvexOn` and `IsMaxOn`
--   bridge/view: the membership and evaluation simp lemmas
-- * derived API: convexity and feasible-descent certification

/-- The polyhedral feasible set `X = {x | Aᵀ x ≥ b}` written componentwise. -/
def linearlyConstrainedPolyhedron
    (A : ConstraintMatrix) (b : ConstraintPoint) : Set Point :=
  {x | ∀ i : Fin m, b i ≤ (A.transpose.mulVec x) i}

/-- Membership in `linearlyConstrainedPolyhedron A b` is exactly the componentwise inequality
system `Aᵀ x ≥ b`. -/
@[simp] theorem mem_linearlyConstrainedPolyhedron_iff
    (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point) :
    x ∈ linearlyConstrainedPolyhedron A b ↔ ∀ i : Fin m, b i ≤ (A.transpose.mulVec x) i :=
  Iff.rfl

/-- The active constraint indices of the polyhedron `Aᵀ x ≥ b` at the base point `x`. -/
def activeConstraintSet
    (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point) : Set (Fin m) :=
  {i | (A.transpose.mulVec x) i = b i}

/-- Membership in `activeConstraintSet A b x` is exactly the source active-set equality
`a_iᵀ x = b_i`. -/
@[simp] theorem mem_activeConstraintSet_iff
    (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point) (i : Fin m) :
    i ∈ activeConstraintSet A b x ↔ (A.transpose.mulVec x) i = b i :=
  Iff.rfl

/-- The normalized feasible-direction search set at `x`: the direction has norm at most `1` and
points weakly inward along every active constraint of `Aᵀ x ≥ b`. -/
def linearlyConstrainedDirectionSearchFeasibleSet
    (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point) : Set Point :=
  {d | ‖d‖ ≤ 1 ∧ ∀ i ∈ activeConstraintSet A b x, 0 ≤ (A.transpose.mulVec d) i}

/-- Membership in `linearlyConstrainedDirectionSearchFeasibleSet A b x` is exactly the unit-ball
bound together with the active-constraint linear inequalities. -/
@[simp] theorem mem_linearlyConstrainedDirectionSearchFeasibleSet_iff
    (A : ConstraintMatrix) (b : ConstraintPoint) (x d : Point) :
    d ∈ linearlyConstrainedDirectionSearchFeasibleSet A b x ↔
      ‖d‖ ≤ 1 ∧ ∀ i ∈ activeConstraintSet A b x, 0 ≤ (A.transpose.mulVec d) i :=
  Iff.rfl

/-- The linear objective `d ↦ dᵀ ∇ f(x)` used to choose a feasible descent direction at `x`. -/
def linearlyConstrainedDirectionSearchObjective
    (f : Point → ℝ) (x : Point) : Point → ℝ :=
  fun d ↦ inner ℝ d (gradient f x)

/-- Evaluating `linearlyConstrainedDirectionSearchObjective f x` gives the directional pairing
with `gradient f x`. -/
@[simp] theorem linearlyConstrainedDirectionSearchObjective_apply
    (f : Point → ℝ) (x d : Point) :
    linearlyConstrainedDirectionSearchObjective f x d = inner ℝ d (gradient f x) :=
  rfl

/-- Helper for Chapter11 Exercise 11.1: the normalized feasible-direction search set is convex,
because the unit-ball bound and the active-constraint inequalities are both preserved under convex
combinations. -/
lemma linearlyConstrainedDirectionSearchFeasibleSet_convex
    (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point) :
    Convex ℝ (linearlyConstrainedDirectionSearchFeasibleSet A b x) := by
  intro u hu v hv a c ha hc hac
  rcases hu with ⟨hu_norm, hu_active⟩
  rcases hv with ⟨hv_norm, hv_active⟩
  refine ⟨?_, ?_⟩
  · -- The norm bound is stable under convex combinations by the triangle inequality.
    calc
      ‖a • u + c • v‖ ≤ ‖a • u‖ + ‖c • v‖ := norm_add_le _ _
      _ = a * ‖u‖ + c * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hc]
      _ ≤ a * 1 + c * 1 := by
        nlinarith
      _ = 1 := by
        nlinarith
  · intro i hi
    -- The active-constraint directional inequalities are linear in the direction.
    simpa [Matrix.mulVec_add, Matrix.mulVec_smul] using
      add_nonneg (mul_nonneg ha (hu_active i hi)) (mul_nonneg hc (hv_active i hi))

/-- Helper for Chapter11 Exercise 11.1: an inactive constraint has strictly positive slack at a
feasible base point. -/
lemma inactive_constraint_slack_pos
    (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point)
    (i : Fin m) (hx : x ∈ linearlyConstrainedPolyhedron A b)
    (hi : i ∉ activeConstraintSet A b x) :
    0 < (A.transpose.mulVec x) i - b i := by
  have hx_i : b i ≤ (A.transpose.mulVec x) i := hx i
  have hne : b i ≠ (A.transpose.mulVec x) i := by
    intro hEq
    exact hi (by simpa [eq_comm] using hEq)
  exact sub_pos.mpr (lt_of_le_of_ne hx_i hne)

/-- Helper for Chapter11 Exercise 11.1: each individual linear constraint stays feasible for all
sufficiently small nonnegative steps along a normalized feasible search direction. -/
lemma linearlyConstrainedPolyhedron_component_smallStep
    (A : ConstraintMatrix) (b : ConstraintPoint) {x d : Point}
    (hx : x ∈ linearlyConstrainedPolyhedron A b)
    (hd : d ∈ linearlyConstrainedDirectionSearchFeasibleSet A b x)
    (i : Fin m) :
    ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) δ, b i ≤ (A.transpose.mulVec (x + t • d)) i := by
  rcases hd with ⟨_, hd_active⟩
  by_cases hi : i ∈ activeConstraintSet A b x
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    have hactive : 0 ≤ (A.transpose.mulVec d) i := hd_active i hi
    have hx_active : (A.transpose.mulVec x) i = b i := by
      simpa using hi
    have hmove :
        (A.transpose.mulVec (x + t • d)) i =
          (A.transpose.mulVec x) i + t * (A.transpose.mulVec d) i := by
      simp [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [hmove, hx_active]
    -- Active constraints remain feasible because their directional derivative is nonnegative.
    nlinarith [ht.1, hactive]
  · let slack : ℝ := (A.transpose.mulVec x) i - b i
    let slope : ℝ := (A.transpose.mulVec d) i
    let δ : ℝ := slack / (|slope| + 1)
    have hslack_pos : 0 < slack := by
      simpa [slack] using inactive_constraint_slack_pos A b x i hx hi
    have hden_pos : 0 < |slope| + 1 := by
      positivity
    have hδ_pos : 0 < δ := by
      exact div_pos hslack_pos hden_pos
    refine ⟨δ, hδ_pos, ?_⟩
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.1
    have ht_le : t ≤ δ := ht.2
    have hslope_lower : -(t * |slope|) ≤ t * slope := by
      have hmul := mul_le_mul_of_nonneg_left (neg_abs_le slope) ht_nonneg
      simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
    have habs_bound : t * |slope| ≤ slack := by
      have hmul1 : t * |slope| ≤ t * (|slope| + 1) := by
        nlinarith [ht_nonneg, abs_nonneg slope]
      have hmul2 : t * (|slope| + 1) ≤ slack := by
        exact (le_div_iff₀ hden_pos).mp ht_le
      exact hmul1.trans hmul2
    have hslope_ge : -slack ≤ t * slope := by
      linarith
    have hmove :
        (A.transpose.mulVec (x + t • d)) i =
          (A.transpose.mulVec x) i + t * slope := by
      simp [slope, Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [hmove]
    -- Inactive constraints start with positive slack, and the step is short enough not to lose it.
    dsimp [slack] at hslope_ge ⊢
    linarith

/-- Helper for Chapter11 Exercise 11.1: a normalized feasible search direction for
`Aᵀ x ≥ b` yields a common positive step length whose whole initial segment stays in the
polyhedron. -/
lemma linearlyConstrainedPolyhedron_smallStep_of_directionSearch
    (A : ConstraintMatrix) (b : ConstraintPoint) {x d : Point}
    (hx : x ∈ linearlyConstrainedPolyhedron A b)
    (hd : d ∈ linearlyConstrainedDirectionSearchFeasibleSet A b x) :
    ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) δ, x + t • d ∈ linearlyConstrainedPolyhedron A b := by
  classical
  choose δ hδ_pos hδ using
    fun i : Fin m ↦ linearlyConstrainedPolyhedron_component_smallStep A b hx hd i
  cases isEmpty_or_nonempty (Fin m) with
  | inl hm =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro t ht
      rw [mem_linearlyConstrainedPolyhedron_iff]
      intro i
      exact False.elim (hm.false i)
  | inr hm =>
      letI : Nonempty (Fin m) := hm
      let ε : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
      have hε_pos : 0 < ε := by
        exact (Finset.lt_inf'_iff _).2 fun i _ ↦ hδ_pos i
      refine ⟨ε, hε_pos, ?_⟩
      intro t ht
      rw [mem_linearlyConstrainedPolyhedron_iff]
      intro i
      have ht_i : t ∈ Set.Icc (0 : ℝ) (δ i) := by
        refine ⟨ht.1, ?_⟩
        exact ht.2.trans (Finset.inf'_le _ (Finset.mem_univ i))
      exact hδ i t ht_i

/-- Chapter11 Exercise 11.1 (1): the normalized feasible-direction search problem with feasible
set `linearlyConstrainedDirectionSearchFeasibleSet A b x` and objective
`linearlyConstrainedDirectionSearchObjective f x` is a convex program in the canonical Chapter 8
owner sense `ConvexOn`. The source feasibility and differentiability assumptions are not needed
for this convexity statement itself. -/
theorem linearlyConstrainedDirectionSearch_isConvexProgram
    (f : Point → ℝ) (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point) :
    ConvexOn ℝ (linearlyConstrainedDirectionSearchFeasibleSet A b x)
      (linearlyConstrainedDirectionSearchObjective f x) := by
  refine ⟨linearlyConstrainedDirectionSearchFeasibleSet_convex A b x, ?_⟩
  intro d _hd e _he a c ha hc hac
  -- The objective is linear in the search direction, so Jensen holds with equality.
  have hlinear :
      linearlyConstrainedDirectionSearchObjective f x (a • d + c • e) =
        a * linearlyConstrainedDirectionSearchObjective f x d +
          c * linearlyConstrainedDirectionSearchObjective f x e := by
    simp [linearlyConstrainedDirectionSearchObjective]
  have hsmul :
      a • linearlyConstrainedDirectionSearchObjective f x d +
          c • linearlyConstrainedDirectionSearchObjective f x e =
        a * linearlyConstrainedDirectionSearchObjective f x d +
          c * linearlyConstrainedDirectionSearchObjective f x e := by
    simp [smul_eq_mul]
  rw [hsmul]
  exact hlinear.le

/-- If `x ∈ linearlyConstrainedPolyhedron A b` and `d` satisfies the linearized feasibility
conditions with strictly negative objective value, then `d` satisfies the Chapter 11
feasible-descent owner at `x` for the polyhedron `linearlyConstrainedPolyhedron A b`. The source
differentiability assumption is redundant here because strict negativity of the objective already
forces differentiability through `IsFeasibleDescentDirection`. -/
theorem linearlyConstrainedDirectionSearchFeasibleDescentConditions
    (f : Point → ℝ) (A : ConstraintMatrix) (b : ConstraintPoint) {x d : Point}
    (hx : x ∈ linearlyConstrainedPolyhedron A b)
    (hd : d ∈ linearlyConstrainedDirectionSearchFeasibleSet A b x)
    (hobj : linearlyConstrainedDirectionSearchObjective f x d < 0) :
    IsFeasibleDescentDirection f x (linearlyConstrainedPolyhedron A b) d := by
  -- Translate the strict objective decrease into the canonical Chapter 1 descent predicate.
  have hdescent : IsDescentDirectionAt f x d := by
    change inner ℝ (gradient f x) d < 0
    simpa [linearlyConstrainedDirectionSearchObjective, real_inner_comm] using hobj
  have hfeasible : IsFeasibleDirectionAt (linearlyConstrainedPolyhedron A b) x d := by
    rw [isFeasibleDirectionAt_iff]
    refine ⟨hdescent.direction_ne, ?_⟩
    -- The linearly constrained search conditions give a uniform feasible segment in the polyhedron.
    exact linearlyConstrainedPolyhedron_smallStep_of_directionSearch A b hx hd
  -- Assemble the feasible-direction and descent-direction owners.
  exact
    (isFeasibleDescentDirection_iff_feasible_and_descent
      f x d (linearlyConstrainedPolyhedron A b)).2 ⟨hfeasible, hdescent⟩

/-- Chapter11 Exercise 11.1 (2): the dual feasible multipliers are nonnegative on the active
constraints of `Aᵀ x ≥ b` and vanish on the inactive constraints. -/
def linearlyConstrainedDirectionSearchDualFeasibleSet
    (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point) : Set ConstraintPoint :=
  {lam |
    (∀ i ∈ activeConstraintSet A b x, 0 ≤ lam i) ∧
      ∀ i ∉ activeConstraintSet A b x, lam i = 0}

/-- Membership in `linearlyConstrainedDirectionSearchDualFeasibleSet A b x` is exactly the
nonnegativity condition on active multipliers together with vanishing off the active set. -/
@[simp] theorem mem_linearlyConstrainedDirectionSearchDualFeasibleSet_iff
    (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point) (lam : ConstraintPoint) :
    lam ∈ linearlyConstrainedDirectionSearchDualFeasibleSet A b x ↔
      (∀ i ∈ activeConstraintSet A b x, 0 ≤ lam i) ∧
        ∀ i ∉ activeConstraintSet A b x, lam i = 0 :=
  Iff.rfl

/-- Chapter11 Exercise 11.1 (2): the dual objective of the normalized feasible-direction search
problem is `λ ↦ -‖∇ f(x) - A λ‖`. Together with
`linearlyConstrainedDirectionSearchDualFeasibleSet A b x`, this is the full source dual problem
data; no additional problem wrapper is needed. -/
def linearlyConstrainedDirectionSearchDualObjective
    (f : Point → ℝ) (A : ConstraintMatrix) (x : Point) : ConstraintPoint → ℝ :=
  fun lam ↦ -‖gradient f x - A.mulVec lam‖

/-- Evaluating `linearlyConstrainedDirectionSearchDualObjective f A x` gives the dual
objective formula `-‖∇ f(x) - A λ‖`. -/
@[simp] theorem linearlyConstrainedDirectionSearchDualObjective_apply
    (f : Point → ℝ) (A : ConstraintMatrix) (x : Point)
    (lam : ConstraintPoint) :
    linearlyConstrainedDirectionSearchDualObjective f A x lam =
      -‖gradient f x - A.mulVec lam‖ :=
  rfl

#print axioms linearlyConstrainedPolyhedron
#print axioms linearlyConstrainedDirectionSearchObjective
#print axioms linearlyConstrainedDirectionSearchDualObjective

end
