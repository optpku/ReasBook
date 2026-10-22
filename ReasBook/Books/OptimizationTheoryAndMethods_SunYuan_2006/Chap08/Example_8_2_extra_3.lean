/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section

section Chapter08Example82Extra3

local notation "Point" => Fin 2 → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin 2)

/-- The objective in the Chapter 8 constraint-qualification counterexample is `x ↦ x 0`. -/
def cubicConstraintCounterexampleObjective (x : Point) : ℝ :=
  x 0

/-- The first inequality constraint in the Chapter 8 counterexample is
`x ↦ (x 0)^3 - x 1`. -/
def cubicConstraintCounterexampleConstraint1 (x : Point) : ℝ :=
  (x 0) ^ (3 : ℕ) - x 1

/-- The second inequality constraint in the Chapter 8 counterexample is `x ↦ x 1`. -/
def cubicConstraintCounterexampleConstraint2 (x : Point) : ℝ :=
  x 1

/-- The canonical Chapter 8 constraint family for the cubic counterexample. -/
def cubicConstraintCounterexampleConstraint : Fin 2 → Point → ℝ
  | 0 => cubicConstraintCounterexampleConstraint1
  | 1 => cubicConstraintCounterexampleConstraint2

/-- The constrained problem whose feasible set is cut out by
`(x 0)^3 - x 1 ≥ 0` and `x 1 ≥ 0`. -/
def cubicConstraintCounterexampleProblem :
    ConstrainedOptimizationProblem 2 2 (∅ : Set (Fin 2)) (Set.univ : Set (Fin 2)) where
  objective := cubicConstraintCounterexampleObjective
  constraint := cubicConstraintCounterexampleConstraint
  eqIndices_union_ineqIndices := by
    ext i
    simp
  eqIndices_disjoint_ineqIndices := by
    simp

/-- Membership in `cubicConstraintCounterexampleProblem.feasibleSet` is exactly the pair of
source inequalities `(x 0)^3 - x 1 ≥ 0` and `x 1 ≥ 0`. -/
theorem mem_cubicConstraintCounterexampleProblem_feasibleSet_iff (x : Point) :
    x ∈ cubicConstraintCounterexampleProblem.feasibleSet ↔
      0 ≤ cubicConstraintCounterexampleConstraint1 x ∧
        0 ≤ cubicConstraintCounterexampleConstraint2 x := by
  simp [ConstrainedOptimizationProblem.feasibleSet, cubicConstraintCounterexampleProblem,
    cubicConstraintCounterexampleConstraint]

/-- The feasible minimizer `x*` in the Chapter 8 counterexample is the origin. -/
def cubicConstraintCounterexampleSolution : Point :=
  0

/-- The feasible minimizer `x*`, viewed in the Euclidean model used for gradients. -/
def cubicConstraintCounterexampleEuclideanSolution : EPoint :=
  WithLp.toLp 2 cubicConstraintCounterexampleSolution

local notation "xStar" => cubicConstraintCounterexampleSolution
local notation "xStarE" => cubicConstraintCounterexampleEuclideanSolution

/-- The source set `{d | d = (α, 0), α ≥ 0}` is the nonnegative horizontal ray in `ℝ²`. -/
def cubicConstraintCounterexampleHorizontalRay : Set Point :=
  {d | ∃ α : ℝ, 0 ≤ α ∧ d = EuclideanSpace.single 0 α}

/-- The source set `{d | d = (α, 0), α ∈ ℝ}` is the horizontal axis in `ℝ²`. -/
def cubicConstraintCounterexampleHorizontalAxis : Set Point :=
  {d | ∃ α : ℝ, d = EuclideanSpace.single 0 α}

#print axioms cubicConstraintCounterexampleObjective
#print axioms cubicConstraintCounterexampleConstraint1
#print axioms cubicConstraintCounterexampleConstraint2
#print axioms cubicConstraintCounterexampleConstraint
#print axioms cubicConstraintCounterexampleProblem
#print axioms cubicConstraintCounterexampleSolution
#print axioms cubicConstraintCounterexampleEuclideanSolution
#print axioms cubicConstraintCounterexampleHorizontalRay
#print axioms cubicConstraintCounterexampleHorizontalAxis

/-- Helper for Chapter08 Example 8.2-extra-3: feasible points are exactly the points whose second
coordinate lies between `0` and the cubic graph `x₂ = x₁^3`. -/
theorem mem_cubicConstraintCounterexampleProblem_feasibleSet_iff_coord_bounds (x : Point) :
    x ∈ cubicConstraintCounterexampleProblem.feasibleSet ↔
      0 ≤ x 1 ∧ x 1 ≤ x 0 ^ (3 : ℕ) := by
  constructor
  · intro hx
    rcases (mem_cubicConstraintCounterexampleProblem_feasibleSet_iff x).1 hx with
      ⟨hConstraint1, hConstraint2⟩
    constructor
    · -- The second source constraint is exactly the nonnegativity of the second coordinate.
      simpa [cubicConstraintCounterexampleConstraint2] using hConstraint2
    · -- Rearranging the cubic inequality isolates the upper bound on the second coordinate.
      simpa [cubicConstraintCounterexampleConstraint1] using hConstraint1
  · rintro ⟨hx2_nonneg, hx2_le⟩
    refine (mem_cubicConstraintCounterexampleProblem_feasibleSet_iff x).2 ?_
    constructor
    · -- Rewriting the bound back into constraint form recovers the first source inequality.
      simpa [cubicConstraintCounterexampleConstraint1] using hx2_le
    · -- The second coordinate nonnegativity is already the second source inequality.
      simpa [cubicConstraintCounterexampleConstraint2] using hx2_nonneg

/-- Helper for Chapter08 Example 8.2-extra-3: every feasible point has nonnegative first
coordinate. -/
theorem cubicConstraintCounterexample_nonneg_first_of_feasible {x : Point}
    (hx : x ∈ cubicConstraintCounterexampleProblem.feasibleSet) :
    0 ≤ x 0 := by
  rcases (mem_cubicConstraintCounterexampleProblem_feasibleSet_iff_coord_bounds x).1 hx with
    ⟨hx2_nonneg, hx2_le⟩
  have hcube_nonneg : 0 ≤ x 0 ^ (3 : ℕ) := le_trans hx2_nonneg hx2_le
  by_contra hx0_neg
  have hx0_lt : x 0 < 0 := lt_of_not_ge hx0_neg
  have hcube_lt : x 0 ^ (3 : ℕ) < 0 := by
    have hsq_pos : 0 < x 0 ^ (2 : ℕ) := by
      nlinarith
    have hcube_eq : x 0 ^ (3 : ℕ) = x 0 * x 0 ^ (2 : ℕ) := by ring
    nlinarith [hcube_eq, hsq_pos, hx0_lt]
  -- A negative first coordinate would force a negative cube, contradicting feasibility.
  linarith

/-- Helper for Chapter08 Example 8.2-extra-3: the horizontal ray description is equivalent to
nonnegative first coordinate and vanishing second coordinate. -/
theorem cubicConstraintCounterexample_mem_horizontalRay_iff (d : Point) :
    d ∈ cubicConstraintCounterexampleHorizontalRay ↔ 0 ≤ d 0 ∧ d 1 = 0 := by
  constructor
  · rintro ⟨α, hα, rfl⟩
    constructor
    · -- A horizontal-ray point has first coordinate equal to its scalar parameter.
      simpa [EuclideanSpace.single_apply] using hα
    · -- Its second coordinate vanishes because the vector is supported only at index `0`.
      simp [EuclideanSpace.single_apply]
  · rintro ⟨hd0, hd1⟩
    refine ⟨d 0, hd0, ?_⟩
    -- Extensionality reduces equality to the two coordinates.
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply, hd1]

/-- Helper for Chapter08 Example 8.2-extra-3: the horizontal axis description is equivalent to
vanishing second coordinate. -/
theorem cubicConstraintCounterexample_mem_horizontalAxis_iff (d : Point) :
    d ∈ cubicConstraintCounterexampleHorizontalAxis ↔ d 1 = 0 := by
  constructor
  · rintro ⟨α, rfl⟩
    -- Axis vectors are supported only in the first coordinate.
    simp [EuclideanSpace.single_apply]
  · intro hd1
    refine ⟨d 0, ?_⟩
    -- The first coordinate determines the whole vector once the second coordinate is zero.
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply, hd1]

/-- Helper for Chapter08 Example 8.2-extra-3: the `i`-th coordinate projection on Euclidean
space has gradient `eᵢ`. -/
theorem hasGradientAt_euclidean_coordinate_projection (i : Fin 2) (x : EPoint) :
    HasGradientAt (fun y : EPoint ↦ y i) (EuclideanSpace.single i (1 : ℝ)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single i (1 : ℝ)) =
        PiLp.proj 2 (fun _ : Fin 2 => ℝ) i := by
    ext v
    -- The Fréchet-Riesz identification sends `eᵢ` to evaluation at the `i`-th coordinate.
    simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
  simpa [hdual] using
    (PiLp.hasFDerivAt_apply (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 2 => ℝ) x i)

/-- Helper for Chapter08 Example 8.2-extra-3: the Euclidean objective is the first coordinate
projection, so its gradient at `x*` is `e₀`. -/
theorem hasGradientAt_cubicConstraintCounterexample_euclideanObjective :
    HasGradientAt cubicConstraintCounterexampleProblem.euclideanObjective
      (EuclideanSpace.single 0 (1 : ℝ)) xStarE := by
  -- The transported objective is exactly the first coordinate projection.
  change HasGradientAt (fun y : EPoint ↦ y 0) (EuclideanSpace.single 0 (1 : ℝ)) xStarE
  exact hasGradientAt_euclidean_coordinate_projection 0 xStarE

/-- Helper for Chapter08 Example 8.2-extra-3: the transported second constraint is the second
coordinate projection, so its gradient at `x*` is `e₁`. -/
theorem hasGradientAt_cubicConstraintCounterexample_euclideanConstraint2 :
    HasGradientAt (cubicConstraintCounterexampleProblem.euclideanConstraint 1)
      (EuclideanSpace.single 1 (1 : ℝ)) xStarE := by
  -- The second source constraint is linear in the second coordinate.
  change HasGradientAt (fun y : EPoint ↦ y 1) (EuclideanSpace.single 1 (1 : ℝ)) xStarE
  exact hasGradientAt_euclidean_coordinate_projection 1 xStarE

/-- Helper for Chapter08 Example 8.2-extra-3: the cubic term `(x 0)^3` has zero gradient at the
origin because its one-dimensional derivative vanishes there. -/
theorem hasGradientAt_cubicConstraintCounterexample_coordinateCube :
    HasGradientAt (fun y : EPoint ↦ y 0 ^ (3 : ℕ)) 0 xStarE := by
  have hcoord :
      HasFDerivAt (fun y : EPoint ↦ y 0)
        (InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single 0 (1 : ℝ))) xStarE :=
    (hasGradientAt_euclidean_coordinate_projection 0 xStarE).hasFDerivAt
  have hpow :
      HasDerivAt (fun z : ℝ ↦ z ^ (3 : ℕ)) (0 : ℝ) ((fun y : EPoint ↦ y 0) xStarE) := by
    -- The scalar cubic derivative equals `3 z²`, hence vanishes at `z = 0`.
    simpa [cubicConstraintCounterexampleEuclideanSolution,
      cubicConstraintCounterexampleSolution] using
      (hasDerivAt_pow 3 ((fun y : EPoint ↦ y 0) xStarE))
  -- Composing the scalar cubic derivative with the coordinate projection yields a zero derivative.
  have hcomp := hpow.comp_hasFDerivAt xStarE hcoord
  change HasGradientAt ((fun z : ℝ ↦ z ^ (3 : ℕ)) ∘ fun y : EPoint ↦ y 0) 0 xStarE
  have hgrad_zeroDual :
      HasGradientAt ((fun z : ℝ ↦ z ^ (3 : ℕ)) ∘ fun y : EPoint ↦ y 0)
        ((InnerProductSpace.toDual ℝ EPoint).symm (0 : StrongDual ℝ EPoint)) xStarE := by
    simpa using hcomp.hasGradientAt
  simpa using hgrad_zeroDual

/-- Helper for Chapter08 Example 8.2-extra-3: the transported first constraint has gradient
`(0, -1)` at `x*`. -/
theorem hasGradientAt_cubicConstraintCounterexample_euclideanConstraint1 :
    HasGradientAt (cubicConstraintCounterexampleProblem.euclideanConstraint 0)
      (EuclideanSpace.single 1 (-1 : ℝ)) xStarE := by
  change HasGradientAt (fun y : EPoint ↦ y 0 ^ (3 : ℕ) - y 1)
    (EuclideanSpace.single 1 (-1 : ℝ)) xStarE
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt ((fun y : EPoint ↦ y 0 ^ (3 : ℕ)) - fun y : EPoint ↦ y 1)
    (InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single 1 (-1 : ℝ))) xStarE
  have hcube := hasGradientAt_cubicConstraintCounterexample_coordinateCube.hasFDerivAt
  have hcoord1 :
      HasFDerivAt (fun y : EPoint ↦ y 1)
        (InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single 1 (1 : ℝ))) xStarE :=
    (hasGradientAt_euclidean_coordinate_projection 1 xStarE).hasFDerivAt
  have hneg_map :
      -(InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single 1 (1 : ℝ))) =
        InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single 1 (-1 : ℝ)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
  -- The cubic term contributes zero derivative at the origin, while the linear term contributes
  -- the negative second coordinate functional.
  simpa [hneg_map] using hcube.sub hcoord1

/-- Helper for Chapter08 Example 8.2-extra-3: both active constraints are differentiable at
`x*`. -/
theorem cubicConstraintCounterexample_hasActiveConstraintGradientsAt :
    cubicConstraintCounterexampleProblem.HasActiveConstraintGradientsAt xStar := by
  intro i hi
  fin_cases i
  · -- The first constraint is differentiable because its Euclidean transport has a gradient.
    exact
      (cubicConstraintCounterexampleProblem.differentiableAt_euclideanConstraint_iff 0 xStar).1
        hasGradientAt_cubicConstraintCounterexample_euclideanConstraint1.differentiableAt
  · -- The second constraint is linear, so its Euclidean transport is differentiable everywhere.
    exact
      (cubicConstraintCounterexampleProblem.differentiableAt_euclideanConstraint_iff 1 xStar).1
        hasGradientAt_cubicConstraintCounterexample_euclideanConstraint2.differentiableAt

/-- Helper for Chapter08 Example 8.2-extra-3: the first linearized constraint pairing at `x*`
is `-d₂`. -/
theorem cubicConstraintCounterexample_linearizedConstraintPairing_constraint1 (d : Point) :
    cubicConstraintCounterexampleProblem.linearizedConstraintPairing xStar d 0 = -d 1 := by
  rw [cubicConstraintCounterexampleProblem.linearizedConstraintPairing_eq_euclideanConstraint
    xStar d 0]
  change (fderiv ℝ (cubicConstraintCounterexampleProblem.euclideanConstraint 0) xStarE)
      (WithLp.toLp 2 d) = -d 1
  rw [hasGradientAt_cubicConstraintCounterexample_euclideanConstraint1.hasFDerivAt.fderiv]
  -- Evaluating the derivative against `d` reads off the second coordinate with a minus sign.
  simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]

/-- Helper for Chapter08 Example 8.2-extra-3: the second linearized constraint pairing at `x*`
is `d₂`. -/
theorem cubicConstraintCounterexample_linearizedConstraintPairing_constraint2 (d : Point) :
    cubicConstraintCounterexampleProblem.linearizedConstraintPairing xStar d 1 = d 1 := by
  rw [cubicConstraintCounterexampleProblem.linearizedConstraintPairing_eq_euclideanConstraint
    xStar d 1]
  change (fderiv ℝ (cubicConstraintCounterexampleProblem.euclideanConstraint 1) xStarE)
      (WithLp.toLp 2 d) = d 1
  rw [hasGradientAt_cubicConstraintCounterexample_euclideanConstraint2.hasFDerivAt.fderiv]
  -- The second constraint is the second coordinate projection itself.
  simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]

/-- Helper for Chapter08 Example 8.2-extra-3: a linearly feasible direction is exactly a
horizontal direction. -/
theorem cubicConstraintCounterexample_mem_linearizedFeasibleDirectionSet_iff_second_eq_zero
    (d : Point) :
    d ∈ cubicConstraintCounterexampleProblem.linearizedFeasibleDirectionSet xStar ↔ d 1 = 0 := by
  rw [cubicConstraintCounterexampleProblem.mem_linearizedFeasibleDirectionSet_iff_explicit]
  constructor
  · rintro ⟨hxStar_feasible, hActiveGrad, hEq, hIneq⟩
    have hactive0 :
        (0 : Fin 2) ∈ cubicConstraintCounterexampleProblem.activeIneqIndexSet xStar := by
      exact (cubicConstraintCounterexampleProblem.mem_activeIneqIndexSet_iff xStar 0).2 (by
        simp [ConstrainedOptimizationProblem.ineqIndices, cubicConstraintCounterexampleProblem,
          cubicConstraintCounterexampleConstraint, cubicConstraintCounterexampleConstraint1,
          cubicConstraintCounterexampleSolution])
    have hactive1 :
        (1 : Fin 2) ∈ cubicConstraintCounterexampleProblem.activeIneqIndexSet xStar := by
      exact (cubicConstraintCounterexampleProblem.mem_activeIneqIndexSet_iff xStar 1).2 (by
        simp [ConstrainedOptimizationProblem.ineqIndices, cubicConstraintCounterexampleProblem,
          cubicConstraintCounterexampleConstraint, cubicConstraintCounterexampleConstraint2,
          cubicConstraintCounterexampleSolution])
    have hConstraint1_nonneg :
        0 ≤ cubicConstraintCounterexampleProblem.linearizedConstraintPairing xStar d 0 :=
      hIneq 0 hactive0
    have hConstraint2_nonneg :
        0 ≤ cubicConstraintCounterexampleProblem.linearizedConstraintPairing xStar d 1 :=
      hIneq 1 hactive1
    rw [cubicConstraintCounterexample_linearizedConstraintPairing_constraint1] at hConstraint1_nonneg
    rw [cubicConstraintCounterexample_linearizedConstraintPairing_constraint2] at hConstraint2_nonneg
    -- The two active-constraint inequalities force `d 1` to be both nonnegative and nonpositive.
    linarith
  · intro hd1
    refine ⟨(show xStar ∈ cubicConstraintCounterexampleProblem from by
        change xStar ∈ cubicConstraintCounterexampleProblem.feasibleSet
        rw [mem_cubicConstraintCounterexampleProblem_feasibleSet_iff_coord_bounds]
        simp [cubicConstraintCounterexampleSolution]),
      cubicConstraintCounterexample_hasActiveConstraintGradientsAt, ?_, ?_⟩
    · -- There are no equality constraints in this problem.
      intro i hi
      simpa [ConstrainedOptimizationProblem.eqIndices, cubicConstraintCounterexampleProblem] using hi
    · intro i hi
      fin_cases i
      · -- The first active inequality says `-d₂ ≥ 0`, which is automatic when `d₂ = 0`.
        change 0 ≤ cubicConstraintCounterexampleProblem.linearizedConstraintPairing xStar d 0
        rw [cubicConstraintCounterexample_linearizedConstraintPairing_constraint1]
        simp [hd1]
      · -- The second active inequality says `d₂ ≥ 0`, also automatic when `d₂ = 0`.
        change 0 ≤ cubicConstraintCounterexampleProblem.linearizedConstraintPairing xStar d 1
        rw [cubicConstraintCounterexample_linearizedConstraintPairing_constraint2]
        simp [hd1]

/-- Helper for Chapter08 Example 8.2-extra-3: every sequential feasible direction lies in the
nonnegative horizontal ray. -/
theorem cubicConstraintCounterexample_mem_horizontalRay_of_mem_posTangentConeAt
    {d : Point}
    (hd : d ∈ posTangentConeAt cubicConstraintCounterexampleProblem.feasibleSet xStar) :
    d ∈ cubicConstraintCounterexampleHorizontalRay := by
  rcases (mem_posTangentConeAt_iff_exists_seq_pos).1 hd with
    ⟨dSeq, delta, hdelta_pos, hfeasible, hTendsto_dSeq, hTendsto_delta⟩
  rw [tendsto_pi_nhds] at hTendsto_dSeq
  have hTendsto_first :
      Filter.Tendsto (fun k ↦ dSeq k 0) Filter.atTop (nhds (d 0)) :=
    hTendsto_dSeq 0
  have hTendsto_second :
      Filter.Tendsto (fun k ↦ dSeq k 1) Filter.atTop (nhds (d 1)) :=
    hTendsto_dSeq 1
  have hsecond_nonneg : ∀ k, 0 ≤ dSeq k 1 := by
    intro k
    have hk_feasible :
        delta k • dSeq k ∈ cubicConstraintCounterexampleProblem.feasibleSet := by
      simpa [cubicConstraintCounterexampleSolution] using hfeasible k
    have hk_bounds :=
      (mem_cubicConstraintCounterexampleProblem_feasibleSet_iff_coord_bounds (delta k • dSeq k)).1
        hk_feasible
    have hk_scaled : 0 ≤ delta k * dSeq k 1 := by
      simpa [Pi.smul_apply] using hk_bounds.1
    nlinarith [hk_scaled, hdelta_pos k]
  have hfirst_nonneg : ∀ k, 0 ≤ dSeq k 0 := by
    intro k
    have hk_feasible :
        delta k • dSeq k ∈ cubicConstraintCounterexampleProblem.feasibleSet := by
      simpa [cubicConstraintCounterexampleSolution] using hfeasible k
    have hk_first_nonneg :
        0 ≤ (delta k • dSeq k) 0 :=
      cubicConstraintCounterexample_nonneg_first_of_feasible hk_feasible
    have hk_scaled : 0 ≤ delta k * dSeq k 0 := by
      simpa [Pi.smul_apply] using hk_first_nonneg
    nlinarith [hk_scaled, hdelta_pos k]
  have hsecond_le_rhs : ∀ k, dSeq k 1 ≤ delta k ^ (2 : ℕ) * dSeq k 0 ^ (3 : ℕ) := by
    intro k
    have hk_feasible :
        delta k • dSeq k ∈ cubicConstraintCounterexampleProblem.feasibleSet := by
      simpa [cubicConstraintCounterexampleSolution] using hfeasible k
    have hk_bounds :=
      (mem_cubicConstraintCounterexampleProblem_feasibleSet_iff_coord_bounds (delta k • dSeq k)).1
        hk_feasible
    have hk_scaled :
        delta k * dSeq k 1 ≤ delta k * (delta k ^ (2 : ℕ) * dSeq k 0 ^ (3 : ℕ)) := by
      simpa [Pi.smul_apply, mul_pow, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hk_bounds.2
    nlinarith [hk_scaled, hdelta_pos k]
  have hTendsto_rhs :
      Filter.Tendsto (fun k ↦ delta k ^ (2 : ℕ) * dSeq k 0 ^ (3 : ℕ))
        Filter.atTop (nhds (0 : ℝ)) := by
    have hdelta_sq :
        Filter.Tendsto (fun k ↦ delta k ^ (2 : ℕ)) Filter.atTop (nhds ((0 : ℝ) ^ (2 : ℕ))) :=
      hTendsto_delta.pow 2
    have hfirst_cube :
        Filter.Tendsto (fun k ↦ dSeq k 0 ^ (3 : ℕ)) Filter.atTop (nhds (d 0 ^ (3 : ℕ))) :=
      hTendsto_first.pow 3
    simpa using hdelta_sq.mul hfirst_cube
  have hd0_nonneg : 0 ≤ d 0 :=
    ge_of_tendsto' hTendsto_first hfirst_nonneg
  have hd1_nonneg : 0 ≤ d 1 :=
    ge_of_tendsto' hTendsto_second hsecond_nonneg
  have hd1_nonpos : d 1 ≤ 0 :=
    le_of_tendsto_of_tendsto' hTendsto_second hTendsto_rhs hsecond_le_rhs
  have hd1_zero : d 1 = 0 := le_antisymm hd1_nonpos hd1_nonneg
  -- The tangent-cone limit therefore lies on the nonnegative horizontal ray.
  exact (cubicConstraintCounterexample_mem_horizontalRay_iff d).2 ⟨hd0_nonneg, hd1_zero⟩

/-- Helper for Chapter08 Example 8.2-extra-3: every point on the nonnegative horizontal ray is a
sequential feasible direction. -/
theorem cubicConstraintCounterexample_horizontalRay_subset_posTangentConeAt :
    cubicConstraintCounterexampleHorizontalRay ⊆
      posTangentConeAt cubicConstraintCounterexampleProblem.feasibleSet xStar := by
  intro d hd
  rcases (cubicConstraintCounterexample_mem_horizontalRay_iff d).1 hd with ⟨hd0_nonneg, hd1_zero⟩
  refine (mem_posTangentConeAt_iff_exists_seq_pos).2 ?_
  refine ⟨fun _ ↦ d, fun k ↦ 1 / ((k : ℝ) + 1), ?_, ?_, ?_, ?_⟩
  · -- The standard reciprocal sequence gives strictly positive step sizes.
    intro k
    positivity
  · intro k
    have hdelta_nonneg : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
    have hscaled_nonneg : 0 ≤ (1 / ((k : ℝ) + 1)) * d 0 :=
      mul_nonneg hdelta_nonneg hd0_nonneg
    have hcube_nonneg : 0 ≤ ((1 / ((k : ℝ) + 1)) * d 0) ^ (3 : ℕ) := by positivity
    -- The explicit feasible points lie on the feasible horizontal ray `(t α, 0)`.
    simpa [cubicConstraintCounterexampleSolution,
      mem_cubicConstraintCounterexampleProblem_feasibleSet_iff_coord_bounds, Pi.smul_apply, hd1_zero]
      using And.intro (show (0 : ℝ) ≤ (1 / ((k : ℝ) + 1)) * d 1 by simp [hd1_zero])
        hcube_nonneg
  · -- The direction sequence is constant and converges to `d`.
    simpa using tendsto_const_nhds
  · -- The reciprocal step sizes converge to zero.
    exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Chapter08 Example 8.2-extra-3 (1): the origin `x* = (0, 0)` is a global minimizer of
`cubicConstraintCounterexampleProblem` on the feasible set cut out by `(x 0)^3 - x 1 ≥ 0` and
`x 1 ≥ 0`. -/
instance instCubicConstraintCounterexampleIsGlobalMinimizer :
    cubicConstraintCounterexampleProblem.IsGlobalMinimizer xStar where
  feasible := by
    -- The origin satisfies both defining inequalities with equality.
    change xStar ∈ cubicConstraintCounterexampleProblem.feasibleSet
    rw [mem_cubicConstraintCounterexampleProblem_feasibleSet_iff_coord_bounds]
    simp [cubicConstraintCounterexampleSolution]
  isMinOn := by
    rw [isMinOn_iff]
    intro x hx
    have hx0_nonneg := cubicConstraintCounterexample_nonneg_first_of_feasible hx
    -- Feasibility forces every admissible point to have objective value at least `0 = f(x*)`.
    change 0 ≤ x 0
    simpa [cubicConstraintCounterexampleObjective, cubicConstraintCounterexampleSolution] using
      hx0_nonneg

/-- Chapter08 Example 8.2-extra-3 (2): the source sequential feasible direction set `SFD(x*, X)`
is the nonnegative horizontal ray. Canonically, this is
`posTangentConeAt cubicConstraintCounterexampleProblem.feasibleSet xStar`. -/
theorem cubicConstraintCounterexample_sequentialFeasibleDirections_eq_horizontalRay :
    posTangentConeAt cubicConstraintCounterexampleProblem.feasibleSet xStar =
      cubicConstraintCounterexampleHorizontalRay := by
  ext d
  constructor
  · intro hd
    -- The hard direction extracts the sequential witnesses and squeezes the coordinates.
    exact cubicConstraintCounterexample_mem_horizontalRay_of_mem_posTangentConeAt hd
  · intro hd
    -- The converse direction uses the textbook explicit feasible ray.
    exact cubicConstraintCounterexample_horizontalRay_subset_posTangentConeAt hd

/-- Chapter08 Example 8.2-extra-3 (3): the linearized feasible direction set `LFD(x*, X)` of the
counterexample problem is the entire horizontal axis. -/
theorem cubicConstraintCounterexample_linearizedFeasibleDirections_eq_horizontalAxis :
    cubicConstraintCounterexampleProblem.linearizedFeasibleDirectionSet xStar =
      cubicConstraintCounterexampleHorizontalAxis := by
  ext d
  -- Both sides are exactly the condition that the second coordinate vanishes.
  rw [cubicConstraintCounterexample_mem_linearizedFeasibleDirectionSet_iff_second_eq_zero,
    cubicConstraintCounterexample_mem_horizontalAxis_iff]

/-- Chapter08 Example 8.2-extra-3 (4): the Chapter 8 constraint qualification `(8.2.19)` fails
at `x*` for `cubicConstraintCounterexampleProblem`. -/
theorem cubicConstraintCounterexample_constraintQualification_fails :
    ¬ cubicConstraintCounterexampleProblem.ConstraintQualificationAt xStar := by
  intro hCQ
  let witness : Point := EuclideanSpace.single 0 (-1 : ℝ)
  have hw_linearized :
      witness ∈ cubicConstraintCounterexampleProblem.linearizedFeasibleDirectionSet xStar := by
    rw [cubicConstraintCounterexample_linearizedFeasibleDirections_eq_horizontalAxis,
      cubicConstraintCounterexample_mem_horizontalAxis_iff]
    -- The witness lies on the horizontal axis because its second coordinate is zero.
    simp [witness, EuclideanSpace.single_apply]
  have hw_tangent :
      witness ∈ posTangentConeAt cubicConstraintCounterexampleProblem.feasibleSet xStar := by
    rw [hCQ]
    exact hw_linearized
  have hw_not_tangent :
      witness ∉ posTangentConeAt cubicConstraintCounterexampleProblem.feasibleSet xStar := by
    rw [cubicConstraintCounterexample_sequentialFeasibleDirections_eq_horizontalRay,
      cubicConstraintCounterexample_mem_horizontalRay_iff]
    -- The same witness is excluded from the tangent cone because its first coordinate is negative.
    simp [witness, EuclideanSpace.single_apply]
  exact hw_not_tangent hw_tangent

/-- Chapter08 Example 8.2-extra-3 (5): the objective gradient at `x* = 0` is `(1, 0)`. -/
theorem cubicConstraintCounterexample_gradient_objective :
    gradient cubicConstraintCounterexampleProblem.euclideanObjective xStarE =
      EuclideanSpace.single 0 (1 : ℝ) := by
  -- The objective is the first coordinate projection in Euclidean coordinates.
  exact hasGradientAt_cubicConstraintCounterexample_euclideanObjective.gradient

/-- Chapter08 Example 8.2-extra-3 (6): the gradient of the first inequality constraint at
`x* = 0` is `(0, -1)`. -/
theorem cubicConstraintCounterexample_gradient_constraint1 :
    gradient (cubicConstraintCounterexampleProblem.euclideanConstraint 0) xStarE =
      EuclideanSpace.single 1 (-1 : ℝ) := by
  -- The cubic term contributes no first-order part at the origin, leaving only `-x₂`.
  exact hasGradientAt_cubicConstraintCounterexample_euclideanConstraint1.gradient

/-- Chapter08 Example 8.2-extra-3 (7): the gradient of the second inequality constraint at
`x* = 0` is `(0, 1)`. -/
theorem cubicConstraintCounterexample_gradient_constraint2 :
    gradient (cubicConstraintCounterexampleProblem.euclideanConstraint 1) xStarE =
      EuclideanSpace.single 1 (1 : ℝ) := by
  -- The second constraint is exactly the second coordinate projection.
  exact hasGradientAt_cubicConstraintCounterexample_euclideanConstraint2.gradient

/-- Chapter08 Example 8.2-extra-3 (8): there are no real multipliers `λ₁` and `λ₂` with
`∇ f(x*) = λ₁ ∇ c₁(x*) + λ₂ ∇ c₂(x*)`. -/
theorem cubicConstraintCounterexample_no_multiplier_combination :
    ¬ ∃ lam1 lam2 : ℝ,
        gradient cubicConstraintCounterexampleProblem.euclideanObjective xStarE =
          lam1 • gradient (cubicConstraintCounterexampleProblem.euclideanConstraint 0) xStarE +
            lam2 •
              gradient (cubicConstraintCounterexampleProblem.euclideanConstraint 1) xStarE := by
  rintro ⟨lam1, lam2, hGradientEq⟩
  rw [cubicConstraintCounterexample_gradient_objective,
    cubicConstraintCounterexample_gradient_constraint1,
    cubicConstraintCounterexample_gradient_constraint2] at hGradientEq
  have hCoord0 : (EuclideanSpace.single 0 (1 : ℝ) : EPoint) 0 =
      (lam1 • EuclideanSpace.single 1 (-1 : ℝ) +
        lam2 • EuclideanSpace.single 1 (1 : ℝ) : EPoint) 0 :=
    congrArg (fun v : EPoint ↦ v 0) hGradientEq
  -- Reading the zeroth coordinate gives the contradiction `1 = 0`.
  simpa using hCoord0

end Chapter08Example82Extra3
