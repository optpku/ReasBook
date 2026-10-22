/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Order.Interval.Set.ProjIcc
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Definition_9_1_extra_1

noncomputable section

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin (n + n))

private abbrev point (x : Fin n → ℝ) : Point :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm x

private abbrev constraintPoint (x : Fin (n + n) → ℝ) : ConstraintPoint :=
  (EuclideanSpace.equiv (Fin (n + n)) ℝ).symm x

/-- The diagonal Hessian `Diag(h)` appearing in Exercise 9.1. -/
def chapter09Exercise91Hessian (h : Point) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal h

/-- The inequality matrix encoding the box constraints `-1 ≤ x i` and `-1 ≤ -x i`,
equivalently `|x i| ≤ 1`. -/
def chapter09Exercise91ConstraintMatrix : Matrix (Fin (n + n)) (Fin n) ℝ :=
  fun i ↦ match finSumFinEquiv.symm i with
  | Sum.inl j => Pi.single j (1 : ℝ)
  | Sum.inr j => Pi.single j (-1 : ℝ)

/-- The right-hand side vector `(-1, ..., -1)ᵀ` for the box constraints in Exercise 9.1. -/
def chapter09Exercise91ConstraintBound : ConstraintPoint :=
  constraintPoint fun _ ↦ (-1 : ℝ)

/-- The box feasible set of Exercise 9.1 is the cube `[-1, 1]^n`, written coordinatewise as
`|x i| ≤ 1`. -/
def chapter09Exercise91FeasibleSet : Set Point :=
  {x | ∀ i : Fin n, |x i| ≤ 1}

/-- Membership in `chapter09Exercise91FeasibleSet` is exactly the source box condition
`|x i| ≤ 1` for every coordinate. -/
@[simp] theorem chapter09Exercise91_mem_feasibleSet_iff (x : Point) :
    x ∈ chapter09Exercise91FeasibleSet ↔ ∀ i : Fin n, |x i| ≤ 1 :=
  Iff.rfl

/-- Exercise 9.1 as the chapter's canonical `QuadraticProgram`: diagonal Hessian `Diag(h)`,
linear term `g`, and the box feasible set `‖x‖∞ ≤ 1`. -/
def chapter09Exercise91Problem (h : Point) (g : Point) : QuadraticProgram n 0 (n + n) where
  G := chapter09Exercise91Hessian h
  hG_symm := by
    simp [chapter09Exercise91Hessian]
  g := g
  Aeq := 0
  beq := 0
  Aineq := chapter09Exercise91ConstraintMatrix
  bineq := chapter09Exercise91ConstraintBound

/-- Helper for Chapter09 Exercise 9.1: a quadratic program is evaluated by its quadratic
objective, matching the source-facing `P x` notation used in this exercise. -/
-- Local instance justification (notation bridge): this file records the source-facing objective
-- as `P x`, but the canonical owner `QuadraticProgram` only exposes `objective` explicitly.
local instance quadraticProgramCoeFun {n me mi : ℕ} :
    CoeFun (QuadraticProgram n me mi)
      (fun _ ↦ EuclideanSpace ℝ (Fin n) → ℝ) where
  coe P := P.objective

/-- Evaluating `chapter09Exercise91Problem` as a function recovers the source quadratic formula
with Hessian `chapter09Exercise91Hessian h = Diag(h)`. -/
@[simp] theorem chapter09Exercise91Problem_apply (h : Point) (g : Point) (x : Point) :
    chapter09Exercise91Problem h g x =
      (1 / 2 : ℝ) * dotProduct x ((chapter09Exercise91Hessian h).mulVec x) + dotProduct g x := by
  -- Route correction: expand the quadratic-program objective directly under the local CoeFun
  -- bridge instead of using the missing `QuadraticProgram.coeFn_apply` API.
  simp [chapter09Exercise91Problem, QuadraticProgram.objective]

/-- Helper for Chapter09 Exercise 9.1: each row of `chapter09Exercise91ConstraintMatrix`
extracts either `x j` or `-x j` from a point `x`. -/
private theorem chapter09Exercise91ConstraintMatrix_mulVec_sumCases
    (x : Fin n → ℝ) (i : Fin (n + n)) :
    (chapter09Exercise91ConstraintMatrix.mulVec x) i =
      match finSumFinEquiv.symm i with
      | Sum.inl j => x j
      | Sum.inr j => -x j := by
  rcases h : finSumFinEquiv.symm i with j | j
  · have hsum : ∑ b : Fin n, ((Pi.single j (1 : ℝ) : Fin n → ℝ) b) * x b = x j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    have hi : i = Fin.castAdd n j := by
      simpa using congrArg finSumFinEquiv h
    subst hi
    -- The first block is the row vector `e_jᵀ`, so the matrix-vector product is `x j`.
    simpa only [Matrix.mulVec, dotProduct, chapter09Exercise91ConstraintMatrix,
      finSumFinEquiv_symm_apply_castAdd] using hsum
  · have hsum : ∑ b : Fin n, ((Pi.single j (-1 : ℝ) : Fin n → ℝ) b) * x b = -x j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    have hi : i = Fin.natAdd n j := by
      simpa using congrArg finSumFinEquiv h
    subst hi
    -- The second block is the row vector `-e_jᵀ`, so the matrix-vector product is `-x j`.
    simpa only [Matrix.mulVec, dotProduct, chapter09Exercise91ConstraintMatrix,
      finSumFinEquiv_symm_apply_natAdd] using hsum

/-- Helper for Chapter09 Exercise 9.1: the first inequality block of
`chapter09Exercise91ConstraintMatrix` reads off the selected coordinate. -/
private theorem chapter09Exercise91ConstraintMatrix_mulVec_castAdd
    (x : Fin n → ℝ) (j : Fin n) :
    (chapter09Exercise91ConstraintMatrix.mulVec x) (Fin.castAdd n j) = x j := by
  have hsum : ∑ b : Fin n, ((Pi.single j (1 : ℝ) : Fin n → ℝ) b) * x b = x j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  simpa only [Matrix.mulVec, dotProduct, chapter09Exercise91ConstraintMatrix,
    finSumFinEquiv_symm_apply_castAdd] using hsum

/-- Helper for Chapter09 Exercise 9.1: the second inequality block of
`chapter09Exercise91ConstraintMatrix` reads off the negated selected coordinate. -/
private theorem chapter09Exercise91ConstraintMatrix_mulVec_natAdd
    (x : Fin n → ℝ) (j : Fin n) :
    (chapter09Exercise91ConstraintMatrix.mulVec x) (Fin.natAdd n j) = -x j := by
  have hsum : ∑ b : Fin n, ((Pi.single j (-1 : ℝ) : Fin n → ℝ) b) * x b = -x j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  simpa only [Matrix.mulVec, dotProduct, chapter09Exercise91ConstraintMatrix,
    finSumFinEquiv_symm_apply_natAdd] using hsum

/-- Helper for Chapter09 Exercise 9.1: the printed index form `j.addNat n` agrees with
`Fin.natAdd n j` after commuting natural-number addition. -/
private theorem chapter09Exercise91_addNat_eq_natAdd (j : Fin n) :
    j.addNat n = Fin.natAdd n j := by
  ext
  exact Nat.add_comm _ _

/-- The explicit box feasible set of Exercise 9.1 is exactly the feasible set of the chapter
owner `chapter09Exercise91Problem h g`. -/
theorem chapter09Exercise91_feasibleSet_eq_problem_feasibleSet
    (h : Point) (g : Point) :
    chapter09Exercise91FeasibleSet = (chapter09Exercise91Problem h g).feasibleSet := by
  ext x
  constructor
  · intro hx
    rw [QuadraticProgram.mem_feasibleSet_iff]
    constructor
    · -- The exercise has no equality constraints.
      simp [chapter09Exercise91Problem]
    · intro i
      -- After unfolding the program fields, the two inequality blocks become the box bounds.
      simp [chapter09Exercise91Problem, chapter09Exercise91ConstraintBound, constraintPoint]
      rw [chapter09Exercise91ConstraintMatrix_mulVec_sumCases (x := x.ofLp) (i := i)]
      rcases finSumFinEquiv.symm i with j | j
      · exact (abs_le.mp (hx j)).1
      · linarith [(abs_le.mp (hx j)).2]
  · intro hx
    rw [QuadraticProgram.mem_feasibleSet_iff] at hx
    refine (chapter09Exercise91_mem_feasibleSet_iff x).2 ?_
    intro j
    have hleft : (-1 : ℝ) ≤ x j := by
      have hj := hx.2 (Fin.castAdd n j)
      simpa [chapter09Exercise91Problem, chapter09Exercise91ConstraintBound, constraintPoint,
        chapter09Exercise91ConstraintMatrix_mulVec_castAdd (x := x.ofLp) j] using hj
    have hright : x j ≤ 1 := by
      have hj := hx.2 (Fin.natAdd n j)
      simp [chapter09Exercise91Problem, chapter09Exercise91ConstraintBound, constraintPoint] at hj
      rw [chapter09Exercise91_addNat_eq_natAdd j] at hj
      rw [chapter09Exercise91ConstraintMatrix_mulVec_natAdd (x := x.ofLp) j] at hj
      linarith
    exact abs_le.mpr ⟨hleft, hright⟩

/-- The source positivity condition `0 < h i` is exactly positive definiteness of the diagonal
Hessian `chapter09Exercise91Hessian h = Diag(h)`. -/
@[simp] theorem chapter09Exercise91Hessian_posDef_iff (h : Point) :
    (chapter09Exercise91Hessian h).PosDef ↔ ∀ i : Fin n, 0 < h i := by
  -- Positive definiteness of a real diagonal matrix is coordinatewise positivity.
  simp [chapter09Exercise91Hessian]

/-- The coordinatewise clipped unconstrained minimizer
`x i = max (-1) (min 1 (-g i / h i))`. -/
def chapter09Exercise91Minimizer (h : Point) (g : Point) : Point :=
  point fun i ↦ max (-1 : ℝ) (min (1 : ℝ) (-g i / h i))

/-- Evaluating the clipped minimizer at coordinate `i` recovers the source formula
`max (-1) (min 1 (-g i / h i))`. -/
@[simp] theorem chapter09Exercise91Minimizer_apply (h : Point) (g : Point) (i : Fin n) :
    chapter09Exercise91Minimizer h g i = max (-1 : ℝ) (min (1 : ℝ) (-g i / h i)) :=
  by
    simp [chapter09Exercise91Minimizer, point]

/-- Helper for Chapter09 Exercise 9.1: the quadratic objective separates into a sum of scalar
quadratics because the Hessian is diagonal. -/
lemma chapter09Exercise91Objective_eq_sum (h : Point) (g : Point) (x : Point) :
    chapter09Exercise91Problem h g x =
      ∑ i : Fin n, ((1 / 2 : ℝ) * h i * x i ^ (2 : ℕ) + g i * x i) := by
  -- Expand the diagonal quadratic form into independent coordinate contributions.
  simp only [chapter09Exercise91Problem, QuadraticProgram.objective, chapter09Exercise91Hessian,
    Matrix.mulVec_diagonal, dotProduct]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  congr with i
  ring

/-- Helper for Chapter09 Exercise 9.1: a scalar quadratic with positive coefficient is minimized
on `[-1, 1]` at the clipped unconstrained critical point. -/
lemma scalarQuadratic_le_atClippedPoint
    (a b t : ℝ) (ha : 0 < a) (ht : |t| ≤ 1) :
    (1 / 2 : ℝ) * a * (max (-1 : ℝ) (min (1 : ℝ) (-b / a))) ^ (2 : ℕ) +
        b * max (-1 : ℝ) (min (1 : ℝ) (-b / a)) ≤
      (1 / 2 : ℝ) * a * t ^ (2 : ℕ) + b * t := by
  let c : ℝ := -b / a
  let u : ℝ := max (-1 : ℝ) (min (1 : ℝ) c)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ht_bounds : -1 ≤ t ∧ t ≤ 1 := by
    simpa using abs_le.mp ht
  have hrewrite (z : ℝ) :
      (1 / 2 : ℝ) * a * z ^ (2 : ℕ) + b * z =
        (a / 2) * (z - c) ^ (2 : ℕ) - b ^ (2 : ℕ) / (2 * a) := by
    -- Complete the square around the unconstrained critical point `c = -b / a`.
    dsimp [c]
    field_simp [ha0]
    ring
  have hsquare : (u - c) ^ (2 : ℕ) ≤ (t - c) ^ (2 : ℕ) := by
    by_cases hc_low : c ≤ -1
    · have hu : u = -1 := by simp [u, hc_low]
      rw [hu]
      have hleft : -1 - c ≤ t - c := by linarith [ht_bounds.1]
      have hnonneg : 0 ≤ -1 - c := by linarith
      nlinarith
    · by_cases hc_high : 1 ≤ c
      · have hu : u = 1 := by simp [u, hc_high]
        rw [hu]
        have hright : c - 1 ≤ c - t := by linarith [ht_bounds.2]
        have hnonneg : 0 ≤ c - 1 := by linarith
        nlinarith
      · have hu : u = c := by
          have hc_left : -1 ≤ c := le_of_not_ge hc_low
          have hc_right : c ≤ 1 := le_of_not_ge hc_high
          simp [u, hc_left, hc_right]
        rw [hu]
        nlinarith [sq_nonneg (t - c)]
  calc
    (1 / 2 : ℝ) * a * (max (-1 : ℝ) (min (1 : ℝ) (-b / a))) ^ (2 : ℕ) +
        b * max (-1 : ℝ) (min (1 : ℝ) (-b / a))
        = (1 / 2 : ℝ) * a * u ^ (2 : ℕ) + b * u := by
          simp [u, c]
    _ = (a / 2) * (u - c) ^ (2 : ℕ) - b ^ (2 : ℕ) / (2 * a) := hrewrite u
    _ ≤ (a / 2) * (t - c) ^ (2 : ℕ) - b ^ (2 : ℕ) / (2 * a) := by
      -- Multiply the distance comparison by the nonnegative coefficient `a / 2`.
      have hcoef : 0 ≤ a / 2 := by positivity
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left hsquare hcoef) _
    _ = (1 / 2 : ℝ) * a * t ^ (2 : ℕ) + b * t := by
      rw [hrewrite]

/-- Helper for Chapter09 Exercise 9.1: the clipped coordinatewise minimizer satisfies the box
constraints `|x i| ≤ 1`. -/
lemma chapter09Exercise91Minimizer_mem_feasibleSet (h : Point) (g : Point) :
    chapter09Exercise91Minimizer h g ∈ chapter09Exercise91FeasibleSet := by
  have hIcc : (-1 : ℝ) ≤ 1 := by norm_num
  refine (chapter09Exercise91_mem_feasibleSet_iff _).2 ?_
  intro i
  -- Each coordinate is the projection of `-g i / h i` onto `[-1, 1]`.
  exact abs_le.mpr <| by
    simp [chapter09Exercise91Minimizer_apply, hIcc]

/-- Chapter09 Exercise 9.1: if the diagonal Hessian `chapter09Exercise91Hessian h = Diag(h)` is
positive definite, equivalently `0 < h i` for every `i`, then the minimizer over the box
`‖x‖∞ ≤ 1` is the coordinatewise clipped point
`x i = max (-1) (min 1 (-g i / h i))`. -/
theorem chapter09Exercise91_isMinOn
    (h : Point) (g : Point) (h_pos : ∀ i : Fin n, 0 < h i) :
    IsMinOn
      (chapter09Exercise91Problem h g)
      chapter09Exercise91FeasibleSet
      (chapter09Exercise91Minimizer h g) := by
  rw [isMinOn_iff]
  intro y hy
  have hy_box : ∀ i : Fin n, |y i| ≤ 1 :=
    (chapter09Exercise91_mem_feasibleSet_iff y).1 hy
  -- Compare the objective coordinatewise after rewriting it as a sum of scalar quadratics.
  calc
    chapter09Exercise91Problem h g (chapter09Exercise91Minimizer h g)
        = ∑ i : Fin n,
            ((1 / 2 : ℝ) * h i * (chapter09Exercise91Minimizer h g i) ^ (2 : ℕ) +
              g i * chapter09Exercise91Minimizer h g i) := by
          rw [chapter09Exercise91Objective_eq_sum]
    _ ≤ ∑ i : Fin n, ((1 / 2 : ℝ) * h i * y i ^ (2 : ℕ) + g i * y i) := by
          apply Finset.sum_le_sum
          intro i _
          simpa [chapter09Exercise91Minimizer_apply] using
            scalarQuadratic_le_atClippedPoint (h i) (g i) (y i) (h_pos i) (hy_box i)
    _ = chapter09Exercise91Problem h g y := by
          rw [chapter09Exercise91Objective_eq_sum]

end
