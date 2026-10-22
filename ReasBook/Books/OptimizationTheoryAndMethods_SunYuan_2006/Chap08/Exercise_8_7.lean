/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7

noncomputable section

-- Domain sampling:
-- * primary domain: two-variable constrained maximization and KKT conditions
-- * inspected owner declarations:
--   `ConstrainedOptimizationProblem` from `Chapter01.Definition_1_1_extra_1`
--   `ConstrainedOptimizationProblem.mem_feasibleSet_iff` from `Chapter08.Definition_8_1_1`
--   `ConstrainedOptimizationProblem.IsKKTPoint` from `Chapter08.Theorem_8_2_7`
--   `IsMaxOn` from mathlib's extremum API
-- * primitive data kept here: the concrete objective, feasible set, solution, and multiplier
--   candidate from Exercise 8.7
-- * core/canonical owner reused here: `ConstrainedOptimizationProblem` together with
--   `problem.IsKKTPoint`
-- * bridge/view API kept here: the coordinate identification of the concrete two-variable
--   exercise with the chapter owner via the canonical `Fin 2 → ℝ` vector literals `![x, y]`,
--   and the explicit scalar KKT equations for this problem

local notation "Point" => Fin 2 → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin 2)

/-- The objective `(x, y) ↦ (x + 1)^2 + (y + 1)^2` from Exercise 8.7. -/
def chapter08Exercise87Objective : ℝ × ℝ → ℝ
  | (x, y) => (x + 1) ^ (2 : ℕ) + (y + 1) ^ (2 : ℕ)

/-- The canonical constrained problem attached to Exercise 8.7: minimize the negated objective
subject to the inequality constraints `2 - x^2 - y^2 ≥ 0` and `1 - y ≥ 0`. -/
def chapter08Exercise87Problem :
    ConstrainedOptimizationProblem 2 2 (∅ : Set (Fin 2)) Set.univ where
  objective x := -chapter08Exercise87Objective (x 0, x 1)
  constraint i x :=
    if i = 0 then
      2 - x 0 ^ (2 : ℕ) - x 1 ^ (2 : ℕ)
    else
      1 - x 1
  eqIndices_union_ineqIndices := by
    simp
  eqIndices_disjoint_ineqIndices := by
    simp

@[simp] theorem chapter08Exercise87Problem_constraint_zero (x : Point) :
    chapter08Exercise87Problem.constraint 0 x =
      2 - x 0 ^ (2 : ℕ) - x 1 ^ (2 : ℕ) := by
  simp [chapter08Exercise87Problem]

@[simp] theorem chapter08Exercise87Problem_constraint_one (x : Point) :
    chapter08Exercise87Problem.constraint 1 x = 1 - x 1 := by
  simp [chapter08Exercise87Problem]

/-- The feasible set cut out by `x^2 + y^2 ≤ 2` and `1 - y ≥ 0`. -/
def chapter08Exercise87FeasibleSet : Set (ℝ × ℝ) :=
  {p | p.1 ^ (2 : ℕ) + p.2 ^ (2 : ℕ) ≤ 2 ∧ 1 - p.2 ≥ 0}

/-- The Chapter 8 owner and the source-facing feasible set describe the same feasible points. -/
theorem chapter08Exercise87_mem_problem_iff (p : ℝ × ℝ) :
    ![p.1, p.2] ∈ chapter08Exercise87Problem ↔
      p ∈ chapter08Exercise87FeasibleSet := by
  -- Unfold the owner feasibility conditions and rewrite the two inequality constraints explicitly.
  constructor
  · intro hp
    rcases (chapter08Exercise87Problem.mem_iff ![p.1, p.2]).1 hp with ⟨_, hineq⟩
    refine ⟨?_, ?_⟩
    · have hdisk : 0 ≤ chapter08Exercise87Problem.constraint 0 ![p.1, p.2] :=
        hineq 0 (by simp)
      simp only [chapter08Exercise87Problem_constraint_zero] at hdisk
      have hdisk' : 0 ≤ 2 - p.1 ^ (2 : ℕ) - p.2 ^ (2 : ℕ) := by
        simpa using hdisk
      nlinarith
    · have hcap : 0 ≤ chapter08Exercise87Problem.constraint 1 ![p.1, p.2] :=
        hineq 1 (by simp)
      simpa [chapter08Exercise87Problem_constraint_one] using hcap
  · rintro ⟨hdisk, hcap⟩
    refine (chapter08Exercise87Problem.mem_iff ![p.1, p.2]).2 ?_
    refine ⟨by simp, ?_⟩
    intro i hi
    fin_cases i
    · have hdisk' : 0 ≤ 2 - p.1 ^ (2 : ℕ) - p.2 ^ (2 : ℕ) := by
        nlinarith
      simpa using hdisk'
    · simpa [chapter08Exercise87Problem_constraint_one] using hcap

/-- Helper for Chapter08 Exercise 8.7: differentiating the shifted square in the first Euclidean
coordinate gives the expected linear form. -/
lemma chapter08Exercise87_first_shifted_square_fderiv (x y : ℝ) (z : EPoint) :
    fderiv ℝ (fun q : EPoint ↦ (q 0 + 1) ^ (2 : ℕ)) (WithLp.toLp 2 ![x, y]) z =
      2 * (x + 1) * z 0 := by
  let p : EPoint := WithLp.toLp 2 ![x, y]
  have h0 : DifferentiableAt ℝ (fun q : EPoint ↦ q 0) p :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := p) 0).differentiableAt
  have h0c : DifferentiableAt ℝ (fun q : EPoint ↦ q 0 + 1) p := h0.add_const 1
  have hs :
      ((2 : ℕ) • ((fun q : EPoint ↦ q 0 + 1) p) ^ (1 : ℕ) : ℝ) = 2 * (x + 1) := by
    simp [p]
    ring
  calc
    fderiv ℝ (fun q : EPoint ↦ (q 0 + 1) ^ (2 : ℕ)) p z
        = ((((2 : ℕ) • ((fun q : EPoint ↦ q 0 + 1) p) ^ (1 : ℕ)) : ℝ) •
            fderiv ℝ (fun q : EPoint ↦ q 0 + 1) p) z := by
            exact congrArg (fun L : EPoint →L[ℝ] ℝ ↦ L z) (fderiv_pow 2 h0c)
    _ = ((2 * (x + 1)) • fderiv ℝ (fun q : EPoint ↦ q 0 + 1) p) z := by
            rw [hs]
    _ = ((2 * (x + 1)) • fderiv ℝ (fun q : EPoint ↦ q 0) p) z := by
            rw [fderiv_add_const 1]
    _ = ((2 * (x + 1)) • PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0) z := by
            rw [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2)
              (E := fun _ : Fin 2 ↦ ℝ) (f := p) 0).fderiv]
    _ = 2 * (x + 1) * z 0 := by
            simp [PiLp.proj_apply, mul_comm, mul_assoc]

/-- Helper for Chapter08 Exercise 8.7: differentiating the shifted square in the second Euclidean
coordinate gives the expected linear form. -/
lemma chapter08Exercise87_second_shifted_square_fderiv (x y : ℝ) (z : EPoint) :
    fderiv ℝ (fun q : EPoint ↦ (q 1 + 1) ^ (2 : ℕ)) (WithLp.toLp 2 ![x, y]) z =
      2 * (y + 1) * z 1 := by
  let p : EPoint := WithLp.toLp 2 ![x, y]
  have h1 : DifferentiableAt ℝ (fun q : EPoint ↦ q 1) p :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := p) 1).differentiableAt
  have h1c : DifferentiableAt ℝ (fun q : EPoint ↦ q 1 + 1) p := h1.add_const 1
  have hs :
      ((2 : ℕ) • ((fun q : EPoint ↦ q 1 + 1) p) ^ (1 : ℕ) : ℝ) = 2 * (y + 1) := by
    simp [p]
    ring
  calc
    fderiv ℝ (fun q : EPoint ↦ (q 1 + 1) ^ (2 : ℕ)) p z
        = ((((2 : ℕ) • ((fun q : EPoint ↦ q 1 + 1) p) ^ (1 : ℕ)) : ℝ) •
            fderiv ℝ (fun q : EPoint ↦ q 1 + 1) p) z := by
            exact congrArg (fun L : EPoint →L[ℝ] ℝ ↦ L z) (fderiv_pow 2 h1c)
    _ = ((2 * (y + 1)) • fderiv ℝ (fun q : EPoint ↦ q 1 + 1) p) z := by
            rw [hs]
    _ = ((2 * (y + 1)) • fderiv ℝ (fun q : EPoint ↦ q 1) p) z := by
            rw [fderiv_add_const 1]
    _ = ((2 * (y + 1)) • PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1) z := by
            rw [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2)
              (E := fun _ : Fin 2 ↦ ℝ) (f := p) 1).fderiv]
    _ = 2 * (y + 1) * z 1 := by
            simp [PiLp.proj_apply, mul_comm, mul_assoc]

/-- Helper for Chapter08 Exercise 8.7: differentiating the first coordinate square gives the
expected linear form. -/
lemma chapter08Exercise87_first_square_fderiv (x y : ℝ) (z : EPoint) :
    fderiv ℝ (fun q : EPoint ↦ q 0 ^ (2 : ℕ)) (WithLp.toLp 2 ![x, y]) z =
      2 * x * z 0 := by
  let p : EPoint := WithLp.toLp 2 ![x, y]
  have h0 : DifferentiableAt ℝ (fun q : EPoint ↦ q 0) p :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := p) 0).differentiableAt
  have hs : ((2 : ℕ) • ((fun q : EPoint ↦ q 0) p) ^ (1 : ℕ) : ℝ) = 2 * x := by
    simp [p]
  calc
    fderiv ℝ (fun q : EPoint ↦ q 0 ^ (2 : ℕ)) p z
        = ((((2 : ℕ) • ((fun q : EPoint ↦ q 0) p) ^ (1 : ℕ)) : ℝ) •
            fderiv ℝ (fun q : EPoint ↦ q 0) p) z := by
            exact congrArg (fun L : EPoint →L[ℝ] ℝ ↦ L z) (fderiv_pow 2 h0)
    _ = ((2 * x) • fderiv ℝ (fun q : EPoint ↦ q 0) p) z := by
            rw [hs]
    _ = ((2 * x) • PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0) z := by
            rw [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2)
              (E := fun _ : Fin 2 ↦ ℝ) (f := p) 0).fderiv]
    _ = 2 * x * z 0 := by
            simp [PiLp.proj_apply, mul_comm, mul_assoc]

/-- Helper for Chapter08 Exercise 8.7: differentiating the second coordinate square gives the
expected linear form. -/
lemma chapter08Exercise87_second_square_fderiv (x y : ℝ) (z : EPoint) :
    fderiv ℝ (fun q : EPoint ↦ q 1 ^ (2 : ℕ)) (WithLp.toLp 2 ![x, y]) z =
      2 * y * z 1 := by
  let p : EPoint := WithLp.toLp 2 ![x, y]
  have h1 : DifferentiableAt ℝ (fun q : EPoint ↦ q 1) p :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := p) 1).differentiableAt
  have hs : ((2 : ℕ) • ((fun q : EPoint ↦ q 1) p) ^ (1 : ℕ) : ℝ) = 2 * y := by
    simp [p]
  calc
    fderiv ℝ (fun q : EPoint ↦ q 1 ^ (2 : ℕ)) p z
        = ((((2 : ℕ) • ((fun q : EPoint ↦ q 1) p) ^ (1 : ℕ)) : ℝ) •
            fderiv ℝ (fun q : EPoint ↦ q 1) p) z := by
            exact congrArg (fun L : EPoint →L[ℝ] ℝ ↦ L z) (fderiv_pow 2 h1)
    _ = ((2 * y) • fderiv ℝ (fun q : EPoint ↦ q 1) p) z := by
            rw [hs]
    _ = ((2 * y) • PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1) z := by
            rw [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2)
              (E := fun _ : Fin 2 ↦ ℝ) (f := p) 1).fderiv]
    _ = 2 * y * z 1 := by
            simp [PiLp.proj_apply, mul_comm, mul_assoc]

/-- Helper for Chapter08 Exercise 8.7: the Euclidean gradient of the negated objective is the
vector `(-2(x+1), -2(y+1))`. -/
lemma chapter08Exercise87_objective_gradient (x y : ℝ) :
    gradient chapter08Exercise87Problem.euclideanObjective (WithLp.toLp 2 ![x, y]) =
      WithLp.toLp 2 ![-2 * (x + 1), -2 * (y + 1)] := by
  let p : EPoint := WithLp.toLp 2 ![x, y]
  have h0 : DifferentiableAt ℝ (fun q : EPoint ↦ q 0) p :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := p) 0).differentiableAt
  have h1 : DifferentiableAt ℝ (fun q : EPoint ↦ q 1) p :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := p) 1).differentiableAt
  have hsq0 : DifferentiableAt ℝ (fun q : EPoint ↦ (q 0 + 1) ^ (2 : ℕ)) p :=
    (h0.add_const 1).pow 2
  have hsq1 : DifferentiableAt ℝ (fun q : EPoint ↦ (q 1 + 1) ^ (2 : ℕ)) p :=
    (h1.add_const 1).pow 2
  -- Identify the transported objective with the explicit quadratic and compute its gradient
  -- through the Fréchet derivative on arbitrary test directions.
  apply ext_inner_left ℝ
  intro z
  calc
    inner ℝ z (gradient chapter08Exercise87Problem.euclideanObjective p)
        = fderiv ℝ chapter08Exercise87Problem.euclideanObjective p z := by
            simp [inner_gradient_right]
    _ = -((2 * (x + 1) * z 0) + (2 * (y + 1) * z 1)) := by
          -- Expand the owner objective into the explicit shifted squares,
          -- then differentiate termwise.
          change
            (fderiv ℝ (fun q : EPoint ↦ -((q 0 + 1) ^ (2 : ℕ) + (q 1 + 1) ^ (2 : ℕ))) p) z =
              -((2 * (x + 1) * z 0) + (2 * (y + 1) * z 1))
          rw [fderiv_fun_neg]
          change
            (-(fderiv ℝ ((fun q : EPoint ↦ (q 0 + 1) ^ (2 : ℕ)) +
              fun q : EPoint ↦ (q 1 + 1) ^ (2 : ℕ)) p) z) =
              -((2 * (x + 1) * z 0) + (2 * (y + 1) * z 1))
          rw [fderiv_add hsq0 hsq1]
          rw [add_apply]
          rw [chapter08Exercise87_first_shifted_square_fderiv x y z,
            chapter08Exercise87_second_shifted_square_fderiv x y z]
    _ = inner ℝ z (WithLp.toLp 2 ![-2 * (x + 1), -2 * (y + 1)]) := by
          simp [PiLp.inner_apply, Fin.sum_univ_two]
          ring

/-- Helper for Chapter08 Exercise 8.7: the Euclidean gradient of the disk constraint
`2 - x^2 - y^2` is `(-2x, -2y)`. -/
lemma chapter08Exercise87_disk_constraint_gradient (x y : ℝ) :
    gradient (chapter08Exercise87Problem.euclideanConstraint 0) (WithLp.toLp 2 ![x, y]) =
      WithLp.toLp 2 ![-2 * x, -2 * y] := by
  let p : EPoint := WithLp.toLp 2 ![x, y]
  have h0 : DifferentiableAt ℝ (fun q : EPoint ↦ q 0) p :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := p) 0).differentiableAt
  have h1 : DifferentiableAt ℝ (fun q : EPoint ↦ q 1) p :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := p) 1).differentiableAt
  have hsq0 : DifferentiableAt ℝ (fun q : EPoint ↦ q 0 ^ (2 : ℕ)) p := h0.pow 2
  have hsq1 : DifferentiableAt ℝ (fun q : EPoint ↦ q 1 ^ (2 : ℕ)) p := h1.pow 2
  have hconstraint_eq :
      chapter08Exercise87Problem.euclideanConstraint 0 =
        fun q : EPoint ↦ 2 - (q 0 ^ (2 : ℕ) + q 1 ^ (2 : ℕ)) := by
    ext q
    simp [chapter08Exercise87Problem_constraint_zero]
    ring
  -- Rewrite the owner constraint to the explicit quadratic and compute its derivative
  -- against arbitrary directions.
  apply ext_inner_left ℝ
  intro z
  calc
    inner ℝ z (gradient (chapter08Exercise87Problem.euclideanConstraint 0) p)
        = fderiv ℝ (chapter08Exercise87Problem.euclideanConstraint 0) p z := by
            simp [inner_gradient_right]
    _ = -((2 * x * z 0) + (2 * y * z 1)) := by
          rw [hconstraint_eq]
          rw [fderiv_const_sub]
          change
            (-(fderiv ℝ ((fun q : EPoint ↦ q 0 ^ (2 : ℕ)) +
              fun q : EPoint ↦ q 1 ^ (2 : ℕ)) p) z) =
              -((2 * x * z 0) + (2 * y * z 1))
          rw [fderiv_add hsq0 hsq1]
          rw [add_apply]
          rw [chapter08Exercise87_first_square_fderiv x y z,
            chapter08Exercise87_second_square_fderiv x y z]
    _ = inner ℝ z (WithLp.toLp 2 ![-2 * x, -2 * y]) := by
          simp [PiLp.inner_apply, Fin.sum_univ_two]
          ring

/-- Helper for Chapter08 Exercise 8.7: the Euclidean gradient of the cap constraint `1 - y` is
`(0, -1)`. -/
lemma chapter08Exercise87_cap_constraint_gradient (x y : ℝ) :
    gradient (chapter08Exercise87Problem.euclideanConstraint 1) (WithLp.toLp 2 ![x, y]) =
      WithLp.toLp 2 ![0, -1] := by
  let p : EPoint := WithLp.toLp 2 ![x, y]
  -- The cap constraint is affine, so the derivative is just the negative second projection.
  apply ext_inner_left ℝ
  intro z
  calc
    inner ℝ z (gradient (chapter08Exercise87Problem.euclideanConstraint 1) p)
        = fderiv ℝ (chapter08Exercise87Problem.euclideanConstraint 1) p z := by
            simp [inner_gradient_right]
    _ = -(z 1) := by
          change (fderiv ℝ (fun q : EPoint ↦ 1 - q 1) p) z = -(z 1)
          rw [fderiv_const_sub]
          rw [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2)
            (E := fun _ : Fin 2 ↦ ℝ) (f := p) 1).fderiv]
          simp [PiLp.proj_apply]
    _ = inner ℝ z (WithLp.toLp 2 ![0, -1]) := by
          simp [PiLp.inner_apply, Fin.sum_univ_two]

/-- Helper for Chapter08 Exercise 8.7: the Euclidean stationarity condition for the canonical
Lagrangian is equivalent to the two scalar first-order equations. -/
lemma chapter08Exercise87_stationarity_iff (x y lam mu : ℝ) :
    gradient (chapter08Exercise87Problem.euclideanLagrangian ![lam, mu])
        (WithLp.toLp 2 ![x, y]) = 0 ↔
      (2 * (x + 1) - 2 * lam * x = 0) ∧
        (2 * (y + 1) - 2 * lam * y - mu = 0) := by
  have h0 : DifferentiableAt ℝ (fun q : Point ↦ q 0) ![x, y] := differentiableAt_apply 0 ![x, y]
  have h1 : DifferentiableAt ℝ (fun q : Point ↦ q 1) ![x, y] := differentiableAt_apply 1 ![x, y]
  have h_objective : DifferentiableAt ℝ chapter08Exercise87Problem.objective ![x, y] := by
    -- The owner objective is the negative of a quadratic polynomial in the two coordinates.
    change DifferentiableAt ℝ (fun q : Point ↦ -((q 0 + 1) ^ (2 : ℕ) + (q 1 + 1) ^ (2 : ℕ))) ![x, y]
    exact (((h0.add_const 1).pow 2).add ((h1.add_const 1).pow 2)).neg
  have h_constraints : chapter08Exercise87Problem.HasConstraintGradientsAt ![x, y] := by
    intro i
    fin_cases i
    · -- The disk constraint is a quadratic polynomial in the two coordinates.
      have hneg :
          DifferentiableAt ℝ
            (fun q : Point ↦ -(q 0 ^ (2 : ℕ)) + -(q 1 ^ (2 : ℕ))) ![x, y] :=
        (h0.pow 2).neg.add (h1.pow 2).neg
      simpa [chapter08Exercise87Problem, sub_eq_add_neg, add_assoc] using
        (differentiableAt_const 2).add hneg
    · -- The cap constraint is affine in the second coordinate.
      change DifferentiableAt ℝ (fun q : Point ↦ 1 - q 1) ![x, y]
      exact (differentiableAt_const 1).sub h1
  constructor
  · intro hstationary
    -- Rewrite the owner stationarity vector into the explicit objective and constraint gradients.
    rw [chapter08Exercise87Problem.gradient_euclideanLagrangian_eq_objective_sub_sum
      ![x, y] ![lam, mu] h_objective h_constraints,
      chapter08Exercise87_objective_gradient,
      Fin.sum_univ_two] at hstationary
    rw [chapter08Exercise87_disk_constraint_gradient,
      chapter08Exercise87_cap_constraint_gradient] at hstationary
    refine ⟨?_, ?_⟩
    · have hcoord := congrArg (fun v : EPoint ↦ v 0) hstationary
      simp at hcoord
      linarith
    · have hcoord := congrArg (fun v : EPoint ↦ v 1) hstationary
      simp at hcoord
      linarith
  · rintro ⟨hx, hy⟩
    -- Conversely, the two scalar equations kill the two coordinates of the stationarity vector.
    rw [chapter08Exercise87Problem.gradient_euclideanLagrangian_eq_objective_sub_sum
      ![x, y] ![lam, mu] h_objective h_constraints,
      chapter08Exercise87_objective_gradient,
      Fin.sum_univ_two]
    rw [chapter08Exercise87_disk_constraint_gradient,
      chapter08Exercise87_cap_constraint_gradient]
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · simp
      nlinarith [hx]
    · simp
      nlinarith [hy]

/-- The candidate maximizer `(1, 1)` of Exercise 8.7. -/
def chapter08Exercise87Solution : ℝ × ℝ :=
  (1, 1)

/-- The KKT multiplier candidate `(λ, μ) = (2, 0)` for `chapter08Exercise87Solution`. -/
def chapter08Exercise87Multiplier : ℝ × ℝ :=
  (2, 0)

/-- Chapter08 Exercise 8.7 (1): after rewriting the disk constraint as
`2 - x^2 - y^2 ≥ 0`, the canonical KKT owner for the minimization problem with objective
`-(chapter08Exercise87Objective)` is equivalent to the explicit scalar KKT system
`λ ≥ 0`, `μ ≥ 0`, primal feasibility, stationarity
`2 * (x + 1) - 2 * λ * x = 0`, `2 * (y + 1) - 2 * λ * y - μ = 0`,
and complementary slackness for `2 - x^2 - y^2` and `1 - y`. -/
theorem chapter08Exercise87_isKKTPoint_iff (x y lam mu : ℝ) :
    chapter08Exercise87Problem.IsKKTPoint
      ![x, y]
      ![lam, mu] ↔
      x ^ (2 : ℕ) + y ^ (2 : ℕ) ≤ 2 ∧
        1 - y ≥ 0 ∧
        lam ≥ 0 ∧
        mu ≥ 0 ∧
        (2 * (x + 1) - 2 * lam * x = 0) ∧
        (2 * (y + 1) - 2 * lam * y - mu = 0) ∧
        lam * (2 - x ^ (2 : ℕ) - y ^ (2 : ℕ)) = 0 ∧
        mu * (1 - y) = 0 := by
  constructor
  · intro h
    have hfeasible := (chapter08Exercise87_mem_problem_iff (x, y)).1 h.feasible
    refine ⟨hfeasible.1, hfeasible.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h.dualFeasible 0 (by simp [ConstrainedOptimizationProblem.ineqIndices])
    · exact h.dualFeasible 1 (by simp [ConstrainedOptimizationProblem.ineqIndices])
    · exact (chapter08Exercise87_stationarity_iff x y lam mu).1 h.stationarity |>.1
    · exact (chapter08Exercise87_stationarity_iff x y lam mu).1 h.stationarity |>.2
    · simpa [chapter08Exercise87Problem_constraint_zero] using
        h.complementarySlackness 0 (by simp [ConstrainedOptimizationProblem.ineqIndices])
    · simpa [chapter08Exercise87Problem_constraint_one] using
        h.complementarySlackness 1 (by simp [ConstrainedOptimizationProblem.ineqIndices])
  · rintro ⟨hdisk, hcap, hlam, hmu, hx, hy, hslackDisk, hslackCap⟩
    refine
      { feasible := (chapter08Exercise87_mem_problem_iff (x, y)).2 ⟨hdisk, hcap⟩
        dualFeasible := ?_
        stationarity := ?_
        complementarySlackness := ?_ }
    · intro i hi
      fin_cases i
      · simpa using hlam
      · simpa using hmu
    · exact (chapter08Exercise87_stationarity_iff x y lam mu).2 ⟨hx, hy⟩
    · intro i hi
      fin_cases i
      · simpa [chapter08Exercise87Problem_constraint_zero] using hslackDisk
      · simpa [chapter08Exercise87Problem_constraint_one] using hslackCap

/-- The explicit point `(1, 1)` with multipliers `(2, 0)` satisfies the canonical KKT
conditions for the Exercise 8.7 constrained problem. -/
theorem chapter08Exercise87_solutionSatisfiesKKT :
    chapter08Exercise87Problem.IsKKTPoint
      ![chapter08Exercise87Solution.1, chapter08Exercise87Solution.2]
      ![chapter08Exercise87Multiplier.1, chapter08Exercise87Multiplier.2] := by
  -- Plug the candidate primal point and multipliers into the scalar KKT system.
  have hkkt :=
    (chapter08Exercise87_isKKTPoint_iff 1 1 2 0).2
      (by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num)
  simpa [chapter08Exercise87Solution, chapter08Exercise87Multiplier] using hkkt

/-- Helper for Chapter08 Exercise 8.7: every feasible point satisfies the global objective bound
coming from the disk constraint and the inequality `x + y ≤ 2`. -/
lemma chapter08Exercise87_objective_le_solution_of_mem_feasibleSet {p : ℝ × ℝ}
    (hp : p ∈ chapter08Exercise87FeasibleSet) :
    chapter08Exercise87Objective p ≤ chapter08Exercise87Objective chapter08Exercise87Solution := by
  rcases hp with ⟨hdisk, _⟩
  have hxy : p.1 + p.2 ≤ 2 := by
    -- The nonnegativity of `(x - y)^2` upgrades the disk bound to the linear bound `x + y ≤ 2`.
    nlinarith [sq_nonneg (p.1 - p.2)]
  have hsolution : chapter08Exercise87Objective chapter08Exercise87Solution = 8 := by
    norm_num [chapter08Exercise87Objective, chapter08Exercise87Solution]
  rw [hsolution]
  -- Expand the objective and combine the disk and linear bounds.
  change (p.1 + 1) ^ (2 : ℕ) + (p.2 + 1) ^ (2 : ℕ) ≤ 8
  nlinarith

/-- Chapter08 Exercise 8.7 (2): the maximization problem on
`chapter08Exercise87FeasibleSet` is solved by `(1, 1)`. -/
theorem chapter08Exercise87_solution :
    IsMaxOn chapter08Exercise87Objective chapter08Exercise87FeasibleSet
      chapter08Exercise87Solution := by
  -- The global bound on the objective over the feasible set is exactly the `IsMaxOn` condition.
  rw [isMaxOn_iff]
  intro p hp
  exact chapter08Exercise87_objective_le_solution_of_mem_feasibleSet hp
