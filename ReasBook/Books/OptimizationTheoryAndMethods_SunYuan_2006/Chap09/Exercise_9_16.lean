/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Algorithm_9_7_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Definition_9_1_extra_1

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)
local notation "ConstraintMatrix" => Matrix (Fin m) (Fin n) ℝ

open Matrix

-- Domain-style sampling in Chapter 9:
-- * source-facing layer here: convex quadratic programs in the standard primal-dual interior-point
--   form `min (1 / 2) xᵀ Q x + cᵀ x` subject to `A x = b` and `x ≥ 0`;
-- * core/canonical owner upstream: `QuadraticProgram n me mi` from
--   `Definition_9_1_extra_1`, together with the Chapter 9 primal-dual state API from
--   `Algorithm_9_7_1`;
-- * bridge/view here: `toQuadraticProgram`, specializing the canonical owner to the standard-form
--   inequality block `x ≥ 0`.

/-- A convex quadratic program in the equality-constrained standard form
`min (1 / 2) xᵀ Q x + cᵀ x` subject to `A x = b` and `x ≥ 0`. Convexity is recorded by the
positive-semidefiniteness of `Q`. -/
structure ConvexQuadraticProgram (n m : ℕ) where
  Q : Matrix (Fin n) (Fin n) ℝ
  hQ_convex : Q.PosSemidef
  c : EuclideanSpace ℝ (Fin n)
  A : Matrix (Fin m) (Fin n) ℝ
  b : EuclideanSpace ℝ (Fin m)

namespace ConvexQuadraticProgram

/-- Positive semidefiniteness makes the Hessian matrix symmetric, so the Chapter 9 quadratic
program owner applies directly. -/
theorem hQ_symm (P : ConvexQuadraticProgram n m) : P.Q.IsSymm := by
  simpa [Matrix.isHermitian_iff_isSymm] using P.hQ_convex.isHermitian

/-- The canonical Chapter 9 quadratic-program view of a standard-form convex quadratic
program. -/
abbrev toQuadraticProgram (P : ConvexQuadraticProgram n m) :
    QuadraticProgram n m n where
  G := P.Q
  hG_symm := P.hQ_symm
  g := P.c
  Aeq := P.A
  beq := P.b
  Aineq := 1
  bineq := 0

/-- The canonical owner coercion for standard-form convex quadratic programs. -/
instance : Coe (ConvexQuadraticProgram n m) (QuadraticProgram n m n) where
  coe P := P.toQuadraticProgram

/-- The source objective is the quadratic objective of the associated canonical quadratic
program. -/
abbrev objective (P : ConvexQuadraticProgram n m) : Point → ℝ :=
  P.toQuadraticProgram.objective

/-- A standard-form convex quadratic program can be evaluated as its quadratic objective. -/
instance : CoeFun (ConvexQuadraticProgram n m) (fun _ ↦ Point → ℝ) where
  coe P := P.objective

/-- Evaluating a standard-form convex quadratic program as a function returns its canonical
quadratic objective. -/
theorem coe_apply (P : ConvexQuadraticProgram n m) (x : Point) :
    P x = P.objective x :=
  rfl

/-- Evaluating `P.objective` expands to the source formula
`x ↦ (1 / 2) xᵀ Q x + cᵀ x`. -/
theorem objective_eq (P : ConvexQuadraticProgram n m) (x : Point) :
    P.objective x =
      (1 / 2 : ℝ) * dotProduct x (P.Q.mulVec x) + dotProduct P.c x :=
  rfl

/-- The feasible set is the standard-form feasible set of the associated canonical quadratic
program. -/
abbrev feasibleSet (P : ConvexQuadraticProgram n m) : Set Point :=
  P.toQuadraticProgram.feasibleSet

/-- Feasibility in a standard-form convex quadratic program means satisfying the equality
constraints together with the coordinatewise inequalities `x ≥ 0`. -/
instance : Membership Point (ConvexQuadraticProgram n m) where
  mem P x := x ∈ P.feasibleSet

/-- Membership in a standard-form convex quadratic program means solving `A x = b` with
coordinatewise nonnegativity `x ≥ 0`. -/
@[simp] theorem mem_iff (P : ConvexQuadraticProgram n m) (x : Point) :
    x ∈ P ↔ P.A.mulVec x = P.b ∧ ∀ i : Fin n, 0 ≤ x i := by
  change x ∈ P.feasibleSet ↔ P.A.mulVec x = P.b ∧ ∀ i : Fin n, 0 ≤ x i
  constructor
  · intro hx
    rcases (QuadraticProgram.mem_feasibleSet_iff P.toQuadraticProgram x).1 hx with ⟨hEq, hIneq⟩
    refine ⟨hEq, ?_⟩
    intro i
    simpa [ConvexQuadraticProgram.feasibleSet, ConvexQuadraticProgram.toQuadraticProgram] using
      hIneq i
  · rintro ⟨hEq, hIneq⟩
    refine (QuadraticProgram.mem_feasibleSet_iff P.toQuadraticProgram x).2 ?_
    refine ⟨hEq, ?_⟩
    intro i
    simpa [ConvexQuadraticProgram.feasibleSet, ConvexQuadraticProgram.toQuadraticProgram] using
      hIneq i

/-- Membership in `P.feasibleSet` means solving `A x = b` with coordinatewise nonnegativity
`x ≥ 0`. -/
@[simp] theorem mem_feasibleSet_iff (P : ConvexQuadraticProgram n m) (x : Point) :
    x ∈ P.feasibleSet ↔ P.A.mulVec x = P.b ∧ ∀ i : Fin n, 0 ≤ x i :=
  P.mem_iff x

end ConvexQuadraticProgram

namespace ConvexQuadraticProgram

/-- The strictly feasible set of `P` consists of the states `(x, y, z)` satisfying the primal
equations `A x = b`, the dual equations `Aᵀ y + z = Q x + c`, and strict positivity of `x`
and `z`, represented here by the reused state fields `lam` and `s`. -/
def strictlyFeasibleSet (P : ConvexQuadraticProgram n m) : Set (PrimalDualState n m) :=
  {w |
    P.A.mulVec w.x = P.b ∧
      mulVec P.A.transpose w.lam + w.s = P.Q.mulVec w.x + P.c ∧
      IsStrictlyPositive w.x ∧
      IsStrictlyPositive w.s}

/-- Membership in `P.strictlyFeasibleSet` is exactly strict primal-dual feasibility for the
convex quadratic program `P`. -/
@[simp] theorem mem_strictlyFeasibleSet_iff
    (P : ConvexQuadraticProgram n m) (w : PrimalDualState n m) :
    w ∈ P.strictlyFeasibleSet ↔
      P.A.mulVec w.x = P.b ∧
        mulVec P.A.transpose w.lam + w.s = P.Q.mulVec w.x + P.c ∧
        IsStrictlyPositive w.x ∧
        IsStrictlyPositive w.s :=
  Iff.rfl

/-- `P.solvesPrimalDualNewtonSystem w σ d` is the convex-quadratic analogue of the
Section 9.7 primal-dual Newton system: the linearized primal equation, the linearized dual
equation with Hessian term `Q Δx`, and the coordinatewise perturbed complementarity
equation. -/
def solvesPrimalDualNewtonSystem
    (P : ConvexQuadraticProgram n m) (w : PrimalDualState n m) (sigma : ℝ)
    (d : PrimalDualDirection n m) : Prop :=
  mulVec P.A.transpose d.dlam + d.ds = P.Q.mulVec d.dx ∧
    P.A.mulVec d.dx = 0 ∧
    ∀ i : Fin n, w.s i * d.dx i + w.x i * d.ds i = w.complementarityCorrection sigma i

/-- Unfolding `P.solvesPrimalDualNewtonSystem w σ d` gives the three block equations of the
primal-dual Newton system for the convex quadratic program `P`. -/
@[simp] theorem solvesPrimalDualNewtonSystem_iff
    (P : ConvexQuadraticProgram n m) (w : PrimalDualState n m) (sigma : ℝ)
    (d : PrimalDualDirection n m) :
    P.solvesPrimalDualNewtonSystem w sigma d ↔
      mulVec P.A.transpose d.dlam + d.ds = P.Q.mulVec d.dx ∧
        P.A.mulVec d.dx = 0 ∧
        (∀ i : Fin n,
          w.s i * d.dx i + w.x i * d.ds i = w.complementarityCorrection sigma i) :=
  Iff.rfl

end ConvexQuadraticProgram

/-- Chapter09 Exercise 9.16: a primal-dual interior-point framework for the convex quadratic
program `P`, obtained by extending the Section 9.7 linear-program scheme `(9.7.20)`-`(9.7.21)`
with the quadratic Hessian term `Q Δx` in the dual linearization. The sequence `state k`
represents `(xᵏ, yᵏ, zᵏ)`, `direction k` represents `(Δxᵏ, Δyᵏ, Δzᵏ)`, `sigma k ∈ [0, 1]` is
the centering parameter `σ_k`, and `alpha k` is the step length. The initial state is strictly
feasible, each direction solves the convex-quadratic primal-dual Newton system, and the next
iterate is updated by `(x, y, z) ↦ (x, y, z) + α (Δx, Δy, Δz)` with `x` and `z` staying
strictly positive. -/
structure ConvexQuadraticPrimalDualInteriorPointFramework
    (P : ConvexQuadraticProgram n m) where
  state : ℕ → PrimalDualState n m
  direction : ℕ → PrimalDualDirection n m
  sigma : ℕ → ℝ
  alpha : ℕ → ℝ
  initial_mem : state 0 ∈ P.strictlyFeasibleSet
  sigma_mem_Icc : ∀ k : ℕ, sigma k ∈ Set.Icc (0 : ℝ) 1
  newton_system :
    ∀ k : ℕ, P.solvesPrimalDualNewtonSystem (state k) (sigma k) (direction k)
  update :
    ∀ k : ℕ, state (k + 1) = (state k).updated (alpha k) (direction k)
  next_strictPos :
    ∀ k : ℕ,
      IsStrictlyPositive (state (k + 1)).x ∧
        IsStrictlyPositive (state (k + 1)).s

/-- A convex-quadratic primal-dual interior-point framework can be evaluated as its state
sequence. -/
instance
    (P : ConvexQuadraticProgram n m) :
    CoeFun
      (ConvexQuadraticPrimalDualInteriorPointFramework P)
      (fun _ ↦ ℕ → PrimalDualState n m) where
  coe F := F.state

namespace ConvexQuadraticPrimalDualInteriorPointFramework

/-- The quantity `μ_k` is the complementarity average of the current primal-dual-slack state. -/
def mu
    {P : ConvexQuadraticProgram n m}
    (F : ConvexQuadraticPrimalDualInteriorPointFramework P) (k : ℕ) : ℝ :=
  (F.state k).complementarityAverage

/-- The framework quantity `μ_k` is definitionally the complementarity average
`(state k).xᵀ (state k).z / n`. -/
@[simp] theorem mu_eq
    {P : ConvexQuadraticProgram n m}
    (F : ConvexQuadraticPrimalDualInteriorPointFramework P) (k : ℕ) :
    F.mu k = (F.state k).complementarityAverage :=
  rfl

/-- Evaluating a convex-quadratic primal-dual interior-point framework as a function returns its
state sequence. -/
@[simp] theorem coe_apply
    {P : ConvexQuadraticProgram n m}
    (F : ConvexQuadraticPrimalDualInteriorPointFramework P) (k : ℕ) :
    F k = F.state k :=
  rfl

/-- Unfolding `ConvexQuadraticPrimalDualInteriorPointFramework` gives the strict-feasible
initialization, the centering parameters `σ_k ∈ [0, 1]`, the complementarity averages `μ_k`,
the convex-quadratic Newton solves, the affine updates, and the strict positivity of the next
primal and slack iterates. -/
theorem spec
    {P : ConvexQuadraticProgram n m}
    (F : ConvexQuadraticPrimalDualInteriorPointFramework P) :
    F.state 0 ∈ P.strictlyFeasibleSet ∧
      (∀ k : ℕ, F.sigma k ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ k : ℕ, F.mu k = (F.state k).complementarityAverage) ∧
      (∀ k : ℕ, P.solvesPrimalDualNewtonSystem (F.state k) (F.sigma k) (F.direction k)) ∧
      (∀ k : ℕ, F.state (k + 1) = (F.state k).updated (F.alpha k) (F.direction k)) ∧
      (∀ k : ℕ,
        IsStrictlyPositive (F.state (k + 1)).x ∧
          IsStrictlyPositive (F.state (k + 1)).s) := by
  exact ⟨F.initial_mem, F.sigma_mem_Icc, fun k ↦ F.mu_eq k, F.newton_system, F.update,
    F.next_strictPos⟩

end ConvexQuadraticPrimalDualInteriorPointFramework

end
