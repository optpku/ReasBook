/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Definition_9_1_extra_1

noncomputable section

section Chapter12Definition12_2Extra1

variable {n me mi : ℕ}

local notation "Direction" => Fin n → ℝ
local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "EqPoint" => EuclideanSpace ℝ (Fin me)
local notation "IneqPoint" => EuclideanSpace ℝ (Fin mi)
local notation "pointEquiv" => (EuclideanSpace.equiv (Fin n) ℝ)
local notation "eqResidualEquiv" => (EuclideanSpace.equiv (Fin me) ℝ)
local notation "ineqResidualEquiv" => (EuclideanSpace.equiv (Fin mi) ℝ)
local notation "EqResidual" => Fin me → ℝ
local notation "IneqResidual" => Fin mi → ℝ
local notation "EqMultiplier" => Fin me → ℝ
local notation "IneqMultiplier" => Fin mi → ℝ

-- Domain-style sampling for this refine pass:
-- * primary domain: SQP quadratic subproblems and KKT conditions for Wilson-Han-Powell steps;
-- * inspected owner/data declarations:
--   `TrustRegionSubproblem.IsSolution`,
--   `QuadraticProgram.feasibleSet`,
--   `QuadraticProgram.objective`,
--   and `IsMinOn`;
-- * core/canonical owner for optimality: feasibility together with `IsMinOn` on the subproblem
--   objective and feasible set;
-- * primitive data here: the Wilson-Han-Powell quadratic model and the linearized
--   equality/inequality blocks from `(12.2.1)`-`(12.2.3)`;
-- * derived API here: feasibility as set membership, search-direction optimality, and KKT
--   multipliers.
-- This file keeps the source-facing subproblem data instead of collapsing directly to
-- `QuadraticProgram`, because the current item does not assume the Hessian approximation `B`
-- is symmetric.

/-- The Wilson-Han-Powell quadratic subproblem on `ℝ^n`
records the Hessian approximation `B`, the linear term `g = ∇ f(x_k)`, the equality block
`Aeq.mulVec d + ceq = 0`, and the inequality block `Aineq.mulVec d + cineq ≥ 0` from
`(12.2.1)`-`(12.2.4)`. Here the rows of `Aeq` and `Aineq` encode the vectors `a_i(x_k)ᵀ`. -/
structure WilsonHanPowellSubproblem (n me mi : ℕ) where
  B : Matrix (Fin n) (Fin n) ℝ
  g : Fin n → ℝ
  Aeq : Matrix (Fin me) (Fin n) ℝ
  ceq : Fin me → ℝ
  Aineq : Matrix (Fin mi) (Fin n) ℝ
  cineq : Fin mi → ℝ

namespace WilsonHanPowellSubproblem

/-- The quadratic objective `d ↦ gᵀ d + (1 / 2) dᵀ B d` of the Wilson-Han-Powell subproblem. -/
def objective
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) : ℝ :=
  dotProduct P.g d + (1 / 2 : ℝ) * dotProduct d (P.B.mulVec d)

/-- If `B` is symmetric, the Wilson-Han-Powell subproblem is the Chapter 9 quadratic-program
owner with right-hand sides `-ceq` and `-cineq`, so that the source constraints
`Aeq.mulVec d + ceq = 0` and `0 ≤ Aineq.mulVec d + cineq` become
`Aeq.mulVec x = -ceq` and `-cineq ≤ Aineq.mulVec x`. -/
abbrev toQuadraticProgram
    (P : WilsonHanPowellSubproblem n me mi) (hB : P.B.IsSymm) :
    QuadraticProgram n me mi where
  G := P.B
  hG_symm := hB
  g := WithLp.toLp 2 P.g
  Aeq := P.Aeq
  beq := WithLp.toLp 2 (-P.ceq)
  Aineq := P.Aineq
  bineq := WithLp.toLp 2 (-P.cineq)

/-- A Wilson-Han-Powell subproblem can be evaluated as its quadratic objective. -/
instance : CoeFun (WilsonHanPowellSubproblem n me mi) (fun _ ↦ Direction → ℝ) where
  coe P := P.objective

/-- Evaluating a Wilson-Han-Powell subproblem as a function returns its quadratic objective. -/
@[simp] theorem coe_apply
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) :
    P d = P.objective d :=
  rfl

/-- Unfolding `P.objective d` gives the source quadratic formula from `(12.2.1)`. -/
theorem objective_eq
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) :
    P.objective d =
      dotProduct P.g d + (1 / 2 : ℝ) * dotProduct d (P.B.mulVec d) :=
  rfl

/-- Under `P.B.IsSymm`, the source quadratic model is the Chapter 9 quadratic-program objective
transported along the coordinate equivalence `EuclideanSpace ℝ (Fin n) ≃L[ℝ] Fin n → ℝ`. -/
theorem toQuadraticProgram_objective_eq
    (P : WilsonHanPowellSubproblem n me mi) (hB : P.B.IsSymm) (x : Point) :
    (P.toQuadraticProgram hB).objective x = P.objective (pointEquiv x) := by
  rw [QuadraticProgram.objective_eq, objective_eq]
  have hxcoord : pointEquiv x = x.ofLp := rfl
  rw [hxcoord]
  simp
  ring

/-- The feasible set of the Wilson-Han-Powell subproblem consists of the directions satisfying
the linearized equality constraints and all linearized inequality constraints from
`(12.2.2)`-`(12.2.3)`. -/
def feasibleSet (P : WilsonHanPowellSubproblem n me mi) : Set Direction :=
  {d |
  P.Aeq.mulVec d + P.ceq = 0 ∧
    ∀ i : Fin mi, 0 ≤ (P.Aineq.mulVec d) i + P.cineq i}

/-- Membership in a Wilson-Han-Powell subproblem is feasibility for its linearized
constraints. -/
instance : Membership Direction (WilsonHanPowellSubproblem n me mi) where
  mem P d := d ∈ WilsonHanPowellSubproblem.feasibleSet P

/-- Membership in `P.feasibleSet` gives the equality and inequality conditions from
`(12.2.2)`-`(12.2.3)`. -/
@[simp] theorem mem_feasibleSet_iff
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) :
    d ∈ P.feasibleSet ↔
      P.Aeq.mulVec d + P.ceq = 0 ∧
        ∀ i : Fin mi, 0 ≤ (P.Aineq.mulVec d) i + P.cineq i :=
  Iff.rfl

/-- Under `P.B.IsSymm`, feasibility for the Chapter 9 quadratic-program bridge is exactly the
source Wilson-Han-Powell feasibility condition after transporting `x : EuclideanSpace ℝ (Fin n)`
to its coordinate vector `pointEquiv x`. -/
theorem mem_toQuadraticProgram_feasibleSet_iff
    (P : WilsonHanPowellSubproblem n me mi) (hB : P.B.IsSymm) (x : Point) :
    x ∈ (P.toQuadraticProgram hB).feasibleSet ↔ pointEquiv x ∈ P := by
  constructor
  · intro hx
    rcases (QuadraticProgram.mem_feasibleSet_iff (P.toQuadraticProgram hB) x).1 hx with
      ⟨hEq, hIneq⟩
    change pointEquiv x ∈ P.feasibleSet
    rw [show pointEquiv x = x.ofLp by rfl]
    refine (WilsonHanPowellSubproblem.mem_feasibleSet_iff P x.ofLp).2 ?_
    refine ⟨?_, ?_⟩
    · ext i
      have hi := congrArg (fun y : EqResidual ↦ y i) hEq
      have hi' : P.Aeq.mulVec x.ofLp i = -P.ceq i := by
        simpa [toQuadraticProgram] using hi
      change P.Aeq.mulVec x.ofLp i + P.ceq i = 0
      exact eq_neg_iff_add_eq_zero.mp hi'
    · intro i
      have hi := hIneq i
      have hi' : -P.cineq i ≤ P.Aineq.mulVec x.ofLp i := by
        simpa [toQuadraticProgram] using hi
      change 0 ≤ P.Aineq.mulVec x.ofLp i + P.cineq i
      exact neg_le_iff_add_nonneg.mp hi'
  · intro hx
    change pointEquiv x ∈ P.feasibleSet at hx
    rw [show pointEquiv x = x.ofLp by rfl] at hx
    rcases (WilsonHanPowellSubproblem.mem_feasibleSet_iff P x.ofLp).1 hx with
      ⟨hEq, hIneq⟩
    refine (QuadraticProgram.mem_feasibleSet_iff (P.toQuadraticProgram hB) x).2 ?_
    refine ⟨?_, ?_⟩
    · ext i
      have hxcoord : pointEquiv x = x.ofLp := by rfl
      have hi : P.Aeq.mulVec x.ofLp i + P.ceq i = 0 := by
        simpa [hxcoord] using congrArg (fun y : EqResidual ↦ y i) hEq
      exact (eq_neg_iff_add_eq_zero.mpr hi : P.Aeq.mulVec x.ofLp i = -P.ceq i)
    · intro i
      have hi : 0 ≤ P.Aineq.mulVec x.ofLp i + P.cineq i := hIneq i
      exact (neg_le_iff_add_nonneg.mpr hi : -P.cineq i ≤ P.Aineq.mulVec x.ofLp i)

/-- Unfolding `d ∈ P` gives the equality and inequality conditions from `(12.2.2)`-`(12.2.3)`. -/
@[simp] theorem mem_iff
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) :
    d ∈ P ↔
      P.Aeq.mulVec d + P.ceq = 0 ∧
        ∀ i : Fin mi, 0 ≤ (P.Aineq.mulVec d) i + P.cineq i :=
  by
    change d ∈ P.feasibleSet ↔
      P.Aeq.mulVec d + P.ceq = 0 ∧
        ∀ i : Fin mi, 0 ≤ (P.Aineq.mulVec d) i + P.cineq i
    exact WilsonHanPowellSubproblem.mem_feasibleSet_iff P d

/-- A direction solves the Wilson-Han-Powell subproblem when it is feasible and minimizes the
quadratic objective over all feasible directions. -/
def IsSolution
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) : Prop :=
  d ∈ P ∧ IsMinOn P P.feasibleSet d

/-- Under `P.B.IsSymm`, minimizers of the source subproblem are exactly minimizers of the
associated canonical quadratic program after transporting along `pointEquiv`. -/
theorem isMinOn_toQuadraticProgram_iff
    (P : WilsonHanPowellSubproblem n me mi) (hB : P.B.IsSymm) (x : Point) :
    IsMinOn (P.toQuadraticProgram hB) (P.toQuadraticProgram hB).feasibleSet x ↔
      IsMinOn P P.feasibleSet (pointEquiv x) := by
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro h d hd
    have hd'' : pointEquiv ((EuclideanSpace.equiv (Fin n) ℝ).symm d) ∈ P.feasibleSet := by
      change d ∈ P.feasibleSet
      simpa using hd
    have hd' : (EuclideanSpace.equiv (Fin n) ℝ).symm d ∈ (P.toQuadraticProgram hB).feasibleSet :=
      (P.mem_toQuadraticProgram_feasibleSet_iff hB ((EuclideanSpace.equiv (Fin n) ℝ).symm d)).2
        hd''
    have hle := h ((EuclideanSpace.equiv (Fin n) ℝ).symm d) hd'
    have hobjd :
        (P.toQuadraticProgram hB).objective ((EuclideanSpace.equiv (Fin n) ℝ).symm d) =
          P.objective d := by
      have hobj :=
        P.toQuadraticProgram_objective_eq hB ((EuclideanSpace.equiv (Fin n) ℝ).symm d)
      change
        (P.toQuadraticProgram hB).objective ((EuclideanSpace.equiv (Fin n) ℝ).symm d) =
          P.objective d at hobj
      exact hobj
    rw [P.toQuadraticProgram_objective_eq hB x, hobjd] at hle
    exact hle
  · intro h y hy
    have hy' : pointEquiv y ∈ P :=
      (P.mem_toQuadraticProgram_feasibleSet_iff hB y).1 hy
    have hle := h (pointEquiv y) hy'
    simpa [P.toQuadraticProgram_objective_eq hB x,
      P.toQuadraticProgram_objective_eq hB y] using hle

/-- Unfolding `P.IsSolution d` gives feasibility together with the canonical minimizer surface on
the Wilson-Han-Powell feasible set. -/
theorem isSolution_iff_mem_and_isMinOn
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) :
    P.IsSolution d ↔ d ∈ P ∧ IsMinOn P P.feasibleSet d :=
  by rfl

/-- Under `P.B.IsSymm`, a Wilson-Han-Powell solution is exactly a minimizer of the associated
canonical quadratic program together with feasibility after transporting the direction
coordinates to `EuclideanSpace`. -/
theorem isSolution_iff_toQuadraticProgram
    (P : WilsonHanPowellSubproblem n me mi) (hB : P.B.IsSymm) (x : Point) :
    P.IsSolution (pointEquiv x) ↔
      x ∈ (P.toQuadraticProgram hB).feasibleSet ∧
        IsMinOn (P.toQuadraticProgram hB) (P.toQuadraticProgram hB).feasibleSet x := by
  constructor
  · intro hx
    rcases (P.isSolution_iff_mem_and_isMinOn (pointEquiv x)).1 hx with ⟨hxmem, hxmin⟩
    exact ⟨(P.mem_toQuadraticProgram_feasibleSet_iff hB x).2 hxmem,
      (P.isMinOn_toQuadraticProgram_iff hB x).2 hxmin⟩
  · intro hx
    rcases hx with ⟨hxmem, hxmin⟩
    exact ⟨(P.mem_toQuadraticProgram_feasibleSet_iff hB x).1 hxmem,
      (P.isMinOn_toQuadraticProgram_iff hB x).1 hxmin⟩

/-- Unfolding `P.IsSolution d` gives feasibility together with global minimality of the quadratic
objective on the Wilson-Han-Powell feasible set. -/
@[simp] theorem isSolution_iff
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) :
    P.IsSolution d ↔
      d ∈ P ∧ ∀ d' : Direction, d' ∈ P → P.objective d ≤ P.objective d' := by
  rw [isSolution_iff_mem_and_isMinOn, isMinOn_iff]
  simp

/-- Chapter12 Definition 12.2-extra-1: a direction `d` is a Wilson-Han-Powell search direction
when it solves the quadratic subproblem `(12.2.1)`-`(12.2.3)`, equivalently when it is feasible
and minimizes `P.objective` over all feasible directions. -/
abbrev IsSearchDirection
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) : Prop :=
  WilsonHanPowellSubproblem.IsSolution P d

/-- Unfolding `P.IsSearchDirection d` gives the source statement that a Wilson-Han-Powell search
direction is exactly a solution of the quadratic subproblem. -/
@[simp] theorem isSearchDirection_iff
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) :
    WilsonHanPowellSubproblem.IsSearchDirection P d ↔ WilsonHanPowellSubproblem.IsSolution P d :=
  Iff.rfl

/-- Unfolding `P.IsSearchDirection d` gives the source feasibility and global optimality
conditions for the quadratic subproblem `(12.2.1)`-`(12.2.3)`. -/
theorem isSearchDirection_iff_mem_and_forall
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) :
    WilsonHanPowellSubproblem.IsSearchDirection P d ↔
      d ∈ P ∧ ∀ d' : Direction, d' ∈ P → P.objective d ≤ P.objective d' :=
  WilsonHanPowellSubproblem.isSolution_iff P d

/-- Under `P.B.IsSymm`, a Wilson-Han-Powell search direction is the minimizer of the associated
canonical quadratic program together with feasibility after transporting its coordinates to
`EuclideanSpace`. -/
theorem isSearchDirection_iff_toQuadraticProgram
    (P : WilsonHanPowellSubproblem n me mi) (hB : P.B.IsSymm) (x : Point) :
    WilsonHanPowellSubproblem.IsSearchDirection P (pointEquiv x) ↔
      x ∈ (P.toQuadraticProgram hB).feasibleSet ∧
        IsMinOn (P.toQuadraticProgram hB) (P.toQuadraticProgram hB).feasibleSet x :=
  WilsonHanPowellSubproblem.isSolution_iff_toQuadraticProgram P hB x

/-- `P.SatisfiesKKT d λeq λineq` packages the multiplier relations
`(12.2.5)`-`(12.2.7)` for a Wilson-Han-Powell search direction `d`; `λeq` and `λineq` are the
equality and inequality blocks of the source multiplier `λ_k`. -/
structure SatisfiesKKT
    (P : WilsonHanPowellSubproblem n me mi)
    (d : Direction) (eqMultiplier : EqMultiplier) (ineqMultiplier : IneqMultiplier) : Prop where
  searchDirection : WilsonHanPowellSubproblem.IsSearchDirection P d
  stationarity :
    P.g + P.B.mulVec d =
      (Matrix.transpose P.Aeq).mulVec eqMultiplier +
        (Matrix.transpose P.Aineq).mulVec ineqMultiplier
  dual_nonneg : ∀ i : Fin mi, 0 ≤ ineqMultiplier i
  complementary_slackness :
    ∀ i : Fin mi, ineqMultiplier i * ((P.Aineq.mulVec d) i + P.cineq i) = 0

/-- A Wilson-Han-Powell KKT point is, in particular, a solution of the quadratic subproblem. -/
theorem SatisfiesKKT.isSolution
    {P : WilsonHanPowellSubproblem n me mi}
    {d : Direction} {eqMultiplier : EqMultiplier} {ineqMultiplier : IneqMultiplier}
    (hKKT : WilsonHanPowellSubproblem.SatisfiesKKT P d eqMultiplier ineqMultiplier) :
    WilsonHanPowellSubproblem.IsSolution P d :=
  hKKT.searchDirection

/-- A Wilson-Han-Powell KKT point is feasible for the quadratic subproblem constraints. -/
theorem SatisfiesKKT.feasible
    {P : WilsonHanPowellSubproblem n me mi}
    {d : Direction} {eqMultiplier : EqMultiplier} {ineqMultiplier : IneqMultiplier}
    (hKKT : WilsonHanPowellSubproblem.SatisfiesKKT P d eqMultiplier ineqMultiplier) :
    d ∈ P :=
  (WilsonHanPowellSubproblem.isSearchDirection_iff_mem_and_forall P d).1 hKKT.searchDirection |>.1

/-- A direction has a Wilson-Han-Powell search multiplier when there exist equality and
inequality multipliers satisfying the KKT relations of `(12.2.5)`-`(12.2.7)` for that search
direction. -/
def HasSearchMultiplier
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) : Prop :=
  ∃ eqMultiplier : EqMultiplier,
    ∃ ineqMultiplier : IneqMultiplier,
      WilsonHanPowellSubproblem.SatisfiesKKT P d eqMultiplier ineqMultiplier

/-- Unfolding `P.HasSearchMultiplier d` gives existence of equality and inequality multipliers
satisfying the Wilson-Han-Powell KKT system. -/
theorem hasSearchMultiplier_iff
    (P : WilsonHanPowellSubproblem n me mi) (d : Direction) :
    WilsonHanPowellSubproblem.HasSearchMultiplier P d ↔
      ∃ eqMultiplier : EqMultiplier,
        ∃ ineqMultiplier : IneqMultiplier,
          WilsonHanPowellSubproblem.SatisfiesKKT P d eqMultiplier ineqMultiplier :=
  Iff.rfl

/-- Any Wilson-Han-Powell search multiplier witnesses that the direction is a search direction. -/
theorem HasSearchMultiplier.isSearchDirection
    {P : WilsonHanPowellSubproblem n me mi} {d : Direction}
    (hMultiplier : WilsonHanPowellSubproblem.HasSearchMultiplier P d) :
    WilsonHanPowellSubproblem.IsSearchDirection P d := by
  rcases hMultiplier with ⟨eqMultiplier, ineqMultiplier, hKKT⟩
  exact hKKT.searchDirection

end WilsonHanPowellSubproblem

#print axioms WilsonHanPowellSubproblem.objective

end Chapter12Definition12_2Extra1
