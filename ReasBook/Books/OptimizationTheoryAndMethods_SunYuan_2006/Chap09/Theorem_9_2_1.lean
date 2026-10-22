/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Definition_9_1_extra_1

open Matrix

noncomputable section

namespace QuadraticProgram

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "EqMultiplier" => EuclideanSpace ℝ (Fin me)
local notation "IneqMultiplier" => EuclideanSpace ℝ (Fin mi)
local notation "pointEquiv" => EuclideanSpace.equiv (Fin n) ℝ

-- Domain-style sampling:
-- * primary domain: quadratic-program duality with the explicit source dual problem
-- * inspected owner declarations:
--   `ConstrainedOptimizationProblem.lagrangian`,
--   `ConstrainedOptimizationProblem.IsDualSolution`, and
--   `ConstrainedOptimizationProblem.IsDualOptimalPair` from Chapter 8,
--   together with the Chapter 9 owner `QuadraticProgram`
-- * best owner abstraction here: the source-facing Chapter 9 owner `QuadraticProgram`, while
--   the split-multiplier/Lagrangian owner surface and the positive-definite explicit dual
--   objective follow the Chapter 8 duality API shape
-- * layer triage:
--   source-facing: `Multiplier`, `Λ[P]`, `ℒ[P]`, `DualVariable`, `SatisfiesDualStationarity`,
--   and `IsDualFeasible`
--   core/canonical: `P.dualObjective hG dual` and `P.IsDualSolution hG dual`
--   bridge/view: `multiplierVector` and `dualFeasibleSet`

/-- The split multiplier type `(λeq, λineq)` used throughout Chapter 9 quadratic-program
duality. -/
abbrev Multiplier (me mi : ℕ) := EuclideanSpace ℝ (Fin me) × EuclideanSpace ℝ (Fin mi)

local notation "Multiplier" => QuadraticProgram.Multiplier me mi

/-- The Chapter 8 multiplier vector corresponding to the split equality/inequality pair
`(λeq, λineq)`. -/
abbrev multiplierVector (mult : Multiplier) : Fin (me + mi) → ℝ :=
  Fin.append mult.1 mult.2

@[simp] theorem multiplierVector_castAdd (mult : Multiplier) (i : Fin me) :
    multiplierVector mult (Fin.castAdd mi i) = mult.1 i := by
  simp [QuadraticProgram.multiplierVector]

@[simp] theorem multiplierVector_natAdd (mult : Multiplier) (i : Fin mi) :
    multiplierVector mult (Fin.natAdd me i) = mult.2 i := by
  simp [QuadraticProgram.multiplierVector]

/-- The admissible multiplier set `Λ` consists of arbitrary equality multipliers together with
nonnegative inequality multipliers. -/
def admissibleMultiplierSet (_ : QuadraticProgram n me mi) : Set Multiplier :=
  {mult | ∀ i : Fin mi, 0 ≤ mult.2 i}

/-- Membership in `Λ[P]` is exactly nonnegativity of the inequality multipliers. -/
theorem mem_admissibleMultiplierSet_iff
    (P : QuadraticProgram n me mi) (mult : Multiplier) :
    mult ∈ admissibleMultiplierSet P ↔ ∀ i : Fin mi, 0 ≤ mult.2 i :=
  Iff.rfl

/-- The Lagrangian `ℒ(x, λeq, λineq)` of the quadratic program `P`, viewed through the canonical
Chapter 8 constrained-problem owner. -/
abbrev lagrangian (P : QuadraticProgram n me mi) (x : Point) (mult : Multiplier) : ℝ :=
  ConstrainedOptimizationProblem.lagrangian
    P.toConstrainedOptimizationProblem
    (pointEquiv x)
    (multiplierVector mult)

/-- The admissible multiplier set of `P` is written `Λ[P]`. -/
scoped[QuadraticProgram] notation "Λ[" P "]" => admissibleMultiplierSet P

/-- The Lagrangian of `P` is written `ℒ[P]`, so its value at `(x, mult)` is `ℒ[P] x mult`. -/
scoped[QuadraticProgram] notation:max "ℒ[" P "]" => lagrangian P

open scoped QuadraticProgram

/-- Expanding `ℒ[P] x (λeq, λineq)` recovers the source formula. -/
theorem lagrangian_eq
    (P : QuadraticProgram n me mi) (x : Point) (mult : Multiplier) :
    ℒ[P] x mult =
      P x - dotProduct mult.1 (P.Aeq.mulVec x - P.beq) -
        dotProduct mult.2 (P.Aineq.mulVec x - P.bineq) := sorry

/-- A dual variable for `P`, bundling the equality multipliers, the inequality multipliers, and
the auxiliary vector `y` from `(9.2.8)`-`(9.2.10)`. -/
structure DualVariable (P : QuadraticProgram n me mi) where
  eqMultiplier : EqMultiplier
  ineqMultiplier : IneqMultiplier
  y : Point

/-- The split multiplier pair underlying a Chapter 9 dual variable. -/
abbrev DualVariable.multiplier {P : QuadraticProgram n me mi} (dual : DualVariable P) :
    Multiplier :=
  (dual.eqMultiplier, dual.ineqMultiplier)

/-- A dual variable satisfies the stationarity relation from `(9.2.9)` when the auxiliary vector
`y` matches the affine combination of constraint normals minus `g`. -/
def SatisfiesDualStationarity (P : QuadraticProgram n me mi) (dual : DualVariable P) : Prop :=
  P.Aeqᵀ *ᵥ dual.eqMultiplier + P.Aineqᵀ *ᵥ dual.ineqMultiplier = dual.y + P.g

/-- A dual variable is feasible when it satisfies the stationarity relation from `(9.2.9)` and
the nonnegativity constraint from `(9.2.10)`. -/
def IsDualFeasible (P : QuadraticProgram n me mi) (dual : DualVariable P) : Prop :=
  P.SatisfiesDualStationarity dual ∧
    dual.multiplier ∈ Λ[P]

/-- Dual feasibility includes the stationarity relation `(9.2.9)`. -/
theorem IsDualFeasible.stationarity
    {P : QuadraticProgram n me mi} {dual : DualVariable P} (h : P.IsDualFeasible dual) :
    P.SatisfiesDualStationarity dual :=
  h.1

/-- Dual feasibility includes the multiplier nonnegativity condition `(9.2.10)`. -/
theorem IsDualFeasible.nonneg
    {P : QuadraticProgram n me mi} {dual : DualVariable P} (h : P.IsDualFeasible dual) :
    ∀ i : Fin mi, 0 ≤ dual.ineqMultiplier i :=
  (P.mem_admissibleMultiplierSet_iff dual.multiplier).1 h.2

/-- The stationarity/nonnegativity constraint set appearing in the dual problem
`(9.2.8)`-`(9.2.10)`. -/
def dualFeasibleSet (P : QuadraticProgram n me mi) : Set (DualVariable P) :=
  {dual | P.IsDualFeasible dual}

/-- Membership in `P.dualFeasibleSet` is exactly dual feasibility. -/
theorem mem_dualFeasibleSet_iff
    (P : QuadraticProgram n me mi) (dual : DualVariable P) :
    dual ∈ P.dualFeasibleSet ↔ P.IsDualFeasible dual :=
  Iff.rfl

/-- The dual objective from `(9.2.8)` for the positive-definite quadratic program `P` and the
dual variable `dual`. -/
def dualObjective
    (P : QuadraticProgram n me mi) (hG : P.G.PosDef) (dual : DualVariable P) : ℝ :=
  letI : Invertible P.G := hG.isUnit.invertible
  dotProduct P.beq dual.eqMultiplier + dotProduct P.bineq dual.ineqMultiplier -
    (1 / 2 : ℝ) * dotProduct dual.y ((⅟ P.G).mulVec dual.y)

/-- A dual solution of `(9.2.8)`-`(9.2.10)` for the positive-definite quadratic program `P` is a
dual-feasible variable maximizing the positive-definite dual objective over the dual-feasible
set. -/
def IsDualSolution
    (P : QuadraticProgram n me mi) (hG : P.G.PosDef) (dual : DualVariable P) : Prop :=
  P.IsDualFeasible dual ∧ IsMaxOn (P.dualObjective hG) P.dualFeasibleSet dual

/-- `P.IsDualSolution dual` unfolds to dual feasibility together with maximality of the dual
objective on `P.dualFeasibleSet`. -/
theorem isDualSolution_iff
    (P : QuadraticProgram n me mi) (hG : P.G.PosDef) (dual : DualVariable P) :
    P.IsDualSolution hG dual ↔
      P.IsDualFeasible dual ∧
        ∀ dual' : DualVariable P,
          P.IsDualFeasible dual' →
            P.dualObjective hG dual' ≤ P.dualObjective hG dual := by
  rw [IsDualSolution]
  constructor
  · rintro ⟨hfeasible, hmax⟩
    exact ⟨hfeasible, isMaxOn_iff.mp hmax⟩
  · rintro ⟨hfeasible, hmax⟩
    exact ⟨hfeasible, isMaxOn_iff.mpr hmax⟩

/-- Chapter09 Theorem 9.2.1: let `P` encode primal problem `(9.1.1)`-`(9.1.3)` with
positive-definite Hessian `P.G`. For a feasible point `xStar ∈ X = P.feasibleSet`, `xStar`
solves the primal problem if and only if there exists a dual solution of `(9.2.8)`-`(9.2.10)`
whose auxiliary vector satisfies `y* = G xStar`. -/
theorem primalSolution_iff_dualSolution
    (P : QuadraticProgram n me mi)
    (hG : P.G.PosDef)
    {xStar : Point}
    (hxStar : xStar ∈ P.feasibleSet) :
    IsMinOn P P.feasibleSet xStar ↔
      ∃ dualStar : DualVariable P,
        dualStar.y = P.G.mulVec xStar ∧ P.IsDualSolution hG dualStar := sorry

end QuadraticProgram
