/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_1

section Chapter08Exercise82

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

namespace ConstrainedOptimizationProblem

-- Domain sampling:
-- * core/canonical owner: `Chapter01.ConstrainedOptimizationProblem`
-- * Chapter 8 derived active-set owner: `activeIneqIndexSet` from `Definition_8_1_1`
-- * this file is source-facing: it adds the ε-active inequality index set as a derived view on
--   the existing owner rather than rebuilding constrained-problem data locally

/-- The `ε`-active inequality indices at `x` are the inequality indices whose constraint value is
at most `ε`. -/
def epsilonActiveIneqIndexSet
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (x : Point) (ε : ℝ) :
    Set (Fin m) :=
  {i | i ∈ problem.ineqIndices ∧ problem.constraint i x ≤ ε}

/-- Membership in `problem.epsilonActiveIneqIndexSet x ε` means being an inequality index whose
constraint value at `x` is at most `ε`. -/
theorem mem_epsilonActiveIneqIndexSet_iff
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (x : Point) (ε : ℝ) (i : Fin m) :
    i ∈ problem.epsilonActiveIneqIndexSet x ε ↔
      i ∈ problem.ineqIndices ∧ problem.constraint i x ≤ ε :=
  Iff.rfl

/-- At a point satisfying all inequality constraints, the `0`-active inequality set coincides with
the active inequality set. -/
theorem epsilonActiveIneqIndexSet_zero
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    {x : Point} (hineq : ∀ i ∈ problem.ineqIndices, 0 ≤ problem.constraint i x) :
    problem.epsilonActiveIneqIndexSet x 0 = problem.activeIneqIndexSet x := by
  ext i
  constructor
  · intro hi
    rcases (problem.mem_epsilonActiveIneqIndexSet_iff x 0 i).1 hi with ⟨hi_mem, hi_le⟩
    have hi_nonneg : 0 ≤ problem.constraint i x := hineq i hi_mem
    exact (problem.mem_activeIneqIndexSet_iff x i).2 ⟨hi_mem, le_antisymm hi_le hi_nonneg⟩
  · intro hi
    rcases (problem.mem_activeIneqIndexSet_iff x i).1 hi with ⟨hi_mem, hi_eq⟩
    exact (problem.mem_epsilonActiveIneqIndexSet_iff x 0 i).2 ⟨hi_mem, hi_eq.le⟩

/-- Every active inequality index is `ε`-active for every nonnegative `ε`. -/
theorem activeIneqIndexSet_subset_epsilonActiveIneqIndexSet
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (x : Point) {ε : ℝ} (hε : 0 ≤ ε) :
    problem.activeIneqIndexSet x ⊆ problem.epsilonActiveIneqIndexSet x ε := by
  intro i hi
  rcases (problem.mem_activeIneqIndexSet_iff x i).1 hi with ⟨hi_mem, hi_eq⟩
  exact (problem.mem_epsilonActiveIneqIndexSet_iff x ε i).2 ⟨hi_mem, hi_eq ▸ hε⟩

/-- Chapter08 Exercise 8.2: if `x` satisfies all inequality constraints, the active inequality set
`I(x)` is the intersection of the `ε`-active inequality sets `I_ε(x)` over all `ε > 0`, which
formalizes the right-hand limit `I_ε(x) → I(x)` as `ε → 0+`. -/
theorem iInter_epsilonActiveIneqIndexSet_pos_eq_activeIneqIndexSet
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    {x : Point} (hineq : ∀ i ∈ problem.ineqIndices, 0 ≤ problem.constraint i x) :
    (⋂ ε : {ε : ℝ // 0 < ε}, problem.epsilonActiveIneqIndexSet x ε.1) =
      problem.activeIneqIndexSet x := by
  ext i
  constructor
  · intro hi
    have hi_all : ∀ ε : {ε : ℝ // 0 < ε}, i ∈ problem.epsilonActiveIneqIndexSet x ε.1 := by
      simpa using hi
    have hi_one := hi_all ⟨1, zero_lt_one⟩
    rcases (problem.mem_epsilonActiveIneqIndexSet_iff x 1 i).1 hi_one with ⟨hi_mem, _⟩
    have hi_nonneg : 0 ≤ problem.constraint i x := hineq i hi_mem
    have hi_not_pos : ¬ 0 < problem.constraint i x := by
      intro hi_pos
      have hi_half :=
        hi_all ⟨problem.constraint i x / 2, by simpa using half_pos hi_pos⟩
      have hi_le_half :=
        (problem.mem_epsilonActiveIneqIndexSet_iff x (problem.constraint i x / 2) i).1 hi_half |>.2
      exact (not_le_of_gt (half_lt_self hi_pos)) hi_le_half
    exact
      (problem.mem_activeIneqIndexSet_iff x i).2
        ⟨hi_mem, le_antisymm (le_of_not_gt hi_not_pos) hi_nonneg⟩
  · intro hi
    have hi_active : i ∈ problem.activeIneqIndexSet x := hi
    simp only [Set.mem_iInter]
    intro ε
    exact problem.activeIneqIndexSet_subset_epsilonActiveIneqIndexSet x (le_of_lt ε.2) hi_active

end ConstrainedOptimizationProblem

end Chapter08Exercise82
