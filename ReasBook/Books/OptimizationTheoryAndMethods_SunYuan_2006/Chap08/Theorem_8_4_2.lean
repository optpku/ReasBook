/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Notation_8_2_extra_2

noncomputable section

section Chapter08Theorem842

variable {n m : ℕ}

local notation "Point" => Fin n → ℝ
local notation "Multiplier" => Fin m → ℝ

namespace ConstrainedOptimizationProblem

-- Domain sampling:
-- * primary domain: convex constrained optimization duality
-- * inspected owner declarations:
--   `ConstrainedOptimizationProblem.feasibleSet`,
--   `ConstrainedOptimizationProblem.lagrangian`,
--   `ConstrainedOptimizationProblem.attainedDualFeasibleSet`,
--   `ConstrainedOptimizationProblem.lagrangian_le_of_mem_attainedDualFeasibleSet`,
--   `ConstrainedOptimizationProblem.mem_attainedDualFeasibleSet_iff`
--   from `Chapter08.Theorem_8_4_1`
-- * owner abstraction reused here: the Chapter 8 constrained-problem owner surface
--   `problem.feasibleSet`, `problem.attainedDualFeasibleSet`, and the notation
--   `𝓛[problem](x, lam)`
-- * layer triage:
--   source-facing: primal/dual feasibility and the weak-duality inequality
--   core/canonical: `ConstrainedOptimizationProblem.lagrangian`
--   bridge/view: the notation `𝓛[problem](x, lam)`
-- * primitive data reused from that owner: the problem objective, common constraint family,
--   primal feasible set, Lagrangian, and attained dual-feasible bridge
-- * derived API kept here: only the new weak-duality theorem

/-- Chapter08 Theorem 8.4.2: if `xPrime` is feasible for the primal problem `(8.4.1)` and
`(x, λ)` is attained dual feasible for the dual problem `(8.4.2)`, then
`problem.objective xPrime ≥ 𝓛[problem](x, lam)`. -/
theorem weakDuality
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    {xPrime x : Point} {lam : Multiplier}
    (hxPrime : xPrime ∈ problem.feasibleSet)
    (hdual : (x, lam) ∈ problem.attainedDualFeasibleSet) :
    problem.objective xPrime ≥ 𝓛[problem](x, lam) := by
  have h_min : 𝓛[problem](x, lam) ≤ 𝓛[problem](xPrime, lam) :=
    problem.lagrangian_le_of_mem_attainedDualFeasibleSet hdual
  have hlam : ∀ i : Fin m, 0 ≤ lam i :=
    (problem.mem_admissibleMultiplierSet_iff lam).mp hdual.2
  rcases hxPrime with ⟨_, hxPrime⟩
  have h_lagrangian : 𝓛[problem](xPrime, lam) ≤ problem.objective xPrime := by
    have hsum_nonneg : 0 ≤ ∑ i : Fin m, lam i * problem.constraint i xPrime :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (hlam i) (hxPrime i (by simp))
    simpa [ConstrainedOptimizationProblem.lagrangian] using
      sub_le_self (problem.objective xPrime) hsum_nonneg
  exact le_trans h_min h_lagrangian

end ConstrainedOptimizationProblem

end Chapter08Theorem842
