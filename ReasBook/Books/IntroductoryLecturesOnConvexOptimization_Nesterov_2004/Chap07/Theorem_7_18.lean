/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {Scenario : Type u} {Decision : Type v}

/- Theorem 7.18 lies in Chapter 7's worst-case static-comparison / order-theoretic gap domain.

Mandatory domain-style sampling:
- mathlib `IsLUB`, the canonical owner for least upper bounds of sets of reals;
- mathlib `isLUB_sSup`, the canonical complete-lattice specialization of that owner;
- mathlib `Set.mem_range_self`, the bridge from a fixed scenario to membership in the range of the
  scenario-wise gap function;
- `staticProductionAverageEfficiency_eq_sSup_of_optimalStaticStrategy` in `Chap07/Theorem_7_17`,
  the nearby Chapter 7 pattern of keeping static-comparison values on canonical order owners
  rather than on local wrapper data.

Best owner abstraction:
- source-facing: the scenario-wise gap `v ↦ f (x v) v - f xStatic v` and the claim that every
  realized gap is bounded by any least upper bound `Δ` of its range;
- core/canonical: `IsLUB` on the range of that gap function;
- bridge/view: `Set.mem_range_self u`, which identifies the gap at the fixed scenario `u` as an
  element of the ranged owner set.

Primitive data:
- the payoff function `f`;
- the decision rule `x`;
- the comparison static strategy `xStatic`;
- the least-upper-bound witness `hΔ`.

Derived API:
- the pointwise scenario gap at `u`;
- the upper-bound conclusion obtained by specializing the `IsLUB` owner to the range element
  coming from `u`.

Source/core/bridge triage:
- source-facing: the theorem below;
- core/canonical: `IsLUB`;
- bridge/view: `Set.mem_range_self`.
-/

-- Proof sketch: if `Δ` is the least upper bound of the set of scenario-wise gaps, then it is in
-- particular an upper bound for every element of that set; the gap at a fixed scenario `u` belongs
-- to the range by `Set.mem_range_self u`.
/-- Theorem 7.18: if `Δ` is the least upper bound of the scenario-wise gap
`v ↦ f (x v) v - f xStatic v` of a decision rule relative to a static strategy, then for every
scenario `u` the gap at `u` is bounded above by `Δ`. This is the distribution-free worst-case
guarantee relative to the static strategy. -/
theorem pointwise_gap_le_of_isLUB_worst_case_gap_against_static_strategy
    (f : Decision → Scenario → ℝ)
    (x : Scenario → Decision)
    (xStatic : Decision)
    {Δ : ℝ}
    (hΔ : IsLUB (Set.range fun v : Scenario ↦ f (x v) v - f xStatic v) Δ)
    (u : Scenario) :
    f (x u) u - f xStatic u ≤ Δ :=
  hΔ.1 <| Set.mem_range_self u

end
