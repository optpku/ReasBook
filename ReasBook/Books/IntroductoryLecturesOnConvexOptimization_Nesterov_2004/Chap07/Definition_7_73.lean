/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

section

variable {X : Type u}

/- Definition 7.73 lies in the chapter's attained-maximizer / geometric-mean-growth domain.

Mandatory domain-style sampling:
- mathlib `IsMaxOn`, the canonical owner for a chosen maximizer on a set;
- mathlib `isMaxOn_univ_iff`, the direct bridge from `IsMaxOn ... Set.univ` to the textbook
  pointwise domination formula;
- `BarrierSubgradientMethod.iterateGeometricMean_le_optimal` in `Chap07/Theorem_7_16`, the nearby
  Chapter 7 maximization theorem already phrased with the owner `IsMaxOn` on the feasible subtype;
- `Definition_3_26`, the chapter's recall-style pattern for source-facing optimization notions
  already owned by `IsMaxOn`.

Best owner abstraction:
- source-facing: an optimal static strategy over the feasible subtype `P`;
- core/canonical: `IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic`;
- bridge/view: `isMaxOn_univ_iff`, which expands this owner back to the pointwise inequality
  against every `y : P`.

Primitive data:
- the feasible subtype `P`;
- the horizon `N`;
- the positive period outputs `ψ`;
- a chosen feasible strategy `x : P`.

Derived API:
- the cumulative output `staticProductionTotalOutput ψ x`;
- the geometric-mean efficiency `staticProductionAverageEfficiency ψ x`;
- the optimality owner `IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic`;
- the textbook expansion of that owner through `isMaxOn_univ_iff`.

The previous version introduced a parallel structure
`OptimalStaticProductionStrategy` carrying a chosen feasible point together with the same
maximality condition that `IsMaxOn ... Set.univ` already owns on the subtype `P`. In this domain,
feasibility is already encoded by `xStatic : P`, so the wrapper added no mathematical content.
This file therefore keeps the source-facing production and efficiency objects, but recalls the
optimal-static-strategy notion directly through the canonical maximizer owner.
-/

/-- The cumulative production of a static strategy over the periods `0, ..., N`. -/
def staticProductionTotalOutput
    {P : Set X} {N : ℕ} (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r}) (x : P) : ℝ :=
  ∏ k : Fin (N + 1), (ψ k x : ℝ)

-- Proof sketch: unfold `staticProductionTotalOutput`.
/-- Expanding `staticProductionTotalOutput ψ x` gives the period-by-period product
`∏_{k=0}^N ψ_k(x)`. -/
theorem staticProductionTotalOutput_def
    {P : Set X} {N : ℕ} (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r}) (x : P) :
    staticProductionTotalOutput ψ x = ∏ k : Fin (N + 1), (ψ k x : ℝ) :=
  rfl

/-- The geometric-mean efficiency of a static strategy over the periods `0, ..., N`. -/
def staticProductionAverageEfficiency
    {P : Set X} {N : ℕ} (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r}) (x : P) : ℝ :=
  Real.rpow (staticProductionTotalOutput ψ x) ((1 : ℝ) / (N + 1 : ℝ))

-- Proof sketch: unfold `staticProductionAverageEfficiency`.
/-- Expanding `staticProductionAverageEfficiency ψ x` gives the geometric mean of the period
outputs of the static strategy `x`. -/
theorem staticProductionAverageEfficiency_def
    {P : Set X} {N : ℕ} (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r}) (x : P) :
    staticProductionAverageEfficiency ψ x =
      Real.rpow (staticProductionTotalOutput ψ x) ((1 : ℝ) / (N + 1 : ℝ)) :=
  rfl

section OptimalStaticStrategy

variable (P : Set X) (N : ℕ)
variable (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
variable (xStatic : P)

set_option linter.hashCommand false in
/- Definition 7.73: an optimal static production strategy is a feasible point `xStatic : P` whose
cumulative output is maximal among all feasible static strategies. On the feasible subtype `P`,
this is exactly the canonical owner `IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic`,
and its average efficiency is the already-defined `staticProductionAverageEfficiency ψ xStatic`. -/
#check IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic

set_option linter.hashCommand false in
#check staticProductionAverageEfficiency ψ xStatic

set_option linter.hashCommand false in
#check (
  show IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic ↔
      ∀ y : P, staticProductionTotalOutput ψ y ≤ staticProductionTotalOutput ψ xStatic from
    isMaxOn_univ_iff)

end OptimalStaticStrategy

end
