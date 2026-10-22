/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_10_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

variable {X : Type*} [TopologicalSpace X]
variable {ι : Type*}

/- Definition 1.10.15 lies in the chapter's penalty-function domain for finitely many continuous
inequality constraints.

Relevant owner-style declarations sampled before refinement:
* `IsPenaltyFunction` in `Definition_1_10_14`
* `constraintSet` in `Proposition_1_10_17`, the chapter's finite-family feasible-set owner
* `PosPart.posPart` together with `posPart_def`
* the canonical ring structure on `C(X, ℝ)`, including pointwise sums and powers
* the pointwise order/lattice structure on `C(X, ℝ)`

Best owner abstraction:
* source-facing: the two explicit penalty maps attached to a finite constraint family
* core/canonical: the bundled continuous maps `C(X, ℝ)` together with `IsPenaltyFunction`
* bridge/view: the pointwise evaluation formulas recovering the textbook sums of positive parts

Primitive data:
* a finite family `constraints : ι → C(X, ℝ)` with `[Fintype ι]`

Derived API:
* the feasible-set owner `constraintSet constraints`
* the quadratic and nonsmooth penalty maps
* their pointwise formulas and their certification as penalty functions

The Euclidean model `ℝⁿ` is not used by the constructions themselves, so the owner declarations are
kept at the weaker canonical level of an arbitrary topological space with real-valued continuous
constraints. -/

section

variable [Fintype ι] (constraints : ι → C(X, ℝ))

/-- Definition 1.10.15: for continuous constraint functions `f₁, …, f_m : ℝⁿ → ℝ`, the feasible
set `constraintSet constraints` is cut out by the inequalities `constraints j x ≤ 0`, and one
quadratic penalty for it is
`x ↦ ∑ j, ((fⱼ x)⁺)^2`, where `a⁺ = max a 0` is mathlib's positive-part notation. The nonsmooth
penalty is introduced below as a companion definition. -/
def quadraticPenalty : C(X, ℝ) :=
  ∑ j : ι, ((constraints j)⁺) ^ (2 : ℕ)

@[simp] theorem quadraticPenalty_apply (x : X) :
    quadraticPenalty constraints x = ∑ j : ι, ((constraints j x)⁺) ^ (2 : ℕ) := by
  simp [quadraticPenalty, posPart_def]

/-- The nonsmooth penalty associated to finitely many continuous inequality constraints is the sum
of the positive parts of the constraint violations. -/
def nonsmoothPenalty : C(X, ℝ) :=
  ∑ j : ι, (constraints j)⁺

@[simp] theorem nonsmoothPenalty_apply (x : X) :
    nonsmoothPenalty constraints x = ∑ j : ι, (constraints j x)⁺ := by
  simp [nonsmoothPenalty, posPart_def]

/-- The quadratic penalty is a penalty function for the feasible set cut out by the given
continuous inequality constraints. -/
-- Proof sketch: continuity follows from continuity of each constraint, the positive-part map, the
-- squaring map, and finite sums. On the feasible set every positive part vanishes; outside the
-- feasible set some constraint is positive, so the corresponding summand is strictly positive.
theorem quadraticPenalty_isPenaltyFunction :
    IsPenaltyFunction (constraintSet constraints)
      (quadraticPenalty constraints) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [quadraticPenalty_apply]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  · ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, mem_constraintSet_iff, quadraticPenalty_apply]
    constructor
    · intro hx
      refine (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).2 ?_
      intro j _
      rw [posPart_eq_zero.mpr (hx j)]
      simp
    · intro hx j
      have hzero :
          ∀ j ∈ (Finset.univ : Finset ι), ((constraints j x)⁺) ^ (2 : ℕ) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hx
      exact posPart_eq_zero.mp <| sq_eq_zero_iff.mp <| hzero j (Finset.mem_univ j)

/-- The nonsmooth penalty is a penalty function for the feasible set cut out by the given
continuous inequality constraints. -/
-- Proof sketch: use continuity of the positive-part map and finite sums. Feasible points make
-- every positive part vanish, while an infeasible point has at least one violated constraint whose
-- positive part contributes a strictly positive summand.
theorem nonsmoothPenalty_isPenaltyFunction :
    IsPenaltyFunction (constraintSet constraints)
      (nonsmoothPenalty constraints) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [nonsmoothPenalty_apply]
    exact Finset.sum_nonneg fun _ _ ↦ posPart_nonneg _
  · ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, mem_constraintSet_iff, nonsmoothPenalty_apply]
    constructor
    · intro hx
      refine (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ posPart_nonneg _).2 ?_
      intro j _
      exact posPart_eq_zero.mpr (hx j)
    · intro hx j
      have hzero : ∀ j ∈ (Finset.univ : Finset ι), (constraints j x)⁺ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ posPart_nonneg _).mp hx
      exact posPart_eq_zero.mp (hzero j (Finset.mem_univ j))

end
