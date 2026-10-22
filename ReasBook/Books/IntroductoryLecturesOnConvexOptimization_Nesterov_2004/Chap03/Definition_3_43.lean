/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_26

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {Q : Type u} {ι : Type v} {α : Type w}

/-
Definition 3.43 lies in the family sublevel-set / inequality-feasibility domain.

Sampled owner-style declarations:
- `𝓛[f](a)`, `mem_levelSet_iff`, and `levelSet_eq_setOf` in `Chap01/Definition_1_4_8`, the
  project owner for a single sublevel set;
- mathlib `Set.Iic` and `Set.preimage`, the canonical lower-interval and preimage presentation of
  a pointwise inequality `f x ≤ a`;
- `inequalityConstrainedFeasibleSet` and `mem_inequalityConstrainedFeasibleSet_iff` in
  `Chap03/Theorem_3_1_26`, the specialized finite real `≤ 0` owner used elsewhere in Chapter 3;
- `constraintInequalities_eq_aggregateConstraintSublevelSet` in `Chap03/Definition_3_42`, the
  finite real bridge from coordinatewise inequalities to a single aggregate constraint.

Best owner abstraction:
- the source-facing owner `extendedFeasibleSet`, stated directly at the comparison level
  `constraints j x ≤ ε`;
- the Chapter 3 finite real `≤ 0` feasible-set owner only as a specialized bridge.

Primitive data:
- the constraint family `ι → Q → α`;
- the threshold `ε : α`;
- the preorder structure on the comparison codomain.

Derived API:
- the source-facing extended feasible-set notation `𝓕[constraints](ε) = {x | ∀ j, fⱼ(x) ≤ ε}`;
- the membership equivalence `x ∈ 𝓕[constraints](ε) ↔ ∀ j, constraints j x ≤ ε`.

Source/core/bridge triage:
- source-facing: `extendedFeasibleSet`;
- core/canonical: the family of lower sublevel predicates `constraints j x ≤ ε`;
- bridge/view: `mem_extendedFeasibleSet_iff` and the finite real specialization
  `extendedFeasibleSet_eq_inequalityConstrainedFeasibleSet`.

The source notion is purely about feasibility, not optimization data. The refined file therefore
keeps `extendedFeasibleSet` as the source-facing owner and states it directly at the natural
comparison level `fⱼ(x) ≤ ε` for an arbitrary index type and preorder codomain. The earlier
finite real `≤ 0` Chapter 3 owner remains available only as a bridge theorem rather than as the
defining primitive body.
-/

section

variable [Preorder α]
variable (constraints : ι → Q → α) (ε : α)

/-- Definition 3.43: for a domain `Q`, a family of constraint functions `fⱼ : Q → α`, and a
threshold `ε : α`, the extended feasible set consists of the points `x : Q` such that every
constraint value satisfies `fⱼ(x) ≤ ε`. Its Lean surface notation is `𝓕[constraints](ε)`. -/
def extendedFeasibleSet : Set Q :=
  {x | ∀ j : ι, constraints j x ≤ ε}

end

namespace ExtendedFeasibleSetNotation

/- Source-facing Lean notation for the extended feasible set, with the constraint family kept
explicit in the surface syntax. -/
scoped notation:max "𝓕[" constraints:arg "](" ε:arg ")" =>
  extendedFeasibleSet constraints ε

end ExtendedFeasibleSetNotation

open scoped ExtendedFeasibleSetNotation

section

variable [Preorder α]
variable (constraints : ι → Q → α) (ε : α)

/-- Membership in the extended feasible set at tolerance `ε` is exactly the coordinatewise
inequality family `fⱼ(x) ≤ ε`. -/
@[simp] theorem mem_extendedFeasibleSet_iff {x : Q} :
    x ∈ 𝓕[constraints](ε) ↔ ∀ j : ι, constraints j x ≤ ε :=
  Iff.rfl

end

section

variable {m : ℕ}
variable (constraints : Fin m → Q → ℝ) (ε : ℝ)

/-- For finite real-valued constraints, the source-facing extended feasible set is exactly the
Chapter 3 feasible-set owner applied to the shifted family `x ↦ fⱼ(x) - ε` on `Set.univ`. -/
theorem extendedFeasibleSet_eq_inequalityConstrainedFeasibleSet :
    𝓕[constraints](ε) =
      inequalityConstrainedFeasibleSet Set.univ (fun j x ↦ constraints j x - ε) := by
  ext x
  simp [extendedFeasibleSet, inequalityConstrainedFeasibleSet]

end
