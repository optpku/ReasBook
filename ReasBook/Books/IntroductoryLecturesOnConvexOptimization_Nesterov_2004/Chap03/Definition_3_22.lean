/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ProperCone

universe u

/- Definition 3.22 is the source-facing normal-cone owner built on the chapter's dual-cone
abstraction.

Primary domain:
- tangent and normal cones in real inner-product-space convex analysis.

Relevant sampled declarations:
- `Set.vsub_singleton`
- `ProperCone.innerDual`
- `ProperCone.mem_innerDual`

Owner abstraction:
- `ProperCone.innerDual (Q -ᵥ ({xBar} : Set E))`

Primitive data:
- the set `Q`
- the base point `xBar`

Derived API:
- `mem_normalCone_iff`
- `neg_mem_normalCone_iff`
- downstream bridge/view lemmas such as `level_set_inequality_at_iff`

Source/core/bridge triage:
- source-facing: the textbook normal cone at `xBar`
- core/canonical: `ProperCone.innerDual (Q -ᵥ ({xBar} : Set E))`
- bridge/view: the membership and sign-reversal companion lemmas

The defining object itself does not need closedness, convexity, or the side condition `xBar ∈ Q`;
those hypotheses belong only to later theorems that use this owner abstraction. -/

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Definition 3.22: the normal cone to `Q` at `xBar`, realized as the inner dual cone of the
displacement set `Q - xBar`. -/
abbrev normalCone (Q : Set V) (xBar : V) : ProperCone ℝ V :=
  innerDual (Q -ᵥ ({xBar} : Set V))

/- Source-facing Lean notation for the textbook normal-cone family `N_Q`. -/
namespace NormalCone

scoped notation:max "N[" Q "]" => normalCone Q

end NormalCone

open scoped NormalCone

/-- Membership in the normal cone is exactly the defining supporting-halfspace inequality against
every point of `Q`. -/
theorem mem_normalCone_iff {Q : Set V} {xBar g : V} :
    g ∈ N[Q] xBar ↔ ∀ x ∈ Q, 0 ≤ inner ℝ g (x - xBar) := by
  simp [normalCone, real_inner_comm]

/-- Rewriting the normal-cone condition for `-g` gives the textbook inequality
`⟪g, xBar - x⟫ ≥ 0`. -/
theorem neg_mem_normalCone_iff {Q : Set V} {xBar g : V} :
    -g ∈ N[Q] xBar ↔ ∀ x ∈ Q, inner ℝ g (xBar - x) ≥ 0 := by
  rw [mem_normalCone_iff]
  constructor <;> intro hg x hx <;>
    simpa [sub_eq_add_neg, inner_add_right, inner_neg_right, add_comm] using hg x hx

end
