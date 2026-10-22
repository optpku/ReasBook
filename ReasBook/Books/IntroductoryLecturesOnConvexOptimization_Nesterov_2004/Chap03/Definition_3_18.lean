/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 3.18 is a source-facing item in the chapter's polar/support-function domain.

Sampled owner-style declarations:
- project `supportFunction`
- project `supportFunction_apply`
- mathlib `StrongDual.polar`
- project `polarSetAt`

Best owner abstraction:
- source-facing: the chapter declaration `polarSet`
- core/canonical: the earlier chapter owner `supportFunction`

Primitive data:
- a set `Q : Set E` in a real inner-product space `E`

Derived API:
- the support-function sublevel presentation `ξ[Q] g ≤ 1`
- the inequality characterization `mem_polarSet_iff`
- the later based variant `polarSetAt`

Source/core/bridge triage:
- source-facing: the textbook polar set of `Q`
- core/canonical: `supportFunction`
- bridge/view: the based variant `polarSetAt Q xBar`

The sampled mathlib polar lives in the strong dual and uses the absolute-value bound
`‖x' z‖ ≤ 1`, so it is not the exact source-facing owner for this one-sided Euclidean-pairing
notion. Within the chapter, however, the primitive construction already exists upstream as the
support function `ξ[Q]`. This file therefore keeps the source-facing owner `polarSet`, but defines
it through the canonical Chapter 3 owner `supportFunction` instead of storing the same family of
pairing inequalities as primitive data. As with nearby owner files such as `Definition_3_9`, the
source prose is Euclidean, but the declaration only needs the ambient real inner-product-space
structure used by the pairing.
-/

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped SupportFunction

/-- Definition 3.18, generalized from the textbook Euclidean setting: the polar set of
`Q` consists of the vectors whose pairing with every point of `Q` is at most `1`.
Specializing to `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `Qᵒ ⊆ ℝⁿ`. -/
def polarSet (Q : Set E) : Set E :=
  {g | ξ[Q] g ≤ (1 : EReal)}

/- Source-facing Lean notation for the textbook polar set `Qᵒ`. -/
namespace PolarSet

scoped postfix:max "ᵒ" => polarSet

end PolarSet

open scoped PolarSet

/-- Membership in the polar set is the defining family of inequalities against `Q`. -/
theorem mem_polarSet_iff {Q : Set E} {g : E} :
    g ∈ Qᵒ ↔ ∀ x ∈ Q, inner ℝ g x ≤ 1 :=
by
  change ξ[Q] g ≤ (1 : EReal) ↔ ∀ x ∈ Q, inner ℝ g x ≤ 1
  rw [supportFunction_apply, sSup_le_iff]
  simp_rw [Set.forall_mem_image, real_inner_comm]
  constructor
  · intro h x hx
    exact_mod_cast h hx
  · intro h x hx
    exact_mod_cast h x hx
