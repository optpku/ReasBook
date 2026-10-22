/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.PointwiseSupremumOn

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 3.9 is the source-facing owner declaration in the chapter's support-function domain.

Primary domain:
- support functions of subsets of a real inner-product space.

Sampled owner-style declarations:
- `pointwiseSupremumOn` in `PointwiseSupremumOn`, the generic subset-indexed supremum owner
- `pointwiseSupremumOn_apply` in `PointwiseSupremumOn`, the evaluation bridge for that owner
- downstream recall `Definition_3_1_2_2`
- downstream proposition file `Proposition_3_1_2_2`

Best owner abstraction:
- source-facing: the chapter declaration `supportFunction`
- core/canonical: `pointwiseSupremumOn`

Primitive data:
- a set `Q : Set E`

Derived API:
- the evaluation lemma `supportFunction_apply`
- the convex-hull invariance theorem `supportFunction_convexHull_eq`
- later support-function results such as positive homogeneity and effective-domain theorems

Source/core/bridge triage:
- source-facing: the textbook support function of a set
- core/canonical: `pointwiseSupremumOn`; no more intrinsic mathlib owner for this exact
  `EReal`-valued Euclidean support-function specialization was found in the sampled domain
- bridge/view: the defining evaluation lemma `supportFunction_apply`
-/

/-- Definition 3.9: for a set `Q ⊆ ℝⁿ`, the support function of `Q` is the extended-real-valued
function sending `x` to the supremum of the inner products `⟪g, x⟫` over `g ∈ Q`. The textbook
`ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
def supportFunction (Q : Set E) : E → EReal :=
  pointwiseSupremumOn Q fun x g ↦ ↑(inner ℝ g x)

/- Source-facing Lean notation for the textbook support function `ξ_Q`. -/
namespace SupportFunction

scoped notation:max "ξ[" Q "]" => supportFunction Q

end SupportFunction

open scoped SupportFunction

/-- The support function is given by the defining `EReal` supremum of the inner products with
vectors in `Q`. -/
@[simp] theorem supportFunction_apply (Q : Set E) (x : E) :
    ξ[Q] x = sSup ((fun g ↦ ↑(inner ℝ g x)) '' Q) :=
  pointwiseSupremumOn_apply

/-- The support function is unchanged when `Q` is replaced by its convex hull. -/
theorem supportFunction_convexHull_eq (Q : Set E) :
    ξ[convexHull ℝ Q] = ξ[Q] := by
  funext x
  rw [supportFunction_apply, supportFunction_apply]
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hyz⟩ :=
      (((innerₗ E).flip x).convexOn (convex_convexHull ℝ Q)).exists_ge_of_mem_convexHull
        (subset_convexHull ℝ Q) hy
    exact
      (show ((inner ℝ y x : ℝ) : EReal) ≤ ↑(inner ℝ z x) by
        exact_mod_cast hyz).trans <| le_sSup ⟨z, hz, rfl⟩
  · exact sSup_le_sSup (Set.image_mono (subset_convexHull ℝ Q))

end
