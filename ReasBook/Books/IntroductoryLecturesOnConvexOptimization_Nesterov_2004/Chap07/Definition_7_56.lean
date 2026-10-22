/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {X : Type u}

open SetConstrainedMinimizationProblem

/- Definition 7.56 lies in the basic optimization domain of objective-value suprema on feasible
sets.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the Chapter 1
  owner taking values in `EReal` so empty or unbounded feasible-value sets are represented
  faithfully;
- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in
  `Chap01/Definition_1_3_7`, the canonical expansion theorem for that owner;
- `LinearPackingProblem.optimalValue` in `Chap07/Definition_7_41`, the Chapter 7 maximization-side
  owner likewise living in `EReal` and defined via negation of a Chapter 1 minimization owner;
- `sSup`, the canonical supremum owner in a complete lattice, which belongs here only as the
  expansion surface for the source-facing textbook value.

Best owner abstraction:
- source-facing: the textbook maximal value `f_*` of `f` on the feasible set `P`;
- core/canonical: `(.mk P (fun x ↦ -f x) : SetConstrainedMinimizationProblem X).optimalValue`;
- bridge/view: the expansion theorem `maximalValueOn_eq_sSup_image`.

Primitive data:
- a feasible set `P : Set X`;
- an objective `f : X → ℝ`.

Derived API:
- the source-facing owner name `maximalValueOn`, implemented as maximization through negated
  Chapter 1 minimization;
- the theorem expanding it back to the canonical `sSup` expression;
- the closure-invariance theorem `maximalValueOn_eq_of_closure_eq` for continuous objectives.

Definition 7.56 is source-facing, not a second core optimization owner. The correct refinement is
therefore to keep the textbook value `f_*` as a thin bridge to the Chapter 1 minimization owner
with objective `x ↦ -f x`, matching the Chapter 7 maximization pattern already used in
Definition 7.41. The raw `sSup` formula remains only as the expansion theorem. A dedicated
notation for `f_*` is not introduced: this owner is reused, but not at a frequency or syntactic
regularity that justifies custom parser surface beyond the short canonical name. -/

/-- Definition 7.56: for a feasible set `P ⊆ X` and an objective `f`, the maximal value `f_*`
of the associated problem is the negated Chapter 1 optimal value of the minimization problem with
feasible set `P` and objective `x ↦ -f x`. This keeps maximization on the project's canonical
`EReal`-valued optimization owner. -/
def maximalValueOn (P : Set X) (f : X → ℝ) : EReal :=
  -((.mk P (fun x ↦ -f x) : SetConstrainedMinimizationProblem X).optimalValue)

/-- Expanding `maximalValueOn P f` gives the supremum of the objective values over `P`. -/
theorem maximalValueOn_eq_sSup_image (P : Set X) (f : X → ℝ) :
    maximalValueOn P f = sSup ((fun x ↦ (f x : EReal)) '' P) := by
  let s : Set EReal := ((fun x ↦ (f x : EReal)) '' P)
  have hs : -sInf ((fun y : EReal ↦ -y) '' s) = sSup s := by
    apply le_antisymm
    · rw [EReal.neg_le]
      refine le_sInf ?_
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      rw [EReal.neg_le, neg_neg]
      exact le_sSup hy
    · refine sSup_le ?_
      intro y hy
      rw [EReal.le_neg]
      exact sInf_le (Set.mem_image_of_mem (fun z : EReal ↦ -z) hy)
  rw [maximalValueOn]
  simpa [optimalValue, s, Set.image_image] using hs

/-- If `x ∈ P` attains the maximum of `f` on `P`, then `maximalValueOn P f` is the attained value
`f x`. -/
theorem maximalValueOn_eq_of_isMaxOn
    {P : Set X} {f : X → ℝ} {x : X} (hx : x ∈ P) (hmax : IsMaxOn f P x) :
    maximalValueOn P f = (f x : EReal) := by
  rw [maximalValueOn_eq_sSup_image]
  apply le_antisymm
  · refine sSup_le ?_
    intro y hy
    rcases hy with ⟨y, hyP, rfl⟩
    change (f y : EReal) ≤ (f x : EReal)
    exact_mod_cast (isMaxOn_iff.1 hmax y hyP)
  · exact le_sSup (Set.mem_image_of_mem (fun y ↦ (f y : EReal)) hx)

section Closure

variable {E : Type u} [TopologicalSpace E]

-- Proof sketch: if `s ⊆ t ⊆ closure s`, then the order-topology criterion
-- `isLUB_iff_of_subset_of_subset_closure` identifies the two `IsLUB` predicates, hence their
-- suprema coincide.
private theorem sSup_eq_of_subset_of_subset_closure
    {α : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ closure s) : sSup t = sSup s := by
  refine (isLUB_sSup t).unique ?_
  exact ((isLUB_iff_of_subset_of_subset_closure hst hts).1 (isLUB_sSup s))

-- Proof sketch: continuity on `closure P` identifies the image of `closure P` with the closure of
-- the image of `P`; taking `sSup` is unchanged when passing from a subset of `ℝ` to a set sitting
-- between it and its closure.
/-- If `Q` is the closure of `P` and `f` is continuous on `Q`, then maximizing `f` over `P` or
over `Q` gives the same maximal value. -/
theorem maximalValueOn_eq_of_closure_eq
    {P Q : Set E} {f : E → ℝ} (hclosure : closure P = Q) (hf : ContinuousOn f Q) :
    maximalValueOn P f = maximalValueOn Q f := by
  have hf' : ContinuousOn f (closure P) := by
    simpa [hclosure] using hf
  have hfEReal : ContinuousOn (fun x ↦ (f x : EReal)) (closure P) :=
    continuous_coe_real_ereal.comp_continuousOn hf'
  rw [maximalValueOn_eq_sSup_image, ← hclosure, maximalValueOn_eq_sSup_image]
  symm
  exact sSup_eq_of_subset_of_subset_closure
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, subset_closure hx, rfl⟩)
    hfEReal.image_closure

end Closure

end
