/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this core owner will be reused by Chapter 3 source-facing specializations.

noncomputable section

universe u v w

/- The primary domain here is subset-indexed pointwise suprema.

Sampled owner-style declarations:
- mathlib `sSup`
- Chapter 3 `supportFunction`, which is a source-facing specialization to linear slices
- Chapter 3 `pointwiseSupremumOnEffectiveDomain`, which is a later `WithTop ℝ` domain bridge

Best owner abstraction:
- the generic owner `pointwiseSupremumOn`

Primitive data:
- an index subset `Δ : Set ι`
- a family `φ : X → ι → α`

Derived API:
- the evaluation lemma `pointwiseSupremumOn_apply`

Source/core/bridge triage:
- core/canonical: `pointwiseSupremumOn`
- bridge/view: `pointwiseSupremumOn_apply`

This file isolates the generic supremum owner so source-facing constructions such as support
functions can reuse it directly, instead of re-declaring the same `sSup` wheel locally. -/

/-- The pointwise supremum over a parameter subset `Δ` of an indexed family of functions on `X`. -/
def pointwiseSupremumOn
    {ι : Type u} {X : Type v} {α : Type w} [ConditionallyCompleteLattice α]
    (Δ : Set ι) (φ : X → ι → α) : X → α :=
  fun x ↦ sSup ((fun y ↦ φ x y) '' Δ)

/-- Evaluating `pointwiseSupremumOn Δ φ` at `x` gives the defining supremum of the slice
`y ↦ φ x y` over `Δ`. -/
@[simp] theorem pointwiseSupremumOn_apply
    {ι : Type u} {X : Type v} {α : Type w} [ConditionallyCompleteLattice α]
    {Δ : Set ι} {φ : X → ι → α} {x : X} :
    pointwiseSupremumOn Δ φ x = sSup ((fun y ↦ φ x y) '' Δ) :=
  rfl

end
