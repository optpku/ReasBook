/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SupportFunction

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 7.24 lies in the support-function geometry of convex bodies.

Primary domain:
- support functions of convex bodies in real inner-product spaces.

Sampled owner-style declarations:
- `supportFunction` with notation `ξ[Q]` in `Chap03/Definition_3_9`
- `ConvexBody.supportFunctionReal` in `Chap07/Definition_7_11`
- `ConvexBody.supportFunctionReal_apply` in `Chap07/Definition_7_11`
- `IsCompact.exists_isMaxOn` in mathlib's extreme-value API

Best owner abstraction:
- source-facing bridge owner: `ConvexBody.supportFunctionReal`

Primitive data:
- a convex body `C : ConvexBody E`
- an evaluation vector `x : E`

Derived API:
- the recalled owner `C.supportFunctionReal`
- the real supremum formula for `C.supportFunctionReal x`
- attainment of the maximum of `t ↦ ⟪t, x⟫` on `C`

Source/core/bridge triage:
- source-facing: the textbook real-valued support function `x ↦ max_{s ∈ C} ⟪s, x⟫`
- core/canonical: the Chapter 3 support-function owner `ξ[Q]` and the Chapter 7 convex-body bridge
  `ConvexBody.supportFunctionReal`
- bridge/view: this file's real-supremum and maximizer theorems

The previous version introduced a second public owner `ConvexBody.supportFunction` with exactly the
same mathematical content as `ConvexBody.supportFunctionReal`. This refinement deletes that
duplicate owner and keeps Definition 7.24 at the bridge layer over the existing Chapter 3/7 API.
The textbook `ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/

/- Definition 7.24 reuses the existing convex-body owner `supportFunctionReal`. -/
recall ConvexBody.supportFunctionReal
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : ConvexBody E) :
    E → ℝ

/- The defining `toReal` bridge for the convex-body support function is also recalled directly. -/
recall ConvexBody.supportFunctionReal_apply
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : ConvexBody E) (x : E) :
    C.supportFunctionReal x = (ξ[(C : Set E)] x).toReal

namespace ConvexBody

/-- The linear functional `s ↦ ⟪s, x⟫` attains its maximum on the convex body `C`. -/
theorem exists_isMaxOn_inner (C : ConvexBody E) (x : E) :
    ∃ s ∈ (C : Set E), IsMaxOn (fun t : E ↦ inner ℝ t x) (C : Set E) s := by
  simpa using C.isCompact.exists_isMaxOn C.nonempty
    ((continuous_id'.inner continuous_const).continuousOn)

/-- Definition 7.24 in source-facing real form: for a convex body `C`, the support function at
`x` is the supremum of the Euclidean pairings `⟪s, x⟫` over `s ∈ C`. -/
theorem supportFunctionReal_eq_sSup_inner (C : ConvexBody E) (x : E) :
    C.supportFunctionReal x = sSup ((fun s : E ↦ inner ℝ s x) '' (C : Set E)) := by
  obtain ⟨s, hsC, hsMax⟩ := C.exists_isMaxOn_inner x
  have hsGreatestReal :
      IsGreatest ((fun t : E ↦ inner ℝ t x) '' (C : Set E)) (inner ℝ s x) := by
    refine ⟨⟨s, hsC, rfl⟩, ?_⟩
    rintro _ ⟨t, htC, rfl⟩
    exact hsMax htC
  have hsSupReal :
      sSup ((fun t : E ↦ inner ℝ t x) '' (C : Set E)) = inner ℝ s x :=
    hsGreatestReal.csSup_eq
  have hsGreatestEReal :
      IsGreatest ((fun t : E ↦ (inner ℝ t x : EReal)) '' (C : Set E)) (inner ℝ s x : EReal) := by
    simpa only [Set.image_image] using
      (EReal.coe_strictMono.map_isGreatest).2 hsGreatestReal
  have hsSupEReal :
      sSup ((fun t : E ↦ (inner ℝ t x : EReal)) '' (C : Set E)) = (inner ℝ s x : EReal) :=
    hsGreatestEReal.csSup_eq
  calc
    C.supportFunctionReal x = (ξ[(C : Set E)] x).toReal := by
      simp
    _ = (sSup ((fun t : E ↦ (inner ℝ t x : EReal)) '' (C : Set E))).toReal := by
      rw [supportFunction_apply]
    _ = inner ℝ s x := by
      rw [hsSupEReal]
      simp
    _ = sSup ((fun t : E ↦ inner ℝ t x) '' (C : Set E)) := hsSupReal.symm

end ConvexBody
