/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped Gradient SupportFunction WithTopConvexAnalysis EuclideanOrthant

universe u

variable {m : ℕ} {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Lemma 3.16 is a source-facing bounded-to-compact bridge in the chapter's
support-function-composition domain.

Primary domain:
- support-function compositions and their active-multiplier subdifferentials.

Sampled owner and bridge declarations:
- `activeSupportFunctionMultipliers`
- `subdifferential_supportFunction_comp_vectorMap_eq_image_activeMultipliers`
- `Bornology.IsBounded.isCompact_closure`
- `subset_convexHull`

Best owner abstraction:
- the owner theorem
  `subdifferential_supportFunction_comp_vectorMap_eq_image_activeMultipliers`
  over the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)`, its active multipliers
  `activeSupportFunctionMultipliers Λ fs x`, its thin `WithTop` bridge
  `supportFunctionCompWithTop Λ fs`, and `weightedGradientCombination`

Primitive data:
- a weight set `Λ : Set Eₘ`
- a coordinate family `fs : Fin m → E → ℝ`
- a pointwise gradient witness `HasGradientAt (fs i) (∇ (fs i) x) x` at the base point

Derived API kept here:
- the source-facing orthant hypothesis `Λ ⊆ nonnegativeOrthant m`
- the bounded-to-compact passage `Bornology.IsBounded.isCompact_closure`
- the closure active multiplier face `activeSupportFunctionMultipliers (closure Λ) fs x`
- the convex-hull enclosure `subset_convexHull`
- the direct image `(weightedGradientCombination fs x) ''
    activeSupportFunctionMultipliers (closure Λ) fs x`

Source/core/bridge triage:
- source-facing: Lemma 3.16's bounded-to-compact subdifferential description
- core/canonical: `EuclideanSpace.nonnegativeOrthant`, `supportFunction`, `pointwiseSupremumOn`,
  `weightedGradientCombination`, `subdifferential`,
  `subdifferential_supportFunction_comp_vectorMap_eq_image_activeMultipliers`
- bridge/view: `Bornology.IsBounded.isCompact_closure`, the closure specialization, and the
  `WithTop` bridge `supportFunctionCompWithTop Λ fs` on the left-hand side of the theorem
  statements

This file therefore refines part (1) to direct canonical recall of the exact owner theorem
`convexOn_supportFunction_comp_vectorMap` and keeps only parts (2) and (3) as the genuine
bounded-to-compact bridge layer on top of that owner API.
-/

/- Lemma 3.16 (1): for a nonnegative weight set, the finite real part of the
support-function composition `x ↦ ξ[Λ] (vectorMap fs x)` is convex on its effective domain.

This is exactly the upstream owner theorem `convexOn_supportFunction_comp_vectorMap` from
`Lemma_3_1_16`. In the bounded case considered here, Proposition 3.11 can additionally identify
that effective domain with `Set.univ`. Keeping a renamed local theorem here would duplicate the
owner's exact interface, so this file records that fact only in prose. -/

/-- Helper for Lemma 3.16: if `s ⊆ t ⊆ closure s`, `s` is nonempty, and `t` is bounded above,
then the two `sSup` values in `WithTop ℝ` agree. -/
private theorem sSup_eq_of_subset_of_subset_closure
    {s t : Set (WithTop ℝ)} (hs : s.Nonempty) (ht_bdd : BddAbove t)
    (hst : s ⊆ t) (hts : t ⊆ closure s) :
    sSup t = sSup s := by
  -- The closure hypothesis identifies the upper-bound predicates of `s` and `t`.
  refine (isLUB_csSup (hs.mono hst) ht_bdd).unique ?_
  exact
    ((isLUB_iff_of_subset_of_subset_closure hst hts).1
      (isLUB_csSup hs (ht_bdd.mono hst)))

/-- Helper for Lemma 3.16: the nonnegative orthant in `ℝ^m` is closed. -/
private theorem nonnegativeOrthant_isClosed : IsClosed (ℝ₊^m : Set Eₘ) := by
  let e : Eₘ ≃ₜ (Fin m → ℝ) := (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
  have horthant :
      (ℝ₊^m : Set Eₘ) =
        e ⁻¹' Set.pi Set.univ (fun _ : Fin m ↦ Set.Ici (0 : ℝ)) := by
    ext x
    simp [EuclideanSpace.mem_nonnegativeOrthant_iff, Pi.le_def, e]
  -- Transport the coordinatewise closed halfspaces through the Euclidean homeomorphism.
  rw [horthant]
  exact (isClosed_set_pi fun _ _ ↦ isClosed_Ici).preimage e.continuous

/-- Helper for Lemma 3.16: closing a bounded nonempty multiplier set does not change the
`WithTop` support-function composition. -/
private theorem supportFunctionCompWithTop_closure_eq
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_bounded : Bornology.IsBounded Λ) (hΛ_nonempty : Λ.Nonempty) :
    supportFunctionCompWithTop (closure Λ) fs = supportFunctionCompWithTop Λ fs := by
  ext x
  let φ : Eₘ → WithTop ℝ := fun lam ↦ (inner ℝ lam (vectorMap fs x) : WithTop ℝ)
  have hφ_cont : Continuous φ := by
    -- The support slice is the inner product followed by the `WithTop` coercion.
    simpa [φ] using
      (WithTop.continuous_coe.comp (continuous_id.inner continuous_const))
  rw [supportFunctionCompWithTop, supportFunctionCompWithTop, pointwiseSupremumOn_apply,
    pointwiseSupremumOn_apply]
  change sSup (φ '' closure Λ) = sSup (φ '' Λ)
  -- The closure image sits between the original image and its closure.
  exact sSup_eq_of_subset_of_subset_closure
    (hΛ_nonempty.image φ)
    ((hΛ_bounded.isCompact_closure.image hφ_cont).bddAbove)
    (by
      rintro _ ⟨lam, hlam, rfl⟩
      exact ⟨lam, subset_closure hlam, rfl⟩)
    (hφ_cont.continuousOn.image_closure)

/-- Helper for Lemma 3.16: the active multiplier face over `closure Λ` is convex. -/
private theorem activeSupportFunctionMultipliers_convex_closure
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_convex : Convex ℝ Λ) (x : E) :
    Convex ℝ (activeSupportFunctionMultipliers (closure Λ) fs x) := by
  rw [convex_iff_add_mem]
  intro lam hlam mu hmu a b ha hb hab
  rw [mem_activeSupportFunctionMultipliers_iff] at hlam hmu ⊢
  have hclosure_convex : Convex ℝ (closure Λ) := hΛ_convex.closure
  refine ⟨(convex_iff_add_mem.mp hclosure_convex) hlam.1 hmu.1 ha hb hab, ?_⟩
  have hinner_eq : inner ℝ lam (vectorMap fs x) = inner ℝ mu (vectorMap fs x) := by
    simpa using (hlam.2.trans hmu.2.symm)
  -- Both active multipliers expose the same support value, so every convex combination stays
  -- on that active face.
  calc
    (inner ℝ (a • lam + b • mu) (vectorMap fs x) : WithTop ℝ)
        = (((a + b) * inner ℝ lam (vectorMap fs x) : ℝ) : WithTop ℝ) := by
            simp [inner_add_left, inner_smul_left, hinner_eq, add_mul]
    _ = (inner ℝ lam (vectorMap fs x) : WithTop ℝ) := by
      simp [hab]
    _ = supportFunctionCompWithTop (closure Λ) fs x := hlam.2

/-- Helper for Lemma 3.16: the weighted-gradient combination depends linearly on the multiplier
vector. -/
private theorem weightedGradientCombination_isLinear
    (fs : Fin m → E → ℝ) (x : E) :
    IsLinearMap ℝ (weightedGradientCombination fs x) := by
  refine ⟨?_, ?_⟩
  · intro a b
    -- Expand the defining sum coordinatewise to expose additivity.
    unfold weightedGradientCombination
    change ∑ i, (((a i + b i) : ℝ) • ∇ (fs i) x) = _
    simp [Finset.sum_add_distrib, add_smul]
  · intro c a
    -- Scalar multiplication also acts coordinatewise on the multiplier variable.
    unfold weightedGradientCombination
    change ∑ i, ((c * a i : ℝ) • ∇ (fs i) x) = _
    simp [Finset.smul_sum, mul_smul]

/-- Helper for Lemma 3.16: an active multiplier for `Λ` remains active after passing to
`closure Λ`. -/
private theorem activeSupportFunctionMultipliers_subset_closure
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_bounded : Bornology.IsBounded Λ) (hΛ_nonempty : Λ.Nonempty) {x : E} :
    activeSupportFunctionMultipliers Λ fs x ⊆
      activeSupportFunctionMultipliers (closure Λ) fs x := by
  intro w hw
  rw [mem_activeSupportFunctionMultipliers_iff] at hw ⊢
  refine ⟨subset_closure hw.1, ?_⟩
  -- Closure does not change the support value, so the same touching equality remains valid.
  have hclosure_eq :
      supportFunctionCompWithTop Λ fs x =
        supportFunctionCompWithTop (closure Λ) fs x := by
    exact
      (congrFun
        (supportFunctionCompWithTop_closure_eq
          (Λ := Λ)
          (fs := fs)
          hΛ_bounded
          hΛ_nonempty)
        x).symm
  exact hw.2.trans hclosure_eq

/-- Lemma 3.16 (2): for a bounded convex nonnegative weight set, the subdifferential of the
`WithTop` bridge of the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)` is the convex
hull of the image of the closure active-multiplier face under the owner weighted-gradient map. -/
-- Proof sketch: pass from `Λ` to `closure Λ`; boundedness makes the closure compact without
-- changing the support-function value. The bounded source-facing formulation is then the convex
-- hull of the weighted-gradient image of the closure active-multiplier face.
theorem
    subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers_of_bounded
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_bounded : Bornology.IsBounded Λ) (hΛ_nonempty : Λ.Nonempty)
    (hΛ_nonneg : Λ ⊆ ℝ₊^m) (hΛ_convex : Convex ℝ Λ)
    (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i)) (x : E)
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    ∂ (supportFunctionCompWithTop Λ fs)(x) =
      convexHull ℝ
        ((weightedGradientCombination fs x) ''
          activeSupportFunctionMultipliers (closure Λ) fs x) := by
  have hclosure_nonneg : closure Λ ⊆ ℝ₊^m := by
    -- The nonnegative orthant is closed, so closing `Λ` preserves nonnegativity.
    exact nonnegativeOrthant_isClosed.closure_subset_iff.2 hΛ_nonneg
  have hsub_eq :
      ∂ (supportFunctionCompWithTop (closure Λ) fs)(x) =
        (weightedGradientCombination fs x) ''
          activeSupportFunctionMultipliers (closure Λ) fs x := by
    -- Apply the compact owner theorem to the closed bounded multiplier set.
    exact subdifferential_supportFunction_comp_vectorMap_eq_image_activeMultipliers
      (hΛ_nonempty.mono subset_closure)
      hΛ_bounded.isCompact_closure
      hΛ_convex.closure
      hclosure_nonneg
      hfs_convex
      x
      hfs_grad
  have himage_convex :
      Convex ℝ
        ((weightedGradientCombination fs x) ''
          activeSupportFunctionMultipliers (closure Λ) fs x) := by
    -- The active face is convex and the weighted-gradient map is linear in the multiplier.
    exact
      (activeSupportFunctionMultipliers_convex_closure
        (Λ := Λ) (fs := fs) hΛ_convex x).is_linear_image
        (weightedGradientCombination_isLinear fs x)
  -- Replace `Λ` by `closure Λ`, invoke the owner theorem, and collapse the convex hull of a
  -- convex image.
  calc
    ∂ (supportFunctionCompWithTop Λ fs)(x)
        = ∂ (supportFunctionCompWithTop (closure Λ) fs)(x) := by
            simp [supportFunctionCompWithTop_closure_eq
              (Λ := Λ) (fs := fs) hΛ_bounded hΛ_nonempty]
    _ = (weightedGradientCombination fs x) ''
          activeSupportFunctionMultipliers (closure Λ) fs x := hsub_eq
    _ = convexHull ℝ
          ((weightedGradientCombination fs x) ''
            activeSupportFunctionMultipliers (closure Λ) fs x) := by
            symm
            exact himage_convex.convexHull_eq

/-- Lemma 3.16 (3): every active multiplier in a bounded convex nonnegative weight set `Λ`
produces a subgradient of the support-function composition under the weighted-gradient map. -/
-- Proof sketch: the weighted gradient combination belongs to the image
-- `(weightedGradientCombination fs x) '' activeSupportFunctionMultipliers (closure Λ) fs x`
-- after passing from `Λ` to `closure Λ`. Then apply Lemma 3.16 (2) and the inclusion of a set
-- into its convex hull.
theorem weightedGradientCombination_mem_subdifferential_of_mem_activeMultipliers_of_bounded
    {Λ : Set Eₘ} {fs : Fin m → E → ℝ}
    (hΛ_bounded : Bornology.IsBounded Λ) (hΛ_nonneg : Λ ⊆ ℝ₊^m)
    (hΛ_convex : Convex ℝ Λ) (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i))
    {x : E}
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) {w : Eₘ}
    (hw : w ∈ activeSupportFunctionMultipliers Λ fs x) :
    weightedGradientCombination fs x w ∈
      ∂ (supportFunctionCompWithTop Λ fs)(x) := by
  have hw' := hw
  have hΛ_nonempty : Λ.Nonempty := by
    -- Any active multiplier is, in particular, a point of `Λ`.
    rw [mem_activeSupportFunctionMultipliers_iff] at hw'
    exact ⟨w, hw'.1⟩
  have hw_closure :
      w ∈ activeSupportFunctionMultipliers (closure Λ) fs x := by
    -- Activity persists after passing from `Λ` to its closure.
    exact
      activeSupportFunctionMultipliers_subset_closure
        (Λ := Λ)
        (fs := fs)
        hΛ_bounded
        hΛ_nonempty
        hw
  have hw_image :
      weightedGradientCombination fs x w ∈
        (weightedGradientCombination fs x) ''
          activeSupportFunctionMultipliers (closure Λ) fs x := by
    exact ⟨w, hw_closure, rfl⟩
  have hw_hull :
      weightedGradientCombination fs x w ∈
        convexHull ℝ
          ((weightedGradientCombination fs x) ''
            activeSupportFunctionMultipliers (closure Λ) fs x) := by
    -- Every point of the image lies in its convex hull.
    exact subset_convexHull ℝ _ hw_image
  -- Substitute the bounded subdifferential formula from Lemma 3.16 (2).
  simpa
    [subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers_of_bounded
      (Λ := Λ)
      (fs := fs)
      hΛ_bounded
      hΛ_nonempty
      hΛ_nonneg
      hΛ_convex
      hfs_convex
      x
      hfs_grad]
    using hw_hull

end
