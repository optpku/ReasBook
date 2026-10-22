/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 4.1 is `source-facing` in the chapter conjugacy API. Its primitive notions are the
owner declarations `is_convex_function` from Definition 2.6 and `conjugate_function` from
Definition 4.1; the canonical `bridge/view` owner is `conjugate_function_primal`, which
specializes the dual-space conjugate to the primal inner-product space through `toDualMap`
without reintroducing a local lambda wrapper. -/
recall conjugate_function_primal

/-- Helper for Theorem 4.1: rewrite the primal Fenchel conjugate as the pointwise supremum of its
affine pairing slices. -/
private lemma conjugateFunctionPrimal_eq_iSupAffinePieces (f : E → EReal) :
    f∗ = fun y ↦ ⨆ x : E, ((((toDualMap ℝ E x) y : ℝ) : EReal) - f x) := by
  -- Rewrite the defining `sSup` as an `iSup` indexed directly by primal points.
  funext y
  rw [conjugate_function_primal_apply, conjugate_function_apply, sSup_range]
  -- Identify the dual pairing with the primal inner product in the expected argument order.
  simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]

/-- Helper for Theorem 4.1: every constant extended-real-valued function is convex in the
chapter-owner sense. -/
private lemma isConvexFunction_erealConst (c : EReal) :
    is_convex_function (fun _ : E ↦ c) := by
  -- Split by the three possible constant shapes of `EReal`.
  by_cases hbot : c = ⊥
  · -- The constant-bottom function has epigraph `Set.univ`.
    rw [hbot, is_convex_function_iff_convex_real_epigraph]
    have hepigraph : {p : E × ℝ | (⊥ : EReal) ≤ (p.2 : EReal)} = Set.univ := by
      ext p
      simp
    rw [hepigraph]
    exact (convex_univ : Convex ℝ (Set.univ : Set (E × ℝ)))
  by_cases htop : c = ⊤
  · -- The constant-top function has empty real epigraph.
    rw [htop, is_convex_function_iff_convex_real_epigraph]
    have hepigraph : {p : E × ℝ | (⊤ : EReal) ≤ (p.2 : EReal)} = (∅ : Set (E × ℝ)) := by
      ext p
      simp
    rw [hepigraph]
    exact (convex_empty : Convex ℝ (∅ : Set (E × ℝ)))
  -- The finite branch reduces to the convexity of a half-space.
  have hfinite : c = (((c.toReal : ℝ)) : EReal) := by
    symm
    exact EReal.coe_toReal htop hbot
  rw [hfinite, is_convex_function_iff_convex_real_epigraph]
  have hepigraph :
      {p : E × ℝ | (((c.toReal : ℝ) : EReal)) ≤ (p.2 : EReal)} =
        Set.univ ×ˢ Set.Ici c.toReal := by
    ext p
    simp
  rw [hepigraph]
  exact convex_univ.prod (convex_Ici _)

/-- Helper for Theorem 4.1: subtracting a finite real constant from a primal pairing slice
preserves lower semicontinuity and convexity. -/
private lemma affinePairingSubReal_closed_and_convex (x : E) (c : ℝ) :
    LowerSemicontinuous
        (fun y : E ↦ ((((toDualMap ℝ E x) y : ℝ) : EReal) - (c : EReal))) ∧
      is_convex_function
        (fun y : E ↦ ((((toDualMap ℝ E x) y : ℝ) : EReal) - (c : EReal))) := by
  constructor
  · -- Rewrite the slice as a continuous real affine map followed by the coercion `ℝ → EReal`.
    have hcont :
        Continuous (fun y : E ↦ (((((toDualMap ℝ E x) y) - c : ℝ) : EReal))) := by
      exact
        (continuous_coe_real_ereal.comp (((toDualMap ℝ E x).continuous).sub continuous_const))
    have hslice :
        LowerSemicontinuous (fun y : E ↦ (((((toDualMap ℝ E x) y) - c : ℝ) : EReal))) := by
      exact hcont.lowerSemicontinuous
    simpa [EReal.coe_sub] using hslice
  · -- Convexity is preserved after adding the finite constant slice pointwise.
    have hconst :
        is_convex_function (fun _ : E ↦ (((-c : ℝ) : EReal))) :=
      isConvexFunction_erealConst (((-c : ℝ) : EReal))
    have hsum :
        is_convex_function
          ((fun y : E ↦ ((((toDualMap ℝ E x) y : ℝ) : EReal))) +
            fun _ : E ↦ (((-c : ℝ) : EReal))) := by
      exact
        is_convex_function_pointwise_add
          (isConvexFunction_ereal_toDualEval x)
          hconst
          (fun y ↦ by simp)
          (fun y ↦ by simp)
    simpa [Pi.add_apply, sub_eq_add_neg] using hsum

/-- Helper for Theorem 4.1: each affine slice `y ↦ ⟪y, x⟫ - f x` of the conjugate supremum is
lower semicontinuous and convex, regardless of whether `f x` is finite or infinite. -/
private lemma affinePairingMinusValue_closed_and_convex (f : E → EReal) (x : E) :
    LowerSemicontinuous (fun y : E ↦ ((((toDualMap ℝ E x) y : ℝ) : EReal) - f x)) ∧
      is_convex_function (fun y : E ↦ ((((toDualMap ℝ E x) y : ℝ) : EReal) - f x)) := by
  -- Split on the frozen value `f x`.
  by_cases hbot : f x = ⊥
  · -- Subtracting `⊥` gives the constant-top slice.
    simpa [hbot] using
      (show LowerSemicontinuous (fun _ : E ↦ (⊤ : EReal)) ∧
          is_convex_function (fun _ : E ↦ (⊤ : EReal)) from
        ⟨lowerSemicontinuous_const, isConvexFunction_erealConst ⊤⟩)
  by_cases htop : f x = ⊤
  · -- Subtracting `⊤` gives the constant-bottom slice.
    simpa [htop] using
      (show LowerSemicontinuous (fun _ : E ↦ (⊥ : EReal)) ∧
          is_convex_function (fun _ : E ↦ (⊥ : EReal)) from
        ⟨lowerSemicontinuous_const, isConvexFunction_erealConst ⊥⟩)
  -- The remaining branch is finite, so reuse the real-constant slice lemma.
  have hfinite : f x = ((((f x).toReal : ℝ)) : EReal) := by
    symm
    exact EReal.coe_toReal htop hbot
  rw [hfinite]
  exact affinePairingSubReal_closed_and_convex x (f x).toReal

-- Proof sketch: for each fixed `x : E`, the map
-- `f∗` contributes the affine function
-- `y ↦ ⟪y, x⟫ - f x` in the defining supremum of `f*`. Each such affine function is continuous,
-- hence lower semicontinuous, and convex in the chapter-owner sense. Then closedness follows from
-- lower semicontinuity of pointwise suprema, and convexity follows from the chapter closure result
-- `is_convex_function_iSup` after rewriting the conjugate by its defining supremum.
/-- Theorem 4.1: the primal-space Fenchel conjugate `f∗` is closed and convex. The numbered
statements below are the source-facing projections of this reusable owner theorem. -/
theorem conjugate_function_closed_and_convex (f : E → EReal) :
    LowerSemicontinuous (f∗) ∧ is_convex_function (f∗) :=
  by
    -- Route correction: normalize `f∗` to a supremum of affine slices, then close each field
    -- with the Chapter 2 supremum lemmas.
    rw [conjugateFunctionPrimal_eq_iSupAffinePieces]
    constructor
    · -- Lower semicontinuity is stable under arbitrary pointwise suprema.
      exact lowerSemicontinuous_iSup fun x ↦ (affinePairingMinusValue_closed_and_convex f x).1
    · -- Convexity is stable under arbitrary pointwise suprema of convex slices.
      exact is_convex_function_iSup fun x ↦ (affinePairingMinusValue_closed_and_convex f x).2

/-- Closedness projection for Theorem 4.1: the conjugate function of an extended-real-valued
function on a real inner product space, viewed on the primal space as `f∗`, is lower
semicontinuous. -/
theorem conjugate_function_lowerSemicontinuous (f : E → EReal) :
    LowerSemicontinuous (f∗) :=
  (conjugate_function_closed_and_convex f).1

/-- Convexity projection for Theorem 4.1: the conjugate function of an extended-real-valued
function on a real inner product space, viewed on the primal space as `f∗`, is convex in the
chapter-owner sense. -/
theorem conjugate_function_convex (f : E → EReal) :
    is_convex_function (f∗) :=
  (conjugate_function_closed_and_convex f).2

end
