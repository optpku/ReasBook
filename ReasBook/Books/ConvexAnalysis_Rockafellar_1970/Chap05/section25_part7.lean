/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part6

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- Helper for Theorem 25.6: a closed proper convex `EReal`-valued function gives the usual
`ProperConvexFunctionOn univ` package needed by the Chapter 23 and 24 lemmas. -/
lemma helperForTheorem_25_6_properConvexFunctionOn
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
  have hnotBot : ∀ x : Fin n → Real, f x ≠ (⊥ : EReal) := hf.1.1
  have hconvE : ConvexERealFunction (F := (Fin n → Real)) f := hf.2
  have hconvOn : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
    refine
      (convexFunctionOn_iff_segment_inequality
        (C := (Set.univ : Set (Fin n → Real))) (f := f) convex_univ
        (by
          intro x hx
          simpa using hnotBot x)).2 ?_
    intro x hx y hy t ht0 ht1
    -- The Jensen-style convexity in `ProperConvexERealFunction` is exactly the segment inequality.
    simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hconvE (x := x) (y := y) (a := 1 - t) (b := t) (by linarith) (le_of_lt ht0) (by ring)
  refine ⟨hconvOn, ?_, ?_⟩
  · rcases hf.1.2 with ⟨x0, hx0Top⟩
    -- A finite point of `f` gives a concrete epigraph point.
    refine ⟨(x0, (f x0).toReal), ?_⟩
    exact
      (mem_epigraph_univ_iff (f := f) (x := x0) (μ := (f x0).toReal)).2
        (EReal.le_coe_toReal hx0Top)
  · intro x hx
    -- Properness rules out the forbidden value `⊥` everywhere.
    simpa using hnotBot x

/-- Helper for Theorem 25.6: every gradient-limit vector is a genuine Euclidean subgradient at
the limit point, by the closed graph of the subdifferential. -/
lemma helperForTheorem_25_6_gradientLimitVectors_subset_preimageSubdifferential
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x : Fin n → Real} :
    gradientLimitVectorsAt f x ⊆
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hclosed : ClosedConvexFunction f := ⟨hfConv, hf_closed⟩
  intro g hg
  rcases hg with ⟨xSeq, hdiff, hxSeq_tendsto, hgrad_tendsto⟩
  have hgradMem :
      ∀ i : ℕ,
        dotProductEquiv Real (Fin n) (erealGradientAt (hdiff i)) ∈
          subdifferentialAt f (xSeq i) := by
    intro i
    -- Differentiability identifies the gradient with the unique Euclidean subgradient.
    simpa using
      (((convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hfConv (xSeq i) (ERealDifferentiableAt.finiteAt (hdiff i))).1 (hdiff i)).1 : _)
  -- The closed-graph theorem lets the limit of nearby gradients stay inside `∂ f (x)`.
  exact
    (subdifferential_limit_mem_and_isClosed_graph (f := f) hclosed hproper).1
      xSeq (fun i => erealGradientAt (hdiff i)) hgradMem hxSeq_tendsto hgrad_tendsto

/-- Helper for Theorem 25.6: every gradient-limit vector at an interior-domain point is already a
genuine Euclidean subgradient there. -/
lemma helperForTheorem_25_6_gradientLimitVectors_subset_preimageSubdifferential_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    gradientLimitVectorsAt f x ⊆
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) := by
  let A : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    -- Interior-domain points are finite, and properness excludes `⊥`.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) (interior_subset hx),
        hproper.2.2 x (by simp)⟩
  have hAClosed : IsClosed A := by
    -- The vectorized subdifferential is closed by Theorem 23.2.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.1
  intro g hg
  rcases hg with ⟨xSeq, hdiff, hxSeq_tendsto, hgrad_tendsto⟩
  by_contra hgA
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.ball g (2 * ε) ⊆ Aᶜ := by
    -- Closedness of `A` gives a separating open ball around any exterior point.
    rcases Metric.mem_nhds_iff.1 (hAClosed.isOpen_compl.mem_nhds hgA) with ⟨r, hr, hrsub⟩
    refine ⟨r / 2, half_pos hr, ?_⟩
    intro y hy
    apply hrsub
    have hrad : 2 * (r / 2) = r := by ring
    simpa [Metric.mem_ball, hrad] using hy
  obtain ⟨δ, hδpos, hδsub⟩ :=
    helperForCorollary_5_24_2_local_subdifferential_subset
      (f := f) hproper hx ε hε
  have hSeqClosedBall :
      ∀ᶠ i : ℕ in Filter.atTop, xSeq i ∈ Metric.closedBall x δ :=
    hxSeq_tendsto (Metric.closedBall_mem_nhds x hδpos)
  have hGradBall :
      ∀ᶠ i : ℕ in Filter.atTop, erealGradientAt (hdiff i) ∈ Metric.ball g ε :=
    hgrad_tendsto (Metric.ball_mem_nhds g hε)
  rcases Filter.eventually_atTop.1 hSeqClosedBall with ⟨iClosed, hiClosed⟩
  rcases Filter.eventually_atTop.1 hGradBall with ⟨iBall, hiBall⟩
  let i : ℕ := max iClosed iBall
  have hxi : xSeq i ∈ Metric.closedBall x δ := hiClosed i (le_max_left _ _)
  have hgi : erealGradientAt (hdiff i) ∈ Metric.ball g ε := hiBall i (le_max_right _ _)
  have hgradPreimage :
      erealGradientAt (hdiff i) ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f (xSeq i)) := by
    -- Differentiability turns the nearby subdifferential into the singleton gradient.
    simpa using
      (((convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hfConv (xSeq i) (ERealDifferentiableAt.finiteAt (hdiff i))).1 (hdiff i)).1 : _)
  have hnear := hδsub hxi hgradPreimage
  rcases hnear with ⟨u, hu, v, hv, huv⟩
  have hvNorm : ‖v‖ ≤ ε := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv
  have hgradNorm : ‖u + v - g‖ < ε := by
    have hgi' := hgi
    rw [← huv] at hgi'
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hgi'
  have huBall : u ∈ Metric.ball g (2 * ε) := by
    -- The nearby gradient is within `ε` of both `u` and `g`, so `u` lies in the larger ball.
    rw [Metric.mem_ball, dist_eq_norm]
    have huEq : u - g = (u + v - g) - v := by
      abel_nf
    have huLe : ‖u - g‖ ≤ ‖u + v - g‖ + ‖v‖ := by
      rw [huEq]
      exact norm_sub_le _ _
    linarith
  exact hball huBall hu

/-- Helper for Theorem 25.6: at an interior-domain point, the closed convex hull generated by the
gradient-limit vectors already sits inside the Euclideanized subdifferential. -/
lemma helperForTheorem_25_6_closureConvexHull_gradientLimitVectors_subset_preimageSubdifferential_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    closure (convexHull Real (gradientLimitVectorsAt f x)) ⊆
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) := by
  let A : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    -- The closed/convex description of `∂f(x)` applies because `x` is finite.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) (interior_subset hx),
        hproper.2.2 x (by simp)⟩
  have hAClosed : IsClosed A := by
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.1
  have hAConvex : Convex Real A := by
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
  have hLimitSubset :
      gradientLimitVectorsAt f x ⊆ A :=
    helperForTheorem_25_6_gradientLimitVectors_subset_preimageSubdifferential
      (f := f) hf hf_closed
  have hHullSubset : convexHull Real (gradientLimitVectorsAt f x) ⊆ A := by
    -- Convexity of the target set upgrades the pointwise inclusion to the convex hull.
    exact (hAConvex.convexHull_subset_iff).2 hLimitSubset
  -- Closedness then absorbs the closure of that convex hull.
  exact closure_minimal hHullSubset hAClosed

/-- Helper for Theorem 25.6: at any domain point, the closed convex hull of the gradient-limit
vectors already lies in the Euclideanized subdifferential. -/
lemma helperForTheorem_25_6_closureConvexHull_gradientLimitVectors_subset_preimageSubdifferential_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    closure (convexHull Real (gradientLimitVectorsAt f x)) ⊆
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) := by
  let A : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    -- Domain membership gives finiteness at `x`, and properness excludes `⊥`.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) hx,
        hproper.2.2 x (by simp)⟩
  have hAClosed : IsClosed A := by
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.1
  have hAConvex : Convex Real A := by
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
  have hLimitSubset :
      gradientLimitVectorsAt f x ⊆ A :=
    helperForTheorem_25_6_gradientLimitVectors_subset_preimageSubdifferential
      (f := f) hf hf_closed
  have hHullSubset : convexHull Real (gradientLimitVectorsAt f x) ⊆ A := by
    -- Convexity of `∂ f (x)` lifts the pointwise inclusion to the convex hull.
    exact (hAConvex.convexHull_subset_iff).2 hLimitSubset
  -- Closedness then absorbs the closure of the convex hull.
  exact closure_minimal hHullSubset hAClosed

/-- Helper for Theorem 25.6: any point in the closure of `gradientLimitVectorsAt f x` is already
an actual Euclidean subgradient when `x` is interior to `dom f`. -/
lemma helperForTheorem_25_6_closureGradientLimitVectors_subset_preimageSubdifferential_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x q : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hq : q ∈ closure (gradientLimitVectorsAt f x)) :
    dotProductEquiv Real (Fin n) q ∈ subdifferentialAt f x := by
  have hqHull :
      q ∈ closure (convexHull Real (gradientLimitVectorsAt f x)) := by
    -- Passing from `S(x)` to its closed convex hull only uses `S(x) ⊆ conv S(x)`.
    exact
      closure_minimal
        (Set.Subset.trans
          (subset_convexHull Real (gradientLimitVectorsAt f x))
          subset_closure)
        isClosed_closure hq
  -- The interior hull theorem then upgrades the closure witness to a genuine subgradient.
  exact
    helperForTheorem_25_6_closureConvexHull_gradientLimitVectors_subset_preimageSubdifferential_of_mem_interior
      (f := f) hf hf_closed hx hqHull

/-- Helper for Theorem 25.6: the same closure-to-subgradient upgrade remains valid at arbitrary
domain points, using the domain-level hull inclusion. -/
lemma helperForTheorem_25_6_closureGradientLimitVectors_subset_preimageSubdifferential_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x q : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hq : q ∈ closure (gradientLimitVectorsAt f x)) :
    dotProductEquiv Real (Fin n) q ∈ subdifferentialAt f x := by
  have hqHull :
      q ∈ closure (convexHull Real (gradientLimitVectorsAt f x)) := by
    -- The closed convex hull still contains `closure S(x)`.
    exact
      closure_minimal
        (Set.Subset.trans
          (subset_convexHull Real (gradientLimitVectorsAt f x))
          subset_closure)
        isClosed_closure hq
  -- Apply the domain-point hull inclusion from the forward half of Theorem 25.6.
  exact
    helperForTheorem_25_6_closureConvexHull_gradientLimitVectors_subset_preimageSubdifferential_of_mem_effectiveDomain
      (f := f) hf hf_closed hx hqHull

/-- Helper for Theorem 25.6: at an interior-domain point, the Euclideanized subdifferential is
nonempty and bounded, exactly as in Theorem 23.4. -/
lemma helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    Set.Nonempty (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) ∧
      Bornology.IsBounded
        (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  rcases
      ((subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        (f := f) hproper x).2.2.1).2 hx with
    ⟨hsub, hbounded⟩
  rcases hsub with ⟨xStar, hxStar⟩
  constructor
  · -- Pull the dual subgradient back to Euclidean coordinates through `dotProductEquiv`.
    refine ⟨(dotProductEquiv Real (Fin n)).symm xStar, ?_⟩
    simpa using hxStar
  · -- The boundedness clause is already packaged in Theorem 23.4.
    exact hbounded

/-- Helper for Theorem 25.6: at an interior-domain point, exposed points of the Euclideanized
subdifferential are exactly gradients of the directional-derivative support function. -/
lemma helperForTheorem_25_6_isExposedPoint_preimageSubdifferential_iff_exists_gradient_upperDirectionalDerivative_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x p : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    IsExposedPoint (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) p ↔
      ∃ y : Fin n → Real,
        ∃ hdiff : ERealDifferentiableAt (upperDirectionalDerivativeAt f x) y,
          erealGradientAt hdiff = p := by
  let C : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    -- Interior-domain points are finite, and properness excludes the value `⊥`.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) (interior_subset hx),
        hproper.2.2 x (by simp)⟩
  have hCnonempty : Set.Nonempty C :=
    (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
      (f := f) hf hx).1
  have hCclosed : IsClosed C := by
    -- Theorem 23.2 gives closedness of the Euclideanized subdifferential fiber.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.1
  have hCconv : Convex Real C := by
    -- The same theorem packages convexity of that fiber.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
  have hDpos :
      PositivelyHomogeneous (upperDirectionalDerivativeAt f x) := by
    -- The directional derivative is positively homogeneous at every finite convex point.
    rcases convex_directionalDerivative_monotone_exists_and_sublinear f hfConv x hxFinite with
      ⟨_hmono, hpos, _hconv, _hzero, _hsymm⟩
    exact hpos
  have hDproper :
      ProperConvexFunctionOn
        (Set.univ : Set (Fin n → Real)) (upperDirectionalDerivativeAt f x) := by
    have hxri :
        x ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      helperForTheorem_23_4_mem_relativeInterior_of_mem_interior
        (C := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hx
    -- Theorem 23.4 supplies properness of the directional derivative on the relative interior.
    exact
      ((subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        (f := f) hproper x).2.1 hxri).2.1
  have hCeq :
      C =
        {z : Fin n → Real |
          ∀ y : Fin n → Real,
            ((dotProduct y z : Real) : EReal) ≤ upperDirectionalDerivativeAt f x y} := by
    ext z
    -- Rewrite Euclidean subgradient membership as the universal directional-minorant property.
    simpa [C] using
      (helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
        f hfConv x hxFinite z)
  -- Theorem 25.1.3 is exactly the exposed-point characterization for this support function.
  exact
    isExposedPoint_iff_exists_gradient_of_differentiable_positivelyHomogeneous_properConvex
      (C := C) (g := upperDirectionalDerivativeAt f x) (z := p)
      hCnonempty hCclosed hCconv hDproper hDpos hCeq

/-- Helper for Theorem 25.6: when an exposed subgradient is realized as the gradient of the
directional derivative in direction `y`, the corresponding normal face of the Euclideanized
subdifferential collapses to the singleton `{p}`. -/
lemma helperForTheorem_25_6_subdifferentialNormalFace_singleton_of_gradient_upperDirectionalDerivative
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x y p : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hdiff : ERealDifferentiableAt (upperDirectionalDerivativeAt f x) y)
    (hgrad : erealGradientAt hdiff = p) :
    subdifferentialNormalFaceAt f x y = ({p} : Set (Fin n → Real)) := by
  let C : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    -- Interior-domain points are finite, so Chapter 23 identifies the directional derivative with
    -- the support function of the Euclideanized subdifferential fiber.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) (interior_subset hx),
        hproper.2.2 x (by simp)⟩
  have hCnonempty : Set.Nonempty C :=
    (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
      (f := f) hf hx).1
  have hCclosed : IsClosed C := by
    -- Chapter 23 gives closedness of the Euclideanized subdifferential fiber.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.1
  have hCconv : Convex Real C := by
    -- The same representation also packages convexity of the fiber.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
  have hDpos :
      PositivelyHomogeneous (upperDirectionalDerivativeAt f x) := by
    -- The directional derivative is positively homogeneous at every finite convex point.
    rcases convex_directionalDerivative_monotone_exists_and_sublinear f hfConv x hxFinite with
      ⟨_hmono, hpos, _hconv, _hzero, _hsymm⟩
    exact hpos
  have hDproper :
      ProperConvexFunctionOn
        (Set.univ : Set (Fin n → Real)) (upperDirectionalDerivativeAt f x) := by
    have hxri :
        x ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      helperForTheorem_23_4_mem_relativeInterior_of_mem_interior
        (C := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hx
    -- Theorem 23.4 supplies properness of the directional derivative on the relative interior.
    exact
      ((subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        (f := f) hproper x).2.1 hxri).2.1
  have hCeq :
      C =
        {z : Fin n → Real |
          ∀ y' : Fin n → Real,
            ((dotProduct y' z : Real) : EReal) ≤ upperDirectionalDerivativeAt f x y'} := by
    ext z
    -- Rewrite Euclidean subgradient membership as the universal directional-minorant property.
    simpa [C] using
      (helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
        f hfConv x hxFinite z)
  have hClosureEq :
      convexFunctionClosure (upperDirectionalDerivativeAt f x) =
        supportFunctionEReal C := by
    -- Corollary 25.1.3 identifies the convex closure with the support function of `C`.
    exact
      helperForCorollary_25_1_3_closure_eq_supportFunction
        (C := C) (g := upperDirectionalDerivativeAt f x) hDproper hDpos hCeq
  have hyInt :
      y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real))
        (upperDirectionalDerivativeAt f x)) := by
    -- Differentiability of the directional derivative forces `y` into the interior of its domain.
    exact
      (convexFunction_proper_and_mem_interior_of_differentiableAt
        (upperDirectionalDerivativeAt f x) hDproper.1 y hdiff).2
  have htransfer :=
    convexFunction_differentiableAt_iff_convexFunctionClosure_differentiableAt_and_gradient_eq
      (upperDirectionalDerivativeAt f x) hDproper.1 y hyInt
  have hcldiff :
      ERealDifferentiableAt
        (convexFunctionClosure (upperDirectionalDerivativeAt f x)) y :=
    htransfer.1.1 hdiff
  have hSuppDiff : ERealDifferentiableAt (supportFunctionEReal C) y := by
    -- Rewrite the closure differentiability statement along the support-function identity.
    simpa [hClosureEq] using hcldiff
  have hsupport :=
    section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCnonempty hCconv
  have hyFiniteSupp :
      supportFunctionEReal C y ≠ ⊤ ∧ supportFunctionEReal C y ≠ ⊥ :=
    ERealDifferentiableAt.finiteAt hSuppDiff
  have hSuppGrad : erealGradientAt hSuppDiff = p := by
    -- The gradient is preserved when passing from the directional derivative to its closure.
    have hclgrad : erealGradientAt hcldiff = p := by
      calc
        erealGradientAt hcldiff = erealGradientAt hdiff := htransfer.2 hdiff hcldiff
        _ = p := hgrad
    have hclosureProper :
        ProperConvexFunctionOn
          (Set.univ : Set (Fin n → Real))
          (convexFunctionClosure (upperDirectionalDerivativeAt f x)) :=
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := upperDirectionalDerivativeAt f x) hDproper).1.2
    have hclSub :
        IsSubgradientAt
          (convexFunctionClosure (upperDirectionalDerivativeAt f x)) y
          (dotProductEquiv Real (Fin n) (erealGradientAt hcldiff)) := by
      exact
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (convexFunctionClosure (upperDirectionalDerivativeAt f x))
          hclosureProper.1 y (ERealDifferentiableAt.finiteAt hcldiff)).1 hcldiff |>.1
    have hclSubSupport :
        IsSubgradientAt (supportFunctionEReal C) y
          (dotProductEquiv Real (Fin n) (erealGradientAt hcldiff)) := by
      simpa [hClosureEq] using hclSub
    have hEqGrad :
        erealGradientAt hcldiff = erealGradientAt hSuppDiff := by
      exact
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (supportFunctionEReal C) hsupport.1.1 y hyFiniteSupp).1 hSuppDiff |>.2.2
          (erealGradientAt hcldiff) hclSubSupport
    calc
      erealGradientAt hSuppDiff = erealGradientAt hcldiff := hEqGrad.symm
      _ = p := hclgrad
  ext z
  constructor
  · intro hz
    have hzMax :
        z ∈ C ∧ ∀ v ∈ C, dotProduct v y ≤ dotProduct z y := by
      refine ⟨hz.1, ?_⟩
      intro v hv
      have hface : dotProduct y (v - z) ≤ 0 := hz.2 v hv
      have hrewrite :
          dotProduct v y - dotProduct z y ≤ 0 := by
        simpa [dotProduct_comm, sub_eq_add_neg] using hface
      linarith
    have hzSubE :
        IsEuclideanSubgradientAt (supportFunctionEReal C) y z := by
      -- Maximizers of the support function are exactly its Euclidean subgradients.
      exact
        (euclidean_subgradient_supportFunctionEReal_iff_mem_and_maximizes_on_closed_convex_set
          C hCnonempty hCclosed hCconv y z).2 hzMax
    have hzSub :
        IsSubgradientAt (supportFunctionEReal C) y
          (dotProductEquiv Real (Fin n) z) := by
      simpa [IsEuclideanSubgradientAt] using hzSubE
    have hzEqGrad :
        z = erealGradientAt hSuppDiff := by
      -- Differentiability of the support function makes its gradient the unique subgradient.
      exact
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (supportFunctionEReal C) hsupport.1.1 y hyFiniteSupp).1 hSuppDiff |>.2.2 z hzSub
    have hzEq : z = p := by
      simpa [hSuppGrad] using hzEqGrad
    simpa [hzEq]
  · intro hz
    have hzEqGrad : z = erealGradientAt hSuppDiff := by
      simpa [hSuppGrad] using hz
    subst hzEqGrad
    have hpSubSupport :
        IsSubgradientAt (supportFunctionEReal C) y
          (dotProductEquiv Real (Fin n) (erealGradientAt hSuppDiff)) := by
      -- The support-function gradient is always a genuine subgradient at the same point.
      have hcore :=
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (supportFunctionEReal C) hsupport.1.1 y hyFiniteSupp).1 hSuppDiff
      exact hcore.1
    have hpSubE :
        IsEuclideanSubgradientAt
          (supportFunctionEReal C) y (erealGradientAt hSuppDiff) := by
      simpa [IsEuclideanSubgradientAt] using hpSubSupport
    have hpMax :
        erealGradientAt hSuppDiff ∈ C ∧
          ∀ v ∈ C, dotProduct v y ≤ dotProduct (erealGradientAt hSuppDiff) y :=
      (euclidean_subgradient_supportFunctionEReal_iff_mem_and_maximizes_on_closed_convex_set
        C hCnonempty hCclosed hCconv y (erealGradientAt hSuppDiff)).1 hpSubE
    refine ⟨hpMax.1, ?_⟩
    intro zStar hzStar
    -- Rewriting the maximizing inequality gives the normal-face condition.
    simpa [dotProduct_comm, sub_eq_add_neg] using (sub_nonpos.mpr (hpMax.2 zStar hzStar))

/-- Helper for Theorem 25.6: scaling an exposing direction by a positive real leaves the
corresponding Euclidean normal face unchanged. -/
lemma helperForTheorem_25_6_subdifferentialNormalFace_eq_of_pos_smul_direction
    {n : Nat} (f : (Fin n → Real) → EReal)
    {x y : Fin n → Real} {a : Real} (ha : 0 < a) :
    subdifferentialNormalFaceAt f x (a • y) = subdifferentialNormalFaceAt f x y := by
  ext p
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro z hz
    have hface : dotProduct (a • y) (z - p) ≤ 0 := hp.2 z hz
    have hscaled : a * dotProduct y (z - p) ≤ 0 := by
      rw [smul_dotProduct, smul_eq_mul] at hface
      exact hface
    have hbase : dotProduct y (z - p) ≤ 0 := by
      nlinarith [hscaled, ha]
    exact hbase
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro z hz
    have hbase : dotProduct y (z - p) ≤ 0 := hp.2 z hz
    have hscaled : a * dotProduct y (z - p) ≤ 0 := by
      nlinarith [hbase, ha]
    have hface : dotProduct (a • y) (z - p) ≤ 0 := by
      rw [smul_dotProduct, smul_eq_mul]
      exact hscaled
    exact hface

/-- Helper for Theorem 25.6: an interior sequence whose Euclideanized subdifferentials shrink
into arbitrarily small balls around `p` yields `p` as a genuine gradient-limit vector. -/
lemma helperForTheorem_25_6_gradientLimitVector_of_eventuallySmallSubdifferentials
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x p : Fin n → Real}
    (q : ℕ → Fin n → Real)
    (hqInt : ∀ i : ℕ,
      q i ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hqTendsto : Filter.Tendsto q Filter.atTop (nhds x))
    (hqSmall :
      ∀ ε : Real, 0 < ε → ∃ i0 : ℕ, ∀ i ≥ i0,
        ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f (q i)) ⊆
          Set.image2 (fun u v : Fin n → Real => u + v)
            ({p} : Set (Fin n → Real))
            (Metric.closedBall (0 : Fin n → Real) ε)) :
    p ∈ gradientLimitVectorsAt f x := by
  classical
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  let U : Set (Fin n → Real) := interior domf
  let D : Set (Fin n → Real) := {z | z ∈ U ∧ ERealDifferentiableAt f z}
  let εSeq : ℕ → Real := fun i => 1 / ((i : Real) + 1)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hDense :
      U ⊆ closure D := by
    -- Theorem 25.5 gives dense differentiability on the interior of the effective domain.
    simpa [U, D, domf] using
      (properConvexFunction_differentiabilitySet_dense_null_complement_and_gradient_continuous
        (f := f) hproper).1
  have hεpos : ∀ i : ℕ, 0 < εSeq i := by
    intro i
    dsimp [εSeq]
    positivity
  choose N hN using fun i : ℕ => hqSmall (εSeq i) (hεpos i)
  let k : ℕ → ℕ := fun i => max i (N i)
  have hk_ge : ∀ i : ℕ, i ≤ k i := by
    intro i
    exact le_max_left _ _
  have hk_tendsto : Filter.Tendsto k Filter.atTop Filter.atTop :=
    by
      refine (Filter.tendsto_atTop).2 ?_
      intro b
      exact (Filter.eventually_atTop).2 ⟨b, fun a ha => le_trans ha (hk_ge a)⟩
  have hqkInt : ∀ i : ℕ, q (k i) ∈ U := by
    intro i
    simpa [U, domf] using hqInt (k i)
  have hqkTendsto :
      Filter.Tendsto (fun i : ℕ => q (k i)) Filter.atTop (nhds x) :=
    hqTendsto.comp hk_tendsto
  have hqkSmall :
      ∀ i : ℕ,
        ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f (q (k i))) ⊆
          Set.image2 (fun u v : Fin n → Real => u + v)
            ({p} : Set (Fin n → Real))
            (Metric.closedBall (0 : Fin n → Real) (εSeq i)) := by
    intro i
    exact hN i (k i) (le_max_right _ _)
  choose δ hδpos hδsub using
    fun i : ℕ =>
      (properConvex_upperSemicontinuousOn_upperDirectionalDerivative_and_subdifferential_subset
        (f := f) hproper).2 (by simpa [U, domf] using hqkInt i) (εSeq i) (hεpos i)
  have hzExists :
      ∀ i : ℕ,
        ∃ z : Fin n → Real,
          z ∈ D ∧ dist z (q (k i)) < min (δ i) (εSeq i) := by
    intro i
    have hqClosure : q (k i) ∈ closure D := hDense (hqkInt i)
    rw [Metric.mem_closure_iff] at hqClosure
    rcases hqClosure (min (δ i) (εSeq i)) (lt_min (hδpos i) (hεpos i)) with ⟨z, hzD, hzdist⟩
    refine ⟨z, hzD, ?_⟩
    simpa [dist_comm] using hzdist
  choose zSeq hzSeq_mem hzSeq_dist using hzExists
  have hzSeq_data :
      ∀ i : ℕ, zSeq i ∈ U ∧ ERealDifferentiableAt f (zSeq i) := by
    intro i
    simpa [D] using hzSeq_mem i
  let hdiff : ∀ i : ℕ, ERealDifferentiableAt f (zSeq i) := fun i => (hzSeq_data i).2
  have hzGradMem :
      ∀ i : ℕ,
        erealGradientAt (hdiff i) ∈
          ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f (zSeq i)) := by
    intro i
    -- Differentiability identifies the Euclidean gradient with the unique subgradient.
    simpa using
      (((convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hfConv (zSeq i) (ERealDifferentiableAt.finiteAt (hdiff i))).1 (hdiff i)).1 : _)
  have hzBall :
      ∀ i : ℕ, zSeq i ∈ Metric.closedBall (q (k i)) (δ i) := by
    intro i
    change dist (zSeq i) (q (k i)) ≤ δ i
    exact le_of_lt (lt_of_lt_of_le (hzSeq_dist i) (min_le_left _ _))
  have hzNearSub :
      ∀ i : ℕ,
        erealGradientAt (hdiff i) ∈
          Set.image2 (fun u v : Fin n → Real => u + v)
            ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f (q (k i)))
            (Metric.closedBall (0 : Fin n → Real) (εSeq i)) := by
    intro i
    exact hδsub i (hzBall i) (hzGradMem i)
  have hGradDistLe :
      ∀ i : ℕ, dist (erealGradientAt (hdiff i)) p ≤ 2 * εSeq i := by
    intro i
    rcases hzNearSub i with ⟨u, hu, v, hv, huv⟩
    rcases hqkSmall i hu with ⟨u0, hu0, w, hw, huw⟩
    have hu0Eq : u0 = p := Set.mem_singleton_iff.1 hu0
    have hwNorm : ‖w‖ ≤ εSeq i := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hvNorm : ‖v‖ ≤ εSeq i := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hv
    have hEq :
        erealGradientAt (hdiff i) - p = w + v := by
      rw [huv.symm, huw.symm, hu0Eq]
      change ((p + w) + v) - p = w + v
      abel_nf
    calc
      dist (erealGradientAt (hdiff i)) p = ‖w + v‖ := by
        rw [dist_eq_norm, hEq]
      _ ≤ ‖w‖ + ‖v‖ := norm_add_le _ _
      _ ≤ εSeq i + εSeq i := add_le_add hwNorm hvNorm
      _ = 2 * εSeq i := by ring
  have hInvTendsto :
      Filter.Tendsto (fun i : ℕ => (((i : Real) + 1)⁻¹)) Filter.atTop (nhds 0) := by
    simpa [Function.comp, one_mul] using
      (tendsto_mul_add_inv_atTop_nhds_zero (1 : Real) 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hεTendsto :
      Filter.Tendsto εSeq Filter.atTop (nhds 0) := by
    simpa [εSeq, one_div, one_mul, Function.comp] using hInvTendsto
  have hzDistTendsto :
      Filter.Tendsto (fun i : ℕ => dist (zSeq i) x) Filter.atTop (nhds 0) := by
    have hqDistTendsto :
        Filter.Tendsto (fun i : ℕ => dist (q (k i)) x) Filter.atTop (nhds 0) := by
      simpa using
        hqkTendsto.dist (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x))
    have hUpper :
        Filter.Tendsto (fun i : ℕ => εSeq i + dist (q (k i)) x) Filter.atTop (nhds 0) :=
      by simpa using hεTendsto.add hqDistTendsto
    refine squeeze_zero (fun i => dist_nonneg) ?_ hUpper
    intro i
    calc
      dist (zSeq i) x ≤ dist (zSeq i) (q (k i)) + dist (q (k i)) x := dist_triangle _ _ _
      _ ≤ εSeq i + dist (q (k i)) x := by
        exact add_le_add
          (le_of_lt (lt_of_lt_of_le (hzSeq_dist i) (min_le_right _ _))) le_rfl
  have hzSeqTendsto :
      Filter.Tendsto zSeq Filter.atTop (nhds x) :=
    tendsto_iff_dist_tendsto_zero.2 hzDistTendsto
  have hTwoεTendsto :
      Filter.Tendsto (fun i : ℕ => 2 * εSeq i) Filter.atTop (nhds 0) :=
    by simpa using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (2 : Real)) Filter.atTop (nhds 2)).mul
        hεTendsto
  have hGradTendsto :
      Filter.Tendsto (fun i : ℕ => erealGradientAt (hdiff i)) Filter.atTop (nhds p) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun i => dist_nonneg) hGradDistLe hTwoεTendsto
  -- The dense differentiability selections now realize `p` as an actual gradient limit at `x`.
  exact ⟨zSeq, hdiff, hzSeqTendsto, hGradTendsto⟩

/-- Helper for Theorem 25.6: a singleton normal face along a nonzero direction yields an interior
ray approaching `x` whose Euclideanized subdifferentials are eventually trapped in arbitrarily
small balls around the exposed point `p`. -/
lemma helperForTheorem_25_6_normalizedRay_eventual_preimageSubdifferential_subset_singletonBall
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x y p : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hy : y ≠ 0)
    (hFace : subdifferentialNormalFaceAt f x y = ({p} : Set (Fin n → Real))) :
    ∃ s : Real, 0 < s ∧
      (∀ i : ℕ,
        x + (s / ((i : Real) + 1)) • (‖y‖⁻¹ • y) ∈
          interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) ∧
      (∀ ε : Real, 0 < ε → ∃ i0 : ℕ, ∀ i ≥ i0,
        ((dotProductEquiv Real (Fin n)) ⁻¹'
            subdifferentialAt f (x + (s / ((i : Real) + 1)) • (‖y‖⁻¹ • y))) ⊆
          Set.image2 (fun u v : Fin n → Real => u + v)
            ({p} : Set (Fin n → Real))
            (Metric.closedBall (0 : Fin n → Real) ε)) := by
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  let yHat : Fin n → Real := ‖y‖⁻¹ • y
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hclosed : ClosedConvexFunction f := ⟨hfConv, hf_closed⟩
  have hyNormPos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hyHatNe : yHat ≠ 0 := by
    dsimp [yHat]
    exact smul_ne_zero (inv_ne_zero hyNormPos.ne') hy
  have hyHatNorm : ‖yHat‖ = 1 := by
    dsimp [yHat]
    calc
      ‖‖y‖⁻¹ • y‖ = |‖y‖⁻¹| * ‖y‖ := by simp [norm_smul]
      _ = ‖y‖⁻¹ * ‖y‖ := by rw [abs_of_pos (inv_pos.mpr hyNormPos)]
      _ = 1 := by exact inv_mul_cancel₀ hyNormPos.ne'
  have hFaceHat :
      subdifferentialNormalFaceAt f x yHat = ({p} : Set (Fin n → Real)) := by
    dsimp [yHat]
    rw [helperForTheorem_25_6_subdifferentialNormalFace_eq_of_pos_smul_direction
      (f := f) (x := x) (y := y) (a := ‖y‖⁻¹) (inv_pos.mpr hyNormPos)]
    exact hFace
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) (interior_subset hx),
        hproper.2.2 x (by simp)⟩
  have hCconv :
      Convex Real ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) := by
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
  have hCne :
      (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) : Set (Fin n → Real)).Nonempty :=
    (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
      (f := f) hf hx).1
  have hSupport :
      ClosedConvexFunction
          (supportFunctionEReal ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) ∧
        ProperConvexFunctionOn
          (Set.univ : Set (Fin n → Real))
          (supportFunctionEReal ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) ∧
        PositivelyHomogeneous
          (supportFunctionEReal ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) :=
    section13_supportFunctionEReal_closedProperConvex_posHom
      (n := n) (C := ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) hCne hCconv
  have hfiniteDir : upperDirectionalDerivativeAt f x yHat ≠ (⊥ : EReal) := by
    rcases hCne with ⟨v, hv⟩
    have hminor :
        (((dotProduct yHat v : Real) : EReal)) ≤ upperDirectionalDerivativeAt f x yHat := by
      exact
        (helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
          f hfConv x hxFinite v).1 hv yHat
    exact ne_of_gt <| lt_of_lt_of_le (show (⊥ : EReal) < (((dotProduct yHat v : Real) : EReal)) by simp)
      hminor
  rcases helperForTheorem_25_1_exists_closedBall_subset_of_isOpen
      (n := n) (C := interior domf) isOpen_interior hx with
    ⟨s, hs_pos, hs_ball⟩
  have hqInt :
      ∀ i : ℕ,
        x + (s / ((i : Real) + 1)) • yHat ∈ interior domf := by
    intro i
    have hcoef_nonneg : 0 ≤ s / ((i : Real) + 1) := by
      have hden_pos : 0 < (i : Real) + 1 := by positivity
      exact div_nonneg hs_pos.le hden_pos.le
    have hcoef_le : s / ((i : Real) + 1) ≤ s := by
      have hi_nonneg : 0 ≤ (i : Real) := by exact_mod_cast Nat.zero_le i
      have hden_ge : (1 : Real) ≤ (i : Real) + 1 := by
        nlinarith
      exact div_le_self (le_of_lt hs_pos) hden_ge
    have hmemBall :
        x + (s / ((i : Real) + 1)) • yHat ∈ Metric.closedBall x s := by
      change dist (x + (s / ((i : Real) + 1)) • yHat) x ≤ s
      have hsub :
          x + (s / ((i : Real) + 1)) • yHat - x = (s / ((i : Real) + 1)) • yHat := by
        abel_nf
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg hcoef_nonneg, hyHatNorm, mul_one]
      exact hcoef_le
    exact hs_ball hmemBall
  have hqDom :
      ∀ i : ℕ, x + (s / ((i : Real) + 1)) • yHat ∈ domf := by
    intro i
    exact interior_subset (hqInt i)
  have hInvTendsto :
      Filter.Tendsto (fun i : ℕ => (((i : Real) + 1)⁻¹)) Filter.atTop (nhds 0) := by
    simpa [Function.comp, one_mul] using
      (tendsto_mul_add_inv_atTop_nhds_zero (1 : Real) 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hScaleTendsto :
      Filter.Tendsto (fun i : ℕ => s / ((i : Real) + 1)) Filter.atTop (nhds 0) := by
    have hMul : Filter.Tendsto (fun i : ℕ => s * (((i : Real) + 1)⁻¹)) Filter.atTop (nhds 0) :=
      by simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => s) Filter.atTop (nhds s)).mul
          hInvTendsto
    simpa [div_eq_mul_inv] using hMul
  have hqTendsto :
      Filter.Tendsto (fun i : ℕ => x + (s / ((i : Real) + 1)) • yHat)
        Filter.atTop (nhds x) := by
    have hContSmul : Continuous fun t : Real => t • yHat := by
      fun_prop
    have hSmul :
        Filter.Tendsto (fun i : ℕ => (s / ((i : Real) + 1)) • yHat)
          Filter.atTop (nhds (0 : Fin n → Real)) := by
      simpa using hContSmul.continuousAt.tendsto.comp hScaleTendsto
    simpa using tendsto_const_nhds.add hSmul
  have hqNe :
      ∀ i : ℕ, x + (s / ((i : Real) + 1)) • yHat ≠ x := by
    intro i hEq
    have hcoef_pos : 0 < s / ((i : Real) + 1) := by positivity
    have hsub :
        (s / ((i : Real) + 1)) • yHat = 0 := by
      have hsubEq := congrArg (fun z : Fin n → Real => z - x) hEq
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsubEq
    exact hyHatNe ((smul_eq_zero.mp hsub).resolve_left hcoef_pos.ne')
  have hdir :
      Filter.Tendsto
        (fun i : ℕ =>
          ‖(x + (s / ((i : Real) + 1)) • yHat) - x‖⁻¹ •
            ((x + (s / ((i : Real) + 1)) • yHat) - x))
        Filter.atTop (nhds yHat) := by
    have hdirEq :
        ∀ i : ℕ,
          ‖(x + (s / ((i : Real) + 1)) • yHat) - x‖⁻¹ •
              ((x + (s / ((i : Real) + 1)) • yHat) - x) = yHat := by
      intro i
      have hcoef_pos : 0 < s / ((i : Real) + 1) := by positivity
      have hsub :
          (x + (s / ((i : Real) + 1)) • yHat) - x = (s / ((i : Real) + 1)) • yHat := by
        abel_nf
      have hnorm :
          ‖(x + (s / ((i : Real) + 1)) • yHat) - x‖ = s / ((i : Real) + 1) := by
        rw [hsub, norm_smul, Real.norm_of_nonneg (le_of_lt hcoef_pos), hyHatNorm, mul_one]
      calc
        ‖(x + (s / ((i : Real) + 1)) • yHat) - x‖⁻¹ •
            ((x + (s / ((i : Real) + 1)) • yHat) - x) =
            ‖(x + (s / ((i : Real) + 1)) • yHat) - x‖⁻¹ •
              ((s / ((i : Real) + 1)) • yHat) := by rw [hsub]
        _ =
            (‖(x + (s / ((i : Real) + 1)) • yHat) - x‖⁻¹ * (s / ((i : Real) + 1))) • yHat := by
              rw [smul_smul]
        _ = yHat := by
              rw [hnorm, inv_mul_cancel₀ hcoef_pos.ne', one_smul]
    have hConst :
        (fun i : ℕ =>
          ‖(x + (s / ((i : Real) + 1)) • yHat) - x‖⁻¹ •
            ((x + (s / ((i : Real) + 1)) • yHat) - x)) = fun _ : ℕ => yHat := by
      funext i
      exact hdirEq i
    rw [hConst]
    exact tendsto_const_nhds
  rcases
      closedProperConvex_limsup_upperDirectionalDerivative_le_iterated_and_eventual_subdifferential_subset_normalFace
        (f := f) hclosed hproper (x := x) (y := yHat) (by simpa [domf] using interior_subset hx)
        (fun i : ℕ => x + (s / ((i : Real) + 1)) • yHat) hqDom hqTendsto hqNe hdir hfiniteDir
        ⟨0, le_rfl, by simpa [domf] using hx⟩ with
    ⟨_hlimsup, hEventual⟩
  refine ⟨s, hs_pos, ?_, ?_⟩
  · intro i
    simpa [domf, yHat] using hqInt i
  · intro ε hε
    rcases hEventual ε hε with ⟨i0, hi0⟩
    refine ⟨i0, ?_⟩
    intro i hi
    simpa [yHat, hFaceHat] using hi0 i hi

/-- Helper for Theorem 25.6: a singleton normal face at an interior-domain point already gives a
genuine gradient-limit vector. -/
lemma helperForTheorem_25_6_gradientLimitVector_of_singletonNormalFace
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x y p : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hFace : subdifferentialNormalFaceAt f x y = ({p} : Set (Fin n → Real))) :
    p ∈ gradientLimitVectorsAt f x := by
  by_cases hy : y = 0
  · have hFaceZero :
        ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) =
          ({p} : Set (Fin n → Real)) := by
      simpa [hy, subdifferentialNormalFaceAt] using hFace
    -- When `y = 0`, the whole Euclideanized subdifferential fiber is already the singleton `{p}`.
    exact
      helperForTheorem_25_6_gradientLimitVector_of_eventuallySmallSubdifferentials
        (f := f) hf (x := x) (p := p) (q := fun _ : ℕ => x)
        (hqInt := fun _ => hx)
        (hqTendsto := tendsto_const_nhds)
        (hqSmall := by
          intro ε hε
          refine ⟨0, ?_⟩
          intro i _hi
          intro u hu
          have huEq : u = p := by
            exact Set.mem_singleton_iff.1 (by simpa [hFaceZero] using hu)
          refine ⟨p, by simp, 0, ?_, ?_⟩
          · simpa [Metric.mem_closedBall, dist_eq_norm] using (show ‖(0 : Fin n → Real)‖ ≤ ε by
              simp [le_of_lt hε])
          · simpa [huEq])
  · rcases
      helperForTheorem_25_6_normalizedRay_eventual_preimageSubdifferential_subset_singletonBall
        (f := f) hf hf_closed hx hy hFace with
      ⟨s, hs_pos, hqInt, hqSmall⟩
    -- Along the normalized interior ray, dense differentiability turns the shrinking
    -- singleton-ball control into an actual gradient-limit sequence.
    exact
      helperForTheorem_25_6_gradientLimitVector_of_eventuallySmallSubdifferentials
        (f := f) hf (x := x) (p := p)
        (q := fun i : ℕ => x + (s / ((i : Real) + 1)) • (‖y‖⁻¹ • y))
        (hqInt := hqInt)
        (hqTendsto := by
          have hInvTendsto :
              Filter.Tendsto (fun i : ℕ => (((i : Real) + 1)⁻¹)) Filter.atTop (nhds 0) := by
            simpa [Function.comp, one_mul] using
              (tendsto_mul_add_inv_atTop_nhds_zero (1 : Real) 1 one_ne_zero).comp
                tendsto_natCast_atTop_atTop
          have hScaleTendsto :
              Filter.Tendsto (fun i : ℕ => s / ((i : Real) + 1)) Filter.atTop (nhds 0) := by
            have hMul :
                Filter.Tendsto (fun i : ℕ => s * (((i : Real) + 1)⁻¹)) Filter.atTop (nhds 0) :=
              by simpa using
                (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => s) Filter.atTop (nhds s)).mul
                  hInvTendsto
            simpa [div_eq_mul_inv] using hMul
          have hContSmul : Continuous fun t : Real => t • (‖y‖⁻¹ • y) := by
            fun_prop
          have hSmul :
              Filter.Tendsto (fun i : ℕ => (s / ((i : Real) + 1)) • (‖y‖⁻¹ • y))
                Filter.atTop (nhds (0 : Fin n → Real)) := by
            simpa using hContSmul.continuousAt.tendsto.comp hScaleTendsto
          simpa using tendsto_const_nhds.add hSmul)
        (hqSmall := hqSmall)


end Section25
end Chap05
