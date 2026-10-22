/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part8

section Chap05
section Section23

open scoped ConvexAnalysis Pointwise

/-- Helper for Theorem 23.9: in the polyhedral branch, the Section 16 closure identity collapses
to an exact coordinate-space `imageUnderLinearMap` formula for `(h ∘ A)*`. -/
lemma helperForTheorem_23_9_fenchelConjugate_precomp_eq_imageUnderCoordinateAdjoint_of_polyhedral
    {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (h : (Fin m → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ h)
    (hpoly : IsPolyhedralConvexFunction m h)
    (hone : RangeMeetsEffectiveDomainInOnePoint A h) :
    fenchelConjugate n (fun y => h (A y)) =
      imageUnderLinearMap
        (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h) := by
  rcases hone with ⟨z, hz⟩
  have hzMem : z ∈ Set.range A ∧ z ∈ effectiveDomain Set.univ h := by
    have hzInter : z ∈ Set.range A ∩ effectiveDomain Set.univ h := by
      simpa [hz]
    exact hzInter
  have hconv : ConvexFunction h := by
    simpa [ConvexFunction] using hproper.1
  have hsec16 :=
    section16_fenchelConjugate_precomp_convexFunctionClosure_eq_convexFunctionClosure_adjoint_image
      (A := helperForTheorem_23_9_euclideanLinearLift A) (g := h) hconv
  have hhClosure :=
    helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_polyhedral_proper
      (g := h) hpoly hproper
  have hstarPoly : IsPolyhedralConvexFunction m (fenchelConjugate m h) :=
    polyhedralConvexFunction_fenchelConjugate m h hpoly
  have hImagePoly :
      IsPolyhedralConvexFunction n
        (imageUnderLinearMap
          (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h)) :=
    ((polyhedralConvexFunction_image_preimage_linear m n
        (helperForTheorem_23_9_coordinateAdjointMap A)).1
      (fenchelConjugate m h) hstarPoly).1
  have hImageProper :
      ProperConvexFunctionOn Set.univ
        (imageUnderLinearMap
          (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h)) :=
    helperForTheorem_23_9_coordinateAdjointImage_proper_of_polyhedral
      A h hproper hpoly ⟨z, hzMem.1, hzMem.2⟩
  have hImageClosure :=
    helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_polyhedral_proper
      (g := imageUnderLinearMap
        (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h))
      hImagePoly hImageProper
  -- Remove the closures on both sides using polyhedral properness, then rewrite the raw Section 16
  -- adjoint image as the coordinate-space image function.
  calc
    fenchelConjugate n (fun y => h (A y)) =
        fenchelConjugate n (fun y => convexFunctionClosure h (A y)) := by
          congr 1
          ext y
          rw [hhClosure]
    _ = convexFunctionClosure
          (fun xStar : Fin n → ℝ =>
            sInf
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  fenchelConjugate m h (yStar : Fin m → ℝ)) ''
                {yStar |
                  (LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)) yStar =
                    WithLp.toLp 2 xStar})) := hsec16
    _ = convexFunctionClosure
          (imageUnderLinearMap
            (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h)) := by
          rw [helperForTheorem_23_9_rawAdjointImage_eq_imageUnderCoordinateAdjoint A h]
    _ = imageUnderLinearMap
          (helperForTheorem_23_9_coordinateAdjointMap A) (fenchelConjugate m h) :=
        hImageClosure

/-- Helper for Theorem 23.9: the polyhedral branch should identify the closure-side adjoint image
with the exact adjoint image and supply an attained fiber witness. -/
lemma helperForTheorem_23_9_mem_image_subdifferential_of_polyhedralQualification {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (h : (Fin m → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ h)
    (hpoly : IsPolyhedralConvexFunction m h)
    (hone : RangeMeetsEffectiveDomainInOnePoint A h)
    (x : Fin n → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ))
    (hxStar : xStar ∈ subdifferentialAt (fun y => h (A y)) x) :
    xStar ∈ A.dualMap '' subdifferentialAt h (A x) := by
  rcases hone with ⟨z, hz⟩
  have hzMem : z ∈ Set.range A ∧ z ∈ effectiveDomain Set.univ h := by
    have hzInter : z ∈ Set.range A ∩ effectiveDomain Set.univ h := by
      simpa [hz]
    exact hzInter
  have hAproper :=
    helperForTheorem_23_9_precomp_proper_of_range_meets_effectiveDomain A h hproper
      ⟨z, hzMem.1, hzMem.2⟩
  let xStarE : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xStar
  let B := helperForTheorem_23_9_coordinateAdjointMap A
  have hxStarE : IsEuclideanSubgradientAt (fun y => h (A y)) x xStarE := by
    change dotProductEquiv ℝ (Fin n) xStarE ∈ subdifferentialAt (fun y => h (A y)) x
    simpa [xStarE] using hxStar
  have hfy_precomp : FenchelYoungEqualityAt (fun y => h (A y)) x xStarE := by
    exact
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        (fun y => h (A y)) hAproper x xStarE).1.out 0 3).1 hxStarE
  have hconj_ne_top : fenchelConjugate n (fun y => h (A y)) xStarE ≠ (⊤ : EReal) := by
    have hfinite :=
      helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality
        (f := fun y => h (A y)) hAproper x xStarE (le_of_eq hfy_precomp)
    intro htop
    rw [FenchelYoungEqualityAt] at hfy_precomp
    have hleft_top :
        (fun y => h (A y)) x + fenchelConjugate n (fun y => h (A y)) xStarE = (⊤ : EReal) := by
      simpa [htop] using (EReal.add_top_of_ne_bot hfinite.2)
    exact EReal.coe_ne_top (dotProduct x xStarE) (hfy_precomp.symm.trans hleft_top)
  have hEq :
      fenchelConjugate n (fun y => h (A y)) xStarE =
        imageUnderLinearMap B (fenchelConjugate m h) xStarE := by
    simpa [B] using
      congrArg (fun f => f xStarE)
        (helperForTheorem_23_9_fenchelConjugate_precomp_eq_imageUnderCoordinateAdjoint_of_polyhedral
          A h hproper hpoly ⟨z, hz⟩)
  have hstarPoly : IsPolyhedralConvexFunction m (fenchelConjugate m h) :=
    polyhedralConvexFunction_fenchelConjugate m h hpoly
  have hImageData :=
    (polyhedralConvexFunction_image_preimage_linear m n B).1 (fenchelConjugate m h) hstarPoly
  have hImageProper :
      ProperConvexFunctionOn Set.univ (imageUnderLinearMap B (fenchelConjugate m h)) :=
    helperForTheorem_23_9_coordinateAdjointImage_proper_of_polyhedral
      A h hproper hpoly ⟨z, hzMem.1, hzMem.2⟩
  have hImage_ne_top : imageUnderLinearMap B (fenchelConjugate m h) xStarE ≠ (⊤ : EReal) := by
    simpa [hEq] using hconj_ne_top
  have hImage_ne_bot : imageUnderLinearMap B (fenchelConjugate m h) xStarE ≠ (⊥ : EReal) :=
    hImageProper.2.2 xStarE (by simp)
  have hfiniteImage : ∃ r : ℝ, imageUnderLinearMap B (fenchelConjugate m h) xStarE = (r : EReal) := by
    refine ⟨(imageUnderLinearMap B (fenchelConjugate m h) xStarE).toReal, ?_⟩
    exact helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
      (hTop := hImage_ne_top) (hBot := hImage_ne_bot)
  rcases hImageData.2 xStarE hfiniteImage with ⟨yStarE, hyFiber, hyAtt⟩
  let yStar : Module.Dual ℝ (Fin m → ℝ) := dotProductEquiv ℝ (Fin m) yStarE
  have hAadj :
      (LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)) (WithLp.toLp 2 yStarE) =
        WithLp.toLp 2 xStarE := by
    -- Convert the coordinate-space fiber equality back into the Euclidean adjoint equality used by
    -- the existing dual-map transport lemma.
    ext i
    simpa [B, helperForTheorem_23_9_coordinateAdjointMap] using
      congrArg (fun f : Fin n → ℝ => f i) hyFiber
  have hdual : A.dualMap yStar = xStar := by
    simpa [xStarE, yStar] using
      helperForTheorem_23_9_dualMap_eq_of_adjoint_eq A xStarE yStarE hAadj
  have hconj :
      fenchelConjugate m h ((dotProductEquiv ℝ (Fin m)).symm yStar) =
        fenchelConjugate n (fun y => h (A y)) ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
    -- The attained fiber value now matches the exact conjugate value of `(h ∘ A)*`.
    calc
      fenchelConjugate m h ((dotProductEquiv ℝ (Fin m)).symm yStar) =
          imageUnderLinearMap B (fenchelConjugate m h) xStarE := by
            simpa [B, xStarE, yStar] using hyAtt.symm
      _ = fenchelConjugate n (fun y => h (A y)) xStarE := by
            simpa [hEq] using rfl
      _ = fenchelConjugate n (fun y => h (A y)) ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
            rfl
  have hySub : yStar ∈ subdifferentialAt h (A x) :=
    helperForTheorem_23_9_subgradient_of_h_of_attained_dualFiber
      A h hproper hAproper x xStar yStar hxStar hdual hconj
  exact ⟨yStar, hySub, hdual⟩

/-- Theorem 23.9: If `f(x) = h (A x)` with `h` a proper convex function on `ℝ^m`, then for every
`x` the subdifferential of `f` contains the image of `∂ h (A x)` under `A*`; if the range of `A`
meets `ri (dom h)`, or if `h` is polyhedral and the range of `A` meets `dom h` in exactly one
point, then this inclusion is an equality for every `x`. -/
theorem subdifferential_precomp_linearMap_contains_dualMapImage_and_eq_under_qualification {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (h : (Fin m → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ h) :
    (∀ x : Fin n → ℝ,
      A.dualMap '' subdifferentialAt h (A x) ⊆ subdifferentialAt (fun y => h (A y)) x) ∧
    ((RangeMeetsRelativeInteriorEffectiveDomain A h) ∨
        (IsPolyhedralConvexFunction m h ∧ RangeMeetsEffectiveDomainInOnePoint A h) →
      ∀ x : Fin n → ℝ, subdifferentialAt (fun y => h (A y)) x = A.dualMap '' subdifferentialAt h (A x)) := by
  constructor
  · intro x
    -- The easy direction is the defining subgradient inequality pushed through `A`.
    intro xStar hxStar
    rcases hxStar with ⟨yStar, hyStar, rfl⟩
    exact helperForTheorem_23_9_dualMapImage_mem_subdifferential_precomp A h x yStar hyStar
  · intro hqual x
    ext xStar
    constructor
    · intro hxStar
      rcases hqual with hri | ⟨hpoly, hone⟩
      · -- The relative-interior qualification lets Section 16 produce an attained dual fiber.
        exact
          helperForTheorem_23_9_mem_image_subdifferential_of_relativeInteriorQualification
            A h hproper hri x xStar hxStar
      · -- Route correction: the relative-interior branch is complete; the remaining blocker is
        -- the polyhedral exact-conjugate/attainment bridge promised by Corollary 19.3.1.
        exact
          helperForTheorem_23_9_mem_image_subdifferential_of_polyhedralQualification
            A h hproper hpoly hone x xStar hxStar
    · intro hxStar
      rcases hxStar with ⟨yStar, hyStar, rfl⟩
      exact helperForTheorem_23_9_dualMapImage_mem_subdifferential_precomp A h x yStar hyStar

/-- Helper for Theorem 23.10: a polyhedral convex function that is finite at one point cannot
take the value `⊥` anywhere. -/
lemma helperForTheorem_23_10_pointwise_ne_bot_of_polyhedral_finitePoint {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hpoly : IsPolyhedralConvexFunction n f)
    {x : Fin n → ℝ} (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ∀ z : Fin n → ℝ, f z ≠ (⊥ : EReal) := by
  intro z hzbot
  let E : Set ((Fin n → ℝ) × ℝ) := epigraph (Set.univ : Set (Fin n → ℝ)) f
  let M : Set (Fin (n + 1) → ℝ) := ((fun p => prodLinearEquiv_append_coord (n := n) p) '' E)
  let μx : ℝ := (f x).toReal
  let μ : ℝ := μx - 1
  let lam : ℕ → ℝ := fun t => ((t : ℝ) + 1)⁻¹
  let v : ℕ → ℝ := fun t => (μ - (1 - lam t) * μx) / lam t
  have hconvE : Convex ℝ E := by
    -- Use convexity of the epigraph so that finite heights above `x` can be combined with
    -- arbitrary heights above a hypothetical bottom point `z`.
    simpa [E] using convex_epigraph_of_convexFunctionOn (f := f) (hf := hpoly.1)
  have hMpoly : IsPolyhedralConvexSet (n + 1) M := by
    simpa [M, E, prodLinearEquiv_append_coord] using hpoly.2
  have hMclosed : IsClosed M := by
    exact
      (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
        (n := n + 1) (C := M) hMpoly).1
  have hxepi : (x, μx) ∈ E := by
    -- Record one finite epigraph point above `x`.
    refine (mem_epigraph_univ_iff (f := f)).2 ?_
    rw [helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
      (hTop := hx.1) (hBot := hx.2)]
  have hlam_tendsto :
      Filter.Tendsto lam Filter.atTop (nhds (0 : ℝ)) := by
    -- The convex-combination weight tends to `0`, so the first coordinate returns to `x`.
    have hshift :
        Filter.Tendsto (fun t : ℕ => (t : ℝ) + 1) Filter.atTop Filter.atTop := by
      simpa [add_comm] using
        (Filter.Tendsto.add_atTop
          (show Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) by
            simpa using
              (tendsto_const_nhds :
                Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)))
          (tendsto_natCast_atTop_atTop :
            Filter.Tendsto (fun t : ℕ => (t : ℝ)) Filter.atTop Filter.atTop))
    simpa [lam] using tendsto_inv_atTop_zero.comp hshift
  have hpair_tendsto :
      Filter.Tendsto
        (fun t : ℕ => (((1 - lam t) • x + lam t • z), μ))
        Filter.atTop (nhds (x, μ)) := by
    have hone_minus :
        Filter.Tendsto (fun t : ℕ => 1 - lam t) Filter.atTop (nhds (1 : ℝ)) := by
      simpa using
        ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)).sub
          hlam_tendsto)
    have hxcoord :
        Filter.Tendsto (fun t : ℕ => (1 - lam t) • x + lam t • z)
          Filter.atTop (nhds x) := by
      have hsum :=
        (hone_minus.smul_const x).add (hlam_tendsto.smul_const z)
      simpa using hsum
    have hpair' :
        Filter.Tendsto
          (fun t : ℕ => ((((1 - lam t) • x + lam t • z)), μ))
          Filter.atTop ((nhds x) ×ˢ (nhds μ)) :=
      hxcoord.prodMk (by
        simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => μ) Filter.atTop (nhds μ)))
    simpa [nhds_prod_eq] using hpair'
  have htrans_tendsto :
      Filter.Tendsto
        (fun t : ℕ => (prodLinearEquiv_append_coord (n := n))
          ((((1 - lam t) • x + lam t • z)), μ))
        Filter.atTop
        (nhds ((prodLinearEquiv_append_coord (n := n)) (x, μ))) := by
    let eCL : ((Fin n → ℝ) × ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
      (prodLinearEquiv_append_coord (n := n)).toContinuousLinearEquiv
    exact eCL.continuous.continuousAt.tendsto.comp hpair_tendsto
  have hmem_eventually :
      ∀ᶠ t : ℕ in Filter.atTop,
        (prodLinearEquiv_append_coord (n := n))
          ((((1 - lam t) • x + lam t • z)), μ) ∈ M := by
    refine Filter.Eventually.of_forall ?_
    intro t
    have hlam_pos : 0 < lam t := by
      dsimp [lam]
      exact inv_pos.mpr (by positivity)
    have hlam_le : lam t ≤ 1 := by
      have hmul : lam t * ((t : ℝ) + 1) = 1 := by
        dsimp [lam]
        field_simp [ne_of_gt (show (0 : ℝ) < (t : ℝ) + 1 by positivity)]
      have hden_nonneg : 0 ≤ (t : ℝ) + 1 := by positivity
      nlinarith
    have hzepi : (z, v t) ∈ E := by
      -- A bottom value places every real height above `z` in the epigraph.
      refine (mem_epigraph_univ_iff (f := f)).2 ?_
      simpa [hzbot]
    have hcombo : (1 - lam t) • (x, μx) + lam t • (z, v t) ∈ E := by
      exact convex_combo_mem_epigraph_aux hconvE hxepi hzepi (le_of_lt hlam_pos) hlam_le
    have hsecond :
        (1 - lam t) * μx + lam t * v t = μ := by
      -- Choose the auxiliary height at `z` so that the convex-combination height stays fixed.
      dsimp [v]
      field_simp [ne_of_gt hlam_pos]
      ring
    have hcombo_eq :
        (1 - lam t) • (x, μx) + lam t • (z, v t) =
          ((((1 - lam t) • x + lam t • z)), μ) := by
      ext <;> simp [hsecond]
    refine ⟨(((1 - lam t) • x + lam t • z), μ), ?_, rfl⟩
    rw [hcombo_eq] at hcombo
    exact hcombo
  have hlimit_mem :
      (prodLinearEquiv_append_coord (n := n)) (x, μ) ∈ M :=
    IsClosed.mem_of_tendsto hMclosed htrans_tendsto hmem_eventually
  rcases hlimit_mem with ⟨q, hqEpi, hqMap⟩
  have hqEq : q = (x, μ) := by
    exact (prodLinearEquiv_append_coord (n := n)).injective hqMap
  have hxμ_epi : (x, μ) ∈ E := by
    simpa [hqEq, E] using hqEpi
  have hμ_ge : f x ≤ (μ : EReal) := by
    simpa [E] using (mem_epigraph_univ_iff (f := f)).1 hxμ_epi
  have hμ_lt : (μ : EReal) < f x := by
    have hreal : μ < μx := by
      dsimp [μ]
      linarith
    have hcoe : (μ : EReal) < ((μx : ℝ) : EReal) := by
      exact_mod_cast hreal
    calc
      (μ : EReal) < ((μx : ℝ) : EReal) := by simpa [μx] using hcoe
      _ = f x := by
        symm
        exact helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := hx.1) (hBot := hx.2)
  exact (not_lt_of_ge hμ_ge) hμ_lt

/-- Helper for Theorem 23.10: a finite point of a max-affine-plus-indicator representation lies
in the represented indicator domain. -/
lemma helperForTheorem_23_10_finitePoint_mem_domain_of_representation {n k m : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, y j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              y)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    x ∈ {y : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i} := by
  -- Evaluate the representation at `x` and rule out the `indicator = ⊤` branch.
  have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hrepr
  by_contra hxC
  have hIndicatorTop :
      indicatorFunction
        (C := {y : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
          (∑ j, y j * b i j) ≤ β i}) x = (⊤ : EReal) := by
    simp [indicatorFunction, hxC]
  have hfxTop : f x = (⊤ : EReal) := by
    calc
      f x =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              x := hreprx
      _ = (⊤ : EReal) := by simp [hIndicatorTop]
  exact hx.1 hfxTop

/-- Helper for Theorem 23.10: evaluating a represented affine constraint along the ray
`x + t • d` separates into the base value and the directional slope. -/
lemma helperForTheorem_23_10_constraint_eval_add_smul {n m : ℕ}
    (b : Fin m → Fin n → ℝ) (x d : Fin n → ℝ) (i : Fin m) (t : ℝ) :
    (∑ j, (x + t • d) j * b i j) =
      (∑ j, x j * b i j) + t * (∑ j, d j * b i j) := by
  -- Expand the affine constraint on the ray and regroup the finite sum.
  calc
    (∑ j, (x + t • d) j * b i j)
        = ∑ j, ((x j + t * d j) * b i j) := by
            simp
    _ = ∑ j, (x j * b i j + t * (d j * b i j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (∑ j, x j * b i j) + ∑ j, t * (d j * b i j) := by
          simp [Finset.sum_add_distrib]
    _ = (∑ j, x j * b i j) + t * (∑ j, d j * b i j) := by
          rw [Finset.mul_sum]

/-- Helper for Theorem 23.10: if a ray `x + t • d` stays in the represented domain for all
sufficiently small positive `t`, then every constraint active at `x` has nonpositive directional
slope. -/
lemma helperForTheorem_23_10_activeDirectionCone_eventually_domain_only_if {n k m : ℕ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    {x d : Fin n → ℝ}
    (heventually :
      ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, 0 < t → t < ε →
          x + t • d ∈ {y : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
            (∑ j, y j * b i j) ≤ β i}) :
    d ∈ {d : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
      (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0} := by
  rcases heventually with ⟨ε, hεpos, hε⟩
  -- Test the represented domain condition at the specific step `t = ε / 2`.
  intro i hki hactive
  by_contra hdir
  have hdirPos : 0 < ∑ j, d j * b i j := lt_of_not_ge hdir
  have htPos : 0 < ε / 2 := by linarith
  have htLt : ε / 2 < ε := by linarith
  have hmem : x + (ε / 2) • d ∈ {y : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
      (∑ j, y j * b i j) ≤ β i} :=
    hε (ε / 2) htPos htLt
  have hconstraint :
      (∑ j, (x + (ε / 2) • d) j * b i j) ≤ β i := hmem i hki
  rw [helperForTheorem_23_10_constraint_eval_add_smul b x d i (ε / 2), hactive] at hconstraint
  have hstepPos : 0 < (ε / 2) * (∑ j, d j * b i j) := by positivity
  linarith

/-- Helper for Theorem 23.10: if a direction violates one active domain constraint at `x`, then
every sufficiently small positive step immediately leaves the represented domain. -/
lemma helperForTheorem_23_10_not_mem_activeDirectionCone_eventually_not_domain {n k m : ℕ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    {x d : Fin n → ℝ}
    (hdTx :
      d ∉ {d : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
        (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0}) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 0 < t → t < ε →
        x + t • d ∉ {y : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
          (∑ j, y j * b i j) ≤ β i} := by
  classical
  have hwitness :
      ∃ i : Fin m, k ≤ (i : ℕ) ∧
        (∑ j, x j * b i j) = β i ∧ 0 < (∑ j, d j * b i j) := by
    by_contra hwitness
    apply hdTx
    intro i hki hactive
    by_contra hdir
    exact hwitness ⟨i, hki, hactive, lt_of_not_ge hdir⟩
  rcases hwitness with ⟨i, hki, hactive, hdirPos⟩
  refine ⟨1, by norm_num, ?_⟩
  intro t htPos htLt hmem
  have hconstraint :
      (∑ j, (x + t • d) j * b i j) ≤ β i := hmem i hki
  rw [helperForTheorem_23_10_constraint_eval_add_smul b x d i t, hactive] at hconstraint
  have hstepPos : 0 < t * (∑ j, d j * b i j) := by positivity
  linarith

/-- Helper for Theorem 23.10: a represented domain constraint that is strict at `x` stays
feasible along every sufficiently small positive step from `x`. -/
lemma helperForTheorem_23_10_strictConstraint_stays_feasible_for_small_steps {n k m : ℕ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    {x d : Fin n → ℝ} {i : Fin m}
    (hki : k ≤ (i : ℕ)) (hstrict : (∑ j, x j * b i j) < β i) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 0 < t → t < ε →
        (∑ j, (x + t • d) j * b i j) ≤ β i := by
  let base : ℝ := ∑ j, x j * b i j
  let slope : ℝ := ∑ j, d j * b i j
  have hgapPos : 0 < β i - base := by
    dsimp [base]
    linarith
  -- Split on the directional slope of the strict constraint.
  by_cases hslope : slope ≤ 0
  · refine ⟨1, by norm_num, ?_⟩
    intro t htPos _htLt
    -- A nonpositive slope can only decrease the already strict left-hand side.
    rw [helperForTheorem_23_10_constraint_eval_add_smul b x d i t]
    nlinarith [le_of_lt htPos, hslope]
  · have hslopePos : 0 < slope := lt_of_not_ge hslope
    refine ⟨(β i - base) / slope, div_pos hgapPos hslopePos, ?_⟩
    intro t htPos htLt
    -- For a positive slope, choose the radius from the remaining slack divided by the slope.
    rw [helperForTheorem_23_10_constraint_eval_add_smul b x d i t]
    have hstepLt : t * slope < β i - base := by
      exact (lt_div_iff₀ hslopePos).1 htLt
    dsimp [base, slope] at hstepLt ⊢
    linarith

/-- Helper for Theorem 23.10: every direction in the active-constraint cone keeps the represented
domain feasible for all sufficiently small positive steps. -/
lemma helperForTheorem_23_10_activeDirectionCone_smallStep_radius {n k m : ℕ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    {x d : Fin n → ℝ}
    (hxC :
      x ∈ {y : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
        (∑ j, y j * b i j) ≤ β i})
    (hdTx :
      d ∈ {d : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
        (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0}) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 0 < t → t < ε →
        x + t • d ∈ {y : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
          (∑ j, y j * b i j) ≤ β i} := by
  classical
  let radius : Fin m → ℝ := fun i =>
    if hki : k ≤ (i : ℕ) then
      if hstrict : (∑ j, x j * b i j) < β i then
        Classical.choose
          (helperForTheorem_23_10_strictConstraint_stays_feasible_for_small_steps
            (k := k) (b := b) (β := β) (x := x) (d := d) (i := i) hki hstrict)
      else 1
    else 1
  let radii : Finset ℝ := insert 1 (Finset.univ.image radius)
  have hradius_pos : ∀ i : Fin m, 0 < radius i := by
    intro i
    by_cases hki : k ≤ (i : ℕ)
    · by_cases hstrict : (∑ j, x j * b i j) < β i
      · -- In the strict branch, import the positivity from the one-constraint radius lemma.
        have hchosen :=
          Classical.choose_spec
            (helperForTheorem_23_10_strictConstraint_stays_feasible_for_small_steps
              (k := k) (b := b) (β := β) (x := x) (d := d) (i := i) hki hstrict)
        simpa [radius, hki, hstrict] using hchosen.1
      · simp [radius, hki, hstrict]
    · simp [radius, hki]
  have hradii_nonempty : radii.Nonempty := by
    simp [radii]
  let ε : ℝ := radii.min' hradii_nonempty
  have hεpos : 0 < ε := by
    have hmem : ε ∈ radii := by
      simpa [ε, radii] using Finset.min'_mem radii hradii_nonempty
    rcases Finset.mem_insert.1 hmem with hεeq | hεimage
    · have hone : (0 : ℝ) < 1 := by norm_num
      have hεone : ε = 1 := hεeq
      linarith
    · rcases Finset.mem_image.1 hεimage with ⟨i, -, hEq⟩
      simpa [ε, hEq] using hradius_pos i
  have hεle_radius : ∀ i : Fin m, ε ≤ radius i := by
    intro i
    have hmem : radius i ∈ radii := by
      simp [radii]
    have hmin_le : radii.min' hradii_nonempty ≤ radius i :=
      Finset.min'_le (s := radii) (x := radius i) hmem
    have hproof :
        (⟨radius i, hmem⟩ : radii.Nonempty) = hradii_nonempty :=
      Subsingleton.elim _ _
    simpa [ε, hproof] using hmin_le
  refine ⟨ε, hεpos, ?_⟩
  intro t htPos htLt
  intro i hki
  have ht_radius : t < radius i := lt_of_lt_of_le htLt (hεle_radius i)
  by_cases hstrict : (∑ j, x j * b i j) < β i
  · -- Strict constraints are controlled by the dedicated one-constraint radius.
    have hchosen :=
      Classical.choose_spec
        (helperForTheorem_23_10_strictConstraint_stays_feasible_for_small_steps
          (k := k) (b := b) (β := β) (x := x) (d := d) (i := i) hki hstrict)
    have ht_chosen :
        t <
          Classical.choose
            (helperForTheorem_23_10_strictConstraint_stays_feasible_for_small_steps
              (k := k) (b := b) (β := β) (x := x) (d := d) (i := i) hki hstrict) := by
      simpa [radius, hki, hstrict] using ht_radius
    exact hchosen.2 t htPos ht_chosen
  · have hxCi : (∑ j, x j * b i j) ≤ β i := hxC i hki
    have hactive : (∑ j, x j * b i j) = β i := by
      linarith [hxCi, le_of_not_gt hstrict]
    have hslope : (∑ j, d j * b i j) ≤ 0 := hdTx i hki hactive
    -- Active constraints have nonpositive slope, so they remain feasible for every `t > 0`.
    rw [helperForTheorem_23_10_constraint_eval_add_smul b x d i t, hactive]
    nlinarith [le_of_lt htPos, hslope]

/-- Helper for Theorem 23.10: the active-constraint feasible-direction cone is polyhedral, and it
contains the zero direction. -/
lemma helperForTheorem_23_10_activeDirectionCone_polyhedral_of_representation {n k m : ℕ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ} {x : Fin n → ℝ} :
    IsPolyhedralConvexSet n
      {d : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
        (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0} ∧
      (0 : Fin n → ℝ) ∈
        {d : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
          (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0} := by
  let Tx : Set (Fin n → ℝ) :=
    {d : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
      (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0}
  let b' : Fin m → Fin n → ℝ :=
    fun i =>
      if k ≤ (i : ℕ) ∧ (∑ j, x j * b i j) = β i then b i else 0
  have hTx :
      Tx = ⋂ i : Fin m, closedHalfSpaceLE n (b' i) 0 := by
    ext d
    constructor
    · intro hd
      refine Set.mem_iInter.2 ?_
      intro i
      by_cases hactive : k ≤ (i : ℕ) ∧ (∑ j, x j * b i j) = β i
      · have hdir : (∑ j, d j * b i j) ≤ 0 := hd i hactive.1 hactive.2
        simpa [Tx, b', hactive, closedHalfSpaceLE, dotProduct] using hdir
      · simp [b', hactive, closedHalfSpaceLE]
    · intro hd
      intro i hki hactive
      have hmem : d ∈ closedHalfSpaceLE n (b' i) 0 := (Set.mem_iInter.1 hd) i
      have hactive' : k ≤ (i : ℕ) ∧ (∑ j, x j * b i j) = β i := ⟨hki, hactive⟩
      simpa [Tx, b', hactive', closedHalfSpaceLE, dotProduct] using hmem
  have hTxPoly : IsPolyhedralConvexSet n Tx := by
    refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces n Tx).2 ?_
    exact ⟨m, b', fun _ => 0, hTx⟩
  have hzero : (0 : Fin n → ℝ) ∈ Tx := by
    intro i hki hactive
    simp
  exact ⟨by simpa [Tx] using hTxPoly, by simpa [Tx] using hzero⟩

/-- Helper for Theorem 23.10: outside the active-constraint cone, the represented domain exits
immediately, so every positive directional-difference quotient is `⊤` and the upper directional
derivative is `⊤`. -/
lemma helperForTheorem_23_10_upperDirectionalDerivative_eq_top_of_not_mem_activeDirectionCone
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    (hf : ConvexFunction f) {x d : Fin n → ℝ}
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, y j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              y)
    (hdTx :
      d ∉ {d : Fin n → ℝ | ∀ i : Fin m, k ≤ (i : ℕ) →
        (∑ j, x j * b i j) = β i → (∑ j, d j * b i j) ≤ 0}) :
    upperDirectionalDerivativeAt f x d = (⊤ : EReal) := by
  let C : Set (Fin n → ℝ) :=
    {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
  rcases
      helperForTheorem_23_10_not_mem_activeDirectionCone_eventually_not_domain
        (k := k) (b := b) (β := β) (x := x) (d := d) hdTx with
    ⟨ε, hεpos, hεexit⟩
  rcases (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx).1 d with
    ⟨hmono, _htend, hsInfEq⟩
  let Q : Set EReal := (Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x d t
  have hquot_top_small :
      ∀ t : ℝ, 0 < t → t < ε → directionalDifferenceQuotientAt f x d t = (⊤ : EReal) := by
    intro t htPos htLt
    have hnotC : x + t • d ∉ C := hεexit t htPos htLt
    have hreprt := congrArg (fun g : (Fin n → ℝ) → EReal => g (x + t • d)) hrepr
    have hIndicatorTop : indicatorFunction (C := C) (x + t • d) = (⊤ : EReal) := by
      simp [C, indicatorFunction, hnotC]
    have hftop : f (x + t • d) = (⊤ : EReal) := by
      calc
        f (x + t • d) =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧
                  r = (∑ j, (x + t • d) j * b i j) - β i} : ℝ) : EReal) +
              indicatorFunction (C := C) (x + t • d) := hreprt
        _ = (⊤ : EReal) := by simp [hIndicatorTop]
    rw [directionalDifferenceQuotientAt, hftop]
    simp [hx.1]
    exact EReal.top_div_of_pos_ne_top (by exact_mod_cast htPos) (by simp)
  have hquot_top_all :
      ∀ t : ℝ, 0 < t → directionalDifferenceQuotientAt f x d t = (⊤ : EReal) := by
    intro t htPos
    by_cases htLt : t < ε
    · exact hquot_top_small t htPos htLt
    · have hhalfPos : 0 < ε / 2 := by linarith
      have hhalfLt : ε / 2 < ε := by linarith
      have hhalfTop : directionalDifferenceQuotientAt f x d (ε / 2) = (⊤ : EReal) :=
        hquot_top_small (ε / 2) hhalfPos hhalfLt
      have hmono_le :
          directionalDifferenceQuotientAt f x d (ε / 2) ≤ directionalDifferenceQuotientAt f x d t :=
        hmono (by simpa using hhalfPos) (by simpa using htPos) (by linarith)
      exact top_le_iff.1 (by simpa [hhalfTop] using hmono_le)
  have hQeq : Q = {(⊤ : EReal)} := by
    ext q
    constructor
    · rintro ⟨t, ht, rfl⟩
      simp [Q, hquot_top_all t (by simpa using ht)]
    · intro hq
      simp at hq
      refine ⟨1, by simp, ?_⟩
      simpa [hq] using hquot_top_all 1 (by norm_num : 0 < (1 : ℝ))
  calc
    upperDirectionalDerivativeAt f x d = sInf Q := hsInfEq
    _ = (⊤ : EReal) := by rw [hQeq]; simp

/-- Helper for Theorem 23.10: at a finite represented point, the affine supremum in the
max-affine-plus-indicator formula is exactly the finite real value of `f x`. -/
lemma helperForTheorem_23_10_representationSup_eq_toReal {n k m : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, y j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              y)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    (sSup {r : ℝ |
        ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) = (f x).toReal := by
  let Sx : Set ℝ :=
    {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i}
  let C : Set (Fin n → ℝ) :=
    {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
  have hxC : x ∈ C := by
    -- Finiteness at `x` forces the indicator branch of the representation to vanish.
    simpa [C] using
      helperForTheorem_23_10_finitePoint_mem_domain_of_representation
        (f := f) (x := x) (b := b) (β := β) hrepr hx
  have hreprx : f x = ((sSup Sx : ℝ) : EReal) := by
    -- Evaluate the representation at `x` and simplify the indicator to `0`.
    simpa [Sx, C, indicatorFunction, hxC] using
      congrArg (fun g : (Fin n → ℝ) → EReal => g x) hrepr
  have hsSup_coe : ((sSup Sx : ℝ) : EReal) = (((f x).toReal : ℝ) : EReal) := by
    calc
      ((sSup Sx : ℝ) : EReal) = f x := hreprx.symm
      _ = (((f x).toReal : ℝ) : EReal) := by
        exact helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := hx.1) (hBot := hx.2)
  exact (EReal.coe_eq_coe_iff).1 hsSup_coe

/-- Helper for Theorem 23.10: every represented affine piece at a finite point lies below the
finite value `f x`. -/
lemma helperForTheorem_23_10_affinePiece_le_finiteValue_of_representation {n k m : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ} {i : Fin m}
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ j : Fin m, (j : ℕ) < k ∧ r = (∑ ℓ, y ℓ * b j ℓ) - β j} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ j : Fin m, k ≤ (j : ℕ) →
                (∑ ℓ, y ℓ * b j ℓ) ≤ β j})
              y)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hi : (i : ℕ) < k) :
    (∑ j, x j * b i j) - β i ≤ (f x).toReal := by
  let Sx : Set ℝ :=
    {r : ℝ | ∃ j : Fin m, (j : ℕ) < k ∧ r = (∑ ℓ, x ℓ * b j ℓ) - β j}
  let Iaff : Finset (Fin m) := Finset.univ.filter fun j : Fin m => (j : ℕ) < k
  let value : Fin m → ℝ := fun j => (∑ ℓ, x ℓ * b j ℓ) - β j
  have hsup_eq :
      (sSup Sx : ℝ) = (f x).toReal :=
    helperForTheorem_23_10_representationSup_eq_toReal
      (f := f) (x := x) (b := b) (β := β) hrepr hx
  have hfinite : Sx.Finite := by
    have hEq : Sx = value '' (↑Iaff : Set (Fin m)) := by
      ext r
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, by simp [Iaff, hj], rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, by simpa [Iaff] using hj, rfl⟩
    rw [hEq]
    exact Set.Finite.image value Iaff.finite_toSet
  have hbounded : BddAbove Sx := hfinite.bddAbove
  have hmem :
      (∑ j, x j * b i j) - β i ∈ Sx := by
    exact ⟨i, hi, rfl⟩
  -- Compare this affine piece directly with the supremum appearing in the representation.
  calc
    (∑ j, x j * b i j) - β i ≤ sSup Sx := by
      exact le_csSup hbounded hmem
    _ = (f x).toReal := hsup_eq

/-- Helper for Theorem 23.10: when `k > 0`, some affine piece is active at the finite point `x`.
-/
lemma helperForTheorem_23_10_exists_activeAffine_piece {n k m : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    (hkpos : 0 < k) (hkm : k ≤ m)
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, y j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              y)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ∃ i : Fin m,
      (i : ℕ) < k ∧ ((∑ j, x j * b i j) - β i) = (f x).toReal := by
  let Iaff : Finset (Fin m) := Finset.univ.filter fun i : Fin m => (i : ℕ) < k
  let value : Fin m → ℝ := fun i => (∑ j, x j * b i j) - β i
  let Sx : Set ℝ := {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = value i}
  have hkpred : k - 1 < m := lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hkpos)) hkm
  let i0 : Fin m := ⟨k - 1, hkpred⟩
  have hi0k : (i0 : ℕ) < k := by
    -- The distinguished index `k - 1` certifies the finite affine family is nonempty.
    simpa [i0] using Nat.pred_lt (Nat.ne_of_gt hkpos)
  have hIaff_nonempty : Iaff.Nonempty := by
    refine ⟨i0, ?_⟩
    simp [Iaff, hi0k]
  rcases Finset.exists_max_image Iaff value hIaff_nonempty with ⟨imax, himaxI, hmax⟩
  have himaxk : (imax : ℕ) < k := by
    simpa [Iaff] using (Finset.mem_filter.1 himaxI).2
  have hsup_eq :
      (sSup Sx : ℝ) = (f x).toReal :=
    helperForTheorem_23_10_representationSup_eq_toReal
      (f := f) (x := x) (b := b) (β := β) hrepr hx
  have hSx_nonempty : Sx.Nonempty := by
    exact ⟨value imax, ⟨imax, himaxk, rfl⟩⟩
  have hSx_bdd : BddAbove Sx := by
    refine ⟨value imax, ?_⟩
    intro r hr
    rcases hr with ⟨i, hi, rfl⟩
    exact hmax i (by simp [Iaff, hi])
  have himax_le_sup : value imax ≤ sSup Sx := by
    exact le_csSup hSx_bdd ⟨imax, himaxk, rfl⟩
  have hsup_le_imax : sSup Sx ≤ value imax := by
    -- The maximizing affine piece is an upper bound for the whole represented affine family.
    refine csSup_le hSx_nonempty ?_
    intro r hr
    rcases hr with ⟨i, hi, rfl⟩
    exact hmax i (by simp [Iaff, hi])
  have himax_eq : value imax = (f x).toReal := by
    calc
      value imax = sSup Sx := by exact le_antisymm himax_le_sup hsup_le_imax
      _ = (f x).toReal := hsup_eq
  exact ⟨imax, himaxk, himax_eq⟩

/-- Helper for Theorem 23.10: among the affine pieces active at `x`, one has maximal directional
slope in any fixed direction `d`. -/
lemma helperForTheorem_23_10_exists_activeSlopeMaximizer {n k m : ℕ}
    {f : (Fin n → ℝ) → EReal} {x d : Fin n → ℝ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    (hkpos : 0 < k) (hkm : k ≤ m)
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, y j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                (∑ j, y j * b i j) ≤ β i})
              y)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ∃ imax : Fin m,
      (imax : ℕ) < k ∧
        ((∑ j, x j * b imax j) - β imax) = (f x).toReal ∧
        ∀ i : Fin m,
          (i : ℕ) < k →
            ((∑ j, x j * b i j) - β i) = (f x).toReal →
              (∑ j, d j * b i j) ≤ (∑ j, d j * b imax j) := by
  let ActiveI : Finset (Fin m) := Finset.univ.filter fun i : Fin m =>
    (i : ℕ) < k ∧ ((∑ j, x j * b i j) - β i) = (f x).toReal
  let slope : Fin m → ℝ := fun i => ∑ j, d j * b i j
  rcases
      helperForTheorem_23_10_exists_activeAffine_piece
        (f := f) (x := x) (b := b) (β := β) hkpos hkm hrepr hx with
    ⟨i0, hi0k, hi0active⟩
  have hActive_nonempty : ActiveI.Nonempty := by
    refine ⟨i0, ?_⟩
    simp [ActiveI, hi0k, hi0active]
  rcases Finset.exists_max_image ActiveI slope hActive_nonempty with ⟨imax, himaxA, hmax⟩
  have himax_active :
      (imax : ℕ) < k ∧ ((∑ j, x j * b imax j) - β imax) = (f x).toReal := by
    simpa [ActiveI] using (Finset.mem_filter.1 himaxA).2
  refine ⟨imax, himax_active.1, himax_active.2, ?_⟩
  intro i hi hactive
  -- Repackage any active index as an element of the active finset, then use maximality of `imax`.
  exact hmax i (by simp [ActiveI, hi, hactive])

/-- Helper for Theorem 23.10: an inactive affine piece stays strictly below a chosen active piece
for all sufficiently small positive steps along the ray `x + t • d`. -/
lemma helperForTheorem_23_10_inactiveAffine_piece_stays_below_activeSlopeMaximizer {n k m : ℕ}
    {f : (Fin n → ℝ) → EReal} {x d : Fin n → ℝ}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ} {i imax : Fin m}
    (hrepr :
      f =
        fun y =>
          ((sSup {r : ℝ |
              ∃ j : Fin m, (j : ℕ) < k ∧ r = (∑ ℓ, y ℓ * b j ℓ) - β j} : ℝ) : EReal) +
            indicatorFunction
              (C := {y | ∀ j : Fin m, k ≤ (j : ℕ) →
                (∑ ℓ, y ℓ * b j ℓ) ≤ β j})
              y)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hi : (i : ℕ) < k)
    (himax : (imax : ℕ) < k ∧ ((∑ j, x j * b imax j) - β imax) = (f x).toReal)
    (hi_not_active : ((∑ j, x j * b i j) - β i) ≠ (f x).toReal) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 0 < t → t < ε →
        ((∑ j, (x + t • d) j * b i j) - β i) <
          ((∑ j, (x + t • d) j * b imax j) - β imax) := by
  let basei : ℝ := (∑ j, x j * b i j) - β i
  let baseMax : ℝ := (∑ j, x j * b imax j) - β imax
  let slopei : ℝ := ∑ j, d j * b i j
  let slopeMax : ℝ := ∑ j, d j * b imax j
  have hbasei_le : basei ≤ (f x).toReal := by
    simpa [basei] using
      helperForTheorem_23_10_affinePiece_le_finiteValue_of_representation
        (f := f) (x := x) (b := b) (β := β) (i := i) hrepr hx hi
  have hbasei_lt : basei < (f x).toReal := by
    exact lt_of_le_of_ne hbasei_le hi_not_active
  have hgap_pos : 0 < baseMax - basei := by
    -- The chosen active piece sits strictly above this inactive one at the base point `x`.
    dsimp [baseMax, basei]
    rw [himax.2]
    linarith
  by_cases hsigma : slopei - slopeMax ≤ 0
  · refine ⟨1, by norm_num, ?_⟩
    intro t htPos _htLt
    -- A nonpositive slope difference preserves the strict base-point gap for every positive step.
    rw [helperForTheorem_23_10_constraint_eval_add_smul b x d i t,
      helperForTheorem_23_10_constraint_eval_add_smul b x d imax t]
    have hgoal : basei + t * slopei < baseMax + t * slopeMax := by
      nlinarith [le_of_lt htPos, hbasei_lt, hsigma, himax.2]
    simpa [basei, baseMax, slopei, slopeMax, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hgoal
  · have hsigma_pos : 0 < slopei - slopeMax := lt_of_not_ge hsigma
    refine ⟨(baseMax - basei) / (slopei - slopeMax), div_pos hgap_pos hsigma_pos, ?_⟩
    intro t htPos htLt
    have hstep_lt : t * (slopei - slopeMax) < baseMax - basei := by
      exact (lt_div_iff₀ hsigma_pos).1 htLt
    -- If the inactive slope is larger, choose the radius from the ratio `gap / sigma`.
    rw [helperForTheorem_23_10_constraint_eval_add_smul b x d i t,
      helperForTheorem_23_10_constraint_eval_add_smul b x d imax t]
    have hgoal : basei + t * slopei < baseMax + t * slopeMax := by
      nlinarith [le_of_lt htPos, hstep_lt, himax.2]
    simpa [basei, baseMax, slopei, slopeMax, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hgoal


end Section23
end Chap05
