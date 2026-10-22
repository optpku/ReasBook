/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part3

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Helper for Lemma 31.0.3: if the packed separator has `t < 0`, then the exact lower-slice
objective already attains its minimum on `dom g`. -/
lemma helperForLemma_31_0_3_exactLowerBoundaryContact_fromStrictNegativePackedSeparator
    {n : ℕ} (α : ℝ) {g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    {β c : ℝ} {b : Fin n → ℝ} {t : ℝ}
    (ht : t < 0)
    (hLower :
      ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        β ≤ -x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c) :
    ∃ x0 : Fin n → ℝ,
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g ∧
        ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
          -x0 ⬝ᵥ b + t * (-(α + (g x0).toReal)) - c ≤
            -x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c := by
  let L := helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g
  let wPacked : Fin (n + 2) → ℝ :=
    prodLinearEquiv_append_coord (n := n + 1)
      (prodLinearEquiv_append_coord (n := n) (b, t), c)
  let φ : (Fin (n + 2) → ℝ) → EReal :=
    fun z => ((z ⬝ᵥ wPacked : ℝ) : EReal)
  let F : (Fin (n + 2) → ℝ) → EReal :=
    fun z => indicatorFunction L z + φ z
  have hdotPacked :
      ∀ (lam : ℝ) (x : Fin n → ℝ) (μ : ℝ),
        dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
            wPacked =
          x ⬝ᵥ b + μ * t + lam * c := by
    intro lam x μ
    calc
      dotProduct
          (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
          wPacked
          =
        dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (b, t), c)) := by
              simp [wPacked]
      _ =
        dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ))
            (prodLinearEquiv_append_coord (n := n) (b, t)) + lam * c := by
          simpa using
            helperForText_19_0_9_dotProduct_prodLinearEquivAppendCoord
              (n := n + 1)
              (p := (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
              (q := (prodLinearEquiv_append_coord (n := n) (b, t), c))
      _ = x ⬝ᵥ b + μ * t + lam * c := by
          have hInner :
              dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ))
                  (prodLinearEquiv_append_coord (n := n) (b, t)) =
                x ⬝ᵥ b + μ * t := by
            simpa using
              helperForText_19_0_9_dotProduct_prodLinearEquivAppendCoord
                (n := n) (p := (x, μ)) (q := (b, t))
          rw [hInner]
  obtain ⟨xg, rg, hxgVal⟩ :=
    properConvexFunctionOn_exists_finite_point (n := n) (f := g) hg
  have hdomG : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) := by
    refine ⟨xg, ?_⟩
    refine ⟨rg, ?_⟩
    rw [mem_epigraph_univ_iff]
    simpa [hxgVal]
  have hLpoly : IsPolyhedralConvexSet (n + 2) L :=
    helperForLemma_31_0_3_shiftedLowerLiftedEpigraph_polyhedral
      (n := n) (g := g) α hg_poly
  have hLconv : Convex ℝ L :=
    helperForTheorem_19_1_polyhedral_isConvex (n + 2) L hLpoly
  have hLnonempty : L.Nonempty :=
    helperForLemma_31_0_3_shiftedLowerLiftedEpigraph_nonempty
      (n := n) (g := g) α hg hdomG
  have hIndicatorPoly : IsPolyhedralConvexFunction (n + 2) (indicatorFunction L) :=
    helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet hLpoly
  have hIndicatorProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + 2) → ℝ)) (indicatorFunction L) :=
    properConvexFunctionOn_indicator_of_convex_of_nonempty (C := L) hLconv hLnonempty
  have hφPoly : IsPolyhedralConvexFunction (n + 2) φ :=
    by
      -- Unfold the local alias so the affine-function polyhedral lemma applies definitionally.
      simpa [φ] using
        helperForLemma_31_0_3_coeAffineFunctional_polyhedral wPacked 0
  have hφProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + 2) → ℝ)) φ :=
    by
      -- The same definitional unfolding packages the real affine map as a proper convex
      -- `EReal`-valued function.
      simpa [φ] using
        helperForLemma_31_0_3_coeAffineFunctional_proper wPacked 0
  have hFPoly : IsPolyhedralConvexFunction (n + 2) F := by
    simpa [F, φ] using
      (polyhedralConvexFunction_add_of_proper (n + 2) (indicatorFunction L) φ
        hIndicatorPoly hφPoly hIndicatorProper hφProper)
  let A0 : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin 0 → ℝ) := 0
  let y0 : Fin 0 → ℝ := 0
  have hLowerOnL : ∀ z ∈ L, (β : EReal) ≤ φ z := by
    intro z hz
    rcases hz with ⟨x, μ, hμ, rfl⟩
    have hgx_ne_top : g x ≠ (⊤ : EReal) := by
      intro hgx_top
      have : (⊤ : EReal) ≤ (μ : EReal) := by
        simpa [hgx_top] using hμ
      exact (not_top_le_coe μ) this
    have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
      rw [effectiveDomain_eq]
      exact ⟨by simp, (lt_top_iff_ne_top).2 hgx_ne_top⟩
    have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
    have hμrealE :
        (((α + (g x).toReal : ℝ) : EReal)) ≤ (μ : EReal) := by
      have hgx_eq : g x = (((g x).toReal : ℝ) : EReal) := by
        simpa using (EReal.coe_toReal (x := g x) hgx_ne_top hgx_ne_bot).symm
      have hμ' := hμ
      rw [hgx_eq] at hμ'
      simpa [EReal.coe_add] using hμ'
    have hμreal : α + (g x).toReal ≤ μ := by
      exact_mod_cast hμrealE
    have hneg : -μ ≤ -(α + (g x).toReal) := by
      linarith
    have htMul :
        t * (-(α + (g x).toReal)) ≤ t * (-μ) := by
      exact mul_le_mul_of_nonpos_left hneg (le_of_lt ht)
    have hβreal : β ≤ -x ⬝ᵥ b + t * (-μ) - c := by
      linarith [hLower (x := x) hxDom, htMul]
    have hphiEq :
        φ (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x, -μ), (-1 : ℝ))) =
          ((-x ⬝ᵥ b + t * (-μ) - c : ℝ) : EReal) := by
      dsimp [φ]
      rw [hdotPacked (-1 : ℝ) (-x) (-μ)]
      change (((-x : Fin n → ℝ) ⬝ᵥ b + (-μ) * t + (-1 : ℝ) * c : ℝ) : EReal) =
          ((-x ⬝ᵥ b + t * (-μ) - c : ℝ) : EReal)
      congr 1
      ring
    rw [hphiEq]
    exact_mod_cast hβreal
  have hImageLower :
      (β : EReal) ≤ imageUnderLinearMap A0 F y0 := by
    rw [imageUnderLinearMap]
    refine le_sInf ?_
    rintro z ⟨x, _hxA, rfl⟩
    by_cases hxL : x ∈ L
    · have hβφ : (β : EReal) ≤ φ x := hLowerOnL x hxL
      have hFx : F x = φ x := by
        simp [F, indicatorFunction, hxL]
      rw [hFx]
      exact hβφ
    · have hFx : F x = (⊤ : EReal) := by
        change indicatorFunction L x + φ x = (⊤ : EReal)
        rw [indicatorFunction, if_neg hxL]
        simpa [φ] using
          (EReal.top_add_of_ne_bot (EReal.coe_ne_bot (x ⬝ᵥ wPacked)))
      rw [hFx]
      simp
  rcases hLnonempty with ⟨zW, hzW⟩
  have hImageUpper :
      imageUnderLinearMap A0 F y0 ≤ φ zW := by
    have hzWmem :
        F zW ∈ {z : EReal | ∃ x : Fin (n + 2) → ℝ, A0 x = y0 ∧ z = F x} := by
      refine ⟨zW, ?_, rfl⟩
      ext i
      exact Fin.elim0 i
    have hsInfLe :
        imageUnderLinearMap A0 F y0 ≤ F zW := by
      simpa [imageUnderLinearMap] using sInf_le hzWmem
    have hFzW : F zW = φ zW := by
      simp [F, indicatorFunction, hzW]
    rw [hFzW] at hsInfLe
    exact hsInfLe
  have hImage_ne_top : imageUnderLinearMap A0 F y0 ≠ (⊤ : EReal) := by
    intro htop
    have : (⊤ : EReal) ≤ φ zW := by
      simpa [htop] using hImageUpper
    exact (not_top_le_coe (zW ⬝ᵥ wPacked)) this
  have hImage_ne_bot : imageUnderLinearMap A0 F y0 ≠ (⊥ : EReal) := by
    intro hbot
    have : (β : EReal) ≤ (⊥ : EReal) := by
      simpa [hbot] using hImageLower
    simpa using this
  have hImageFinite :
      ∃ r : ℝ, imageUnderLinearMap A0 F y0 = (r : EReal) := by
    refine ⟨(imageUnderLinearMap A0 F y0).toReal, ?_⟩
    simpa using
      (EReal.coe_toReal (x := imageUnderLinearMap A0 F y0) hImage_ne_top hImage_ne_bot).symm
  rcases
      (helperForCorollary_19_3_1_attainment_of_finite_imageValue
        (A := A0) (f := F) hFPoly y0 hImageFinite) with
    ⟨zMin, _hzMinA, hzMinEq⟩
  have hzMinL : zMin ∈ L := by
    by_contra hzMinNotL
    have hFtop : F zMin = (⊤ : EReal) := by
      change indicatorFunction L zMin + φ zMin = (⊤ : EReal)
      rw [indicatorFunction, if_neg hzMinNotL]
      simpa [φ] using
        (EReal.top_add_of_ne_bot (EReal.coe_ne_bot (zMin ⬝ᵥ wPacked)))
    have hImageTop : imageUnderLinearMap A0 F y0 = (⊤ : EReal) := by
      rw [hzMinEq, hFtop]
    exact hImage_ne_top hImageTop
  rcases hzMinL with ⟨x0, μ0, hμ0, rfl⟩
  have hgx0_ne_top : g x0 ≠ (⊤ : EReal) := by
    intro hgx0_top
    have : (⊤ : EReal) ≤ (μ0 : EReal) := by
      simpa [hgx0_top] using hμ0
    exact (not_top_le_coe μ0) this
  have hx0Dom : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
    rw [effectiveDomain_eq]
    exact ⟨by simp, (lt_top_iff_ne_top).2 hgx0_ne_top⟩
  have hμ0realE :
      (((α + (g x0).toReal : ℝ) : EReal)) ≤ (μ0 : EReal) := by
    have hgx0_ne_bot : g x0 ≠ (⊥ : EReal) := hg.2.2 x0 (by simp)
    have hgx0_eq : g x0 = (((g x0).toReal : ℝ) : EReal) := by
      simpa using (EReal.coe_toReal (x := g x0) hgx0_ne_top hgx0_ne_bot).symm
    have hμ0' := hμ0
    rw [hgx0_eq] at hμ0'
    simpa [EReal.coe_add] using hμ0'
  have hμ0real : α + (g x0).toReal ≤ μ0 := by
    exact_mod_cast hμ0realE
  refine ⟨x0, hx0Dom, ?_⟩
  intro x hx
  let zExact : Fin (n + 2) → ℝ :=
    prodLinearEquiv_append_coord (n := n + 1)
      (prodLinearEquiv_append_coord (n := n) (-x, -(α + (g x).toReal)), (-1 : ℝ))
  have hzExact : zExact ∈ L :=
    helperForLemma_31_0_3_mem_shiftedLowerLiftedEpigraph_of_mem_effectiveDomain
      (n := n) (g := g) α hg hx
  have hImageLeExact :
      imageUnderLinearMap A0 F y0 ≤ F zExact := by
    have hzExactMem :
        F zExact ∈ {z : EReal | ∃ x' : Fin (n + 2) → ℝ, A0 x' = y0 ∧ z = F x'} := by
      refine ⟨zExact, ?_, rfl⟩
      ext i
      exact Fin.elim0 i
    simpa [imageUnderLinearMap] using sInf_le hzExactMem
  have hPackedLeExactE :
      (((-x0 ⬝ᵥ b + t * (-μ0) - c : ℝ) : EReal)) ≤
        (((-x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c : ℝ) : EReal)) := by
    have hzMinPacked :
        prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (-x0, -μ0), (-1 : ℝ)) ∈ L := by
      exact ⟨x0, μ0, hμ0, rfl⟩
    have hphiMinEq :
        φ (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x0, -μ0), (-1 : ℝ))) =
          (((-x0 ⬝ᵥ b + t * (-μ0) - c : ℝ) : EReal)) := by
      dsimp [φ]
      rw [hdotPacked (-1 : ℝ) (-x0) (-μ0)]
      change (((-x0 : Fin n → ℝ) ⬝ᵥ b + (-μ0) * t + (-1 : ℝ) * c : ℝ) : EReal) =
          (((-x0 ⬝ᵥ b + t * (-μ0) - c : ℝ) : EReal))
      congr 1
      ring
    have hphiExactEq :
        φ zExact = (((-x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c : ℝ) : EReal)) := by
      dsimp [zExact, φ]
      rw [hdotPacked (-1 : ℝ) (-x) (-(α + (g x).toReal))]
      change (((-x : Fin n → ℝ) ⬝ᵥ b + (-(α + (g x).toReal)) * t + (-1 : ℝ) * c : ℝ) : EReal) =
          (((-x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c : ℝ) : EReal))
      congr 1
      ring
    have hMinLeExact : F
          (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x0, -μ0), (-1 : ℝ))) ≤
        F zExact := by
      simpa [hzMinEq] using hImageLeExact
    have hFMinEq :
        F (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x0, -μ0), (-1 : ℝ))) =
          (((-x0 ⬝ᵥ b + t * (-μ0) - c : ℝ) : EReal)) := by
      rw [show F
          (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x0, -μ0), (-1 : ℝ))) =
          φ
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (-x0, -μ0), (-1 : ℝ))) by
            simp [F, indicatorFunction, hzMinPacked]]
      exact hphiMinEq
    have hFExactEq :
        F zExact = (((-x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c : ℝ) : EReal)) := by
      rw [show F zExact = φ zExact by simp [F, indicatorFunction, hzExact]]
      exact hphiExactEq
    rw [hFMinEq, hFExactEq] at hMinLeExact
    exact hMinLeExact
  have hPackedLeExact :
      -x0 ⬝ᵥ b + t * (-μ0) - c ≤
        -x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c := by
    exact_mod_cast hPackedLeExactE
  have hExact0LePacked0 :
      -x0 ⬝ᵥ b + t * (-(α + (g x0).toReal)) - c ≤
        -x0 ⬝ᵥ b + t * (-μ0) - c := by
    have hneg0 : -μ0 ≤ -(α + (g x0).toReal) := by
      linarith
    have htMul0 :
        t * (-(α + (g x0).toReal)) ≤ t * (-μ0) := by
      exact mul_le_mul_of_nonpos_left hneg0 (le_of_lt ht)
    linarith
  exact le_trans hExact0LePacked0 hPackedLeExact

/-- Helper for Lemma 31.0.3: the exact lower contact point from the strict packed separator
produces an affine map that touches `α + g` there and stays below `α + g` on `dom g`. -/
lemma helperForLemma_31_0_3_touchedStrictNegativePackedSeparator_contactMinorantOnDomainG
    {n : ℕ} {g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    {c : ℝ} {b : Fin n → ℝ} {t : ℝ}
    (ht : t < 0)
    {xContact : Fin n → ℝ}
    (hxContact : xContact ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)
    (hMinimal :
      ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        -xContact ⬝ᵥ b + t * (-(α + (g xContact).toReal)) - c ≤
          -x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c) :
    let gxContact : ℝ := (g xContact).toReal
    let m : ℝ := -xContact ⬝ᵥ b + t * (-(α + gxContact)) - c
    let hAff : AffineMap ℝ (Fin n → ℝ) ℝ :=
      (((-1 / t : ℝ) • dotProductLinear n b).toAffineMap) -
        AffineMap.const ℝ (Fin n → ℝ) ((m + c) / t)
    (∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g,
      (hAff x : EReal) ≤ (α : EReal) + g x) ∧
      ((hAff xContact : EReal) = (α : EReal) + g xContact) := by
  have hgxContact_ne_top : g xContact ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hxContact
  have hgxContact_ne_bot : g xContact ≠ (⊥ : EReal) := hg.2.2 xContact (by simp)
  let gxContact : ℝ := (g xContact).toReal
  let m : ℝ := -xContact ⬝ᵥ b + t * (-(α + gxContact)) - c
  let hAff : AffineMap ℝ (Fin n → ℝ) ℝ :=
    (((-1 / t : ℝ) • dotProductLinear n b).toAffineMap) -
      AffineMap.const ℝ (Fin n → ℝ) ((m + c) / t)
  have hAff_repr :
      ∀ x : Fin n → ℝ, hAff x = (-m - c - x ⬝ᵥ b) / t := by
    intro x
    simp [hAff, dotProductLinear, div_eq_mul_inv, sub_eq_add_neg]
    ring
  change
    (∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g,
      (hAff x : EReal) ≤ (α : EReal) + g x) ∧
      ((hAff xContact : EReal) = (α : EReal) + g xContact)
  refine ⟨?_, ?_⟩
  · intro x hxG
    -- Normalize the lower packed inequality by the touched contact level `m`.
    have hgx_ne_top : g x ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hxG
    have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
    let gx : ℝ := (g x).toReal
    let s : ℝ := α + gx
    have hgx_eq : g x = (gx : EReal) := by
      simpa [gx] using (EReal.coe_toReal (x := g x) hgx_ne_top hgx_ne_bot).symm
    have hs_eq : (α : EReal) + g x = (s : EReal) := by
      simp [s, hgx_eq, EReal.coe_add]
    have hMinimalSlice : m ≤ -x ⬝ᵥ b + t * (-s) - c := by
      simpa [m, gxContact, gx, s] using hMinimal (x := x) hxG
    have hNumerator : t * s ≤ -m - c - x ⬝ᵥ b := by
      have hStep0 :
          x ⬝ᵥ b + c + m ≤ x ⬝ᵥ b + c + (-x ⬝ᵥ b - t * s - c) :=
        by
          have hStep0' := add_le_add_right hMinimalSlice (x ⬝ᵥ b + c)
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hStep0'
      have hStep' : m + x ⬝ᵥ b + c ≤ -(t * s) := by
        calc
          m + x ⬝ᵥ b + c = x ⬝ᵥ b + c + m := by ring
          _ ≤ x ⬝ᵥ b + c + (-x ⬝ᵥ b - t * s - c) := hStep0
          _ = x ⬝ᵥ b + (-x ⬝ᵥ b) - t * s := by ring
          _ = 0 - t * s := by simp
          _ = -(t * s) := by ring
      have hNeg : t * s ≤ -(m + x ⬝ᵥ b + c) := by
        simpa [neg_mul, mul_comm] using neg_le_neg hStep'
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hNeg
    have hReal : hAff x ≤ s := by
      rw [hAff_repr x]
      exact (div_le_iff_of_neg ht).2 (by simpa [mul_comm] using hNumerator)
    have hCoe : (hAff x : EReal) ≤ (s : EReal) := by
      exact_mod_cast hReal
    calc
      (hAff x : EReal) ≤ (s : EReal) := hCoe
      _ = (α : EReal) + g x := hs_eq.symm
  · -- Evaluate the affine map at the contact point to recover the touched lower boundary.
    have hgxContact_eq : g xContact = (gxContact : EReal) := by
      simpa [gxContact] using
        (EReal.coe_toReal (x := g xContact) hgxContact_ne_top hgxContact_ne_bot).symm
    have hNumerator :
        -m - c - xContact ⬝ᵥ b = t * (α + gxContact) := by
      let d : ℝ := xContact ⬝ᵥ b
      dsimp [m, d]
      have hExpand :
          -(-xContact ⬝ᵥ b + t * (-(α + gxContact)) - c) - c - xContact ⬝ᵥ b =
            -(-xContact ⬝ᵥ b) - (t * (-(α + gxContact))) - xContact ⬝ᵥ b := by
        ring
      rw [hExpand]
      have hCancel : -(-xContact ⬝ᵥ b) - xContact ⬝ᵥ b = 0 := by simp
      nlinarith
    have ht_ne : t ≠ 0 := ne_of_lt ht
    have hRealTouch : hAff xContact = α + gxContact := by
      rw [hAff_repr xContact, hNumerator]
      field_simp [ht_ne]
    have hTouchE : (hAff xContact : EReal) = ((α + gxContact : ℝ) : EReal) := by
      exact_mod_cast hRealTouch
    calc
      (hAff xContact : EReal) = ((α + gxContact : ℝ) : EReal) := hTouchE
      _ = (α : EReal) + (gxContact : EReal) := by simp [EReal.coe_add]
      _ = (α : EReal) + g xContact := by rw [hgxContact_eq]

/-- Helper for Lemma 31.0.3: once the touched strict-branch contact level `m` satisfies the
sign upgrade `m + β ≤ 0`, the same explicit affine map also lies below `f` everywhere. -/
lemma helperForLemma_31_0_3_touchedStrictNegativePackedSeparator_globalUpperOnF_of_contactLevelAddRawLevel_nonpos
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {β c m : ℝ} {b : Fin n → ℝ} {t : ℝ}
    (ht : t < 0)
    (hLevel : m + β ≤ 0)
    (hUpper :
      ∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
        x ⬝ᵥ b + t * μ + c ≤ β)
    (hAff : AffineMap ℝ (Fin n → ℝ) ℝ)
    (hAff_repr : ∀ x : Fin n → ℝ, hAff x = (-m - c - x ⬝ᵥ b) / t) :
    ∀ x : Fin n → ℝ, (hAff x : EReal) ≤ f x := by
  intro x
  -- Evaluate `f` at a finite upper epigraph point when possible; the `⊤` case is immediate.
  by_cases hfx_top : f x = (⊤ : EReal)
  · simpa [hfx_top]
  · have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
    let μ : ℝ := (f x).toReal
    have hμ_eq : f x = (μ : EReal) := by
      simpa [μ] using (EReal.coe_toReal (x := f x) hfx_top hfx_ne_bot).symm
    have hUpperSlice : x ⬝ᵥ b + t * μ + c ≤ β := by
      exact hUpper (x := x) (μ := μ) (by simpa [hμ_eq])
    have hUpperNumerator : μ * t ≤ β - c - x ⬝ᵥ b := by
      nlinarith [hUpperSlice]
    have hUpperReal : (β - c - x ⬝ᵥ b) / t ≤ μ := by
      exact (div_le_iff_of_neg ht).2 hUpperNumerator
    have hCompareReal : hAff x ≤ (β - c - x ⬝ᵥ b) / t := by
      rw [hAff_repr x]
      exact (div_le_div_right_of_neg ht).2 (by linarith)
    have hReal : hAff x ≤ μ := le_trans hCompareReal hUpperReal
    have hCoe : (hAff x : EReal) ≤ (μ : EReal) := by
      exact_mod_cast hReal
    calc
      (hAff x : EReal) ≤ (μ : EReal) := hCoe
      _ = f x := hμ_eq.symm

/-- Helper for Lemma 31.0.3: once an affine map lies below `f` and touches `α + g` at one
effective-domain point of `g`, the touched point already yields the required dual witness. -/
lemma helperForLemma_31_0_3_directDualWitnessFromTouchedAffineMinorant {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (h : AffineMap ℝ (Fin n → ℝ) ℝ)
    {xContact : Fin n → ℝ}
    (hxContact : xContact ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)
    (hUpper : ∀ x : Fin n → ℝ, (h x : EReal) ≤ f x)
    (hTouch : (h xContact : EReal) = (α : EReal) + g xContact) :
    ∃ xStar : Fin n → ℝ,
      fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  rcases affineMap_exists_dotProduct_sub (h := h) with ⟨xStar, δ, hrepr⟩
  refine ⟨xStar, ?_⟩
  -- First turn the affine upper bound into the standard conjugate upper estimate for `f*`.
  have hF :
      fenchelConjugate n f xStar ≤ (δ : EReal) :=
    helperForLemma_31_0_2_fenchelConjugateUpperBound_of_affineUpperBound
      (n := n) (f := f) h hrepr hUpper
  have hgx_ne_top : g xContact ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hxContact
  have hgx_ne_bot : g xContact ≠ (⊥ : EReal) := hg.2.2 xContact (by simp)
  -- Then rewrite the touched equality at `xContact` into a single Fenchel term for `g*`.
  have hTouchAtContact :
      (α : EReal) + g xContact ≤
        (((xContact ⬝ᵥ xStar : ℝ) : EReal) - (δ : EReal)) := by
    simpa [hrepr xContact, sub_eq_add_neg, EReal.coe_add, add_assoc, add_left_comm, add_comm]
      using hTouch.symm.le
  have hShifted :
      (((α + δ : ℝ) : EReal) + g xContact) ≤ ((xContact ⬝ᵥ xStar : ℝ) : EReal) := by
    have hδ :
        ((α : EReal) + g xContact) + (δ : EReal) ≤ ((xContact ⬝ᵥ xStar : ℝ) : EReal) :=
      (EReal.le_sub_iff_add_le
        (Or.inl (by simp))
        (Or.inl (by simp))).1 hTouchAtContact
    simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hδ
  have hG :
      ((α + δ : ℝ) : EReal) ≤ fenchelConjugate n g xStar := by
    have hPoint :
        ((α + δ : ℝ) : EReal) ≤
          ((xContact ⬝ᵥ xStar : ℝ) : EReal) - g xContact := by
      exact
        (EReal.le_sub_iff_add_le
          (Or.inl hgx_ne_bot)
          (Or.inl hgx_ne_top)).2 hShifted
    have hTerm :
        (((xContact ⬝ᵥ xStar : ℝ) : EReal) - g xContact) ≤ fenchelConjugate n g xStar := by
      unfold fenchelConjugate
      exact le_sSup ⟨xContact, rfl⟩
    exact le_trans hPoint hTerm
  -- Finally subtract the two conjugate estimates to recover the target dual gap `α`.
  have hGapToδ :
      (α : EReal) ≤ fenchelConjugate n g xStar - (δ : EReal) := by
    exact
      (EReal.le_sub_iff_add_le
        (Or.inl (by simp))
        (Or.inl (by simp))).2
        (by simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hG)
  have hδToF :
      fenchelConjugate n g xStar - (δ : EReal) ≤
        fenchelConjugate n g xStar - fenchelConjugate n f xStar := by
    exact EReal.sub_le_sub le_rfl hF
  exact le_trans hGapToδ hδToF

/-- Helper for Lemma 31.0.3: any admissible-pair bound on an affine map immediately descends to a
global lower bound on the Section 31.0.2 zero-balance slice-gap infimum. -/
lemma helperForLemma_31_0_3_zeroBalanceSliceGapMinorant_of_admissiblePairBound {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (ℓ : AffineMap ℝ (Fin n → ℝ) ℝ)
    (hPairBound :
      ∀ {u v : Fin n → ℝ},
        u ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f →
          v ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
            (ℓ (u - v) : EReal) ≤ f u - ((α : EReal) + g v)) :
    ∀ z : Fin n → ℝ, (ℓ z : EReal) ≤ helperForLemma_31_0_2_zeroBalanceSliceGap α f g z := by
  intro z
  -- Unfold the slice infimum and bound every admissible pair `(u, v)` individually.
  rw [helperForLemma_31_0_2_zeroBalanceSliceGap]
  refine le_iInf ?_
  intro uv
  rcases uv with ⟨u, v⟩
  by_cases hEq : u - v = z
  · by_cases hDom :
        u ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
          v ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
    · have hGap : (ℓ z : EReal) ≤ f u - ((α : EReal) + g v) := by
        simpa [hEq] using hPairBound hDom.1 hDom.2
      simpa [hEq, hDom] using hGap
    · simp [hEq, hDom]
  · simp [hEq]

/-- Helper for Lemma 31.0.3: once a nonnegative affine minorant of the zero-balance slice gap is
available, the Section 31.0.2 dual-witness bridge finishes the argument. -/
lemma helperForLemma_31_0_3_directDualWitnessFromZeroBalanceSliceGapMinorant {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (ℓ : AffineMap ℝ (Fin n → ℝ) ℝ)
    (hMinorant :
      ∀ z : Fin n → ℝ, (ℓ z : EReal) ≤ helperForLemma_31_0_2_zeroBalanceSliceGap α f g z)
    (hNonnegAtZero : 0 ≤ ℓ 0) :
    ∃ xStar : Fin n → ℝ,
      fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  -- This is exactly the Section 31.0.2 bridge, repackaged for the current polyhedral argument.
  exact
    helperForLemma_31_0_2_dualWitnessOfNonnegativeSliceGapMinorant
      (n := n) (f := f) (g := g) α hg ℓ hMinorant hNonnegAtZero

/-- Helper for Lemma 31.0.3: once the raw separator is known to satisfy `t ≤ 0`, either the
strict-slope/nonpositive-level normalization produces the affine upper bound package already
available in this file, or one is in the genuine residual sign cases `t = 0 ∨ 0 < β`. -/
lemma helperForLemma_31_0_3_caseSplitFromPackedSeparatorSignData
    {n : ℕ} {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    {β c : ℝ} {b : Fin n → ℝ} {t : ℝ}
    (htNonpos : t ≤ 0)
    (hUpper :
      ∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
        x ⬝ᵥ b + t * μ + c ≤ β)
    (hLower :
      ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        β ≤ -x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c) :
    (∃ h : AffineMap ℝ (Fin n → ℝ) ℝ,
      (∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g,
        (h x : EReal) ≤ (α : EReal) + g x) ∧
        (∀ x : Fin n → ℝ, (h x : EReal) ≤ f x)) ∨
      t = 0 ∨ 0 < β := by
  by_cases hGood : t < 0 ∧ β ≤ 0
  · left
    exact
      helperForLemma_31_0_3_affineMinorantOfPackedSeparatorWithLevel
        (n := n) (f := f) (g := g) α hf hg hGood.1 hGood.2 hUpper hLower
  · right
    by_cases htStrict : t < 0
    · right
      have hβnot : ¬ β ≤ 0 := by
        intro hBetaNonpos
        exact hGood ⟨htStrict, hBetaNonpos⟩
      exact lt_of_not_ge hβnot
    · left
      exact le_antisymm htNonpos (le_of_not_gt htStrict)

/-- Helper for Lemma 31.0.3: at a common effective-domain point, the raw packed separator already
forces the corresponding upper packed value to be nonpositive. -/
lemma helperForLemma_31_0_3_rawPackedSigns_at_commonEffectivePoint
    {n : ℕ} {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    {β c : ℝ} {b : Fin n → ℝ} {t : ℝ}
    (htNonpos : t ≤ 0)
    (hUpper :
      ∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
        x ⬝ᵥ b + t * μ + c ≤ β)
    (hLower :
      ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        β ≤ -x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c)
    (hPointwiseOnCommon :
      ∀ x : Fin n → ℝ,
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
          (α : EReal) ≤ f x - g x)
    {x : Fin n → ℝ}
    (hxF : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (hxG : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :
    x ⬝ᵥ b + t * (f x).toReal + c ≤ 0 := by
  have hfx_ne_top : f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hxF
  have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  have hgx_ne_top : g x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hxG
  have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
  let fx : ℝ := (f x).toReal
  let gx : ℝ := (g x).toReal
  have hfx_eq : f x = (fx : EReal) := by
    simpa [fx] using (EReal.coe_toReal (x := f x) hfx_ne_top hfx_ne_bot).symm
  have hgx_eq : g x = (gx : EReal) := by
    simpa [gx] using (EReal.coe_toReal (x := g x) hgx_ne_top hgx_ne_bot).symm
  have hShifted :
      ((α + gx : ℝ) : EReal) ≤ (fx : EReal) := by
    -- Rewrite the textbook common-domain lower bound into the exact finite real slice used by the
    -- packed separator at this witness.
    have hPointwiseShifted :
        (α : EReal) + g x ≤ f x :=
      helperForLemma_31_0_3_shiftedPointwiseBoundOnDomainG
        (n := n) (f := f) (g := g) α hg hPointwiseOnCommon hxG
    rw [hfx_eq, hgx_eq] at hPointwiseShifted
    simpa [EReal.coe_add] using hPointwiseShifted
  have hShiftedReal : α + gx ≤ fx := by
    exact_mod_cast hShifted
  have hGapNonneg : 0 ≤ fx - (α + gx) := by
    linarith
  have hUpperAtWitness : x ⬝ᵥ b + t * fx + c ≤ β := by
    exact hUpper (x := x) (μ := fx) (by simpa [hfx_eq])
  have hLowerAtWitness : β ≤ -x ⬝ᵥ b + t * (-(α + gx)) - c := by
    simpa [gx] using hLower (x := x) hxG
  have hGapTermNonpos :
      t * (fx - (α + gx)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg htNonpos hGapNonneg
  have hUpperLeLower :
      x ⬝ᵥ b + t * fx + c ≤ -x ⬝ᵥ b + t * (-(α + gx)) - c := by
    exact le_trans hUpperAtWitness hLowerAtWitness
  have hSumNonpos :
      (x ⬝ᵥ b + t * fx + c) + (-x ⬝ᵥ b + t * (-(α + gx)) - c) ≤ 0 := by
    have hCancel : x ⬝ᵥ b + -x ⬝ᵥ b = 0 := by
      simpa using add_right_neg (x ⬝ᵥ b)
    have hEq :
        (x ⬝ᵥ b + t * fx + c) + (-x ⬝ᵥ b + t * (-(α + gx)) - c) =
          t * (fx - (α + gx)) := by
      calc
        (x ⬝ᵥ b + t * fx + c) + (-x ⬝ᵥ b + t * (-(α + gx)) - c)
            = (x ⬝ᵥ b + -x ⬝ᵥ b) + (t * fx + t * (-(α + gx))) := by ring
        _ = t * fx + t * (-(α + gx)) := by rw [hCancel, zero_add]
        _ = t * (fx - (α + gx)) := by ring
    rw [hEq]
    exact hGapTermNonpos
  -- The common-domain witness lies below its matching lower packed value, so the sum estimate
  -- forces the upper packed value itself to be nonpositive.
  linarith

/-- Helper for Lemma 31.0.3: when the raw packed separator has `t < 0`, adding its upper and
lower inequalities produces a linear admissible-pair bound on the zero-balance slice gap. -/
lemma helperForLemma_31_0_3_contactLevelDominatesRawLevel {n : ℕ}
    {g : (Fin n → ℝ) → EReal} (α : ℝ)
    {β c : ℝ} {b : Fin n → ℝ} {t : ℝ}
    {xContact : Fin n → ℝ}
    (hxContact : xContact ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)
    (hLower :
      ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        β ≤ -x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c) :
    β ≤ -xContact ⬝ᵥ b + t * (-(α + (g xContact).toReal)) - c := by
  -- Evaluate the raw lower separator inequality at the exact contact point.
  simpa using hLower (x := xContact) hxContact

/-- Helper for Lemma 31.0.3: in the zero-slope branch, every effective-domain point of `f`
already satisfies the projected upper half-space inequality `x ⬝ᵥ b + c ≤ β`. -/
lemma helperForLemma_31_0_3_zeroSlopePackedSeparator_projectedUpperBoundOnDomainF {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {β c : ℝ} {b : Fin n → ℝ}
    (hUpper :
      ∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
        x ⬝ᵥ b + (0 : ℝ) * μ + c ≤ β)
    {x : Fin n → ℝ}
    (hxF : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :
    x ⬝ᵥ b + c ≤ β := by
  have hfx_ne_top : f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hxF
  have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  let μ : ℝ := (f x).toReal
  have hμ_eq : f x = (μ : EReal) := by
    simpa [μ] using (EReal.coe_toReal (x := f x) hfx_ne_top hfx_ne_bot).symm
  have hUpperAtX : x ⬝ᵥ b + (0 : ℝ) * μ + c ≤ β :=
    hUpper (x := x) (μ := μ) (by simpa [hμ_eq])
  -- Remove the degenerate vertical term `0 * μ`.
  simpa using hUpperAtX

/-- Helper for Lemma 31.0.3: in the zero-slope branch, every effective-domain point of `g`
already satisfies the projected lower half-space inequality `β ≤ -x ⬝ᵥ b - c`. -/
lemma helperForLemma_31_0_3_zeroSlopePackedSeparator_projectedLowerBoundOnDomainG {n : ℕ}
    {g : (Fin n → ℝ) → EReal} (α : ℝ)
    {β c : ℝ} {b : Fin n → ℝ}
    (hLower :
      ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        β ≤ -x ⬝ᵥ b + (0 : ℝ) * (-(α + (g x).toReal)) - c)
    {x : Fin n → ℝ}
    (hxG : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :
    β ≤ -x ⬝ᵥ b - c := by
  -- Drop the zero-slope term from the raw lower separator inequality.
  simpa [sub_eq_add_neg] using hLower (x := x) hxG

/-- Helper for Lemma 31.0.3: the zero-slope `hUpperNotSubset` witness projects to a genuine
effective-domain point of `f` where the projected half-space inequality is strict. -/
lemma helperForLemma_31_0_3_zeroSlopePackedSeparator_projectedUpperWitness {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {β c : ℝ} {b : Fin n → ℝ}
    (hUpper :
      ∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
        x ⬝ᵥ b + (0 : ℝ) * μ + c ≤ β)
    (hUpperNotSubset :
      ¬ helperForLemma_31_0_3_upperLiftedEpigraph f ⊆
          {z : Fin (n + 2) → ℝ |
            z ⬝ᵥ
                prodLinearEquiv_append_coord (n := n + 1)
                  (prodLinearEquiv_append_coord (n := n) (b, (0 : ℝ)), c) =
              β}) :
    ∃ xF : Fin n → ℝ,
      xF ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
        xF ⬝ᵥ b + c < β := by
  have hExists :
      ∃ z : Fin (n + 2) → ℝ,
        z ∈ helperForLemma_31_0_3_upperLiftedEpigraph f ∧
          z ∉
            {z : Fin (n + 2) → ℝ |
              z ⬝ᵥ
                  prodLinearEquiv_append_coord (n := n + 1)
                    (prodLinearEquiv_append_coord (n := n) (b, (0 : ℝ)), c) =
                β} := by
    by_contra hNoWitness
    apply hUpperNotSubset
    intro z hzUpper
    by_contra hzNotOnLevel
    exact hNoWitness ⟨z, hzUpper, hzNotOnLevel⟩
  rcases hExists with ⟨z, hzUpper, hzNotOnLevel⟩
  rcases hzUpper with ⟨xF, μF, hμF, rfl⟩
  have hfx_ne_bot : f xF ≠ (⊥ : EReal) := hf.2.2 xF (by simp)
  have hfx_ne_top : f xF ≠ (⊤ : EReal) := by
    intro hTop
    have : (⊤ : EReal) ≤ (μF : EReal) := by
      simpa [hTop] using hμF
    exact (not_top_le_coe μF) this
  have hxF : xF ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    rw [effectiveDomain_eq]
    exact ⟨by simp, (lt_top_iff_ne_top).2 hfx_ne_top⟩
  have hLe : xF ⬝ᵥ b + c ≤ β :=
    helperForLemma_31_0_3_zeroSlopePackedSeparator_projectedUpperBoundOnDomainF
      (n := n) (f := f) hf hUpper hxF
  have hDot :
      prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (xF, μF), (1 : ℝ)) ⬝ᵥ
            prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (b, (0 : ℝ)), c) =
        xF ⬝ᵥ b + c := by
    calc
      prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (xF, μF), (1 : ℝ)) ⬝ᵥ
          prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (b, (0 : ℝ)), c)
          =
        (prodLinearEquiv_append_coord (n := n) (xF, μF)) ⬝ᵥ
            (prodLinearEquiv_append_coord (n := n) (b, (0 : ℝ))) +
          (1 : ℝ) * c := by
            simpa using
              helperForText_19_0_9_dotProduct_prodLinearEquivAppendCoord
                (n := n + 1)
                (p := (prodLinearEquiv_append_coord (n := n) (xF, μF), (1 : ℝ)))
                (q := (prodLinearEquiv_append_coord (n := n) (b, (0 : ℝ)), c))
      _ = xF ⬝ᵥ b + μF * (0 : ℝ) + (1 : ℝ) * c := by
            congr 1
            simpa using
              helperForText_19_0_9_dotProduct_prodLinearEquivAppendCoord
                (n := n) (p := (xF, μF)) (q := (b, (0 : ℝ)))
      _ = xF ⬝ᵥ b + c := by ring
  have hNe : xF ⬝ᵥ b + c ≠ β := by
    intro hEq
    apply hzNotOnLevel
    simpa [hDot, hEq]
  -- The upper epigraph witness already satisfies the non-strict inequality, so missing the level
  -- set means the projected value is strictly smaller than `β`.
  refine ⟨xF, hxF, lt_of_le_of_ne hLe hNe⟩

/-- Helper for Lemma 31.0.3: in the zero-slope branch, package the projected upper/lower
half-space bounds together with one strict projected witness from `dom f`. -/
lemma helperForLemma_31_0_3_zeroSlopePackedSeparator_projectedSupportData {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {β c : ℝ} {b : Fin n → ℝ}
    (hUpper :
      ∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
        x ⬝ᵥ b + (0 : ℝ) * μ + c ≤ β)
    (hLower :
      ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        β ≤ -x ⬝ᵥ b + (0 : ℝ) * (-(α + (g x).toReal)) - c)
    (hUpperNotSubset :
      ¬ helperForLemma_31_0_3_upperLiftedEpigraph f ⊆
          {z : Fin (n + 2) → ℝ |
            z ⬝ᵥ
                prodLinearEquiv_append_coord (n := n + 1)
                  (prodLinearEquiv_append_coord (n := n) (b, (0 : ℝ)), c) =
              β}) :
    ∃ xF : Fin n → ℝ,
      xF ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
        xF ⬝ᵥ b + c < β ∧
          (∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f,
            x ⬝ᵥ b + c ≤ β) ∧
            (∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g,
              β ≤ -x ⬝ᵥ b - c) := by
  rcases
      helperForLemma_31_0_3_zeroSlopePackedSeparator_projectedUpperWitness
        (n := n) (f := f) hf hUpper hUpperNotSubset with
    ⟨xF, hxF, hxFStrict⟩
  refine ⟨xF, hxF, hxFStrict, ?_, ?_⟩
  · intro x hxDomF
    -- This is exactly the projected upper half-space control on `dom f`.
    exact
      helperForLemma_31_0_3_zeroSlopePackedSeparator_projectedUpperBoundOnDomainF
        (n := n) (f := f) hf hUpper hxDomF
  · intro x hxDomG
    -- The lower packed inequality collapses to the projected lower half-space when `t = 0`.
    exact
      helperForLemma_31_0_3_zeroSlopePackedSeparator_projectedLowerBoundOnDomainG
        (n := n) (g := g) α hLower hxDomG

/-- Helper for Lemma 31.0.3: the qualification witness already yields one common point where the
projected zero-slope upper and lower half-space bounds can be evaluated simultaneously. -/
lemma helperForLemma_31_0_3_zeroSlopePackedSeparator_commonWitnessBounds {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
    {β c : ℝ} {b : Fin n → ℝ}
    (hUpper :
      ∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
        x ⬝ᵥ b + (0 : ℝ) * μ + c ≤ β)
    (hLower :
      ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        β ≤ -x ⬝ᵥ b + (0 : ℝ) * (-(α + (g x).toReal)) - c) :
    ∃ x0 : Fin n → ℝ,
      x0 ∈ euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g ∧
          x0 ⬝ᵥ b + c ≤ β ∧
            β ≤ -x0 ⬝ᵥ b - c := by
  rcases hri with ⟨x0, hx0riF, hx0G⟩
  have hx0F : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    -- Relative-interior membership on `dom f` immediately gives ordinary domain membership.
    exact helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin hx0riF
  have hx0Upper : x0 ⬝ᵥ b + c ≤ β :=
    helperForLemma_31_0_3_zeroSlopePackedSeparator_projectedUpperBoundOnDomainF
      (n := n) (f := f) hf hUpper hx0F
  have hx0Lower : β ≤ -x0 ⬝ᵥ b - c :=
    helperForLemma_31_0_3_zeroSlopePackedSeparator_projectedLowerBoundOnDomainG
      (n := n) (g := g) α hLower hx0G
  -- Package the common witness together with both projected inequalities for later geometric use.
  exact ⟨x0, hx0riF, hx0G, hx0Upper, hx0Lower⟩

-- Proof sketch: the valid remaining route is the mixed-polyhedral Chapter 20 bridge, which
-- replaces the abandoned raw packed-separator branch split by an explicit attained binary
-- infimal-convolution decomposition.
/-- Helper for Lemma 31.0.3: the mixed `dom g ∩ ri(dom f)` witness is exactly the input needed by
the Chapter 20 mixed two-block exactness theorem for the binary pair `(g, f)`. -/
lemma helperForLemma_31_0_3_binaryMixedPolyhedralExactTopOrAttained {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hMixedWitness :
      Set.Nonempty
        ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
          ∩
          euclideanRelativeInterior n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)))) :
    (fenchelConjugate n (fun x => g x + f x) =
      infimalConvolution (fenchelConjugate n g) (fenchelConjugate n f)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n g) (fenchelConjugate n f) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n g) (fenchelConjugate n f) xStar =
              fenchelConjugate n g (xStar - y) + fenchelConjugate n f y) := by
  -- Reuse the Chapter 20 two-block bridge in exactly the mixed qualification format prepared
  -- earlier in this section.
  simpa using
    (_root_.helperForTheorem_20_1_mixed_two_block_exact_topOrAttained_of_polyLeft_domRi_without_riInter
      (p := g) (q := f) hg_poly hg hf hMixedWitness)

/-- Helper for Lemma 31.0.3: after specializing the Chapter 20 binary bridge at a dual point
where `(g + f)⋆` is finite, only the attained-split branch remains. -/
lemma helperForLemma_31_0_3_specializedBinaryAttainedSplitForDualGap {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hMixedWitness :
      Set.Nonempty
        ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
          ∩
          euclideanRelativeInterior n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))))
    (xStar : Fin n → ℝ)
    (hFinite : fenchelConjugate n (fun x => g x + f x) xStar ≠ (⊤ : EReal)) :
    ∃ y : Fin n → ℝ,
      fenchelConjugate n (fun x => g x + f x) xStar =
        fenchelConjugate n g (xStar - y) + fenchelConjugate n f y := by
  let hBridge :=
    helperForLemma_31_0_3_binaryMixedPolyhedralExactTopOrAttained
      (n := n) (f := f) (g := g) hg_poly hg hf hMixedWitness
  -- First rewrite the Chapter 20 equality at the chosen dual point.
  have hEqAt :
      fenchelConjugate n (fun x => g x + f x) xStar =
        infimalConvolution (fenchelConjugate n g) (fenchelConjugate n f) xStar := by
    simpa using congrArg (fun h : (Fin n → ℝ) → EReal => h xStar) hBridge.1
  -- Finiteness rules out the `⊤` branch, leaving only an attained decomposition.
  rcases hBridge.2 xStar with hTop | ⟨y, hy⟩
  · exact False.elim (hFinite (hEqAt.trans hTop))
  · exact ⟨y, hEqAt.trans hy⟩

/-- Helper for Lemma 31.0.3: rewrite the attained binary split at `xStar` into the zero-dual
coordinate system obtained by tilting both summands by the negated dual vectors. -/
lemma helperForLemma_31_0_3_attainedSplit_rewrite_as_zeroDualForLinearTilts {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    {xStar y : Fin n → ℝ}
    (hAttained :
      fenchelConjugate n (fun x => g x + f x) xStar =
        fenchelConjugate n g (xStar - y) + fenchelConjugate n f y) :
    let z : Fin n → ℝ := xStar - y
    fenchelConjugate n
        (fun x => g x + f x + (((x ⬝ᵥ (-xStar) : ℝ)) : EReal)) 0 =
      fenchelConjugate n
          (fun x => g x + (((x ⬝ᵥ (-z) : ℝ)) : EReal)) 0 +
        fenchelConjugate n
          (fun x => f x + (((x ⬝ᵥ (-y) : ℝ)) : EReal)) 0 := by
  let z : Fin n → ℝ := xStar - y
  -- Move the common dual point `xStar` to the origin by the usual linear-tilt rewrite.
  calc
    fenchelConjugate n
        (fun x => g x + f x + (((x ⬝ᵥ (-xStar) : ℝ)) : EReal)) 0 =
      fenchelConjugate n (fun x => g x + f x) xStar := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          congrArg (fun h : (Fin n → ℝ) → EReal => h 0)
            (section16_fenchelConjugate_add_linear
              (h := fun x => g x + f x) (-xStar))
    _ = fenchelConjugate n g z + fenchelConjugate n f y := by
      simpa [z] using hAttained
    _ =
        fenchelConjugate n
            (fun x => g x + (((x ⬝ᵥ (-z) : ℝ)) : EReal)) 0 +
          fenchelConjugate n
            (fun x => f x + (((x ⬝ᵥ (-y) : ℝ)) : EReal)) 0 := by
        -- Rewrite the individual raw conjugates at `z` and `y` back to zero-dual values.
        rw [show fenchelConjugate n g z =
            fenchelConjugate n
              (fun x => g x + (((x ⬝ᵥ (-z) : ℝ)) : EReal)) 0 by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (congrArg (fun h : (Fin n → ℝ) → EReal => h 0)
                  (section16_fenchelConjugate_add_linear (h := g) (-z))).symm]
        rw [show fenchelConjugate n f y =
            fenchelConjugate n
              (fun x => f x + (((x ⬝ᵥ (-y) : ℝ)) : EReal)) 0 by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (congrArg (fun h : (Fin n → ℝ) → EReal => h 0)
                  (section16_fenchelConjugate_add_linear (h := f) (-y))).symm]


end Section31
end Chap06
