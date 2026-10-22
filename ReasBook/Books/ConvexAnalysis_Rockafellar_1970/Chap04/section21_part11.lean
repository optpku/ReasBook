/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part10

section Chap04
section Section21

set_option maxHeartbeats 1000000 in
/-- Helper for Theorem 21.4: the genuine remaining `I = I₀ ⊔ I₁` core in the nonempty
affine-block branch. At this point `C₀ = {x | fᵢ(x) ≤ 0, i ∈ I₀}` is nonempty, `I₁` is
nonempty, and `C₀ ∩ C₁ = ∅` with `C₁ = {x | fⱼ(x) ≤ 0, j ∈ I₁}`. -/
lemma helperForTheorem_21_4_originalRoute_univ_convexHullConjugate_zero_neg_of_nonempty_twoBlock
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hConstOutside :
      ∀ d : Fin n → ℝ,
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
          ∀ i : I, i ∉ I0 →
            ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x)
    (hInonempty : ¬ IsEmpty I)
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal))
    (hA :
      ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)).Nonempty) :
    ¬ IsEmpty {i : I // i ∉ I0} →
    (¬ ∃ x : Fin n → ℝ,
        x ∈ {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} ∧
          ∀ j : {i : I // i ∉ I0}, f j.1 x ≤ (0 : EReal)) →
    convexHullFunctionFamily (fun i : I => fenchelConjugate n (f i)) 0 < (0 : EReal) := by
  intro hJnonempty hNotPrimalOnOutsideSubtype
  classical
  let A : Set (Fin n → ℝ) := {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)}
  let J0 := ↥I0
  let g1 : {i : I // i ∉ I0} → (Fin n → ℝ) → EReal := fun j => fenchelConjugate n (f j.1)
  let h1 : (Fin n → ℝ) → EReal := convexHullFunctionFamily g1
  let k1 : (Fin n → ℝ) → EReal := positivelyHomogeneousConvexFunctionGenerated h1
  let a0 : J0 → AffineMap ℝ (Fin n → ℝ) ℝ := fun i => Classical.choose (hAffine i.1 i.2)
  have ha0 : ∀ i : J0, ∀ x : Fin n → ℝ, f i.1 x = (a0 i x : EReal) := by
    intro i x
    exact Classical.choose_spec (hAffine i.1 i.2) x
  let b0 : J0 → Fin n → ℝ := fun i =>
    Classical.choose
      (helperForTheorem_21_4_effectiveDomain_fenchelConjugate_affine_eq_singleton (a0 i))
  have hAffineConjData :
      ∀ i : J0, ∃ β : ℝ,
        (∀ x : Fin n → ℝ, a0 i x = x ⬝ᵥ b0 i - β) ∧
          effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (fenchelConjugate n (fun x : Fin n → ℝ => (a0 i x : EReal))) =
              ({b0 i} : Set (Fin n → ℝ)) := by
    intro i
    let hconj :=
      helperForTheorem_21_4_effectiveDomain_fenchelConjugate_affine_eq_singleton (a0 i)
    refine ⟨Classical.choose (Classical.choose_spec hconj), ?_⟩
    simpa [b0, hconj] using Classical.choose_spec (Classical.choose_spec hconj)
  let α0 : J0 → ℝ := fun i => Classical.choose (hAffineConjData i)
  have hb0 : ∀ i : J0, ∀ x : Fin n → ℝ, a0 i x = x ⬝ᵥ b0 i - α0 i := by
    intro i x
    exact (Classical.choose_spec (hAffineConjData i)).1 x
  have hdom0 :
      ∀ i : J0,
        effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fenchelConjugate n (fun x : Fin n → ℝ => (a0 i x : EReal))) =
            ({b0 i} : Set (Fin n → ℝ)) := by
    intro i
    exact (Classical.choose_spec (hAffineConjData i)).2
  have hdom0_actual :
      ∀ i : J0,
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i.1)) =
          ({b0 i} : Set (Fin n → ℝ)) := by
    intro i
    have hfi_eq : f i.1 = fun x : Fin n → ℝ => (a0 i x : EReal) := by
      funext x
      exact ha0 i x
    simpa [g1, hfi_eq] using hdom0 i
  let K0 : Set (Fin n → ℝ) := cone n (Set.range b0)
  have hK0poly : IsPolyhedralConvexSet n K0 := by
    simpa [K0] using
      (helperForTheorem_19_1_cone_polyhedral_of_finite_generators
        (hT := Set.finite_range b0))
  have hnegK0poly : IsPolyhedralConvexSet n (-K0) :=
    helperForCorollary_19_3_3_neg_polyhedral hK0poly
  have h0K0 : (0 : Fin n → ℝ) ∈ K0 := by
    unfold K0
    have h0ray : (0 : Fin n → ℝ) ∈ ray n (Set.range b0) := by
      exact (Set.mem_insert_iff).2 (Or.inl rfl)
    exact (subset_convexHull (𝕜 := ℝ) (s := ray n (Set.range b0))) h0ray
  have hnegK0ne : (-K0).Nonempty := ⟨0, by simpa using h0K0⟩
  have hJ : Nonempty {i : I // i ∉ I0} := not_isEmpty_iff.mp hJnonempty
  have hg1Proper :
      ∀ j : {i : I // i ∉ I0}, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g1 j) := by
    intro j
    simpa [g1] using proper_fenchelConjugate_of_proper (n := n) (f := f j.1) (hfProper j.1)
  have hh1Minor := convexHullFunctionFamily_greatest_convex_minorant (f := g1)
  have hh1ConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h1 := by
    simpa [h1] using hh1Minor.1
  have hh1Le : ∀ j : {i : I // i ∉ I0}, h1 ≤ g1 j := by
    simpa [h1] using hh1Minor.2.1
  have hk1max :
      (∃ C : ConvexCone ℝ ((Fin n → ℝ) × ℝ),
        (C : Set ((Fin n → ℝ) × ℝ)) =
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) k1 ∧
        (0 : (Fin n → ℝ) × ℝ) ∈
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) k1) ∧
      (ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k1 ∧
        PositivelyHomogeneous k1 ∧
        k1 0 ≤ 0 ∧
        k1 ≤ h1) ∧
      (∀ u : (Fin n → ℝ) → EReal,
        PositivelyHomogeneous u →
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) u →
        u 0 ≤ 0 →
        u ≤ h1 →
        u ≤ k1) := by
    simpa [h1, k1] using
      (maximality_posHomogeneousHull (n := n) (h := h1) hh1ConvOn)
  have hk1ConvOn :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k1 := hk1max.2.1.1
  have hk10le : k1 0 ≤ 0 := hk1max.2.1.2.2.1
  have hk1Le : k1 ≤ h1 := hk1max.2.1.2.2.2
  have hk10_ne_top : k1 0 ≠ (⊤ : EReal) := by
    intro hk10_top
    have : (⊤ : EReal) ≤ (0 : EReal) := by
      simpa [hk10_top] using hk10le
    exact (not_top_le_coe 0) this
  have h0domK1 :
      (0 : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1 := by
    have hk10_lt : k1 0 < (⊤ : EReal) := (lt_top_iff_ne_top).2 hk10_ne_top
    simpa [effectiveDomain_eq] using
      (show (0 : Fin n → ℝ) ∈ {x : Fin n → ℝ | x ∈ Set.univ ∧ k1 x < (⊤ : EReal)} from
        ⟨by simp, hk10_lt⟩)
  have hdomK1ne :
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1).Nonempty := ⟨0, h0domK1⟩
  have hdomK1conv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) := by
    simpa using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := k1) hk1ConvOn)
  have hdomMemberSub :
      ∀ j : {i : I // i ∉ I0},
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (g1 j) ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1 := by
    intro j xStar hxStar
    have hxStar_lt : g1 j xStar < (⊤ : EReal) := by
      simpa [g1, effectiveDomain_eq] using hxStar
    have hk1_le_j : k1 xStar ≤ g1 j xStar :=
      le_trans (hk1Le xStar) (hh1Le j xStar)
    have hk1_ne_top : k1 xStar ≠ (⊤ : EReal) := by
      intro hk1_top
      have : (⊤ : EReal) ≤ g1 j xStar := by
        simpa [hk1_top] using hk1_le_j
      exact (lt_top_iff_ne_top.mp hxStar_lt) ((top_le_iff).1 this)
    have hk1_lt : k1 xStar < (⊤ : EReal) := (lt_top_iff_ne_top).2 hk1_ne_top
    simpa [effectiveDomain_eq] using
      (show xStar ∈ {x : Fin n → ℝ | x ∈ Set.univ ∧ k1 x < (⊤ : EReal)} from
        ⟨by simp, hk1_lt⟩)
  have hInterNonempty :
      Set.Nonempty
        ((-K0) ∩ intrinsicInterior ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)) := by
    by_contra hInterEmpty
    have hInterEmpty' :
        (-K0) ∩ intrinsicInterior ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) =
          (∅ : Set (Fin n → ℝ)) := by
      exact Set.not_nonempty_iff_eq_empty.mp hInterEmpty
    rcases
        (exists_hyperplaneSeparatesProperly_and_not_subset_right_iff_inter_intrinsicInterior_eq_empty_of_nonempty_convex_polyhedral_left
          n (-K0) (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)
          hnegK0ne hdomK1ne hdomK1conv hnegK0poly).2 hInterEmpty' with
      ⟨H, hHproper, hDomK1NotSubsetH⟩
    rcases hyperplaneSeparatesProperly_oriented n H (-K0)
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) hHproper with
      ⟨y, β, hy_ne_zero, hHdef, hnegK0_lower, hdomK1_upper, _hNotBoth⟩
    have hβle : β ≤ 0 := by
      simpa [hHdef] using hnegK0_lower 0 (by simpa using h0K0)
    have hβge : 0 ≤ β := by
      simpa [hHdef] using hdomK1_upper 0 h0domK1
    have hβ0 : β = 0 := le_antisymm hβle hβge
    rcases hA with ⟨x0, hx0A⟩
    have hb0_nonpos : ∀ i : J0, dotProduct (b0 i) y ≤ 0 := by
      intro i
      have hb0_memK0 : b0 i ∈ K0 := by
        unfold K0
        have hb0_ray : b0 i ∈ ray n (Set.range b0) :=
          mem_ray_of_mem (n := n) (S := Set.range b0) (x := b0 i) ⟨i, rfl⟩
        have hb0_conv : b0 i ∈ convexHull ℝ (ray n (Set.range b0)) :=
          (subset_convexHull (𝕜 := ℝ) (s := ray n (Set.range b0))) hb0_ray
        simpa [cone, conv] using hb0_conv
      have hnegmem : -(b0 i) ∈ -K0 := by
        simpa using hb0_memK0
      have hnonneg : 0 ≤ dotProduct (-b0 i) y := by
        simpa [hβ0] using hnegK0_lower (-(b0 i)) hnegmem
      have hnonneg' : 0 ≤ -(dotProduct (b0 i) y) := by
        simpa [dotProduct_neg] using hnonneg
      exact neg_nonneg.mp hnonneg'
    have hOutsideDomNonpos :
        ∀ j : {i : I // i ∉ I0},
          ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f j.1)),
            dotProduct xStar y ≤ 0 := by
      intro j xStar hxStar
      have hxStar_k1 :
          xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1 :=
        hdomMemberSub j (by simpa [g1] using hxStar)
      simpa [g1, hβ0] using hdomK1_upper xStar hxStar_k1
    have hAffineRay :
        ∀ i : I, i ∈ I0 →
          ∀ t : ℝ, 0 ≤ t → f i (x0 + t • y) ≤ (0 : EReal) := by
      intro i hi t ht
      let i0 : J0 := ⟨i, hi⟩
      have hx0le_real : x0 ⬝ᵥ b0 i0 - α0 i0 ≤ 0 := by
        have hx0le : f i x0 ≤ (0 : EReal) := hx0A i hi
        have hx0le' :
            (((x0 ⬝ᵥ b0 i0 - α0 i0 : ℝ)) : EReal) ≤ (0 : EReal) := by
          rw [ha0 i0 x0, hb0 i0 x0] at hx0le
          simpa using hx0le
        exact EReal.coe_le_coe_iff.mp hx0le'
      have hslope_real : y ⬝ᵥ b0 i0 ≤ 0 := by
        simpa [dotProduct_comm] using hb0_nonpos i0
      have hreal :
          x0 ⬝ᵥ b0 i0 - α0 i0 + t * (y ⬝ᵥ b0 i0) ≤ 0 := by
        nlinarith
      have hereal :
          (((x0 ⬝ᵥ b0 i0 - α0 i0 + t * (y ⬝ᵥ b0 i0) : ℝ)) : EReal) ≤ (0 : EReal) := by
        exact_mod_cast hreal
      have hval :
          f i (x0 + t • y) =
            (((x0 ⬝ᵥ b0 i0 - α0 i0) + t * (y ⬝ᵥ b0 i0) : ℝ) : EReal) := by
        have hdot :
            (x0 + t • y) ⬝ᵥ b0 i0 = x0 ⬝ᵥ b0 i0 + t * (y ⬝ᵥ b0 i0) := by
          calc
            (x0 + t • y) ⬝ᵥ b0 i0 = x0 ⬝ᵥ b0 i0 + (t • y) ⬝ᵥ b0 i0 := by
              simp [dotProduct_add]
            _ = x0 ⬝ᵥ b0 i0 + t * (y ⬝ᵥ b0 i0) := by
              simp [dotProduct_smul, smul_eq_mul]
        calc
          f i (x0 + t • y) = ((a0 i0 (x0 + t • y) : ℝ) : EReal) := by
            rw [ha0 i0 (x0 + t • y)]
          _ = ((((x0 + t • y) ⬝ᵥ b0 i0 - α0 i0 : ℝ)) : EReal) := by
            rw [hb0 i0 (x0 + t • y)]
          _ = (((x0 ⬝ᵥ b0 i0 - α0 i0) + t * (y ⬝ᵥ b0 i0) : ℝ) : EReal) := by
            rw [hdot]
            ring_nf
      rw [hval]
      exact hereal
    have hMonoAll :
        ∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • y) ≤ f i x := by
      intro i x t ht
      by_cases hi : i ∈ I0
      · exact
          helperForTheorem_21_4_affineBlock_rayNonpositive_to_globalMonotonicity
            f I0 hAffine x0 y hAffineRay i hi x t ht
      · exact
          helperForTheorem_21_4_ray_antitone_of_nonpositive_effectiveDomain_fenchelConjugate
            (g := f i) (hgProper := hfProper i) (hgClosed := hfClosed i) (d := y)
            (hNonpos := fun xStar hxStar =>
              hOutsideDomNonpos ⟨i, hi⟩ xStar (by
                change
                  xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
                    (fenchelConjugate n (f i))
                exact hxStar))
            x t ht
    have hOutsideConst :
        ∀ i : I, i ∉ I0 →
          ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • y) = f i x :=
      hConstOutside y hMonoAll
    have hOutsideZeroDom :
        ∀ j : {i : I // i ∉ I0},
          ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f j.1)),
            dotProduct xStar y = 0 := by
      intro j xStar hxStar
      exact
        helperForTheorem_21_4_dotProduct_zero_on_effectiveDomain_fenchelConjugate_of_constancy
          (g := f j.1) (hgProper := hfProper j.1) (hgClosed := hfClosed j.1) (d := y)
          (hConst := hOutsideConst j.1 j.2) xStar hxStar
    have hZeroDomK1 :
        ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1, dotProduct xStar y = 0 := by
      intro xStar hxStar
      by_cases hx0 : xStar = 0
      · simp [hx0]
      · exact
          helperForTheorem_21_4_dotProduct_zero_on_nonzero_effectiveDomain_posHomHullFamily
            (g := g1) (hgProper := hg1Proper) (y := y)
            (hZero := hOutsideZeroDom) hx0 hxStar
    have hdomK1_sub_H :
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1 ⊆ H := by
      intro xStar hxStar
      simpa [hHdef, hβ0] using hZeroDomK1 xStar hxStar
    exact hDomK1NotSubsetH hdomK1_sub_H
  let _ := hInterNonempty
  let C1 : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ | ∀ j : {i : I // i ∉ I0}, f j.1 x ≤ (0 : EReal)}
  have hAclosedConv :
      IsClosed A ∧ Convex ℝ A := by
    simpa [A] using
      helperForTheorem_21_4_affineFeasibleSet_closed_convex
        (f := f) (I0 := I0) (hfProper := hfProper) (hfClosed := hfClosed)
  let hAll : (Fin n → ℝ) → EReal :=
    convexHullFunctionFamily (fun i : I => fenchelConjugate n (f i))
  let kAll : (Fin n → ℝ) → EReal :=
    positivelyHomogeneousConvexFunctionGenerated hAll
  let g0 : J0 → (Fin n → ℝ) → EReal := fun i => fenchelConjugate n (f i.1)
  let h0 : (Fin n → ℝ) → EReal := convexHullFunctionFamily g0
  let k0fun : (Fin n → ℝ) → EReal := positivelyHomogeneousConvexFunctionGenerated h0
  have hfConjProper :
      ∀ i : I,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i)) := by
    intro i
    exact proper_fenchelConjugate_of_proper (n := n) (f := f i) (hfProper i)
  have hhAllMinor :=
    convexHullFunctionFamily_greatest_convex_minorant
      (f := fun i : I => fenchelConjugate n (f i))
  have hhAllConvOn :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) hAll := by
    simpa [hAll] using hhAllMinor.1
  have hhAllLe :
      ∀ i : I, hAll ≤ fun x => fenchelConjugate n (f i) x := by
    simpa [hAll] using hhAllMinor.2.1
  have hkAllmax :
      (∃ C : ConvexCone ℝ ((Fin n → ℝ) × ℝ),
        (C : Set ((Fin n → ℝ) × ℝ)) =
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) kAll ∧
        (0 : (Fin n → ℝ) × ℝ) ∈
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) kAll) ∧
      (ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) kAll ∧
        PositivelyHomogeneous kAll ∧
        kAll 0 ≤ 0 ∧
        kAll ≤ hAll) ∧
      (∀ u : (Fin n → ℝ) → EReal,
        PositivelyHomogeneous u →
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) u →
        u 0 ≤ 0 →
        u ≤ hAll →
        u ≤ kAll) := by
    simpa [hAll, kAll] using
      (maximality_posHomogeneousHull (n := n) (h := hAll) hhAllConvOn)
  have hkAllConvOn :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) kAll := hkAllmax.2.1.1
  have hkAllPos : PositivelyHomogeneous kAll := hkAllmax.2.1.2.1
  have hkAll0le : kAll 0 ≤ 0 := hkAllmax.2.1.2.2.1
  have hkAllLe : kAll ≤ hAll := hkAllmax.2.1.2.2.2
  have hg0Proper :
      ∀ i : J0, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g0 i) := by
    intro i
    simpa [g0] using hfConjProper i.1
  have hh0Minor := convexHullFunctionFamily_greatest_convex_minorant (f := g0)
  have hh0ConvOn :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h0 := by
    simpa [h0] using hh0Minor.1
  have hk0max :
      (∃ C : ConvexCone ℝ ((Fin n → ℝ) × ℝ),
        (C : Set ((Fin n → ℝ) × ℝ)) =
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) k0fun ∧
        (0 : (Fin n → ℝ) × ℝ) ∈
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) k0fun) ∧
      (ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k0fun ∧
        PositivelyHomogeneous k0fun ∧
        k0fun 0 ≤ 0 ∧
        k0fun ≤ h0) ∧
      (∀ u : (Fin n → ℝ) → EReal,
        PositivelyHomogeneous u →
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) u →
        u 0 ≤ 0 →
        u ≤ h0 →
        u ≤ k0fun) := by
    simpa [h0, k0fun] using
      (maximality_posHomogeneousHull (n := n) (h := h0) hh0ConvOn)
  have hk0funLe : k0fun ≤ h0 := hk0max.2.1.2.2.2
  have hAllLeH0 : hAll ≤ h0 := by
    exact hh0Minor.2.2 hAll hhAllConvOn (fun i => hhAllLe i.1)
  have hkAllLeH0 : kAll ≤ h0 := by
    exact le_trans hkAllLe hAllLeH0
  have hkAllLeK0 : kAll ≤ k0fun := by
    exact hk0max.2.2 kAll hkAllPos hkAllConvOn hkAll0le hkAllLeH0
  have hAllLeH1 : hAll ≤ h1 := by
    simpa [hAll] using hh1Minor.2.2 hAll hhAllConvOn (fun j => hhAllLe j.1)
  have hkAllLeK1 : kAll ≤ k1 := by
    exact hk1max.2.2 kAll hkAllPos hkAllConvOn hkAll0le (le_trans hkAllLe hAllLeH1)
  have hhFiniteAll : ∃ x : Fin n → ℝ, hAll x ≠ (⊤ : EReal) := by
    simpa [hAll] using
      (convexHullFunctionFamily_convex_and_exists_ne_top
        (hf := hfConjProper) (not_isEmpty_iff.mp hInonempty)).2
  suffices hkAll0_bot : kAll (0 : Fin n → ℝ) = (⊥ : EReal) by
    simpa [hAll, kAll] using
      helperForTheorem_21_4_convexHullConjugate_origin_neg_of_posHomHull_zero_bot
        hAll hhAllConvOn hhFiniteAll hkAll0_bot
  by_cases hI0empty : I0 = ∅
  · have hJ0empty : IsEmpty J0 := by
      refine ⟨?_⟩
      intro i
      exact Finset.notMem_empty i.1 (hI0empty ▸ i.2)
    have hrange_empty : Set.range b0 = (∅ : Set (Fin n → ℝ)) := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨i, rfl⟩
        exact (hJ0empty.false i).elim
      · intro hx
        exact False.elim hx
    have hK0zero : K0 = ({0} : Set (Fin n → ℝ)) := by
      unfold K0
      rw [hrange_empty, cone_eq_convexConeGenerated, convexConeGenerated_empty]
    have h1LeHAll : h1 ≤ hAll := by
      exact hhAllMinor.2.2 h1 hh1ConvOn (fun i => hh1Le ⟨i, by simpa [hI0empty]⟩)
    have hAllEqH1 : hAll = h1 := by
      funext x
      exact le_antisymm (hAllLeH1 x) (h1LeHAll x)
    have hkAllEqK1 : kAll = k1 := by
      simp [kAll, k1, hAllEqH1]
    rcases hInterNonempty with ⟨z, hznegK0, hzri⟩
    have hz0 : z = 0 := by
      have hzsingleton : z ∈ ({0} : Set (Fin n → ℝ)) := by
        simpa [hK0zero] using hznegK0
      simpa using hzsingleton
    have h0riK1 :
        (0 : EuclideanSpace ℝ (Fin n)) ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) := by
      let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
        EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
      let Ck1E : Set (EuclideanSpace ℝ (Fin n)) :=
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)
      letI :
          Nonempty ↥(affineSpan ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)) := by
        rcases hdomK1ne with ⟨x, hx⟩
        exact ⟨⟨x, subset_affineSpan (k := ℝ) (s := effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) hx⟩⟩
      letI :
          Nonempty ↥(affineSpan ℝ Ck1E) := by
        rcases hdomK1ne with ⟨x, hx⟩
        have hxE : e.symm x ∈ Ck1E := by
          simpa [Ck1E, e] using hx
        refine ⟨⟨e.symm x, ?_⟩⟩
        exact subset_affineSpan (k := ℝ) (s := Ck1E) hxE
      have h0intr :
          (0 : Fin n → ℝ) ∈
            intrinsicInterior ℝ
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) := by
        simpa [hz0] using hzri
      have hriCk1 :
          intrinsicInterior ℝ Ck1E =
            e.symm '' intrinsicInterior ℝ
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) := by
        have hCk1E :
            Ck1E = e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1 := by
          ext y
          constructor
          · intro hy
            refine ⟨(y : Fin n → ℝ), hy, ?_⟩
            simp [e]
          · rintro ⟨x, hx, rfl⟩
            simpa [Ck1E, e] using hx
        simpa [hCk1E] using
          (ContinuousLinearEquiv.image_intrinsicInterior
            (e := e.symm)
            (s := effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1))
      have h0intrE :
          (0 : EuclideanSpace ℝ (Fin n)) ∈
            intrinsicInterior ℝ Ck1E := by
        have hImg :
            (0 : EuclideanSpace ℝ (Fin n)) ∈
              e.symm '' intrinsicInterior ℝ
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) := by
          exact ⟨0, h0intr, by simp [e]⟩
        simpa [hriCk1] using hImg
      simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n)
        (C := Ck1E), Ck1E] using h0intrE
    have h0riAll :
        (0 : EuclideanSpace ℝ (Fin n)) ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) kAll) := by
      simpa [hkAllEqK1] using h0riK1
    have hfenchel_hAll :
        fenchelConjugate n hAll =
          fun x => sSup (Set.range fun i : I => convexFunctionClosure (f i) x) := by
      simpa [hAll] using
        (section16_fenchelConjugate_convexHullFunctionFamily_fenchelConjugate_eq_sSup_convexFunctionClosure
          (f := f) hfProper)
    have hsublevel_emptyAll :
        {x : Fin n → ℝ | fenchelConjugate n hAll x ≤ (0 : EReal)} = (∅ : Set (Fin n → ℝ)) := by
      ext x
      constructor
      · intro hx
        apply False.elim
        apply hNotPrimal
        refine ⟨x, ?_⟩
        intro i
        have hi_le : convexFunctionClosure (f i) x ≤ fenchelConjugate n hAll x := by
          rw [hfenchel_hAll]
          exact le_sSup ⟨i, rfl⟩
        have hClosedConv_i : ClosedConvexFunction (f i) := by
          refine ⟨?_,
            helperForTheorem_21_3_lowerSemicontinuous_of_closedEpigraph
              (f := f i) (hfClosed := hfClosed i)⟩
          simpa [ConvexFunction] using (hfProper i).1
        have hbot_i : ∀ y : Fin n → ℝ, f i y ≠ (⊥ : EReal) := by
          intro y
          exact (hfProper i).2.2 y (by simp)
        have hclosure_i :
            convexFunctionClosure (f i) = f i :=
          convexFunctionClosure_eq_of_closedConvexFunction
            (f := f i) hClosedConv_i hbot_i
        exact le_trans (by simpa [hclosure_i] using hi_le) hx
      · intro hx
        exact False.elim hx
    exact
      helperForTheorem_21_4_posHomHull_zero_bot_of_empty_conjugate_sublevel_and_zero_mem_ri
        hAll hhAllConvOn hhFiniteAll hsublevel_emptyAll h0riAll
  · have hI0nonempty : I0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hI0empty
    let i0 : J0 := ⟨hI0nonempty.choose, hI0nonempty.choose_spec⟩
    have hJ0 : Nonempty J0 := ⟨i0⟩
    have hh0Finite : ∃ x : Fin n → ℝ, h0 x ≠ (⊤ : EReal) := by
      simpa [h0] using
        (convexHullFunctionFamily_convex_and_exists_ne_top
          (hf := hg0Proper) hJ0).2
    have hh1Finite : ∃ x : Fin n → ℝ, h1 x ≠ (⊤ : EReal) := by
      simpa [h1] using
        (convexHullFunctionFamily_convex_and_exists_ne_top
          (hf := hg1Proper) hJ).2
    have hfenchel_h0 :
        fenchelConjugate n h0 =
          fun x => sSup (Set.range fun i : J0 => convexFunctionClosure (f i.1) x) := by
      simpa [h0, g0] using
        (section16_fenchelConjugate_convexHullFunctionFamily_fenchelConjugate_eq_sSup_convexFunctionClosure
          (f := fun i : J0 => f i.1)
          (fun i : J0 => hfProper i.1))
    have hfenchel_h1 :
        fenchelConjugate n h1 =
          fun x => sSup (Set.range fun j : {i : I // i ∉ I0} => convexFunctionClosure (f j.1) x) := by
      simpa [h1, g1] using
        (section16_fenchelConjugate_convexHullFunctionFamily_fenchelConjugate_eq_sSup_convexFunctionClosure
          (f := fun j : {i : I // i ∉ I0} => f j.1)
          (fun j : {i : I // i ∉ I0} => hfProper j.1))
    have hclosure_affine :
        ∀ i : J0, convexFunctionClosure (f i.1) = f i.1 := by
      intro i
      have hClosedConv_i : ClosedConvexFunction (f i.1) := by
        refine ⟨?_,
          helperForTheorem_21_3_lowerSemicontinuous_of_closedEpigraph
            (f := f i.1) (hfClosed := hfClosed i.1)⟩
        simpa [ConvexFunction] using (hfProper i.1).1
      have hbot_i : ∀ y : Fin n → ℝ, f i.1 y ≠ (⊥ : EReal) := by
        intro y
        exact (hfProper i.1).2.2 y (by simp)
      exact convexFunctionClosure_eq_of_closedConvexFunction
        (f := f i.1) hClosedConv_i hbot_i
    have hclosure_outside :
        ∀ j : {i : I // i ∉ I0}, convexFunctionClosure (f j.1) = f j.1 := by
      intro j
      have hClosedConv_j : ClosedConvexFunction (f j.1) := by
        refine ⟨?_,
          helperForTheorem_21_3_lowerSemicontinuous_of_closedEpigraph
            (f := f j.1) (hfClosed := hfClosed j.1)⟩
        simpa [ConvexFunction] using (hfProper j.1).1
      have hbot_j : ∀ y : Fin n → ℝ, f j.1 y ≠ (⊥ : EReal) := by
        intro y
        exact (hfProper j.1).2.2 y (by simp)
      exact convexFunctionClosure_eq_of_closedConvexFunction
        (f := f j.1) hClosedConv_j hbot_j
    have hAeq_sublevel_h0 :
        {x : Fin n → ℝ | fenchelConjugate n h0 x ≤ (0 : EReal)} = A := by
      ext x
      constructor
      · intro hx
        change ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)
        intro i hi
        let i' : J0 := ⟨i, hi⟩
        have hi_le : convexFunctionClosure (f i'.1) x ≤ fenchelConjugate n h0 x := by
          rw [hfenchel_h0]
          exact le_sSup ⟨i', rfl⟩
        exact le_trans (by simpa [hclosure_affine i'] using hi_le) hx
      · intro hx
        have hxA : ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal) := by
          simpa [A] using hx
        change fenchelConjugate n h0 x ≤ (0 : EReal)
        rw [hfenchel_h0]
        refine sSup_le ?_
        rintro y ⟨i, rfl⟩
        simpa [hclosure_affine i] using hxA i.1 i.2
    have hC1closed : IsClosed C1 := by
      have hclosed_each :
          ∀ j : {i : I // i ∉ I0}, IsClosed {x : Fin n → ℝ | f j.1 x ≤ (0 : EReal)} := by
        intro j
        exact
          closed_sublevel_of_closed_epigraph (f := f j.1) (by
            have hepigraph_univ :
                epigraph (S := (Set.univ : Set (Fin n → ℝ))) (f j.1) =
                  {p : (Fin n → ℝ) × ℝ | f j.1 p.1 ≤ (p.2 : EReal)} := by
              ext p
              constructor
              · intro hp
                exact hp.2
              · intro hp
                exact ⟨by trivial, hp⟩
            simpa [hepigraph_univ] using hfClosed j.1) 0
      simpa [C1, Set.setOf_forall] using isClosed_iInter hclosed_each
    have hC1conv : Convex ℝ C1 := by
      have hconv_each :
          ∀ j : {i : I // i ∉ I0}, Convex ℝ {x : Fin n → ℝ | f j.1 x ≤ (0 : EReal)} := by
        intro j
        exact
          (convexFunction_level_sets_convex
            (f := f j.1)
            (by simpa [ConvexFunction] using (hfProper j.1).1)
            (0 : EReal)).2
      simpa [C1, Set.setOf_forall] using convex_iInter hconv_each
    have hC1eq_sublevel_h1 :
        {x : Fin n → ℝ | fenchelConjugate n h1 x ≤ (0 : EReal)} = C1 := by
      ext x
      constructor
      · intro hx
        change ∀ j : {i : I // i ∉ I0}, f j.1 x ≤ (0 : EReal)
        intro j
        have hj_le : convexFunctionClosure (f j.1) x ≤ fenchelConjugate n h1 x := by
          rw [hfenchel_h1]
          exact le_sSup ⟨j, rfl⟩
        exact le_trans (by simpa [hclosure_outside j] using hj_le) hx
      · intro hx
        have hxC1 : ∀ j : {i : I // i ∉ I0}, f j.1 x ≤ (0 : EReal) := by
          simpa [C1] using hx
        change fenchelConjugate n h1 x ≤ (0 : EReal)
        rw [hfenchel_h1]
        refine sSup_le ?_
        rintro y ⟨j, rfl⟩
        simpa [hclosure_outside j] using hxC1 j
    have hclk0 :
        clConv n k0fun = supportFunctionEReal A := by
      simpa [hAeq_sublevel_h0] using
        (helperForTheorem_21_4_clConv_posHomGenerated_eq_supportFunctionEReal_setOf_fenchelConjugate_le_zero
          (n := n) h0 hh0ConvOn hh0Finite)
    have hclk1 :
        clConv n k1 = supportFunctionEReal C1 := by
      simpa [hC1eq_sublevel_h1] using
        (helperForTheorem_21_4_clConv_posHomGenerated_eq_supportFunctionEReal_setOf_fenchelConjugate_le_zero
          (n := n) h1 hh1ConvOn hh1Finite)
    have hk0star :
        fenchelConjugate n k0fun = indicatorFunction A := by
      calc
        fenchelConjugate n k0fun = fenchelConjugate n (clConv n k0fun) := by
          symm
          exact fenchelConjugate_clConv_eq (n := n) (f := k0fun)
        _ = fenchelConjugate n (supportFunctionEReal A) := by rw [hclk0]
        _ = indicatorFunction A := by
          exact (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
            (C := A) hAclosedConv.2 hAclosedConv.1).2
    have hk1star :
        fenchelConjugate n k1 = indicatorFunction C1 := by
      calc
        fenchelConjugate n k1 = fenchelConjugate n (clConv n k1) := by
          symm
          exact fenchelConjugate_clConv_eq (n := n) (f := k1)
        _ = fenchelConjugate n (supportFunctionEReal C1) := by rw [hclk1]
        _ = indicatorFunction C1 := by
          exact (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
            (C := C1) hC1conv hC1closed).2
    let g : (Fin n → ℝ) → EReal := fun z => k0fun (-z)
    have hgstar :
        fenchelConjugate n g = indicatorFunction (-A) := by
      calc
        fenchelConjugate n g = (fun xStar : Fin n → ℝ => fenchelConjugate n k0fun (-xStar)) := by
          simpa [g] using helperForTheorem_21_4_fenchelConjugate_precomp_neg (n := n) k0fun
        _ = (fun xStar : Fin n → ℝ => indicatorFunction A (-xStar)) := by
          simp [hk0star]
        _ = indicatorFunction (-A) := by
          funext xStar
          by_cases hx : -xStar ∈ A
          · have hxNeg : xStar ∈ -A := by simpa using hx
            simp [indicatorFunction, hx, hxNeg]
          · have hxNeg : xStar ∉ -A := by simpa using hx
            simp [indicatorFunction, hx, hxNeg]
    have hAplusC1_disjoint_zero :
        (0 : Fin n → ℝ) ∉ Set.image2 (· + ·) (-A) C1 := by
      intro h0sum
      rcases (by simpa [Set.image2] using h0sum) with ⟨u, huNegA, v, hvC1, huv⟩
      have huv' : v = u := by
        ext i
        have hcoord := congrArg (fun w : Fin n → ℝ => w i) huv
        have hcoord' : -u i + v i = 0 := by simpa using hcoord
        linarith
      have hvA : v ∈ A := by
        have huA : u ∈ A := by simpa using huNegA
        simpa [huv'] using huA
      exact hNotPrimalOnOutsideSubtype ⟨v, by simpa [A] using hvA, by simpa [C1] using hvC1⟩
    have hApoly : IsPolyhedralConvexSet n A := by
      let m0 : ℕ := Fintype.card J0
      let e0 : J0 ≃ Fin m0 := Fintype.equivFin J0
      let bA : Fin m0 → Fin n → ℝ := fun j => b0 (e0.symm j)
      let βA : Fin m0 → ℝ := fun j => α0 (e0.symm j)
      have hpoly :
          IsPolyhedralConvexSet n
            {x : Fin n → ℝ | ∀ j : Fin m0, x ⬝ᵥ bA j ≤ βA j} := by
        simpa using
          (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
            n 0 m0
            (fun i : Fin 0 => (0 : Fin n → ℝ))
            (fun i : Fin 0 => (0 : ℝ))
            bA βA)
      have hEq :
          {x : Fin n → ℝ | ∀ j : Fin m0, x ⬝ᵥ bA j ≤ βA j} = A := by
        ext x
        constructor
        · intro hx
          intro i hi
          let i0 : J0 := ⟨i, hi⟩
          have hineq : x ⬝ᵥ b0 i0 ≤ α0 i0 := by
            simpa [bA, βA, i0] using hx (e0 i0)
          have hreal : x ⬝ᵥ b0 i0 - α0 i0 ≤ 0 := by
            linarith
          have hereal :
              (((x ⬝ᵥ b0 i0 - α0 i0 : ℝ)) : EReal) ≤ (0 : EReal) := by
            exact_mod_cast hreal
          rw [ha0 i0 x, hb0 i0 x]
          exact hereal
        · intro hx
          intro j
          let i0 : J0 := e0.symm j
          have hx0 : f i0.1 x ≤ (0 : EReal) := hx i0.1 i0.2
          have hereal :
              (((x ⬝ᵥ b0 i0 - α0 i0 : ℝ)) : EReal) ≤ (0 : EReal) := by
            rw [ha0 i0 x, hb0 i0 x] at hx0
            exact hx0
          have hreal : x ⬝ᵥ b0 i0 - α0 i0 ≤ 0 := by
            exact_mod_cast hereal
          have hineq : x ⬝ᵥ b0 i0 ≤ α0 i0 := by
            linarith
          simpa [bA, βA, i0] using hineq
      simpa [hEq] using hpoly
    have hk0fun_dom_subset_K0 :
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) k0fun ⊆ K0 := by
      intro x hx
      by_cases hx0 : x = 0
      · simpa [hx0] using h0K0
      · rcases
            helperForTheorem_21_4_nonzero_effectiveDomain_posHomHullFamily_has_domainWitness
              (g := g0) (hgProper := hg0Proper) hx0 hx with
          ⟨m, _hm, idx, x', c, hcpos, hxsum, _hAff, hxDom⟩
        have hx'_eq :
            ∀ j : Fin m, x' j = b0 (idx j) := by
          intro j
          have hxj_dom :
              x' j ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
                (fenchelConjugate n (f (idx j).1)) := by
            simpa [g0] using hxDom j
          rw [hdom0_actual (idx j)] at hxj_dom
          simpa using hxj_dom
        have hK0cone : IsConvexCone n K0 := by
          simpa [K0, cone_eq_convexConeGenerated] using
            (isConvexCone_convexConeGenerated (n := n) (S₁ := Set.range b0))
        have hb0_memK0 : ∀ i : J0, b0 i ∈ K0 := by
          intro i
          unfold K0
          have hb0_ray : b0 i ∈ ray n (Set.range b0) :=
            mem_ray_of_mem (n := n) (S := Set.range b0) (x := b0 i) ⟨i, rfl⟩
          have hb0_conv : b0 i ∈ convexHull ℝ (ray n (Set.range b0)) :=
            (subset_convexHull (𝕜 := ℝ) (s := ray n (Set.range b0))) hb0_ray
          simpa [cone, conv] using hb0_conv
        have hterm :
            ∀ j : Fin m, c j • b0 (idx j) ∈ K0 := by
          intro j
          exact hK0cone.1 _ (hb0_memK0 (idx j)) _ (hcpos j)
        have hsumK0 :
            ∑ j : Fin m, c j • b0 (idx j) ∈ K0 := by
          refine Finset.induction_on (s := (Finset.univ : Finset (Fin m))) ?_ ?_
          · simpa using h0K0
          · intro a s ha hs
            let u : Fin n → ℝ := c a • b0 (idx a)
            let vSum : Fin n → ℝ := ∑ j ∈ s, c j • b0 (idx j)
            have hu_mem : u ∈ K0 := by
              simpa [u] using hterm a
            have hv_mem : vSum ∈ K0 := by
              simpa [vSum] using hs
            have hmid :
                (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • vSum ∈ K0 := by
              refine hK0cone.2 hu_mem hv_mem ?_ ?_ ?_
              · norm_num
              · norm_num
              · norm_num
            have hscale :
                (2 : ℝ) • ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • vSum) ∈ K0 :=
              hK0cone.1 _ hmid _ (by norm_num)
            have hsum_eq :
                (2 : ℝ) • ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • vSum) = u + vSum := by
              ext i
              simp [u, vSum]
              ring
            have hadd_mem : u + vSum ∈ K0 := by
              rw [← hsum_eq]
              exact hscale
            simpa [u, vSum, Finset.sum_insert, ha] using hadd_mem
        simpa [hxsum, hx'_eq] using hsumK0
    have hK0_subset_dom_k0fun :
        K0 ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) k0fun := by
      intro x hxK0
      have hk0funConv : ConvexFunction k0fun := by
        simpa [ConvexFunction] using hk0max.2.1.1
      have hk0funPos : PositivelyHomogeneous k0fun := hk0max.2.1.2.1
      have hAne : A.Nonempty := hA
      have hk0fun_ne_bot : ∀ y : Fin n → ℝ, k0fun y ≠ (⊥ : EReal) := by
        intro y hybot
        have hsupp_ne_bot :
            supportFunctionEReal A y ≠ (⊥ : EReal) :=
          section13_supportFunctionEReal_ne_bot_of_nonempty (C := A) hAne y
        have hcl_bot : clConv n k0fun y = (⊥ : EReal) := by
          have hle : clConv n k0fun y ≤ k0fun y := clConv_le (n := n) (f := k0fun) y
          exact le_antisymm (le_trans hle (by simpa [hybot])) bot_le
        rw [hclk0] at hcl_bot
        exact hsupp_ne_bot hcl_bot
      have hk0funSubadd :
          ∀ y z : Fin n → ℝ, k0fun (y + z) ≤ k0fun y + k0fun z :=
        subadditive_of_convex_posHom hk0funPos hk0funConv hk0fun_ne_bot
      have hk0fun0_ne_top : k0fun 0 ≠ (⊤ : EReal) := by
        intro hk0_top
        have : (⊤ : EReal) ≤ (0 : EReal) := by
          simpa [hk0_top] using hk0max.2.1.2.2.1
        exact (not_top_le_coe 0) this
      have hk0fun0_lt_top : k0fun 0 < (⊤ : EReal) :=
        (lt_top_iff_ne_top).2 hk0fun0_ne_top
      have hb0_dom :
          ∀ i : J0, b0 i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) k0fun := by
        intro i
        have hg0_dom :
            b0 i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (g0 i) := by
          change b0 i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (fenchelConjugate n (f i.1))
          rw [hdom0_actual i]
          simp
        have hg0_lt : g0 i (b0 i) < (⊤ : EReal) := by
          simpa [effectiveDomain_eq] using hg0_dom
        have hk0_lt : k0fun (b0 i) < (⊤ : EReal) := by
          have hk0_le : k0fun (b0 i) ≤ g0 i (b0 i) := by
            exact le_trans (hk0funLe (b0 i)) (hh0Minor.2.1 i (b0 i))
          exact lt_of_le_of_lt hk0_le hg0_lt
        simpa [effectiveDomain_eq] using
          (show b0 i ∈ {y : Fin n → ℝ | y ∈ Set.univ ∧ k0fun y < (⊤ : EReal)} from
            ⟨by simp, hk0_lt⟩)
      have hRange_ne : (Set.range b0).Nonempty := by
        rcases hJ0 with ⟨i⟩
        exact ⟨b0 i, ⟨i, rfl⟩⟩
      rcases
          mem_convexConeGenerated_imp_exists_nonnegLinearCombination_le
            (n := n) (T := Set.range b0) (x := x) hRange_ne
            (by simpa [K0, cone_eq_convexConeGenerated] using hxK0) with
        ⟨m, _hm, v, c, hv, hc, hxsum⟩
      let iv : Fin m → J0 := fun j => Classical.choose (hv j)
      have hiv : ∀ j : Fin m, b0 (iv j) = v j := by
        intro j
        exact Classical.choose_spec (hv j)
      have hterm_lt :
          ∀ j : Fin m, k0fun (c j • v j) < (⊤ : EReal) := by
        intro j
        by_cases hc0 : c j = 0
        · simpa [hc0] using hk0fun0_lt_top
        · have hcpos : 0 < c j := lt_of_le_of_ne (hc j) (Ne.symm hc0)
          have hv_lt : k0fun (v j) < (⊤ : EReal) := by
            have hiv_dom : b0 (iv j) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) k0fun :=
              hb0_dom (iv j)
            have hlt : k0fun (b0 (iv j)) < (⊤ : EReal) := by
              simpa [effectiveDomain_eq] using hiv_dom
            simpa [hiv j] using hlt
          have hmul_ne_top :
              (((c j : ℝ) : EReal) * k0fun (v j)) ≠ (⊤ : EReal) := by
            refine (EReal.mul_ne_top _ _).2 ?_
            refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hk0fun_ne_bot (v j)),
              Or.inl (EReal.coe_ne_top _), Or.inr ((lt_top_iff_ne_top).1 hv_lt)⟩
          have hmul_lt :
              (((c j : ℝ) : EReal) * k0fun (v j)) < (⊤ : EReal) :=
            (lt_top_iff_ne_top).2 hmul_ne_top
          have hhom :
              k0fun (c j • v j) = (((c j : ℝ) : EReal) * k0fun (v j)) := by
            simpa using hk0funPos (v j) (c j) hcpos
          rw [hhom]
          exact hmul_lt
      have hsum_lt :
          k0fun (∑ j : Fin m, c j • v j) < (⊤ : EReal) := by
        have hsum_lt_aux :
            ∀ s : Finset (Fin m),
              k0fun (Finset.sum s (fun j => c j • v j)) < (⊤ : EReal) := by
          intro s
          refine Finset.induction_on s ?_ ?_
          · simpa using hk0fun0_lt_top
          · intro a s ha hs
            have ha_lt : k0fun (c a • v a) < (⊤ : EReal) := hterm_lt a
            have hsum_ne_top :
                k0fun (c a • v a) + k0fun (Finset.sum s (fun j => c j • v j)) ≠ (⊤ : EReal) := by
              exact EReal.add_ne_top ((lt_top_iff_ne_top).1 ha_lt) ((lt_top_iff_ne_top).1 hs)
            have hsum_pair_lt :
                k0fun (c a • v a) + k0fun (Finset.sum s (fun j => c j • v j)) < (⊤ : EReal) :=
              (lt_top_iff_ne_top).2 hsum_ne_top
            have hsub :=
              hk0funSubadd (c a • v a) (Finset.sum s (fun j => c j • v j))
            exact
              lt_of_le_of_lt
                (by simpa [Finset.sum_insert, ha] using hsub)
                hsum_pair_lt
        simpa [hxsum] using hsum_lt_aux (Finset.univ : Finset (Fin m))
      have hk0_lt_top :
          k0fun x < (⊤ : EReal) := by simpa [hxsum] using hsum_lt
      simpa [effectiveDomain_eq] using
        (show x ∈ {y : Fin n → ℝ | y ∈ Set.univ ∧ k0fun y < (⊤ : EReal)} from
          ⟨by simp, hk0_lt_top⟩)
    have hdom_k0fun_eq_K0 :
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) k0fun = K0 :=
      Set.Subset.antisymm hk0fun_dom_subset_K0 hK0_subset_dom_k0fun
    have hk0fun_proper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k0fun := by
      have hAne : A.Nonempty := hA
      have hk0fun_ne_bot : ∀ y : Fin n → ℝ, k0fun y ≠ (⊥ : EReal) := by
        intro y hybot
        have hsupp_ne_bot :
            supportFunctionEReal A y ≠ (⊥ : EReal) :=
          section13_supportFunctionEReal_ne_bot_of_nonempty (C := A) hAne y
        have hcl_bot : clConv n k0fun y = (⊥ : EReal) := by
          have hle : clConv n k0fun y ≤ k0fun y := clConv_le (n := n) (f := k0fun) y
          exact le_antisymm (le_trans hle (by simpa [hybot])) bot_le
        rw [hclk0] at hcl_bot
        exact hsupp_ne_bot hcl_bot
      refine
        (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
          (S := (Set.univ : Set (Fin n → ℝ))) (f := k0fun)).2 ?_
      refine ⟨hk0max.2.1.1, ?_, ?_⟩
      · exact ⟨0, by simpa [hdom_k0fun_eq_K0] using h0K0⟩
      · intro y hy
        exact ⟨hk0fun_ne_bot y,
          mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := k0fun) hy⟩
    have hk0funPos : PositivelyHomogeneous k0fun := hk0max.2.1.2.1
    have hk0funConv : ConvexFunction k0fun := by
      simpa [ConvexFunction] using hk0max.2.1.1
    have hk0fun_ne_bot : ∀ y : Fin n → ℝ, k0fun y ≠ (⊥ : EReal) := by
      intro y
      exact hk0fun_proper.2.2 y (by simp)
    have hk0funSubadd :
        ∀ y z : Fin n → ℝ, k0fun (y + z) ≤ k0fun y + k0fun z :=
      subadditive_of_convex_posHom hk0funPos hk0funConv hk0fun_ne_bot
    have hk0fun0_eq_zero : k0fun 0 = (0 : EReal) := by
      have hnonneg : (0 : EReal) ≤ k0fun 0 :=
        posHom_zero_nonneg (hpos := hk0funPos) (hproper := hk0fun_proper)
      exact le_antisymm hk0max.2.1.2.2.1 hnonneg
    have hk0fun_poly : IsPolyhedralConvexFunction n k0fun := by
      let m0 : ℕ := Fintype.card J0
      let e0 : J0 ≃ Fin m0 := Fintype.equivFin J0
      let aFG : Fin (m0 + 1) → Fin n → ℝ :=
        Fin.cases (0 : Fin n → ℝ) (fun j => b0 (e0.symm j))
      let αFG : Fin (m0 + 1) → ℝ :=
        Fin.cases (0 : ℝ) (fun j => α0 (e0.symm j))
      let Rfixed := fun x : Fin n → ℝ =>
        {r : EReal |
          ∃ lam : Fin (m0 + 1) → ℝ,
            (∀ j, (∑ i, lam i * aFG i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin (m0 + 1) => (i : ℕ) < 1))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i) ∧
            r = ((∑ i, lam i * αFG i : ℝ) : EReal)}
      have hg0_at_b0 :
          ∀ i : J0, g0 i (b0 i) = (α0 i : EReal) := by
        intro i
        rcases
            helperForTheorem_21_4_fenchelConjugate_affine_eq_indicator_singleton_add_const (a0 i) with
          ⟨b, β, hb, hconj⟩
        have hdom_conj :
            effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fenchelConjugate n (fun x : Fin n → ℝ => (a0 i x : EReal))) =
                ({b} : Set (Fin n → ℝ)) := by
          ext xStar
          by_cases hx : xStar = b
          · have hxlt :
                indicatorFunction ({b} : Set (Fin n → ℝ)) b + (β : EReal) < (⊤ : EReal) := by
              simp [indicatorFunction]
            simpa [hconj, effectiveDomain_eq, hx] using hxlt
          · have htop :
                indicatorFunction ({b} : Set (Fin n → ℝ)) xStar + (β : EReal) = (⊤ : EReal) := by
              simp [indicatorFunction, hx]
            simp [hconj, effectiveDomain_eq, hx, htop]
        have hb_eq : b = b0 i := by
          exact Eq.symm (by simpa [hdom0 i] using hdom_conj)
        have hβ_eq : β = α0 i := by
          have hzero_repr :
              (0 : Fin n → ℝ) ⬝ᵥ b0 i - β = (0 : Fin n → ℝ) ⬝ᵥ b0 i - α0 i := by
            calc
              (0 : Fin n → ℝ) ⬝ᵥ b0 i - β = a0 i 0 := by simpa [hb_eq] using (hb 0).symm
              _ = (0 : Fin n → ℝ) ⬝ᵥ b0 i - α0 i := hb0 i 0
          simp at hzero_repr
          linarith
        have hfi_eq : f i.1 = fun x : Fin n → ℝ => (a0 i x : EReal) := by
          funext x
          exact ha0 i x
        have hformula :
            fenchelConjugate n (fun x : Fin n → ℝ => (a0 i x : EReal)) (b0 i) =
              indicatorFunction ({b0 i} : Set (Fin n → ℝ)) (b0 i) + (α0 i : EReal) := by
          simpa [hconj, hb_eq, hβ_eq]
        simpa [g0, hfi_eq, indicatorFunction] using hformula
      have hfixed_upper :
          ∀ x : Fin n → ℝ, ∀ r : EReal, r ∈ Rfixed x → k0fun x ≤ r := by
        intro x r hr
        rcases hr with ⟨lam, hlin, hnorm, hnonneg, rfl⟩
        have hsum0 : lam 0 = 1 := by
          have hnorm' :
              Finset.sum
                (Finset.univ.filter (fun i : Fin (m0 + 1) => i = 0))
                (fun i => lam i) = 1 := by
            simpa [Nat.lt_one_iff] using hnorm
          have hzero_filter :
              (Finset.univ.filter (fun i : Fin (m0 + 1) => i = 0)) =
                ({0} : Finset (Fin (m0 + 1))) := by
            ext i
            simp
          have hnorm'' :
              Finset.sum ({0} : Finset (Fin (m0 + 1))) (fun i => lam i) = 1 := by
            simpa [hzero_filter] using hnorm'
          simpa using hnorm''
        have hxsum :
            x = ∑ j : Fin m0, lam (Fin.succ j) • b0 (e0.symm j) := by
          ext j
          have hlinj := hlin j
          simpa [aFG, Fin.sum_univ_succ, hsum0] using hlinj.symm
        have hterm :
            ∀ j : Fin m0,
              k0fun (lam (Fin.succ j) • b0 (e0.symm j)) ≤
                ((lam (Fin.succ j) * α0 (e0.symm j) : ℝ) : EReal) := by
          intro j
          by_cases hzero : lam (Fin.succ j) = 0
          · simp [hzero, hk0fun0_eq_zero]
          · have hpos : 0 < lam (Fin.succ j) :=
              lt_of_le_of_ne (hnonneg (Fin.succ j)) (Ne.symm hzero)
            have hbase :
                k0fun (b0 (e0.symm j)) ≤ (α0 (e0.symm j) : EReal) := by
              have hle :
                  k0fun (b0 (e0.symm j)) ≤ g0 (e0.symm j) (b0 (e0.symm j)) := by
                exact le_trans (hk0funLe (b0 (e0.symm j))) (hh0Minor.2.1 (e0.symm j) _)
              simpa [hg0_at_b0] using hle
            have hmul :=
              ereal_mul_le_mul_of_pos_left (t := lam (Fin.succ j)) hpos hbase
            have hhom :
                k0fun (lam (Fin.succ j) • b0 (e0.symm j)) =
                  (((lam (Fin.succ j) : ℝ) : EReal) * k0fun (b0 (e0.symm j))) := by
              simpa using hk0funPos (b0 (e0.symm j)) (lam (Fin.succ j)) hpos
            calc
              k0fun (lam (Fin.succ j) • b0 (e0.symm j)) =
                  (((lam (Fin.succ j) : ℝ) : EReal) * k0fun (b0 (e0.symm j))) := hhom
              _ ≤ (((lam (Fin.succ j) : ℝ) : EReal) * (α0 (e0.symm j) : EReal)) := hmul
              _ = ((lam (Fin.succ j) * α0 (e0.symm j) : ℝ) : EReal) := by simp [EReal.coe_mul]
        have hsum_le :
            k0fun (∑ j : Fin m0, lam (Fin.succ j) • b0 (e0.symm j)) ≤
              ∑ j : Fin m0, (((lam (Fin.succ j) * α0 (e0.symm j) : ℝ)) : EReal) := by
          refine Finset.induction_on (s := (Finset.univ : Finset (Fin m0))) ?_ ?_
          · simpa [hk0fun0_eq_zero]
          · intro a s ha hs
            have hsub :=
              hk0funSubadd (lam (Fin.succ a) • b0 (e0.symm a))
                (∑ j ∈ s, lam (Fin.succ j) • b0 (e0.symm j))
            have hs' :
                k0fun (∑ j ∈ s, lam (Fin.succ j) • b0 (e0.symm j)) ≤
                  ∑ j ∈ s, (((lam (Fin.succ j) * α0 (e0.symm j) : ℝ)) : EReal) := by
              simpa using hs
            calc
              k0fun (∑ j ∈ insert a s, lam (Fin.succ j) • b0 (e0.symm j))
                  ≤ k0fun (lam (Fin.succ a) • b0 (e0.symm a)) +
                      k0fun (∑ j ∈ s, lam (Fin.succ j) • b0 (e0.symm j)) := by
                        simpa [Finset.sum_insert, ha] using hsub
              _ ≤ (((lam (Fin.succ a) * α0 (e0.symm a) : ℝ)) : EReal) +
                    ∑ j ∈ s, (((lam (Fin.succ j) * α0 (e0.symm j) : ℝ)) : EReal) := by
                      gcongr
                      exact hterm a
              _ = ∑ j ∈ insert a s, (((lam (Fin.succ j) * α0 (e0.symm j) : ℝ)) : EReal) := by
                    simp [Finset.sum_insert, ha]
        calc
          k0fun x =
              k0fun (∑ j : Fin m0, lam (Fin.succ j) • b0 (e0.symm j)) := by rw [hxsum]
          _ ≤ ∑ j : Fin m0, (((lam (Fin.succ j) * α0 (e0.symm j) : ℝ)) : EReal) := hsum_le
          _ = ((∑ i, lam i * αFG i : ℝ) : EReal) := by
                rw [show ∑ j : Fin m0, (((lam (Fin.succ j) * α0 (e0.symm j) : ℝ)) : EReal) =
                    (((∑ j : Fin m0, lam (Fin.succ j) * α0 (e0.symm j) : ℝ)) : EReal) by
                      exact (helperForTheorem_21_1_coe_finset_sum_real
                        (s := (Finset.univ : Finset (Fin m0)))
                        (g := fun j : Fin m0 => lam (Fin.succ j) * α0 (e0.symm j))).symm]
                simp [αFG, Fin.sum_univ_succ, hsum0]
      have hk0_repr_fixed :
          ∀ x : Fin n → ℝ, k0fun x = sInf (Rfixed x) := by
        intro x
        by_cases hx0 : x = 0
        · have hle : k0fun x ≤ sInf (Rfixed x) := by
            refine le_sInf ?_
            intro r hr
            exact hfixed_upper x r hr
          have hmem :
              ((0 : ℝ) : EReal) ∈ Rfixed x := by
            let lam0 : Fin (m0 + 1) → ℝ := fun i => if i = 0 then 1 else 0
            refine ⟨lam0, ?_, ?_, ?_, ?_⟩
            · intro j
              subst hx0
              simp [lam0, aFG, Fin.sum_univ_succ]
            · simp [lam0, Nat.lt_one_iff]
            · intro i
              by_cases hi : i = 0
              · simp [lam0, hi]
              · simp [lam0, hi]
            · simp [lam0, αFG, Fin.sum_univ_succ]
          have hge : sInf (Rfixed x) ≤ (0 : EReal) := sInf_le hmem
          subst hx0
          exact le_antisymm hle (by simpa [hk0fun0_eq_zero] using hge)
        · have hk_repr_dyn :
            k0fun x =
              sInf { z : EReal |
                ∃ m : Nat, m ≤ n + 1 ∧
                  ∃ (idx : Fin m → J0) (x' : Fin m → Fin n → ℝ) (c : Fin m → ℝ),
                    (∀ j, 0 < c j) ∧
                      x = ∑ j, c j • x' j ∧
                      AffineIndependent ℝ x' ∧
                      z = ∑ j, ((c j : ℝ) : EReal) * g0 (idx j) (x' j) } := by
            change positivelyHomogeneousConvexFunctionGenerated (convexHullFunctionFamily g0) x = _
            exact
              positivelyHomogeneousConvexFunctionGenerated_convexHullFunctionFamily_eq_sInf_linearIndependent_nonnegLinearCombination_le
                (fᵢ := g0) hg0Proper x hx0
          have hleft : k0fun x ≤ sInf (Rfixed x) := by
            refine le_sInf ?_
            intro r hr
            exact hfixed_upper x r hr
          have hright :
              sInf (Rfixed x) ≤
                sInf { z : EReal |
                  ∃ m : Nat, m ≤ n + 1 ∧
                    ∃ (idx : Fin m → J0) (x' : Fin m → Fin n → ℝ) (c : Fin m → ℝ),
                      (∀ j, 0 < c j) ∧
                        x = ∑ j, c j • x' j ∧
                        AffineIndependent ℝ x' ∧
                        z = ∑ j, ((c j : ℝ) : EReal) * g0 (idx j) (x' j) } := by
            refine le_sInf ?_
            intro z hz
            rcases hz with ⟨m, hm, idx, x', c, hcpos, hxsum, hAff, hzEq⟩
            by_cases hztop : z = (⊤ : EReal)
            · simpa [hztop] using (le_top : sInf (Rfixed x) ≤ (⊤ : EReal))
            · have hxDom :
                ∀ j : Fin m, x' j ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (g0 (idx j)) := by
                intro j
                have hterm_ne_top :
                    g0 (idx j) (x' j) ≠ (⊤ : EReal) := by
                  intro htop
                  have hsum_top :
                      ∑ k : Fin m, ((c k : ℝ) : EReal) * g0 (idx k) (x' k) = (⊤ : EReal) := by
                    exact
                      sum_eq_top_of_term_top (s := (Finset.univ : Finset (Fin m)))
                        (f := fun k : Fin m => ((c k : ℝ) : EReal) * g0 (idx k) (x' k))
                        (i := j) (by simp)
                        (by
                          simpa [htop] using EReal.mul_top_of_pos
                            (x := ((c j : ℝ) : EReal)) (by exact_mod_cast hcpos j))
                        (by
                          intro k hk
                          have hnotbot : g0 (idx k) (x' k) ≠ (⊥ : EReal) :=
                            (hg0Proper (idx k)).2.2 _ (by simp)
                          exact ereal_mul_ne_bot_of_pos (hcpos k) hnotbot)
                  exact hztop (by simpa [hzEq] using hsum_top)
                simpa [effectiveDomain_eq] using
                  (show x' j ∈ {y : Fin n → ℝ | y ∈ Set.univ ∧ g0 (idx j) y < (⊤ : EReal)} from
                    ⟨by simp, (lt_top_iff_ne_top).2 hterm_ne_top⟩)
              have hx'_eq :
                  ∀ j : Fin m, x' j = b0 (idx j) := by
                intro j
                have hxDomj := hxDom j
                rw [hdom0_actual (idx j)] at hxDomj
                simpa using hxDomj
              let lamSucc : Fin m0 → ℝ :=
                fun j =>
                  Finset.sum
                    (Finset.univ.filter (fun t : Fin m => idx t = e0.symm j))
                    (fun t => c t)
              have hmaps :
                  ∀ t ∈ (Finset.univ : Finset (Fin m)), e0 (idx t) ∈ (Finset.univ : Finset (Fin m0)) := by
                intro t ht
                simp
              have hmaps0 :
                  ∀ t ∈ (Finset.univ : Finset (Fin m)), idx t ∈ (Finset.univ : Finset J0) := by
                intro t ht
                simp
              have hx_grouped :
                  x = ∑ j : Fin m0, lamSucc j • b0 (e0.symm j) := by
                have hreindex_u (u : Fin n) :
                    (∑ j : Fin m0,
                        Finset.sum
                          (Finset.univ.filter (fun t : Fin m => idx t = e0.symm j))
                          (fun t => c t * b0 (e0.symm j) u)) =
                      ∑ j : J0,
                        Finset.sum
                          (Finset.univ.filter (fun t : Fin m => idx t = j))
                          (fun t => c t * b0 j u) := by
                  refine Fintype.sum_equiv e0.symm
                    (fun j : Fin m0 =>
                      Finset.sum
                        (Finset.univ.filter (fun t : Fin m => idx t = e0.symm j))
                        (fun t => c t * b0 (e0.symm j) u))
                    (fun j : J0 =>
                      Finset.sum
                        (Finset.univ.filter (fun t : Fin m => idx t = j))
                        (fun t => c t * b0 j u)) ?_
                  intro j
                  simp
                have hfiber_u (u : Fin n) :
                    (∑ j : J0,
                        Finset.sum
                          (Finset.univ.filter (fun t : Fin m => idx t = j))
                          (fun t => c t * b0 j u)) =
                      ∑ t : Fin m, c t * b0 (idx t) u := by
                  calc
                    (∑ j : J0,
                        Finset.sum
                          (Finset.univ.filter (fun t : Fin m => idx t = j))
                          (fun t => c t * b0 j u)) =
                      ∑ j : J0,
                        Finset.sum
                          (Finset.univ.filter (fun t : Fin m => idx t = j))
                          (fun t => c t * b0 (idx t) u) := by
                        refine Fintype.sum_congr (fun j : J0 =>
                          Finset.sum
                            (Finset.univ.filter (fun t : Fin m => idx t = j))
                            (fun t => c t * b0 j u))
                          (fun j : J0 =>
                            Finset.sum
                              (Finset.univ.filter (fun t : Fin m => idx t = j))
                              (fun t => c t * b0 (idx t) u)) ?_
                        intro j
                        refine Finset.sum_congr rfl ?_
                        intro t ht
                        have ht' : idx t = j := by
                          simpa using ht
                        simp [ht']
                    _ = ∑ t : Fin m, c t * b0 (idx t) u := by
                        simpa using
                          (Finset.sum_fiberwise_of_maps_to
                            (s := (Finset.univ : Finset (Fin m)))
                            (t := (Finset.univ : Finset J0))
                            (g := idx)
                            (f := fun t : Fin m => c t * b0 (idx t) u) hmaps0)
                calc
                  x = ∑ t : Fin m, c t • b0 (idx t) := by simpa [hx'_eq] using hxsum
                  _ = ∑ j : Fin m0, lamSucc j • b0 (e0.symm j) := by
                    symm
                    ext u
                    simp [lamSucc, Finset.sum_smul]
                    exact (hreindex_u u).trans (hfiber_u u)
              have hobj_grouped :
                  z = ((∑ j : Fin m0, lamSucc j * α0 (e0.symm j) : ℝ) : EReal) := by
                rw [hzEq]
                have hterm :
                    ∀ j : Fin m,
                      ((c j : ℝ) : EReal) * g0 (idx j) (x' j) =
                        ((c j * α0 (idx j) : ℝ) : EReal) := by
                  intro j
                  rw [hx'_eq j, hg0_at_b0 (idx j)]
                  simp [EReal.coe_mul]
                rw [show ∑ j : Fin m, ((c j : ℝ) : EReal) * g0 (idx j) (x' j) =
                    ∑ j : Fin m, ((c j * α0 (idx j) : ℝ) : EReal) by
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      exact hterm j]
                have hgroup_real :
                    ∑ j : Fin m0, lamSucc j * α0 (e0.symm j) =
                      ∑ t : Fin m, c t * α0 (idx t) := by
                  have hreindex_alpha :
                      (∑ j : Fin m0,
                          Finset.sum
                            (Finset.univ.filter (fun t : Fin m => idx t = e0.symm j))
                            (fun t => c t * α0 (e0.symm j))) =
                        ∑ j : J0,
                          Finset.sum
                            (Finset.univ.filter (fun t : Fin m => idx t = j))
                            (fun t => c t * α0 j) := by
                    refine Fintype.sum_equiv e0.symm
                      (fun j : Fin m0 =>
                        Finset.sum
                          (Finset.univ.filter (fun t : Fin m => idx t = e0.symm j))
                          (fun t => c t * α0 (e0.symm j)))
                      (fun j : J0 =>
                        Finset.sum
                          (Finset.univ.filter (fun t : Fin m => idx t = j))
                          (fun t => c t * α0 j)) ?_
                    intro j
                    simp
                  have hfiber_alpha :
                      (∑ j : J0,
                          Finset.sum
                            (Finset.univ.filter (fun t : Fin m => idx t = j))
                            (fun t => c t * α0 j)) =
                        ∑ t : Fin m, c t * α0 (idx t) := by
                    calc
                      (∑ j : J0,
                          Finset.sum
                            (Finset.univ.filter (fun t : Fin m => idx t = j))
                            (fun t => c t * α0 j)) =
                        ∑ j : J0,
                          Finset.sum
                            (Finset.univ.filter (fun t : Fin m => idx t = j))
                            (fun t => c t * α0 (idx t)) := by
                          refine Fintype.sum_congr (fun j : J0 =>
                            Finset.sum
                              (Finset.univ.filter (fun t : Fin m => idx t = j))
                              (fun t => c t * α0 j))
                            (fun j : J0 =>
                              Finset.sum
                                (Finset.univ.filter (fun t : Fin m => idx t = j))
                                (fun t => c t * α0 (idx t))) ?_
                          intro j
                          refine Finset.sum_congr rfl ?_
                          intro t ht
                          have ht' : idx t = j := by
                            simpa using ht
                          simp [ht']
                      _ = ∑ t : Fin m, c t * α0 (idx t) := by
                          simpa using
                            (Finset.sum_fiberwise_of_maps_to
                              (s := (Finset.univ : Finset (Fin m)))
                              (t := (Finset.univ : Finset J0))
                              (g := idx)
                              (f := fun t : Fin m => c t * α0 (idx t)) hmaps0)
                  calc
                    ∑ j : Fin m0, lamSucc j * α0 (e0.symm j)
                        = ∑ j : Fin m0,
                            Finset.sum
                              (Finset.univ.filter (fun t : Fin m => idx t = e0.symm j))
                              (fun t => c t * α0 (e0.symm j)) := by
                            refine Finset.sum_congr rfl ?_
                            intro j hj
                            change
                              (Finset.sum
                                (Finset.univ.filter (fun t : Fin m => idx t = e0.symm j))
                                (fun t => c t)) * α0 (e0.symm j) =
                                Finset.sum
                                  (Finset.univ.filter (fun t : Fin m => idx t = e0.symm j))
                                  (fun t => c t * α0 (e0.symm j))
                            rw [Finset.sum_mul]
                    _ = ∑ t : Fin m, c t * α0 (idx t) := by
                        exact hreindex_alpha.trans hfiber_alpha
                rw [show ∑ j : Fin m, ((c j * α0 (idx j) : ℝ) : EReal) =
                    (((∑ j : Fin m, c j * α0 (idx j) : ℝ)) : EReal) by
                      exact (helperForTheorem_21_1_coe_finset_sum_real
                        (s := (Finset.univ : Finset (Fin m)))
                        (g := fun j : Fin m => c j * α0 (idx j))).symm]
                simp [hgroup_real]
              have hmem_fixed :
                  z ∈ Rfixed x := by
                refine ⟨Fin.cases (1 : ℝ) lamSucc, ?_, ?_, ?_, ?_⟩
                · intro u
                  have hu := congrArg (fun v : Fin n → ℝ => v u) hx_grouped
                  simpa [aFG, Fin.sum_univ_succ] using hu.symm
                · have hzero_filter :
                      (Finset.univ.filter (fun i : Fin (m0 + 1) => i = 0)) =
                        ({0} : Finset (Fin (m0 + 1))) := by
                    ext i
                    simp
                  simpa [hzero_filter]
                · intro i
                  refine Fin.cases ?_ ?_ i
                  · norm_num
                  · intro j
                    simpa [lamSucc] using
                      (Finset.sum_nonneg (by
                        intro t ht
                        exact (hcpos t).le))
                · simpa [αFG, Fin.sum_univ_succ] using hobj_grouped
              exact sInf_le hmem_fixed
          have hright' : sInf (Rfixed x) ≤ k0fun x := by
            rw [hk_repr_dyn]
            exact hright
          exact le_antisymm hleft hright'
      have hfgen : IsFinitelyGeneratedConvexFunction n k0fun := by
        refine ⟨hk0max.2.1.1, ?_⟩
        refine ⟨1, m0 + 1, aFG, αFG, by omega, hk0_repr_fixed⟩
      exact
        helperForCorollary_19_1_2_finitelyGenerated_imp_polyhedral
          (n := n) (f := k0fun) hfgen
    let g : (Fin n → ℝ) → EReal := fun z => k0fun (-z)
    have hdom_g_eq_negK0 :
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) g = -K0 := by
      ext z
      constructor
      · intro hz
        have hzlt : k0fun (-z) < (⊤ : EReal) := by
          simpa [g, effectiveDomain_eq] using hz
        have hzdom : -z ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) k0fun := by
          simpa [effectiveDomain_eq] using
            (show -z ∈ {y : Fin n → ℝ | y ∈ Set.univ ∧ k0fun y < (⊤ : EReal)} from
              ⟨by simp, hzlt⟩)
        simpa [hdom_k0fun_eq_K0] using hzdom
      · intro hz
        have hzdom : -z ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) k0fun := by
          simpa [hdom_k0fun_eq_K0] using hz
        have hzlt : k0fun (-z) < (⊤ : EReal) := by
          simpa [effectiveDomain_eq] using hzdom
        simpa [g, effectiveDomain_eq] using
          (show z ∈ {y : Fin n → ℝ | y ∈ Set.univ ∧ k0fun (-y) < (⊤ : EReal)} from
            ⟨by simp, hzlt⟩)
    by_cases hproperK1 : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k1
    ·
      have hproperG :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
        let Aneg : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
          { toFun := fun x => -x
            invFun := fun x => -x
            left_inv := by intro x; simp
            right_inv := by intro x; simp
            map_add' := by
              intro x y
              ext i
              simp [add_comm]
            map_smul' := by intro t x; simp [smul_neg] }
        simpa [g, Aneg] using
          properConvexFunctionOn_precomp_linearEquiv (n := n) Aneg hk0fun_proper
      have hgpoly : IsPolyhedralConvexFunction n g := by
        let AnegL : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
          { toFun := fun x => -x
            map_add' := by
              intro x y
              ext i
              simp [add_comm]
            map_smul' := by intro t x; ext i <;> simp [smul_neg] }
        simpa [g, inverseImageUnderLinearMap, AnegL] using
          helperForCorollary_19_3_1_polyhedral_inverseImageUnderLinearMap
            (n := n) (m := n) (A := AnegL) (g := k0fun) hk0fun_poly
      have hnonemptyDomInterRi_gk1 :
          Set.Nonempty
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)
              ∩
              euclideanRelativeInterior n
                ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)) := by
        let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
          EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
        let Ck1E : Set (EuclideanSpace ℝ (Fin n)) :=
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)
        rcases hInterNonempty with ⟨z0, hz0negK0, hz0ri⟩
        have hz0_dom_g : z0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
          simpa [hdom_g_eq_negK0] using hz0negK0
        have hz0riE :
            e.symm z0 ∈ euclideanRelativeInterior n Ck1E := by
          letI :
              Nonempty ↥(affineSpan ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)) := by
            rcases hdomK1ne with ⟨x, hx⟩
            exact ⟨⟨x, subset_affineSpan (k := ℝ)
              (s := effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) hx⟩⟩
          letI :
              Nonempty ↥(affineSpan ℝ Ck1E) := by
            rcases hdomK1ne with ⟨x, hx⟩
            have hxE : e.symm x ∈ Ck1E := by
              simpa [Ck1E, e] using hx
            refine ⟨⟨e.symm x, ?_⟩⟩
            exact subset_affineSpan (k := ℝ) (s := Ck1E) hxE
          have hriCk1 :
              intrinsicInterior ℝ Ck1E =
                e.symm '' intrinsicInterior ℝ
                  (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) := by
            have hCk1E :
                Ck1E = e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1 := by
              ext y
              constructor
              · intro hy
                refine ⟨(y : Fin n → ℝ), hy, ?_⟩
                simp [e]
              · rintro ⟨x, hx, rfl⟩
                simpa [Ck1E, e] using hx
            simpa [hCk1E] using
              (ContinuousLinearEquiv.image_intrinsicInterior
                (e := e.symm)
                (s := effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1))
          have hz0ri_intrE :
              e.symm z0 ∈ intrinsicInterior ℝ Ck1E := by
            have hImg :
                e.symm z0 ∈
                  e.symm '' intrinsicInterior ℝ
                    (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) := by
              exact ⟨z0, hz0ri, by simp [e]⟩
            simpa [hriCk1] using hImg
          simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n)
            (C := Ck1E), Ck1E] using hz0ri_intrE
        refine ⟨e.symm z0, ?_⟩
        constructor
        · simpa [e, Set.mem_preimage] using hz0_dom_g
        · simpa [Ck1E] using hz0riE
      let fTwo : Fin 2 → (Fin n → ℝ) → EReal := fun i => Fin.cases g (fun _ => k1) i
      have hpolyTwo :
          ∀ i : Fin 2, i.1 < 1 → IsPolyhedralConvexFunction n (fTwo i) := by
        intro i hi
        fin_cases i
        · simpa [fTwo] using hgpoly
        · exact False.elim (Nat.not_lt.mpr (Nat.le_refl 1) hi)
      have hproperTwo :
          ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
        intro i
        fin_cases i
        · simpa [fTwo] using hproperG
        · simpa [fTwo] using hproperK1
      have hdomRiTwo :
          Set.Nonempty
            ((⋂ i : {i : Fin 2 // i.1 < 1},
                ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))
              ∩
              (⋂ i : {i : Fin 2 // 1 ≤ i.1},
                euclideanRelativeInterior n
                  ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))) := by
        rcases hnonemptyDomInterRi_gk1 with ⟨x0, hx0⟩
        refine ⟨x0, ?_⟩
        refine And.intro ?_ ?_
        · refine Set.mem_iInter.2 ?_
          intro i
          rcases i with ⟨i, hi⟩
          fin_cases i
          · simpa [fTwo] using hx0.1
          · exact False.elim (Nat.not_lt.mpr (Nat.le_refl 1) hi)
        · refine Set.mem_iInter.2 ?_
          intro i
          rcases i with ⟨i, hi⟩
          fin_cases i
          · exact False.elim (Nat.not_le.mpr (Nat.zero_lt_one) hi)
          · simpa [fTwo] using hx0.2
      have hbinaryBridge :
          fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) =
            infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) := by
        exact
          (fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_dom_first_poly_iInter_ri_rest_and_attained
            (f := fTwo) (k := 1) (hk := by decide) (hmPos := by decide)
            hpolyTwo hproperTwo hdomRiTwo).1
      have hgzstar : fenchelConjugate n g = indicatorFunction (-A) := by
        simpa [g] using hgstar
      have hConjTwo :
          (fun i : Fin 2 => fenchelConjugate n (fTwo i)) =
            (fun i : Fin 2 => if i = 0 then indicatorFunction (-A) else indicatorFunction C1) := by
        funext i
        fin_cases i
        · simpa [fTwo] using hgzstar
        · simpa [fTwo] using hk1star
      have hInfConvAtZero_top :
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i))
            (0 : Fin n → ℝ) = (⊤ : EReal) := by
        have hIndicatorEq :
            infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) =
              infimalConvolution (indicatorFunction (-A)) (indicatorFunction C1) := by
          rw [hConjTwo]
          symm
          simpa using
            (infimalConvolution_eq_infimalConvolutionFamily_two
              (f := indicatorFunction (-A)) (g := indicatorFunction C1))
        have hIndicatorTop :
            infimalConvolution (indicatorFunction (-A)) (indicatorFunction C1)
              (0 : Fin n → ℝ) = (⊤ : EReal) := by
          apply le_antisymm le_top
          unfold infimalConvolution
          refine le_sInf ?_
          intro z hz
          rcases hz with ⟨x1, x2, hsum, rfl⟩
          by_cases hx1 : x1 ∈ -A
          · by_cases hx2 : x2 ∈ C1
            · exfalso
              exact hAplusC1_disjoint_zero ⟨x1, hx1, x2, hx2, hsum⟩
            · simp [indicatorFunction, hx1, hx2]
          · by_cases hx2 : x2 ∈ C1
            · simp [indicatorFunction, hx1, hx2]
            · simp [indicatorFunction, hx1, hx2]
        calc
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i))
              (0 : Fin n → ℝ)
              = infimalConvolution (indicatorFunction (-A)) (indicatorFunction C1)
                  (0 : Fin n → ℝ) := by
                    exact congrArg (fun h : (Fin n → ℝ) → EReal => h (0 : Fin n → ℝ)) hIndicatorEq
          _ = (⊤ : EReal) := hIndicatorTop
      have hConjSumAtZero_top :
          fenchelConjugate n (fun x => g x + k1 x) (0 : Fin n → ℝ) = (⊤ : EReal) := by
        have hAtZero :=
          congrArg
            (fun h : (Fin n → ℝ) → EReal => h (0 : Fin n → ℝ))
            hbinaryBridge
        have hAtZero' :
            fenchelConjugate n (fun x => g x + k1 x) (0 : Fin n → ℝ) =
              infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i))
                (0 : Fin n → ℝ) := by
          simpa [fTwo, Fin.sum_univ_two] using hAtZero
        calc
          fenchelConjugate n (fun x => g x + k1 x) (0 : Fin n → ℝ)
              = infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i))
                  (0 : Fin n → ℝ) := hAtZero'
          _ = (⊤ : EReal) := hInfConvAtZero_top
      have hiInf_g_add_k1_bot :
          iInf (fun z : Fin n → ℝ => g z + k1 z) = (⊥ : EReal) := by
        have hnegEq :
            -(iInf (fun z : Fin n → ℝ => g z + k1 z)) = (⊤ : EReal) := by
          simpa [hConjSumAtZero_top] using
            (fenchelConjugate_zero_eq_neg_iInf
              (n := n) (f := fun z : Fin n → ℝ => g z + k1 z)).symm
        exact EReal.neg_eq_top_iff.mp hnegEq
      have hkAll0_le_bot : kAll 0 ≤ (⊥ : EReal) := by
        by_cases hkAll0_bot : kAll 0 = (⊥ : EReal)
        · simpa [hkAll0_bot]
        · have hkAll0_ne_bot : kAll 0 ≠ (⊥ : EReal) := hkAll0_bot
          have hkAll0_ne_top : kAll 0 ≠ (⊤ : EReal) := by
            intro hkAll0_top
            have : (⊤ : EReal) ≤ (0 : EReal) := by
              simpa [hkAll0_top] using hkAll0le
            exact not_top_le_coe 0 this
          let r : ℝ := (kAll 0).toReal
          have hkAll0_coe : ((r : ℝ) : EReal) = kAll 0 := by
            simpa [r] using (EReal.coe_toReal (x := kAll 0) hkAll0_ne_top hkAll0_ne_bot)
          have hInfLt :
              iInf (fun z : Fin n → ℝ => g z + k1 z) <
                (((2 * r - 1 : ℝ)) : EReal) := by
            simpa [hiInf_g_add_k1_bot] using (EReal.bot_lt_coe (2 * r - 1 : ℝ))
          rcases iInf_lt_iff.mp hInfLt with ⟨z, hzlt⟩
          have hgz_ne_bot : g z ≠ (⊥ : EReal) := hproperG.2.2 z (by simp)
          have hk1z_ne_bot : k1 z ≠ (⊥ : EReal) := hproperK1.2.2 z (by simp)
          have hsum_ne_top : g z + k1 z ≠ (⊤ : EReal) := by
            intro hsum_top
            have : (⊤ : EReal) < (((2 * r - 1 : ℝ)) : EReal) := by
              simpa [hsum_top] using hzlt
            simpa using this
          have hgz_ne_top : g z ≠ (⊤ : EReal) := by
            intro hgz_top
            have hsum_top : g z + k1 z = (⊤ : EReal) := by
              simpa [hgz_top] using EReal.top_add_of_ne_bot hk1z_ne_bot
            exact hsum_ne_top hsum_top
          have hk1z_ne_top : k1 z ≠ (⊤ : EReal) := by
            intro hk1z_top
            have hsum_top : g z + k1 z = (⊤ : EReal) := by
              simpa [hk1z_top] using EReal.add_top_of_ne_bot hgz_ne_bot
            exact hsum_ne_top hsum_top
          have hsum_ne_bot : g z + k1 z ≠ (⊥ : EReal) := by
            intro hsum_bot
            rcases (EReal.add_eq_bot_iff.mp hsum_bot) with hbot | hbot
            · exact hgz_ne_bot hbot
            · exact hk1z_ne_bot hbot
          let μz : ℝ := (g z).toReal
          let vz : ℝ := (k1 z).toReal
          have hμz : kAll (-z) ≤ (μz : EReal) := by
            have hle2 : g z ≤ (μz : EReal) := by
              exact EReal.le_coe_toReal (x := g z) hgz_ne_top
            exact le_trans (by simpa [g] using hkAllLeK0 (-z)) hle2
          have hvz : kAll z ≤ (vz : EReal) := by
            have hle2 : k1 z ≤ (vz : EReal) := by
              exact EReal.le_coe_toReal (x := k1 z) hk1z_ne_top
            exact le_trans (hkAllLeK1 z) hle2
          have hsum_coe :
              (((μz + vz : ℝ)) : EReal) = g z + k1 z := by
            calc
              (((μz + vz : ℝ)) : EReal) = (((g z + k1 z).toReal : ℝ) : EReal) := by
                simp [μz, vz, EReal.toReal_add hgz_ne_top hgz_ne_bot hk1z_ne_top hk1z_ne_bot]
              _ = g z + k1 z := by
                exact EReal.coe_toReal (x := g z + k1 z) hsum_ne_top hsum_ne_bot
          have hsum_real_lt : μz + vz < 2 * r - 1 := by
            have :
                (((μz + vz : ℝ)) : EReal) < (((2 * r - 1 : ℝ)) : EReal) := by
              simpa [hsum_coe] using hzlt
            exact EReal.coe_lt_coe_iff.mp this
          have hhalf :=
            epigraph_combo_ineq_aux
              (S := (Set.univ : Set (Fin n → ℝ))) (f := kAll)
              hkAllConvOn
              (x := -z) (y := z) (μ := μz) (v := vz) (t := (1 / 2 : ℝ))
              (by simp) (by simp) hμz hvz
              (by norm_num) (by norm_num)
          have hmid : ((1 - (1 / 2 : ℝ)) • (-z) + (1 / 2 : ℝ) • z) = 0 := by
            ext i
            simp [smul_eq_mul]
            ring
          have hrhs :
              ((((1 - (1 / 2 : ℝ)) * μz + (1 / 2 : ℝ) * vz : ℝ)) : EReal) =
                ((((μz + vz) / 2 : ℝ)) : EReal) := by
            have hreal :
                ((1 - (1 / 2 : ℝ)) * μz + (1 / 2 : ℝ) * vz : ℝ) =
                  (((μz + vz) / 2 : ℝ)) := by
              ring
            exact congrArg (fun t : ℝ => (t : EReal)) hreal
          have hhalf' :
              kAll 0 ≤ ((((μz + vz) / 2 : ℝ)) : EReal) := by
            rw [hmid] at hhalf
            rwa [hrhs] at hhalf
          have hr_le : r ≤ (μz + vz) / 2 := by
            have : ((r : ℝ) : EReal) ≤ ((((μz + vz) / 2 : ℝ)) : EReal) := by
              rw [hkAll0_coe]
              exact hhalf'
            exact EReal.coe_le_coe_iff.mp this
          have hlt : (μz + vz) / 2 < r := by
            linarith
          exact False.elim ((not_lt_of_ge hr_le) hlt)
      exact le_antisymm hkAll0_le_bot bot_le
    ·
      have hgUpper : ∀ z : Fin n → ℝ, kAll (-z) ≤ g z := by
        intro z
        simpa [g] using hkAllLeK0 (-z)
      have hInterNonempty_g :
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g ∩
            intrinsicInterior ℝ
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)).Nonempty := by
        rcases hInterNonempty with ⟨z0, hz0negK0, hz0ri⟩
        have hz0_dom_g : z0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
          simpa [hdom_g_eq_negK0] using hz0negK0
        exact ⟨z0, hz0_dom_g, hz0ri⟩
      exact helperForTheorem_21_4_zero_bot_of_improper_rightBlock
        g k1 kAll hdomK1ne hk1ConvOn hkAllConvOn hkAll0le hkAllLeK1
        hgUpper hInterNonempty_g hproperK1


end Section21
end Chap04
