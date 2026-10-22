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
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part11

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- Helper for Theorem 25.6: because `int (dom f)` is nonempty, the Euclideanized subdifferential
fiber at any domain point contains no lines. This is the local hypothesis needed to invoke the
no-lines form of Theorem 18.6 exactly as in Rockafellar's proof. -/
lemma helperForTheorem_25_6_preimageSubdifferential_contains_no_lines_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hCne :
      (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) : Set
        (Fin n → Real)).Nonempty) :
    ¬ ∃ y : Fin n → Real, y ≠ 0 ∧
      y ∈ (-Set.recessionCone
        (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) : Set (Fin n → Real))) ∩
        Set.recessionCone
          (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) : Set (Fin n → Real)) := by
  let C : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  let K : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹'
      normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) hx,
        hproper.2.2 x (by simp)⟩
  have hRecSubsetK : Set.recessionCone C ⊆ K := by
    intro d hd
    rcases hCne with ⟨p0, hp0C⟩
    rw [Set.mem_preimage]
    refine (mem_normalConeAt_iff).2 ?_
    constructor
    · simpa using hx
    · intro z hz
      have hzFinite : f z ≠ ⊤ ∧ f z ≠ ⊥ := by
        exact
          ⟨mem_effectiveDomain_imp_ne_top
              (S := (Set.univ : Set (Fin n → Real))) (f := f) hz,
            hproper.2.2 z (by simp)⟩
      lift f x to Real using hxFinite with xr hxr
      have hxFinite' : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
        rw [← hxr]
        simp
      lift f z to Real using hzFinite with zr hzr
      by_contra hnonpos
      have hpos : 0 < dotProduct d (z - x) := by
        exact lt_of_not_ge hnonpos
      let M : Real := max (0 : Real) (zr - xr - dotProduct p0 (z - x)) + 1
      let t : Real := M / dotProduct d (z - x)
      have hMpos : 0 < M := by
        dsimp [M]
        linarith [le_max_left (0 : Real) (zr - xr - dotProduct p0 (z - x))]
      have ht : 0 ≤ t := by
        dsimp [t]
        exact div_nonneg hMpos.le hpos.le
      have hpTd_mem : p0 + t • d ∈ C := hd hp0C ht
      have hpTd_sub :
          dotProductEquiv Real (Fin n) (p0 + t • d) ∈ subdifferentialAt f x := by
        simpa [C] using hpTd_mem
      have hineqReal :
          dotProduct p0 (z - x) + t * dotProduct d (z - x) ≤ zr - xr := by
        have hminor :
            (((dotProduct (z - x) (p0 + t • d) : Real) : EReal)) ≤
              upperDirectionalDerivativeAt f x (z - x) := by
          exact
            (helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
              f hfConv x hxFinite' (p0 + t • d)).1 hpTd_sub (z - x)
        have hsecLe :
            upperDirectionalDerivativeAt f x (z - x) ≤
              directionalDifferenceQuotientAt f x (z - x) 1 := by
          rcases convex_directionalDerivative_monotone_exists_and_sublinear
              f hfConv x hxFinite' with
            ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
          rcases hdir (z - x) with ⟨_hmono, _htend, hsInfEq⟩
          have hQbdd :
              BddBelow ((Set.Ioi (0 : ℝ)).image
                fun τ : ℝ => directionalDifferenceQuotientAt f x (z - x) τ) := by
            refine ⟨⊥, ?_⟩
            intro r hr
            simp at hr ⊢
          rw [hsInfEq]
          exact csInf_le hQbdd ⟨1, by norm_num, rfl⟩
        have hdqEq :
            directionalDifferenceQuotientAt f x (z - x) 1 = (((zr - xr : Real) : EReal)) := by
          have hstep : x + (1 : Real) • (z - x) = z := by
            ext j
            simp
          simp [directionalDifferenceQuotientAt, hstep, hxr, hzr, div_eq_mul_inv]
        have hineqE :
            (((dotProduct (z - x) (p0 + t • d) : Real) : EReal)) ≤
              (((zr - xr : Real) : EReal)) := by
          exact le_trans hminor (by simpa [hdqEq] using hsecLe)
        have hrewrite :
            dotProduct (z - x) (p0 + t • d) =
              dotProduct p0 (z - x) + t * dotProduct d (z - x) := by
          rw [dotProduct_comm, add_dotProduct, smul_dotProduct]
          simp [smul_eq_mul]
        have hineqE' :
            (((dotProduct p0 (z - x) + t * dotProduct d (z - x) : Real) : EReal)) ≤
              (((zr - xr : Real) : EReal)) := by
          simpa [hrewrite, smul_eq_mul] using hineqE
        exact_mod_cast hineqE'
      have htMul :
          t * dotProduct d (z - x) = M := by
        have hdnz : dotProduct d (z - x) ≠ 0 := ne_of_gt hpos
        dsimp [t]
        field_simp [hdnz]
      have hMle : M ≤ zr - xr - dotProduct p0 (z - x) := by
        linarith [hineqReal, htMul]
      have hmaxLe :
          max (0 : Real) (zr - xr - dotProduct p0 (z - x)) + 1 ≤
            zr - xr - dotProduct p0 (z - x) := by
        simpa [M] using hMle
      linarith [le_max_right (0 : Real) (zr - xr - dotProduct p0 (z - x))]
  intro hlines
  rcases hlines with ⟨y, hyne, hyline⟩
  have hyRec : y ∈ Set.recessionCone C := hyline.2
  have hyNegRec : -y ∈ Set.recessionCone C := by
    simpa [Set.mem_neg] using hyline.1
  have hyK : y ∈ K := hRecSubsetK hyRec
  have hyNegK : -y ∈ K := hRecSubsetK hyNegRec
  rcases hdom with ⟨z0, hz0⟩
  rcases helperForTheorem_25_1_exists_closedBall_subset_of_isOpen
      (n := n) (C := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
      isOpen_interior hz0 with ⟨r, hrpos, hrball⟩
  have hyEqOnDom :
      ∀ z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f,
        dotProduct y (z - x) = 0 := by
    intro z hz
    rcases (mem_normalConeAt_iff.1 hyK) with ⟨_hxDom, hyIneq⟩
    rcases (mem_normalConeAt_iff.1 hyNegK) with ⟨_hxDom', hyNegIneq⟩
    have hle : dotProduct y (z - x) ≤ 0 := by
      simpa [dotProductEquiv_apply_apply] using hyIneq z hz
    have hge : 0 ≤ dotProduct y (z - x) := by
      have hnegle : dotProduct (-y) (z - x) ≤ 0 := by
        simpa [dotProductEquiv_apply_apply] using hyNegIneq z hz
      have : - dotProduct y (z - x) ≤ 0 := by simpa using hnegle
      linarith
    exact le_antisymm hle hge
  have hyNormPos : 0 < ‖y‖ := norm_pos_iff.2 hyne
  let ε : Real := r / (2 * ‖y‖)
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hwBall : z0 + ε • y ∈ Metric.closedBall z0 r := by
    change dist (z0 + ε • y) z0 ≤ r
    rw [dist_eq_norm]
    have hsub : z0 + ε • y - z0 = ε • y := by
      abel_nf
    rw [hsub, norm_smul, Real.norm_of_nonneg hεpos.le]
    have hhalf : ε * ‖y‖ = r / 2 := by
      dsimp [ε]
      field_simp [hyNormPos.ne']
    linarith
  have hwInt :
      z0 + ε • y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    hrball hwBall
  have hz0Eq :
      dotProduct y (z0 - x) = 0 :=
    hyEqOnDom z0 (interior_subset hz0)
  have hwEq :
      dotProduct y ((z0 + ε • y) - x) = 0 :=
    hyEqOnDom (z0 + ε • y) (interior_subset hwInt)
  have hdiff :
      dotProduct y ((z0 + ε • y) - x) =
        dotProduct y (z0 - x) + ε * dotProduct y y := by
    calc
      dotProduct y ((z0 + ε • y) - x)
          = dotProduct y ((z0 - x) + ε • y) := by
              congr 1
              abel_nf
      _ = dotProduct y (z0 - x) + dotProduct y (ε • y) := by
            rw [dotProduct_add]
      _ = dotProduct y (z0 - x) + ε * dotProduct y y := by
            rw [dotProduct_smul]
            simp [smul_eq_mul]
  have hzero : ε * dotProduct y y = 0 := by
    linarith [hwEq, hz0Eq, hdiff]
  have hyy_nonneg : 0 ≤ dotProduct y y := dotProduct_self_nonneg y
  have hyy_zero : dotProduct y y = 0 := by
    nlinarith [hyy_nonneg, hεpos]
  exact hyne (dotProduct_self_eq_zero.mp hyy_zero)

/-- Helper for Theorem 25.6: Rockafellar's Chapter 18 decomposition treats the extreme-point part
first, so the geometric input needed here is that every extreme point of the Euclideanized fiber
lies in the closure of its exposed points. The interior case uses the bounded form of Theorem 18.6;
the boundary case uses the no-lines form. -/
lemma helperForTheorem_25_6_extremePoints_preimageSubdifferential_subset_closureExposedPoints_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x p : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hp :
      p ∈ (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x).extremePoints ℝ)) :
    p ∈ closure ((((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x).exposedPoints ℝ)) := by
  by_cases hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
  · let C : Set (Fin n → Real) :=
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
    have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
      helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
    have hfConv : ConvexFunction f := by
      simpa [ConvexFunction] using hproper.1
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
      exact
        ⟨mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin n → Real))) (f := f) (interior_subset hxInt),
          hproper.2.2 x (by simp)⟩
    have hCclosed : IsClosed C := by
      exact
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.1
    have hCconv : Convex Real C := by
      exact
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
    have hCbdd : Bornology.IsBounded C :=
      (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
        (f := f) hf hxInt).2
    exact
      (theorem18_6_extremePoints_subset_closure_exposedPoints
        (n := n) (C := C) hCclosed hCbdd hCconv) (by simpa [C] using hp)
  · let C : Set (Fin n → Real) :=
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
    have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
      helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
    have hfConv : ConvexFunction f := by
      simpa [ConvexFunction] using hproper.1
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
      exact
        ⟨mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin n → Real))) (f := f) hx,
          hproper.2.2 x (by simp)⟩
    have hCclosed : IsClosed C := by
      exact
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.1
    have hCconv : Convex Real C := by
      exact
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
    have hpC : p ∈ C := by
      exact (extremePoints_subset (A := C) (𝕜 := ℝ)) (by simpa [C] using hp)
    have hNoLines :
        ¬ ∃ y : Fin n → Real, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
      exact
        helperForTheorem_25_6_preimageSubdifferential_contains_no_lines_of_mem_effectiveDomain
          (f := f) hf hdom hx ⟨p, hpC⟩
    exact
      (theorem18_6_extremePoints_subset_closure_exposedPoints_of_noLines
        (C := C) hCclosed hCconv hNoLines) (by simpa [C] using hp)

/-- Helper for Theorem 25.6: Rockafellar's boundary argument reduces the extreme-point part of the
Euclideanized subdifferential to nearby gradient limits. -/
lemma helperForTheorem_25_6_extremePoints_preimageSubdifferential_subset_closureGradientLimitVectors_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x p : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hp :
      p ∈ (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x).extremePoints ℝ)) :
    p ∈ closure (gradientLimitVectorsAt f x) := by
  let C : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  have hpClosureExposed :
      p ∈ closure (C.exposedPoints ℝ) := by
    simpa [C] using
      helperForTheorem_25_6_extremePoints_preimageSubdifferential_subset_closureExposedPoints_of_mem_effectiveDomain
        (f := f) hf hf_closed hdom hx hp
  have hExposedSubset : C.exposedPoints ℝ ⊆ closure (gradientLimitVectorsAt f x) := by
    intro q hq
    simpa [C] using
      helperForTheorem_25_6_exposedPoints_preimageSubdifferential_subset_closureGradientLimitVectors_of_mem_effectiveDomain
        (f := f) hf hf_closed hdom hx hq
  exact (closure_minimal hExposedSubset isClosed_closure) hpClosureExposed

/-- Helper for Theorem 25.6: the reverse inclusion follows Rockafellar's Chapter 18
decomposition: split the Euclideanized subdifferential into extreme points and extreme directions,
send the points into `closure S(x)`, and send the directions into the normal cone. -/
lemma helperForTheorem_25_6_reverseInclusion_chapter18_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) ⊆
      closure (convexHull Real (gradientLimitVectorsAt f x)) +
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x) := by
  by_cases hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
  · have hInterior :
        ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) =
          closure (convexHull Real (gradientLimitVectorsAt f x)) :=
      helperForTheorem_25_6_interior_preimageSubdifferential_eq_closureConvexHull_gradientLimitVectors
        (f := f) hf hf_closed hxInt
    have hNormalZero :
        ((dotProductEquiv Real (Fin n)) ⁻¹'
            normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x) =
          ({0} : Set (Fin n → Real)) :=
      helperForTheorem_25_6_preimage_normalCone_eq_singleton_zero_of_mem_interior
        (f := f) hf hxInt
    intro z hz
    rw [hInterior] at hz
    rw [hNormalZero]
    exact Set.mem_add.2 ⟨z, hz, 0, by simp, by simp⟩
  · -- Rockafellar's notation: `S = S(x)`, `A = cl (conv S(x))`, `K = K(x)`,
    -- `C` is the Euclideanized fiber `∂f(x)`, and `B = A + K`.
    let S : Set (Fin n → Real) := gradientLimitVectorsAt f x
    let A : Set (Fin n → Real) := closure (convexHull Real S)
    let K : Set (Fin n → Real) :=
      ((dotProductEquiv Real (Fin n)) ⁻¹'
        normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x)
    let C : Set (Fin n → Real) :=
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
    let B : Set (Fin n → Real) := A + K
    have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
      helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
    have hfConv : ConvexFunction f := by
      simpa [ConvexFunction] using hproper.1
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
      exact
        ⟨mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin n → Real))) (f := f) hx,
          hproper.2.2 x (by simp)⟩
    have hCclosed : IsClosed C := by
      exact
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.1
    have hCconv : Convex Real C := by
      exact
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
    have hAconv : Convex Real A := by
      simpa [A, S] using (convex_convexHull Real (gradientLimitVectorsAt f x)).closure
    have hKconv : Convex Real K := by
      intro u hu v hv a b ha hb hab
      rw [Set.mem_preimage] at hu hv ⊢
      refine (mem_normalConeAt_iff).2 ?_
      rcases (mem_normalConeAt_iff.1 hu) with ⟨hxDom, huIneq⟩
      rcases (mem_normalConeAt_iff.1 hv) with ⟨_hxDom, hvIneq⟩
      constructor
      · exact hxDom
      · intro z hz
        have huScaled :
            a * dotProduct u (z - x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos ha (huIneq z hz)
        have hvScaled :
            b * dotProduct v (z - x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hb (hvIneq z hz)
        have hsum :
            a * dotProduct u (z - x) + b * dotProduct v (z - x) ≤ 0 :=
          add_nonpos huScaled hvScaled
        simpa [dotProductEquiv_apply_apply, dotProduct_add, dotProduct_smul, smul_eq_mul,
          mul_comm, mul_left_comm, mul_assoc, hab] using hsum
    have hBconv : Convex Real B := by
      exact hAconv.add hKconv
    by_cases hCne : C.Nonempty
    · have hKzero : (0 : Fin n → Real) ∈ K := by
        rw [Set.mem_preimage]
        refine (mem_normalConeAt_iff).2 ?_
        constructor
        · simpa using hx
        · intro z hz
          simp
      have hClosureS_subset_A : closure S ⊆ A := by
        exact
          closure_minimal
            (Set.Subset.trans
              (subset_convexHull Real S)
              subset_closure)
            isClosed_closure
      have hPointsSubset : C.extremePoints ℝ ⊆ B := by
        intro p hp
        have hpClosure :
            p ∈ closure S :=
          helperForTheorem_25_6_extremePoints_preimageSubdifferential_subset_closureGradientLimitVectors_of_mem_effectiveDomain
            (f := f) hf hf_closed hdom hx (by simpa [C] using hp)
        have hpA : p ∈ A := hClosureS_subset_A hpClosure
        exact Set.mem_add.2 ⟨p, hpA, 0, hKzero, by simp [B]⟩
      have hKsmul :
          ∀ {v : Fin n → Real}, v ∈ K → ∀ {t : Real}, 0 ≤ t → t • v ∈ K := by
        intro v hv t ht
        rw [Set.mem_preimage] at hv ⊢
        rcases (mem_normalConeAt_iff.1 hv) with ⟨hxDom, hvIneq⟩
        refine (mem_normalConeAt_iff).2 ?_
        constructor
        · exact hxDom
        · intro z hz
          have hscaled :
              t * dotProduct v (z - x) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos ht (hvIneq z hz)
          simpa [dotProductEquiv_apply_apply, dotProduct_smul, smul_eq_mul, mul_comm,
            mul_left_comm, mul_assoc] using hscaled
      have hDirsRecede :
          ∀ d ∈ {d : Fin n → Real | IsExtremeDirection (𝕜 := ℝ) C d},
            d ∈ Set.recessionCone B := by
        intro d hd
        have hdK :
            d ∈ K :=
          helperForTheorem_25_6_extremeDirections_preimageSubdifferential_subset_preimageNormalCone_of_mem_effectiveDomain
            (f := f) hf hf_closed hdom hx (by simpa [C] using hd)
        intro y hy t ht
        rcases Set.mem_add.1 hy with ⟨a, ha, k, hk, rfl⟩
        have htdK : t • d ∈ K := hKsmul hdK ht
        have hsumK : k + t • d ∈ K := by
          rw [Set.mem_preimage] at hk htdK ⊢
          rcases (mem_normalConeAt_iff.1 hk) with ⟨hxDom, hkIneq⟩
          rcases (mem_normalConeAt_iff.1 htdK) with ⟨_hxDom, htdIneq⟩
          refine (mem_normalConeAt_iff).2 ?_
          constructor
          · exact hxDom
          · intro z hz
            have hsum :
                dotProduct k (z - x) + dotProduct (t • d) (z - x) ≤ 0 :=
              add_nonpos (hkIneq z hz) (htdIneq z hz)
            change dotProduct (k + t • d) (z - x) ≤ 0
            rw [add_dotProduct]
            exact hsum
        exact Set.mem_add.2 ⟨a, ha, k + t • d, hsumK, by simp [add_assoc]⟩
      have hRecSubsetK : Set.recessionCone C ⊆ K := by
        intro d hd
        rcases hCne with ⟨p, hpC⟩
        rw [Set.mem_preimage]
        refine (mem_normalConeAt_iff).2 ?_
        constructor
        · simpa using hx
        · intro z hz
          have hzFinite : f z ≠ ⊤ ∧ f z ≠ ⊥ := by
            exact
              ⟨mem_effectiveDomain_imp_ne_top
                  (S := (Set.univ : Set (Fin n → Real))) (f := f) hz,
                hproper.2.2 z (by simp)⟩
          lift f x to Real using hxFinite with xr hxr
          have hxFinite' : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
            rw [← hxr]
            simp
          lift f z to Real using hzFinite with zr hzr
          by_contra hnonpos
          have hpos : 0 < dotProduct d (z - x) := by
            exact lt_of_not_ge hnonpos
          let M : Real := max (0 : Real) (zr - xr - dotProduct p (z - x)) + 1
          let t : Real := M / dotProduct d (z - x)
          have hMpos : 0 < M := by
            dsimp [M]
            linarith [le_max_left (0 : Real) (zr - xr - dotProduct p (z - x))]
          have ht : 0 ≤ t := by
            dsimp [t]
            exact div_nonneg hMpos.le hpos.le
          have hpTd_mem : p + t • d ∈ C := hd hpC ht
          have hpTd_sub :
              dotProductEquiv Real (Fin n) (p + t • d) ∈ subdifferentialAt f x := by
            simpa [C] using hpTd_mem
          have hineqReal :
              dotProduct p (z - x) + t * dotProduct d (z - x) ≤ zr - xr := by
            have hminor :
                (((dotProduct (z - x) (p + t • d) : Real) : EReal)) ≤
                  upperDirectionalDerivativeAt f x (z - x) := by
              exact
                (helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
                  f hfConv x hxFinite' (p + t • d)).1 hpTd_sub (z - x)
            have hsecLe :
                upperDirectionalDerivativeAt f x (z - x) ≤
                  directionalDifferenceQuotientAt f x (z - x) 1 := by
              rcases convex_directionalDerivative_monotone_exists_and_sublinear
                  f hfConv x hxFinite' with
                ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
              rcases hdir (z - x) with ⟨_hmono, _htend, hsInfEq⟩
              have hQbdd :
                  BddBelow ((Set.Ioi (0 : ℝ)).image
                    fun τ : ℝ => directionalDifferenceQuotientAt f x (z - x) τ) := by
                refine ⟨⊥, ?_⟩
                intro r hr
                simp at hr ⊢
              rw [hsInfEq]
              exact csInf_le hQbdd ⟨1, by norm_num, rfl⟩
            have hdqEq :
                directionalDifferenceQuotientAt f x (z - x) 1 = (((zr - xr : Real) : EReal)) := by
              have hstep : x + (1 : Real) • (z - x) = z := by
                ext j
                simp
              simp [directionalDifferenceQuotientAt, hstep, hxr, hzr, div_eq_mul_inv]
            have hineqE :
                (((dotProduct (z - x) (p + t • d) : Real) : EReal)) ≤
                  (((zr - xr : Real) : EReal)) := by
              exact le_trans hminor (by simpa [hdqEq] using hsecLe)
            have hrewrite :
                dotProduct (z - x) (p + t • d) =
                  dotProduct p (z - x) + t * dotProduct d (z - x) := by
              rw [dotProduct_comm, add_dotProduct, smul_dotProduct]
              simp [smul_eq_mul]
            have hineqE' :
                (((dotProduct p (z - x) + t * dotProduct d (z - x) : Real) : EReal)) ≤
                  (((zr - xr : Real) : EReal)) := by
              simpa [hrewrite, smul_eq_mul] using hineqE
            exact_mod_cast hineqE'
          have htMul :
              t * dotProduct d (z - x) = M := by
            have hdnz : dotProduct d (z - x) ≠ 0 := ne_of_gt hpos
            dsimp [t]
            field_simp [hdnz]
          have hMle : M ≤ zr - xr - dotProduct p (z - x) := by
            linarith [hineqReal, htMul]
          have hmaxLe :
              max (0 : Real) (zr - xr - dotProduct p (z - x)) + 1 ≤
                zr - xr - dotProduct p (z - x) := by
            simpa [M] using hMle
          linarith [le_max_right (0 : Real) (zr - xr - dotProduct p (z - x))]
      have hNoLines :
          ¬ ∃ y : Fin n → Real, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
        intro hlines
        rcases hlines with ⟨y, hyne, hyline⟩
        have hyRec : y ∈ Set.recessionCone C := hyline.2
        have hyNegRec : -y ∈ Set.recessionCone C := by
          simpa [Set.mem_neg] using hyline.1
        have hyK : y ∈ K := hRecSubsetK hyRec
        have hyNegK : -y ∈ K := hRecSubsetK hyNegRec
        rcases hdom with ⟨z0, hz0⟩
        rcases helperForTheorem_25_1_exists_closedBall_subset_of_isOpen
            (n := n) (C := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
            isOpen_interior hz0 with ⟨r, hrpos, hrball⟩
        have hyEqOnDom :
            ∀ z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f,
              dotProduct y (z - x) = 0 := by
          intro z hz
          rcases (mem_normalConeAt_iff.1 hyK) with ⟨_hxDom, hyIneq⟩
          rcases (mem_normalConeAt_iff.1 hyNegK) with ⟨_hxDom', hyNegIneq⟩
          have hle : dotProduct y (z - x) ≤ 0 := by
            simpa [dotProductEquiv_apply_apply] using hyIneq z hz
          have hge : 0 ≤ dotProduct y (z - x) := by
            have hnegle : dotProduct (-y) (z - x) ≤ 0 := by
              simpa [dotProductEquiv_apply_apply] using hyNegIneq z hz
            have : - dotProduct y (z - x) ≤ 0 := by simpa using hnegle
            linarith
          exact le_antisymm hle hge
        have hyNormPos : 0 < ‖y‖ := norm_pos_iff.2 hyne
        let ε : Real := r / (2 * ‖y‖)
        have hεpos : 0 < ε := by
          dsimp [ε]
          positivity
        have hwBall : z0 + ε • y ∈ Metric.closedBall z0 r := by
          change dist (z0 + ε • y) z0 ≤ r
          rw [dist_eq_norm]
          have hsub : z0 + ε • y - z0 = ε • y := by
            abel_nf
          rw [hsub, norm_smul, Real.norm_of_nonneg hεpos.le]
          have hhalf : ε * ‖y‖ = r / 2 := by
            dsimp [ε]
            field_simp [hyNormPos.ne']
          linarith
        have hwInt :
            z0 + ε • y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
          hrball hwBall
        have hz0Eq :
            dotProduct y (z0 - x) = 0 :=
          hyEqOnDom z0 (interior_subset hz0)
        have hwEq :
            dotProduct y ((z0 + ε • y) - x) = 0 :=
          hyEqOnDom (z0 + ε • y) (interior_subset hwInt)
        have hdiff :
            dotProduct y ((z0 + ε • y) - x) =
              dotProduct y (z0 - x) + ε * dotProduct y y := by
          calc
            dotProduct y ((z0 + ε • y) - x)
                = dotProduct y ((z0 - x) + ε • y) := by
                    congr 1
                    abel_nf
            _ = dotProduct y (z0 - x) + dotProduct y (ε • y) := by
                  rw [dotProduct_add]
            _ = dotProduct y (z0 - x) + ε * dotProduct y y := by
                  rw [dotProduct_smul]
                  simp [smul_eq_mul]
        have hzero : ε * dotProduct y y = 0 := by
          linarith [hwEq, hz0Eq, hdiff]
        have hyy_nonneg : 0 ≤ dotProduct y y := dotProduct_self_nonneg y
        have hyy_zero : dotProduct y y = 0 := by
          nlinarith [hyy_nonneg, hεpos]
        exact hyne (dotProduct_self_eq_zero.mp hyy_zero)
      have hCeq :
          C =
            mixedConvexHull (n := n) (C.extremePoints ℝ)
              {d : Fin n → Real | IsExtremeDirection (𝕜 := ℝ) C d} :=
        closedConvex_eq_mixedConvexHull_extremePoints_extremeDirections
          (n := n) (C := C) hCclosed hCconv hNoLines
      intro z hz
      have hzC : z ∈ C := by
        simpa [C] using hz
      rw [hCeq] at hzC
      exact
        mixedConvexHull_subset_of_convex_of_subset_of_recedes
          (n := n)
          (S₀ := C.extremePoints ℝ)
          (S₁ := {d : Fin n → Real | IsExtremeDirection (𝕜 := ℝ) C d})
          (Ccand := B) hBconv hPointsSubset hDirsRecede hzC
    · intro z hz
      exact (hCne ⟨z, by simpa [C] using hz⟩).elim

/-- Helper for Theorem 25.6: the reverse inclusion is Rockafellar's Chapter 18 extreme-point /
extreme-direction decomposition. -/
lemma helperForTheorem_25_6_reverseInclusion_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) ⊆
      closure (convexHull Real (gradientLimitVectorsAt f x)) +
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x) := by
  exact
    helperForTheorem_25_6_reverseInclusion_chapter18_of_mem_effectiveDomain
      (f := f) hf hf_closed hdom hx

-- Rockafellar's Theorem 25.6 identifies the Euclideanized subdifferential with
-- `cl (conv S(x)) + K(x)`: the reverse inclusion comes from the Chapter 18 decomposition into
-- extreme points and extreme directions, while the forward inclusion is the global domain-point
-- inclusion proved earlier.
/-- Theorem 25.6: let `f` be a closed proper convex function such that `dom f` has nonempty
interior. Identifying dual vectors with Euclidean vectors via `dotProductEquiv`, the vector form of
the subdifferential at `x` is `cl (conv S(x)) + K(x)`, where `K(x)` is the normal cone to `dom f`
at `x` and `S(x)` is the set of limits of gradients `∇ f(x_i)` along differentiability points
`x_i → x`. -/
theorem closedProperConvex_subdifferential_preimage_eq_closure_convexHull_gradientLimitVectors_add_normalCone_preimage
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    (x : Fin n → Real) :
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) =
      closure (convexHull Real (gradientLimitVectorsAt f x)) +
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x) := by
  by_cases hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f
  · apply Set.Subset.antisymm
    · -- Rockafellar's reverse inclusion is the Chapter 18 decomposition.
      exact
        helperForTheorem_25_6_reverseInclusion_of_mem_effectiveDomain
          (f := f) hf hf_closed hdom hx
    · -- The forward inclusion is the domain-point inclusion proved earlier.
      exact
        helperForTheorem_25_6_forwardInclusion_of_mem_effectiveDomain
          (f := f) hf hf_closed hdom hx
  · -- Outside `dom f`, Theorem 23.4 and the empty normal cone collapse both sides to `∅`.
    exact
      helperForTheorem_25_6_preimage_eq_empty_of_not_mem_effectiveDomain
        (f := f) hf hx

-- This is Rockafellar's Theorem 25.7 in Euclidean coordinates: identify directional derivatives
-- along lines, pass to the limit by the one-dimensional convex convergence theorem, and then use
-- differentiability to recover the full gradient vector.
/-- Helper for Theorem 25.7: at an `EReal` differentiability point of a convex function, the
Euclideanized subdifferential fiber collapses to the singleton containing the gradient vector. -/
lemma helperForTheorem_25_7_subdifferentialPreimage_eq_singleton_gradient
    {n : Nat} {g : (Fin n → Real) → EReal} (hgConv : ConvexFunction g)
    {x : Fin n → Real} (hgDiff : ERealDifferentiableAt g x) :
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt g x) =
      ({erealGradientAt hgDiff} : Set (Fin n → Real)) := by
  ext u
  constructor
  · intro hu
    -- Uniqueness of the subgradient at a differentiability point identifies every fiber element.
    rw [Set.mem_singleton_iff]
    exact
      helperForTheorem_25_5_subgradientPreimage_eq_gradient
        (f := g) hgConv (x := x) hgDiff (u := u) hu
  · intro hu
    -- The gradient itself always belongs to the Euclideanized subdifferential fiber.
    rw [Set.mem_singleton_iff] at hu
    rw [hu]
    exact
      helperForTheorem_25_5_gradient_mem_subdifferentialPreimage
        (f := g) hgConv (x := x) hgDiff

/-- Theorem 25.7: let `C` be an open convex subset of `ℝⁿ`, let `f` be a convex function on `C`
that is finite and differentiable on `C`, and let `f₁, f₂, ...` be convex functions on `C` that
are finite and differentiable on `C` and converge pointwise to `f` on `C`. Then for every
`x ∈ C`, the gradients `∇ fᵢ(x)` converge to `∇ f(x)`. -/
theorem convexOn_tendsto_euclideanGradientAt_of_pointwise_convergent
    {n : Nat} {C : Set (Fin n → Real)} (f : (Fin n → Real) → Real)
    (fSeq : ℕ → (Fin n → Real) → Real)
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (hf : ConvexOn ℝ C f)
    (hfdiff : DifferentiableOn ℝ f C)
    (hSeqConvex : ∀ i : ℕ, ConvexOn ℝ C (fSeq i))
    (hSeqDiff : ∀ i : ℕ, DifferentiableOn ℝ (fSeq i) C)
    (hpointwise :
      ∀ x : Fin n → Real, x ∈ C →
        Filter.Tendsto (fun i : ℕ => fSeq i x) Filter.atTop (nhds (f x))) :
    ∀ x : Fin n → Real, x ∈ C →
      Filter.Tendsto (fun i : ℕ => euclideanGradientAt (fSeq i) x) Filter.atTop
        (nhds (euclideanGradientAt f x)) := by
  intro x hx
  let fExt : (Fin n → Real) → EReal := fun y => (f y : EReal) + indicatorFunction C y
  let fSeqExt : ℕ → (Fin n → Real) → EReal :=
    fun i y => (fSeq i y : EReal) + indicatorFunction C y
  have hCne : C.Nonempty := ⟨x, hx⟩
  have hproperExt :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fExt ∧
        interior (effectiveDomain (Set.univ : Set (Fin n → Real)) fExt) = C := by
    -- Replace the real-valued convex function by its standard `+∞` extension on all of `ℝⁿ`.
    simpa [fExt] using
      (helperForCorollary_25_5_1_properConvexExtension
        (hCopen := hCopen) (_hCconv := hCconv) hCne hf)
  have hproperSeq :
      ∀ i : ℕ,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fSeqExt i) := by
    intro i
    -- The same extension construction applies termwise to the approximating sequence.
    simpa [fSeqExt] using
      (helperForCorollary_25_5_1_properConvexExtension
        (hCopen := hCopen) (_hCconv := hCconv) hCne (hSeqConvex i)).1
  have hfExtConv : ConvexFunction fExt := by
    simpa [ConvexFunction] using hproperExt.1.1
  have hSeqExtConv : ∀ i : ℕ, ConvexFunction (fSeqExt i) := by
    intro i
    simpa [ConvexFunction] using (hproperSeq i).1
  have hfExtFinite : ∀ z : Fin n → Real, z ∈ C → fExt z ≠ ⊤ ∧ fExt z ≠ ⊥ := by
    intro z hz
    simp [fExt, add_indicatorFunction_eq, hz]
  have hSeqExtFinite :
      ∀ i : ℕ, ∀ z : Fin n → Real, z ∈ C → fSeqExt i z ≠ ⊤ ∧ fSeqExt i z ≠ ⊥ := by
    intro i z hz
    simp [fSeqExt, add_indicatorFunction_eq, hz]
  have hpointwiseExt :
      ∀ z : Fin n → Real, z ∈ C →
        Filter.Tendsto (fun i : ℕ => fSeqExt i z) Filter.atTop (nhds (fExt z)) := by
    intro z hz
    -- On `C`, the extensions are just the original real-valued functions viewed in `EReal`.
    simpa [fExt, fSeqExt, add_indicatorFunction_eq, hz] using
      (helperForTheorem_5_24_8_tendsto_coe_of_tendsto (hpointwise z hz))
  have hsubdiffStability :=
    convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
      (C := C) hCopen hCconv hfExtConv hfExtFinite
      fSeqExt hSeqExtConv hSeqExtFinite hx (fun _ : ℕ => x) (by intro i; simpa)
      (by simpa using (Filter.tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x)))
      hpointwiseExt
  have hdiffAt : DifferentiableAt ℝ f x :=
    (hfdiff x hx).differentiableAt (hCopen.mem_nhds hx)
  have hExtData :
      ∃ hExt : ERealDifferentiableAt fExt x,
        erealGradientAt hExt = euclideanGradientAt f x := by
    -- Differentiability of `f` on the open set identifies the extension gradient with `∇ f(x)`.
    simpa [fExt] using
      (helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
        (hCopen := hCopen) (f := f) (x := x) hx hdiffAt)
  rcases hExtData with ⟨hExt, hExtGrad⟩
  have hBaseSingleton :
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt fExt x) =
        ({euclideanGradientAt f x} : Set (Fin n → Real)) := by
    -- The extension fiber is the singleton gradient, then `hExtGrad` rewrites back to `∇ f(x)`.
    calc
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt fExt x) =
          ({erealGradientAt hExt} : Set (Fin n → Real)) := by
            exact
              helperForTheorem_25_7_subdifferentialPreimage_eq_singleton_gradient
                (g := fExt) hfExtConv (x := x) hExt
      _ = ({euclideanGradientAt f x} : Set (Fin n → Real)) := by
            simp [hExtGrad]
  -- The eventual singleton-plus-ball inclusion is the metric definition of gradient convergence.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεhalf : 0 < ε / 2 := by linarith
  rcases hsubdiffStability.2 (ε / 2) hεhalf with ⟨i0, hi0⟩
  refine Filter.eventually_atTop.2 ⟨i0, ?_⟩
  intro i hi
  have hSeqDiffAt : DifferentiableAt ℝ (fSeq i) x :=
    (hSeqDiff i x hx).differentiableAt (hCopen.mem_nhds hx)
  have hExtSeqData :
      ∃ hExt : ERealDifferentiableAt (fSeqExt i) x,
        erealGradientAt hExt = euclideanGradientAt (fSeq i) x := by
    -- Each approximating function has the same gradient after passing to the extension.
    simpa [fSeqExt] using
      (helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
        (hCopen := hCopen) (f := fSeq i) (x := x) hx hSeqDiffAt)
  rcases hExtSeqData with ⟨hExtSeq, hExtSeqGrad⟩
  have hGradMem :
      euclideanGradientAt (fSeq i) x ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt (fSeqExt i) x) := by
    rw [← hExtSeqGrad]
    exact
      helperForTheorem_25_5_gradient_mem_subdifferentialPreimage
        (f := fSeqExt i) (hSeqExtConv i) (x := x) hExtSeq
  have hNear :
      euclideanGradientAt (fSeq i) x ∈
        Set.image2 (fun u v : Fin n → Real => u + v)
          ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt fExt x)
          {v : Fin n → Real | ‖v‖ ≤ ε / 2} :=
    hi0 i hi hGradMem
  rcases Set.mem_image2.1 hNear with ⟨u, hu, v, hv, huv⟩
  have huEq : u = euclideanGradientAt f x := by
    rw [hBaseSingleton] at hu
    simpa using hu
  have hvNorm : ‖v‖ ≤ ε / 2 := hv
  have hdist :
      dist (euclideanGradientAt (fSeq i) x) (euclideanGradientAt f x) < ε := by
    calc
      dist (euclideanGradientAt (fSeq i) x) (euclideanGradientAt f x) =
          dist (u + v) (euclideanGradientAt f x) := by
            rw [← huv]
      _ = ‖v‖ := by
            rw [huEq, dist_eq_norm]
            abel_nf
      _ < ε := by linarith
  simpa using hdist

-- Proof sketch: specialize Theorem 25.7 to dimension `1`, where the Euclidean gradient is the
-- ordinary derivative. Pointwise convergence of the gradients gives convergence of `deriv` at each
-- `t ∈ I`, and the one-dimensional compact-interval argument for convex derivatives upgrades this
-- to uniform convergence on every closed bounded subinterval `Set.Icc a b ⊆ I`.
/-- Helper for Corollary 25.7.1: the `Fin 1` gradient of a scalar lift is exactly the scalar
derivative written as a constant `Fin 1` vector. -/
lemma helperForCorollary_25_7_1_euclideanGradientAt_scalarLift_eq_scalarPoint_deriv
    {g : ℝ → ℝ} {t : ℝ} (hg : DifferentiableAt ℝ g t) :
    euclideanGradientAt (fun u : Fin 1 → ℝ => g (u 0)) (scalarPoint t) =
      scalarPoint (deriv g t) := by
  -- Expand the unique coordinate of `Fin 1` and rewrite the Fréchet derivative by the scalar
  -- derivative formula.
  ext i
  fin_cases i
  simp [euclideanGradientAt]
  let proj0 : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
  have hcomp :
      HasFDerivAt (fun u : Fin 1 → ℝ => g (u 0)) ((fderiv ℝ g t).comp proj0) (scalarPoint t) := by
    -- Differentiate the scalar lift by composing `g` with the coordinate projection.
    simpa [proj0] using hg.hasFDerivAt.comp (scalarPoint t) proj0.hasFDerivAt
  have hfderiv :
      fderiv ℝ (fun u : Fin 1 → ℝ => g (u 0)) (scalarPoint t) = (fderiv ℝ g t).comp proj0 :=
    hcomp.fderiv
  rw [hfderiv]
  have hfd : (fderiv ℝ g t) 1 = deriv g t := by
    simpa [ContinuousLinearMap.smulRight_apply] using
      congrFun (fderiv_eq_smul_deriv (f := g) (x := t)) 1
  simpa [proj0, scalarPoint, hfd]

/-- Helper for Corollary 25.7.1: specializing Theorem 25.7 to `Fin 1` transports pointwise
gradient convergence into pointwise convergence of the scalar derivatives. -/
lemma helperForCorollary_25_7_1_pointwise_deriv_tendsto_of_theorem_25_7
    {I : Set ℝ} {f : ℝ → ℝ} (fSeq : ℕ → ℝ → ℝ)
    (hIopen : IsOpen I) (hIconv : Convex ℝ I) (hf : ConvexOn ℝ I f)
    (hfdiff : DifferentiableOn ℝ f I)
    (hSeqConvex : ∀ i : ℕ, ConvexOn ℝ I (fSeq i))
    (hSeqDiff : ∀ i : ℕ, DifferentiableOn ℝ (fSeq i) I)
    (hpointwise :
      ∀ t : ℝ, t ∈ I →
        Filter.Tendsto (fun i : ℕ => fSeq i t) Filter.atTop (nhds (f t))) :
    ∀ t : ℝ, t ∈ I →
      Filter.Tendsto (fun i : ℕ => deriv (fSeq i) t) Filter.atTop (nhds (deriv f t)) := by
  intro t ht
  let C : Set (Fin 1 → ℝ) := {u : Fin 1 → ℝ | u 0 ∈ I}
  have hCopen : IsOpen C := hIopen.preimage (continuous_apply 0)
  have hCconv : Convex ℝ C := by
    -- Pull the interval convexity back along the coordinate projection.
    intro u hu v hv a b ha hb hab
    show ((a • u + b • v) 0) ∈ I
    simpa [C, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      hIconv hu hv ha hb hab
  have hfLift : ConvexOn ℝ C (fun u : Fin 1 → ℝ => f (u 0)) := by
    -- The lifted limit function is still convex on the pulled-back interval.
    simpa [C] using
      hf.comp_linearMap (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
  have hfdiffLift : DifferentiableOn ℝ (fun u : Fin 1 → ℝ => f (u 0)) C := by
    intro u hu
    -- Differentiability also transports through the same linear projection.
    have hprojAt : DifferentiableAt ℝ (fun u : Fin 1 → ℝ => u 0) u := by
      simpa using (differentiableAt_apply (𝕜 := ℝ) (i := (0 : Fin 1)) (f := u))
    have hproj :
        DifferentiableWithinAt ℝ (fun u : Fin 1 → ℝ => u 0) C u :=
      hprojAt.differentiableWithinAt
    have hmaps : Set.MapsTo (fun u : Fin 1 → ℝ => u 0) C I := by
      intro v hv
      exact hv
    simpa [Function.comp] using (hfdiff (u 0) hu).comp u hproj hmaps
  have hSeqConvexLift :
      ∀ i : ℕ, ConvexOn ℝ C (fun u : Fin 1 → ℝ => fSeq i (u 0)) := by
    intro i
    -- Each approximating scalar function has the same convex lift.
    simpa [C] using
      (hSeqConvex i).comp_linearMap (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
  have hSeqDiffLift :
      ∀ i : ℕ, DifferentiableOn ℝ (fun u : Fin 1 → ℝ => fSeq i (u 0)) C := by
    intro i u hu
    -- Differentiability of each approximant lifts in the same way.
    have hprojAt : DifferentiableAt ℝ (fun u : Fin 1 → ℝ => u 0) u := by
      simpa using (differentiableAt_apply (𝕜 := ℝ) (i := (0 : Fin 1)) (f := u))
    have hproj :
        DifferentiableWithinAt ℝ (fun u : Fin 1 → ℝ => u 0) C u :=
      hprojAt.differentiableWithinAt
    have hmaps : Set.MapsTo (fun u : Fin 1 → ℝ => u 0) C I := by
      intro v hv
      exact hv
    simpa [Function.comp] using (hSeqDiff i (u 0) hu).comp u hproj hmaps
  have hpointwiseLift :
      ∀ x : Fin 1 → ℝ, x ∈ C →
        Filter.Tendsto (fun i : ℕ => fSeq i (x 0)) Filter.atTop (nhds (f (x 0))) := by
    intro x hx
    -- On the lifted set `C`, pointwise convergence is just the scalar hypothesis on coordinate `0`.
    simpa [C] using hpointwise (x 0) hx
  have htC : scalarPoint t ∈ C := by
    simpa [C, scalarPoint] using ht
  have hgrad :=
    convexOn_tendsto_euclideanGradientAt_of_pointwise_convergent
      (f := fun u : Fin 1 → ℝ => f (u 0))
      (fSeq := fun i u => fSeq i (u 0))
      hCopen hCconv hfLift hfdiffLift hSeqConvexLift hSeqDiffLift hpointwiseLift
      (scalarPoint t) htC
  have hcontApplyZero : Continuous fun v : Fin 1 → ℝ => v 0 := continuous_apply 0
  have hcoord :
      Filter.Tendsto
        (fun i : ℕ =>
          euclideanGradientAt (fun u : Fin 1 → ℝ => fSeq i (u 0)) (scalarPoint t) 0)
        Filter.atTop
        (nhds (euclideanGradientAt (fun u : Fin 1 → ℝ => f (u 0)) (scalarPoint t) 0)) := by
    -- Read the vector convergence at the unique coordinate of `Fin 1`.
    exact hcontApplyZero.continuousAt.tendsto.comp hgrad
  have hfdiffAt : DifferentiableAt ℝ f t :=
    (hfdiff t ht).differentiableAt (hIopen.mem_nhds ht)
  have hpointEq :
      euclideanGradientAt (fun u : Fin 1 → ℝ => f (u 0)) (scalarPoint t) =
        scalarPoint (deriv f t) :=
    helperForCorollary_25_7_1_euclideanGradientAt_scalarLift_eq_scalarPoint_deriv hfdiffAt
  have hseqEq :
      ∀ i : ℕ,
        euclideanGradientAt (fun u : Fin 1 → ℝ => fSeq i (u 0)) (scalarPoint t) =
          scalarPoint (deriv (fSeq i) t) := by
    intro i
    have hSeqDiffAt : DifferentiableAt ℝ (fSeq i) t :=
      (hSeqDiff i t ht).differentiableAt (hIopen.mem_nhds ht)
    exact
      helperForCorollary_25_7_1_euclideanGradientAt_scalarLift_eq_scalarPoint_deriv hSeqDiffAt
  -- Rewriting the `Fin 1` gradients by the bridge lemma leaves exactly the scalar derivatives.
  simpa [hpointEq, hseqEq, scalarPoint] using hcoord

end Section25
end Chap05
