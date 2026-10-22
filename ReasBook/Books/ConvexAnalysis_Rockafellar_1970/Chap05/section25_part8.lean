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
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part7

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- Helper for Theorem 25.6: the textbook boundary step. If a singleton normal face at `x`
is exposed by a direction whose positive ray enters `interior (dom f)`, then the exposed point is
already a genuine gradient-limit vector at `x`. -/
lemma helperForTheorem_25_6_gradientLimitVector_of_singletonNormalFace_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x y p : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hray : ∃ t : Real, 0 < t ∧
      x + t • y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hFace : subdifferentialNormalFaceAt f x y = ({p} : Set (Fin n → Real))) :
    p ∈ gradientLimitVectorsAt f x := by
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hclosed : ClosedConvexFunction f := ⟨hfConv, hf_closed⟩
  have hdomConv : Convex Real domf :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hfConv
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) hx,
        hproper.2.2 x (by simp)⟩
  by_cases hy : y = 0
  · rcases hray with ⟨t, ht, hxtInt⟩
    have hxInt : x ∈ interior domf := by
      simpa [domf, hy] using hxtInt
    simpa [domf] using
      helperForTheorem_25_6_gradientLimitVector_of_singletonNormalFace
        (f := f) hf hf_closed hxInt (by simpa [hy] using hFace)
  · let yHat : Fin n → Real := ‖y‖⁻¹ • y
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
    have hyEq : ‖y‖ • yHat = y := by
      dsimp [yHat]
      rw [smul_smul]
      simp [hyNormPos.ne']
    have hFaceHat :
        subdifferentialNormalFaceAt f x yHat = ({p} : Set (Fin n → Real)) := by
      calc
        subdifferentialNormalFaceAt f x yHat =
            subdifferentialNormalFaceAt f x (‖y‖ • yHat) := by
              symm
              exact
                helperForTheorem_25_6_subdifferentialNormalFace_eq_of_pos_smul_direction
                  (f := f) (x := x) (y := yHat) hyNormPos
        _ = ({p} : Set (Fin n → Real)) := by simpa [hyEq] using hFace
    rcases hray with ⟨t, ht, hxtInt⟩
    let s : Real := t * ‖y‖
    have hs_pos : 0 < s := by
      dsimp [s]
      positivity
    have hsInt : x + s • yHat ∈ interior domf := by
      have hsEq : x + s • yHat = x + t • y := by
        calc
          x + s • yHat = x + ((t * ‖y‖) * ‖y‖⁻¹) • y := by
            simp [s, yHat, smul_smul]
          _ = x + t • y := by
            congr 1
            field_simp [hyNormPos.ne']
      simpa [domf] using hsEq ▸ hxtInt
    have hpFaceHat : p ∈ subdifferentialNormalFaceAt f x yHat := by
      simpa [hFaceHat]
    have hfiniteDir : upperDirectionalDerivativeAt f x yHat ≠ (⊥ : EReal) := by
      have hminor :
          (((dotProduct yHat p : Real) : EReal)) ≤ upperDirectionalDerivativeAt f x yHat := by
        exact
          (helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
            f hfConv x hxFinite p).1 hpFaceHat.1 yHat
      exact ne_of_gt <|
        lt_of_lt_of_le (show (⊥ : EReal) < (((dotProduct yHat p : Real) : EReal)) by simp) hminor
    have hqInt :
        ∀ i : ℕ,
          x + (s / ((i : Real) + 1)) • yHat ∈ interior domf := by
      intro i
      have hxClosure : x ∈ closure domf := subset_closure hx
      let a : Real := 1 / ((i : Real) + 1)
      let b : Real := (i : Real) / ((i : Real) + 1)
      have ha : 0 < a := by
        dsimp [a]
        positivity
      have hb : 0 ≤ b := by
        dsimp [b]
        positivity
      have hab : a + b = 1 := by
        dsimp [a, b]
        field_simp
        ring
      have hcombo :
          a • (x + s • yHat) + b • x = x + (s / ((i : Real) + 1)) • yHat := by
        ext j
        have hi1 : ((i : Real) + 1) ≠ 0 := by positivity
        dsimp [a, b]
        field_simp [hi1]
        ring
      rw [← hcombo]
      exact hdomConv.combo_interior_closure_mem_interior hsInt hxClosure ha hb hab
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
      have hMul :
          Filter.Tendsto (fun i : ℕ => s * (((i : Real) + 1)⁻¹)) Filter.atTop (nhds 0) := by
        simpa using
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
              (‖(x + (s / ((i : Real) + 1)) • yHat) - x‖⁻¹ *
                (s / ((i : Real) + 1))) • yHat := by
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
          (f := f) hclosed hproper (x := x) (y := yHat) hx
          (fun i : ℕ => x + (s / ((i : Real) + 1)) • yHat) hqDom hqTendsto hqNe hdir hfiniteDir
          ⟨s, le_of_lt hs_pos, hsInt⟩ with
      ⟨_hlimsup, hEventual⟩
    exact
      helperForTheorem_25_6_gradientLimitVector_of_eventuallySmallSubdifferentials
        (f := f) hf (x := x) (p := p)
        (q := fun i : ℕ => x + (s / ((i : Real) + 1)) • yHat)
        (hqInt := hqInt)
        (hqTendsto := hqTendsto)
        (hqSmall := by
          intro ε hε
          rcases hEventual ε hε with ⟨i0, hi0⟩
          refine ⟨i0, ?_⟩
          intro i hi
          simpa [yHat, hFaceHat] using hi0 i hi)

/-- Helper for Theorem 25.6: differentiating a fixed-step secant quotient at `w` gives the same
Euclidean gradient as differentiating `f` at the translated point `x + t • w`. -/
lemma helperForTheorem_25_6_erealGradient_secantQuotient_eq_erealGradient_translatedPoint
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x w : Fin n → Real} {t : Real}
    (hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (ht : 0 < t)
    (hw : ERealDifferentiableAt (fun v => directionalDifferenceQuotientAt f x v t) w)
    (htrans : ERealDifferentiableAt f (x + t • w)) :
    erealGradientAt hw = erealGradientAt htrans := by
  let g : (Fin n → Real) → EReal := fun v => directionalDifferenceQuotientAt f x v t
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hgConv : ConvexFunction g := by
    -- The secant quotient stays convex in the direction variable.
    exact helperForTheorem_5_24_9_secantQuotient_convex (f := f) hproper hfConv hxFinite ht
  have hwFinite : g w ≠ (⊤ : EReal) ∧ g w ≠ (⊥ : EReal) :=
    ERealDifferentiableAt.finiteAt hw
  have htransFinite : f (x + t • w) ≠ (⊤ : EReal) ∧ f (x + t • w) ≠ (⊥ : EReal) :=
    ERealDifferentiableAt.finiteAt htrans
  have hgradSecMem :
      erealGradientAt hw ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt g w) := by
    -- Differentiability identifies the secant-quotient gradient with its unique subgradient.
    simpa [g] using
      (((convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        g hgConv w hwFinite).1 hw).1 : _)
  have htransport :
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt g w) =
        ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f (x + t • w)) :=
    helperForTheorem_5_24_9_secantQuotient_subdifferential_transport
      (f := f) hproper hfConv (x := x) (u := w) (t := t) hxFinite htransFinite ht
  have hgradSecMem' :
      erealGradientAt hw ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f (x + t • w)) := by
    -- Transport the secant-quotient subgradient back to the translated point of `f`.
    rw [← htransport]
    exact hgradSecMem
  -- Uniqueness of the translated-point subgradient identifies the two Euclidean gradients.
  exact
    ((convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      f hfConv (x + t • w) htransFinite).1 htrans).2.2
      (erealGradientAt hw) hgradSecMem'

/-- Helper for Theorem 25.6: the normal cone to `dom f` is trivial at an interior point, so the
boundary term disappears there. -/
lemma helperForTheorem_25_6_preimage_normalCone_eq_singleton_zero_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ((dotProductEquiv Real (Fin n)) ⁻¹'
        normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x) =
      ({0} : Set (Fin n → Real)) := by
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomConv : Convex Real domf :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hfConv
  ext v
  constructor
  · intro hv
    rw [Set.mem_preimage] at hv
    have hxStep :
        ∀ y : Fin n → Real, ∃ ε > (0 : Real), x + ε • y ∈ domf := by
      exact
        (helperForTheorem_23_4_mem_interior_iff_forall_exists_add_smul_mem
          (C := domf) hdomConv x).1 hx
    rcases hxStep v with ⟨ε, hε, hplus⟩
    have hnonpos :
        (ε : Real) * (v ⬝ᵥ v) ≤ 0 := by
      -- Evaluating the normal inequality at the forward interior point controls `‖v‖²`.
      simpa [domf, dotProductEquiv_apply_apply, smul_eq_mul, sub_eq_add_neg] using
        (mem_normalConeAt_iff.1 hv).2 (x + ε • v) hplus
    have hsqZero : v ⬝ᵥ v = 0 := by
      have hsqNonneg : 0 ≤ v ⬝ᵥ v := dotProduct_self_nonneg _
      nlinarith
    -- Zero self-dot-product forces the vector itself to vanish.
    simpa [Set.mem_singleton_iff] using dotProduct_self_eq_zero.mp hsqZero
  · intro hv
    rw [Set.mem_singleton_iff] at hv
    rw [Set.mem_preimage]
    refine (mem_normalConeAt_iff).2 ?_
    constructor
    · exact interior_subset hx
    · intro z hz
      -- The zero vector satisfies the normal inequality trivially.
      simp [hv]

/-- Helper for Theorem 25.6: at a domain point, adding a normal-cone vector preserves
Euclideanized subgradient membership because `f + indicator(dom f) = f` and Chapter 23 applies. -/
lemma helperForTheorem_25_6_add_mem_preimageSubdifferential_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x u v : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hu : u ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x))
    (hv :
      v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
        normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x)) :
    u + v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) := by
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  let fTwo : Fin 2 → (Fin n → Real) → EReal :=
    fun i => Fin.cases f (fun _ => indicatorFunction domf) i
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomConv : Convex Real domf :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hfConv
  have hindicatorProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (indicatorFunction domf) :=
    properConvexFunctionOn_indicator_of_convex_of_nonempty (C := domf) hdomConv ⟨x, hx⟩
  have hriWitness :
      ∃ z : Fin n → Real,
        ∀ i : Fin 2,
          z ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (fTwo i)) := by
    rcases hdom with ⟨z, hz⟩
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
    have hpreimage : e.toHomeomorph ⁻¹' domf = e.symm '' domf := by
      ext u
      constructor
      · intro hu
        exact ⟨e u, hu, by simp [e]⟩
      · rintro ⟨v, hv, rfl⟩
        simpa [e]
    have hzIntE : e.symm z ∈ interior (e.symm '' domf) := by
      have hzPre : e.symm z ∈ e.toHomeomorph ⁻¹' interior domf := by
        simpa [Set.mem_preimage, e] using hz
      have hpre :
          e.toHomeomorph ⁻¹' interior domf = interior (e.symm '' domf) := by
        calc
          e.toHomeomorph ⁻¹' interior domf = interior (e.toHomeomorph ⁻¹' domf) :=
            e.toHomeomorph.preimage_interior (s := domf)
          _ = interior (e.symm '' domf) := by rw [hpreimage]
      rw [hpre] at hzPre
      exact hzPre
    have hzriDom : z ∈ euclideanRelativeInterior_fin n domf := by
      have hzI : e.symm z ∈ intrinsicInterior ℝ (e.symm '' domf) :=
        interior_subset_intrinsicInterior hzIntE
      exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := domf) (x := z)).2
        (intrinsicInterior_subset_euclideanRelativeInterior n (e.symm '' domf) hzI)
    refine ⟨z, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [fTwo, domf] using hzriDom
    · simpa [fTwo, effectiveDomain_indicatorFunction_eq, domf] using hzriDom
  have hsum :
      subdifferentialAt (fun y => ∑ i, fTwo i y) x =
        ∑ i, (subdifferentialAt (fTwo i) x : Set (Module.Dual ℝ (Fin n → Real))) :=
    subdifferential_sum_eq_sum_of_commonRelativeInteriorEffectiveDomain
      fTwo
      (fun i => Fin.cases hproper (fun _ => hindicatorProper) i)
      hriWitness x
  have hsumFn :
      (fun y => ∑ i, fTwo i y) = f := by
    funext y
    rw [Fin.sum_univ_two]
    simp [fTwo]
    change f y + indicatorFunction domf y = f y
    by_cases hy : y ∈ domf
    · -- On the effective domain, the indicator term vanishes.
      simp [indicatorFunction, domf, hy]
    · have hyTop : f y = ⊤ := by
        by_contra hyTop
        have hyMem : y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
          rw [effectiveDomain_eq]
          simp [lt_top_iff_ne_top, hyTop]
        exact hy (by simpa [domf] using hyMem)
      -- Off the effective domain, both sides are `⊤`.
      simp [indicatorFunction, domf, hy, hyTop]
  have hsumAt :
      subdifferentialAt f x =
        subdifferentialAt f x + normalConeAt domf x := by
    calc
      subdifferentialAt f x = subdifferentialAt (fun y => ∑ i, fTwo i y) x := by
        rw [hsumFn]
      _ =
          subdifferentialAt f x +
            subdifferentialAt (indicatorFunction domf) x := by
              simpa [fTwo, Fin.sum_univ_two] using hsum
      _ = subdifferentialAt f x + normalConeAt domf x := by
            rw [subdifferential_indicatorFunction_eq_normalConeAt_of_mem hx]
  have hu' : dotProductEquiv Real (Fin n) u ∈ subdifferentialAt f x := hu
  have hv' : dotProductEquiv Real (Fin n) v ∈ normalConeAt domf x := hv
  rw [Set.mem_preimage]
  rw [hsumAt]
  refine Set.mem_add.2 ?_
  refine ⟨dotProductEquiv Real (Fin n) u, hu', dotProductEquiv Real (Fin n) v, hv', ?_⟩
  -- The Euclidean identification is linear, so it preserves vector addition.
  ext y
  simp [dotProductEquiv_apply_apply]

/-- Helper for Theorem 25.6: every vectorized normal-cone element is a recession direction of the
Euclideanized subdifferential fiber at the same domain point. -/
lemma helperForTheorem_25_6_preimageNormalCone_subset_recessionCone_preimageSubdifferential_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x v : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hv :
      v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
        normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x)) :
    v ∈ Set.recessionCone (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) : Set
      (Fin n → Real)) := by
  intro u hu t ht
  have htv :
      t • v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
        normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x) := by
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
  exact
    helperForTheorem_25_6_add_mem_preimageSubdifferential_of_mem_effectiveDomain
      (f := f) hf hdom hx hu htv

/-- Helper for Theorem 25.6: the representation
`cl (conv S(x)) + K(x) ⊆ ∂ f (x)` already holds at every domain point. -/
lemma helperForTheorem_25_6_forwardInclusion_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    closure (convexHull Real (gradientLimitVectorsAt f x)) +
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x) ⊆
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) := by
  intro y hy
  rcases Set.mem_add.1 hy with ⟨u, hu, v, hv, rfl⟩
  have huSub :
      u ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) :=
    helperForTheorem_25_6_closureConvexHull_gradientLimitVectors_subset_preimageSubdifferential_of_mem_effectiveDomain
      (f := f) hf hf_closed hx hu
  -- The sum rule absorbs the normal-cone contribution into the same subdifferential fiber.
  exact
    helperForTheorem_25_6_add_mem_preimageSubdifferential_of_mem_effectiveDomain
      (f := f) hf hdom hx huSub hv

/-- Helper for Theorem 25.6: for an interior-domain fiber, Chapter 18 reduces the full equality to
the single missing fact that every exposed point of the Euclideanized subdifferential is already a
limit of nearby gradients. -/
lemma helperForTheorem_25_6_interior_preimageSubdifferential_eq_closureConvexHull_gradientLimitVectors_of_exposedPoints
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hExposed :
      ∀ p : Fin n → Real,
        p ∈ ((((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x).exposedPoints ℝ)) →
          p ∈ closure (gradientLimitVectorsAt f x)) :
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) =
      closure (convexHull Real (gradientLimitVectorsAt f x)) := by
  let C : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  let S : Set (Fin n → Real) := gradientLimitVectorsAt f x
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    -- Interior-domain points are finite, so the Chapter 23 fiber description applies.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) (interior_subset hx),
        hproper.2.2 x (by simp)⟩
  have hCclosed : IsClosed C := by
    -- The Euclideanized subdifferential is closed.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.1
  have hCconv : Convex Real C := by
    -- The same Chapter 23 theorem also gives convexity.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
  have hCne : Set.Nonempty C :=
    (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
      (f := f) hf hx).1
  have hCbdd : Bornology.IsBounded C :=
    (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
      (f := f) hf hx).2
  have hForward :
      closure (convexHull Real S) ⊆ C := by
    -- The easy inclusion was already proved directly from subgradient closedness and convexity.
    simpa [C, S] using
      helperForTheorem_25_6_closureConvexHull_gradientLimitVectors_subset_preimageSubdifferential_of_mem_interior
        (f := f) hf hf_closed hx
  apply Set.Subset.antisymm ?_ hForward
  have hExposedSubset : C.exposedPoints ℝ ⊆ closure S := by
    -- This is the only genuinely missing interior input.
    intro p hp
    simpa [C, S] using hExposed p hp
  have hClosureExposedSubset : closure (C.exposedPoints ℝ) ⊆ closure S := by
    -- Passing to closures keeps the same target because `closure S` is already closed.
    exact closure_minimal hExposedSubset isClosed_closure
  have hExtremeSubset : C.extremePoints ℝ ⊆ closure S := by
    -- Chapter 18 upgrades exposed points to all extreme points in the bounded case.
    exact
      Set.Subset.trans
        (theorem18_6_extremePoints_subset_closure_exposedPoints
          (C := C) hCclosed hCbdd hCconv)
        hClosureExposedSubset
  have hClosureSubset : closure S ⊆ closure (convexHull Real S) := by
    -- The target is a closed convex set already containing `S`.
    exact
      closure_minimal
        (Set.Subset.trans (subset_convexHull Real S) subset_closure)
        isClosed_closure
  have hTargetConv : Convex Real (closure (convexHull Real S)) := by
    exact (convex_convexHull Real S).closure
  have hHullSubset :
      convexHull Real (C.extremePoints ℝ) ⊆ closure (convexHull Real S) := by
    -- Convexity transports the extreme-point inclusion to their convex hull.
    exact
      (hTargetConv.convexHull_subset_iff).2
        (Set.Subset.trans hExtremeSubset hClosureSubset)
  intro z hz
  have hCeq :
      C = convexHull Real (C.extremePoints ℝ) :=
    closed_bounded_convex_eq_convexHull_extremePoints_part9
      C hCclosed hCbdd hCconv
  rw [hCeq] at hz
  exact hHullSubset hz

/-- Helper for Theorem 25.6: the only missing interior step is to realize every exposed point of
the bounded Euclideanized subdifferential as a genuine gradient-limit vector. -/
lemma helperForTheorem_25_6_exposedPoints_preimageSubdifferential_subset_closure_gradientLimitVectors_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x).exposedPoints ℝ) ⊆
      closure (gradientLimitVectorsAt f x) := by
  let C : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    -- Interior-domain points are finite, so Chapter 23 describes the Euclideanized
    -- subdifferential fiber by directional-derivative inequalities.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) (interior_subset hx),
        hproper.2.2 x (by simp)⟩
  have hCconv : Convex Real C := by
    -- The Euclideanized subdifferential is convex by Theorem 23.2.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
  intro p hp
  have hpExposed :
      IsExposedPoint C p := by
    rw [exposed_point_def] at hp
    rcases hp with ⟨hpC, l, hl⟩
    refine ⟨hCconv, ?_, ⟨l, ?_⟩⟩
    · intro q hq
      rcases Set.mem_singleton_iff.1 hq with rfl
      exact hpC
    · ext q
      constructor
      · intro hq
        have hqEq : q = p := Set.mem_singleton_iff.1 hq
        refine (mem_maximizers_iff (C := C) (h := l) (x := q)).2 ?_
        refine ⟨hqEq ▸ hpC, ?_⟩
        intro v hv
        simpa [hqEq] using (hl v hv).1
      · intro hq
        have hqData := (mem_maximizers_iff (C := C) (h := l) (x := q)).1 hq
        apply Set.mem_singleton_iff.2
        exact (hl q hqData.1).2 (hqData.2 p hpC)
  rcases
      (helperForTheorem_25_6_isExposedPoint_preimageSubdifferential_iff_exists_gradient_upperDirectionalDerivative_of_mem_interior
        (f := f) hf hx).1 (by simpa [C] using hpExposed) with
    ⟨y, hdiff, hgrad⟩
  have hFaceSingleton :
      subdifferentialNormalFaceAt f x y = ({p} : Set (Fin n → Real)) :=
    helperForTheorem_25_6_subdifferentialNormalFace_singleton_of_gradient_upperDirectionalDerivative
      (f := f) hf hx hdiff hgrad
  have hpGradLimit :
      p ∈ gradientLimitVectorsAt f x :=
    helperForTheorem_25_6_gradientLimitVector_of_singletonNormalFace
      (f := f) hf hf_closed hx hFaceSingleton
  -- The singleton-face reduction now produces an actual gradient-limit vector, hence certainly a
  -- point of the closure of the gradient-limit set.
  exact subset_closure hpGradLimit

/-- Helper for Theorem 25.6: at an interior-domain point, the Euclideanized subdifferential is
exactly the closed convex hull of the gradient-limit vectors. -/
lemma helperForTheorem_25_6_interior_preimageSubdifferential_eq_closureConvexHull_gradientLimitVectors
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) =
      closure (convexHull Real (gradientLimitVectorsAt f x)) := by
  -- Once the exposed-point realization is available, Chapter 18 closes the bounded interior case.
  exact
    helperForTheorem_25_6_interior_preimageSubdifferential_eq_closureConvexHull_gradientLimitVectors_of_exposedPoints
      (f := f) hf hf_closed hx
      (hExposed :=
        helperForTheorem_25_6_exposedPoints_preimageSubdifferential_subset_closure_gradientLimitVectors_of_mem_interior
          (f := f) hf hf_closed hx)

/-- Helper for Theorem 25.6: any exposed point of the Euclideanized fiber is cut out by a
singleton normal face. -/
lemma helperForTheorem_25_6_exists_exposingDirection_singletonNormalFace_of_mem_exposedPoints
    {n : Nat} (f : (Fin n → Real) → EReal)
    {x p : Fin n → Real}
    (hp :
      p ∈ (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x).exposedPoints ℝ)) :
    ∃ y : Fin n → Real, subdifferentialNormalFaceAt f x y = ({p} : Set (Fin n → Real)) := by
  let C : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  rw [exposed_point_def] at hp
  rcases hp with ⟨hpC, l, hl⟩
  let y : Fin n → Real := (dotProductEquiv Real (Fin n)).symm l
  have hy_eq : (dotProductEquiv Real (Fin n) y : Module.Dual ℝ (Fin n → Real)) = ↑l := by
    simp [y]
  have hy_apply : ∀ z : Fin n → Real, l z = dotProduct y z := by
    intro z
    have hEval :=
      congrArg (fun φ : Module.Dual ℝ (Fin n → Real) => φ z) hy_eq
    simpa [dotProductEquiv_apply_apply] using hEval.symm
  refine ⟨y, ?_⟩
  ext q
  constructor
  · intro hq
    have hqC : q ∈ C := by
      simpa [C] using hq.1
    have hpq : l p ≤ l q := by
      have hpq' : dotProduct y (p - q) ≤ 0 := hq.2 p (by simpa [C] using hpC)
      rw [dotProduct_sub] at hpq'
      rw [hy_apply, hy_apply]
      linarith
    have hqSingleton : q ∈ ({p} : Set (Fin n → Real)) := by
      exact Set.mem_singleton_iff.2 ((hl q hqC).2 hpq)
    simpa using hqSingleton
  · intro hq
    have hqEq : q = p := Set.mem_singleton_iff.1 hq
    subst q
    refine ⟨?_, ?_⟩
    · simpa [C] using hpC
    · intro z hz
      have hpMax : l z ≤ l p := (hl z (by simpa [C] using hz)).1
      rw [dotProduct_sub]
      have hzy : dotProduct y z ≤ dotProduct y p := by
        rwa [← hy_apply, ← hy_apply]
      linarith

/-- Helper for Theorem 25.6: an exposing direction for an exposed point of the Euclideanized fiber
lies in the raw polar of the vectorized normal cone. -/
lemma helperForTheorem_25_6_exists_exposingDirection_singletonNormalFace_polar_preimageNormalCone_of_mem_exposedPoints
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x p : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hp :
      p ∈ (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x).exposedPoints ℝ)) :
    ∃ y : Fin n → Real,
      subdifferentialNormalFaceAt f x y = ({p} : Set (Fin n → Real)) ∧
        ∀ v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
            normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x),
          dotProduct v y ≤ 0 := by
  let C : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  let K : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹'
      normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x)
  rcases
      helperForTheorem_25_6_exists_exposingDirection_singletonNormalFace_of_mem_exposedPoints
        (f := f) (x := x) hp with
    ⟨y, hFace⟩
  refine ⟨y, hFace, ?_⟩
  have hpFace : p ∈ subdifferentialNormalFaceAt f x y := by simpa [hFace]
  have hpC : p ∈ C := by
    simpa [C] using hpFace.1
  intro v hv
  have hvRec :
      v ∈ Set.recessionCone C :=
    helperForTheorem_25_6_preimageNormalCone_subset_recessionCone_preimageSubdifferential_of_mem_effectiveDomain
      (f := f) hf hdom hx (by simpa [K] using hv)
  have hpvC : p + (1 : Real) • v ∈ C := hvRec hpC (by norm_num)
  have hineq :
      dotProduct y ((p + (1 : Real) • v) - p) ≤ 0 :=
    hpFace.2 (p + (1 : Real) • v) (by simpa [C] using hpvC)
  simpa [dotProduct_comm] using hineq

/-- Helper for Theorem 25.6: the exposing direction of an exposed point of the Euclideanized
fiber is strictly negative on every nonzero vector of the vectorized normal cone. This is the
precise textbook condition used to show that the positive ray through the exposing direction cannot
be properly separated from `dom f`. -/
lemma helperForTheorem_25_6_exists_exposingDirection_singletonNormalFace_strict_polar_preimageNormalCone_of_mem_exposedPoints
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x p : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hp :
      p ∈ (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x).exposedPoints ℝ)) :
    ∃ y : Fin n → Real,
      subdifferentialNormalFaceAt f x y = ({p} : Set (Fin n → Real)) ∧
        ∀ v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
            normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x),
          v ≠ 0 → dotProduct v y < 0 := by
  let C : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  let K : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹'
      normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x)
  obtain ⟨y, hFace, hyPolar⟩ :=
    helperForTheorem_25_6_exists_exposingDirection_singletonNormalFace_polar_preimageNormalCone_of_mem_exposedPoints
      (f := f) hf hdom hx hp
  refine ⟨y, hFace, ?_⟩
  have hpFace : p ∈ subdifferentialNormalFaceAt f x y := by
    simpa [hFace]
  have hpC : p ∈ C := by
    simpa [C] using hpFace.1
  intro v hv hvne
  have hvle : dotProduct v y ≤ 0 := hyPolar v hv
  by_contra hnotlt
  have hnonneg : 0 ≤ dotProduct v y := le_of_not_gt hnotlt
  have hEq : dotProduct v y = 0 := by linarith
  have hvRec :
      v ∈ Set.recessionCone C :=
    helperForTheorem_25_6_preimageNormalCone_subset_recessionCone_preimageSubdifferential_of_mem_effectiveDomain
      (f := f) hf hdom hx (by simpa [K] using hv)
  have hpvC : p + (1 : Real) • v ∈ C := hvRec hpC (by norm_num)
  have hpvFace : p + (1 : Real) • v ∈ subdifferentialNormalFaceAt f x y := by
    refine ⟨by simpa [C] using hpvC, ?_⟩
    intro z hz
    have hzle : dotProduct y z ≤ dotProduct y p := by
      have hzface : dotProduct y (z - p) ≤ 0 := hpFace.2 z hz
      rw [dotProduct_sub] at hzface
      linarith
    have hpvEq : dotProduct y (p + (1 : Real) • v) = dotProduct y p := by
      have hEq' : dotProduct y v = 0 := by simpa [dotProduct_comm] using hEq
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, one_mul, hEq', add_zero]
    rw [dotProduct_sub, hpvEq]
    linarith
  have hpvEq : p + (1 : Real) • v = p := by
    simpa [hFace] using hpvFace
  have hvZero : v = 0 := by
    have hsubEq := congrArg (fun z : Fin n → Real => z - p) hpvEq
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsubEq
  exact hvne hvZero

/-- Helper for Theorem 25.6: the textbook Theorem 11.3 step. If an exposing direction is strictly
negative on every nonzero vector of the vectorized normal cone, then the positive ray through that
direction must meet `interior (dom f)`. -/
lemma helperForTheorem_25_6_exists_admissibleRay_of_strict_polar_preimageNormalCone
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x y : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hyStrict :
      ∀ v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
          normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x),
        v ≠ 0 → dotProduct v y < 0) :
    ∃ t : Real, 0 < t ∧
      x + t • y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  let S : Set (Fin n → Real) :=
    {u | ∃ t : Real, 0 < t ∧ x + t • u ∈ interior domf}
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomConv : Convex Real domf :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hfConv
  have hIntConv : Convex Real (interior domf) := hdomConv.interior
  let Scone : ConvexCone ℝ (Fin n → Real) :=
    { carrier := S
      smul_mem' := by
        intro c hc u hu
        rcases hu with ⟨t, ht, htu⟩
        refine ⟨t / c, div_pos ht hc, ?_⟩
        have hEq : x + (t / c) • (c • u) = x + t • u := by
          calc
            x + (t / c) • (c • u) = x + ((t / c) * c) • u := by rw [smul_smul]
            _ = x + t • u := by
              congr 1
              field_simp [hc.ne']
        exact hEq.symm ▸ htu
      add_mem' := by
        intro u hu v hv
        rcases hu with ⟨tu, htu, huInt⟩
        rcases hv with ⟨tv, htv, hvInt⟩
        refine ⟨tu * tv / (tu + tv), by positivity, ?_⟩
        have hsum_ne : tu + tv ≠ 0 := by linarith
        have hAlpha_nonneg : 0 ≤ tv / (tu + tv) := by positivity
        have hBeta_nonneg : 0 ≤ tu / (tu + tv) := by positivity
        have hAlphaBeta :
            tv / (tu + tv) + tu / (tu + tv) = 1 := by
          field_simp [hsum_ne]
          ring
        have hcombo :
            x + (tu * tv / (tu + tv)) • (u + v) =
              (tv / (tu + tv)) • (x + tu • u) +
                (tu / (tu + tv)) • (x + tv • v) := by
          ext i
          simp [Pi.add_apply, Pi.smul_apply]
          field_simp [hsum_ne]
          ring
        rw [hcombo]
        have hSeg :
            (tv / (tu + tv)) • (x + tu • u) + (tu / (tu + tv)) • (x + tv • v) ∈
              segment ℝ (x + tv • v) (x + tu • u) := by
          refine ⟨tu / (tu + tv), tv / (tu + tv), hBeta_nonneg, hAlpha_nonneg, ?_, ?_⟩
          · simpa [add_comm] using hAlphaBeta
          · simp [add_comm, add_assoc]
        exact hIntConv.segment_subset hvInt huInt hSeg }
  have hSconv : Convex Real S := Scone.convex
  have hSne : S.Nonempty := by
    rcases hdom with ⟨z, hz⟩
    refine ⟨z - x, ?_⟩
    refine ⟨1, by norm_num, ?_⟩
    simpa [domf]
  by_cases hyS : y ∈ S
  · simpa [S] using hyS
  · rcases
      cor11_5_2_exists_hyperplaneSeparatesProperly_point
        (n := n) (C := S) (a := y) hSne hSconv hyS with
      ⟨H, hsep⟩
    rcases hyperplaneSeparatesProperly_oriented n H ({y} : Set (Fin n → Real)) S hsep with
      ⟨b, β, hb0, _hH, hyβ, hSβ, _hnot⟩
    have hβle : β ≤ y ⬝ᵥ b := hyβ y (by simp)
    have hzeroClosure : (0 : Fin n → Real) ∈ closure S := by
      rcases hSne with ⟨u0, hu0⟩
      let zSeq : ℕ → Fin n → Real := fun i => (1 / ((i : Real) + 1)) • u0
      have hzMem : ∀ i : ℕ, zSeq i ∈ S := by
        intro i
        rcases hu0 with ⟨t, ht, huInt⟩
        refine ⟨t * ((i : Real) + 1), by positivity, ?_⟩
        have hi1 : ((i : Real) + 1) ≠ 0 := by positivity
        have hEq :
          x + (t * ((i : Real) + 1)) • zSeq i =
              x + (t * ((i : Real) + 1)) • ((1 / ((i : Real) + 1)) • u0) := by
                rfl
        have hEq' :
            x + (t * ((i : Real) + 1)) • zSeq i = x + t • u0 := by
          calc
            x + (t * ((i : Real) + 1)) • zSeq i =
                x + (t * ((i : Real) + 1)) • ((1 / ((i : Real) + 1)) • u0) := hEq
            _ = x + ((t * ((i : Real) + 1)) * (1 / ((i : Real) + 1))) • u0 := by
                  rw [smul_smul]
            _ = x + t • u0 := by
                  congr 1
                  field_simp [hi1]
        exact hEq'.symm ▸ huInt
      have hzTendsto :
          Filter.Tendsto zSeq Filter.atTop (nhds (0 : Fin n → Real)) := by
        have hInvTendsto :
            Filter.Tendsto (fun i : ℕ => (((i : Real) + 1)⁻¹)) Filter.atTop (nhds 0) := by
          simpa [Function.comp, one_mul] using
            (tendsto_mul_add_inv_atTop_nhds_zero (1 : Real) 1 one_ne_zero).comp
              tendsto_natCast_atTop_atTop
        have hScaleTendsto :
            Filter.Tendsto (fun i : ℕ => 1 / ((i : Real) + 1)) Filter.atTop (nhds 0) := by
          simpa [div_eq_mul_inv] using hInvTendsto
        have hContSmul : Continuous fun t : Real => t • u0 := by
          fun_prop
        simpa [zSeq] using hContSmul.continuousAt.tendsto.comp hScaleTendsto
      have hzClosure :
          ∀ᶠ i in Filter.atTop, zSeq i ∈ closure S := by
        refine Filter.Eventually.of_forall ?_
        intro i
        exact subset_closure (hzMem i)
      exact isClosed_closure.mem_of_tendsto hzTendsto hzClosure
    let Tβ : Set (Fin n → Real) := {u : Fin n → Real | u ⬝ᵥ b ≤ β}
    have hTβclosed : IsClosed Tβ := by
      have hcont : Continuous fun u : Fin n → Real => u ⬝ᵥ b := by
        fun_prop
      simpa [Tβ] using isClosed_le hcont continuous_const
    have hSsubTβ : S ⊆ Tβ := by
      intro u hu
      exact hSβ u hu
    have hzeroTβ : (0 : Fin n → Real) ∈ Tβ :=
      (hTβclosed.closure_subset_iff.2 hSsubTβ) hzeroClosure
    have hβnonneg : 0 ≤ β := by
      simpa [Tβ] using hzeroTβ
    have hpolar : ∀ u ∈ S, u ⬝ᵥ b ≤ 0 := by
      intro u hu
      by_contra hupos
      have hu_pos : 0 < u ⬝ᵥ b := lt_of_not_ge hupos
      let c : Real := β / (u ⬝ᵥ b) + 1
      have hc_pos : 0 < c := by
        dsimp [c]
        positivity
      have hcu : c • u ∈ S := by
        rcases hu with ⟨t, ht, huInt⟩
        refine ⟨t / c, div_pos ht hc_pos, ?_⟩
        have hEq : x + (t / c) • (c • u) = x + t • u := by
          calc
            x + (t / c) • (c • u) = x + ((t / c) * c) • u := by rw [smul_smul]
            _ = x + t • u := by
              congr 1
              field_simp [hc_pos.ne']
        exact hEq.symm ▸ huInt
      have hcIneq : (c • u) ⬝ᵥ b ≤ β := hSβ (c • u) hcu
      have hcIneq' : c * (u ⬝ᵥ b) ≤ β := by
        simpa [c, smul_eq_mul] using hcIneq
      dsimp [c] at hcIneq'
      have huLt : β < (β / (u ⬝ᵥ b) + 1) * (u ⬝ᵥ b) := by
        calc
          β < β + u ⬝ᵥ b := by linarith
          _ = (β / (u ⬝ᵥ b) + 1) * (u ⬝ᵥ b) := by
                field_simp [hu_pos.ne']
      linarith
    have hbPolar :
        dotProductEquiv Real (Fin n) b ∈ polarCone (E := (Fin n → Real)) S := by
      refine (mem_polarCone_iff (E := (Fin n → Real)) (K := S)
        (φ := dotProductEquiv Real (Fin n) b)).2 ?_
      intro u hu
      simpa [dotProductEquiv_apply_apply, dotProduct_comm] using hpolar u hu
    have hbNormal :
        b ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' normalConeAt domf x) := by
      rw [Set.mem_preimage]
      refine (mem_normalConeAt_iff).2 ?_
      constructor
      · simpa [domf] using hx
      · intro z hz
        let T0 : Set (Fin n → Real) := {w | w ⬝ᵥ b ≤ x ⬝ᵥ b}
        have hT0closed : IsClosed T0 := by
          have hcont : Continuous fun w : Fin n → Real => w ⬝ᵥ b := by
            fun_prop
          simpa [T0] using isClosed_le hcont continuous_const
        have hIntSubset : interior domf ⊆ T0 := by
          intro w hw
          have hwDir : w - x ∈ S := by
            refine ⟨1, by norm_num, ?_⟩
            simpa [domf] using hw
          have hwPolar :
              (dotProductEquiv Real (Fin n) b) (w - x) ≤ 0 :=
            (mem_polarCone_iff (E := (Fin n → Real)) (K := S)
              (φ := dotProductEquiv Real (Fin n) b)).1 hbPolar (w - x) hwDir
          simpa [T0, dotProductEquiv_apply_apply, dotProduct_sub, dotProduct_comm] using hwPolar
        have hzClosure : z ∈ closure (interior domf) := by
          rw [hdomConv.closure_interior_eq_closure_of_nonempty_interior hdom]
          exact subset_closure hz
        have hzInT : z ∈ T0 := (hT0closed.closure_subset_iff.2 hIntSubset) hzClosure
        simpa [T0, dotProduct_sub, dotProduct_comm] using hzInT
    have hyNonneg : 0 ≤ dotProduct b y := by
      have : 0 ≤ y ⬝ᵥ b := le_trans hβnonneg hβle
      simpa [dotProduct_comm] using this
    have hyNeg : dotProduct b y < 0 := hyStrict b hbNormal hb0
    linarith


end Section25
end Chap05
