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
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part10

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-
These lemmas supply the Chapter 18 ingredients for Rockafellar's reverse inclusion in
Theorem 25.6: exposed and extreme points contribute to `cl (conv S(x))`, while extreme directions
contribute to `K(x)`.
-/

/-- Helper for Theorem 25.6: in Rockafellar's Chapter 18 decomposition, every extreme direction of
the Euclideanized subdifferential fiber at `x` must already lie in the vectorized normal cone to
`dom f` at `x`. -/
  lemma helperForTheorem_25_6_extremeDirections_preimageSubdifferential_subset_preimageNormalCone_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x d : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hd :
      d ∈ {d : Fin n → Real | IsExtremeDirection (𝕜 := ℝ)
        (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) d}) :
    d ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
      normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x) := by
  -- Rockafellar's Euclideanized fiber `∂f(x)`.
  let C : Set (Fin n → Real) :=
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
  have hdext : IsExtremeDirection (𝕜 := ℝ) C d := by
    simpa [C] using hd
  rcases hdext with ⟨C', hhalf, hdir⟩
  rcases hdir with ⟨p, hdne, hC'⟩
  have hpC' : p ∈ C' := by
    rw [hC']
    exact ⟨0, by simp, by simp⟩
  have hpC : p ∈ C := hhalf.1.2.subset hpC'
  have hdrec : d ∈ Set.recessionCone C :=
    mem_recessionCone_of_isExtremeDirection_fin (hCclosed := hCclosed) (by simpa [C] using hd)
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
    by_contra hnonpos
    have hpos : 0 < dotProduct d (z - x) := by
      have : ¬ dotProduct d (z - x) ≤ 0 := by
        simpa [dotProductEquiv_apply_apply] using hnonpos
      exact lt_of_not_ge this
    lift f x to Real using hxFinite with xr hxr
    have hxFinite' : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
      rw [← hxr]
      simp
    lift f z to Real using hzFinite with zr hzr
    let M : Real := max (0 : Real) (zr - xr - dotProduct p (z - x)) + 1
    let t : Real := M / dotProduct d (z - x)
    have hMpos : 0 < M := by
      dsimp [M]
      linarith [le_max_left (0 : Real) (zr - xr - dotProduct p (z - x))]
    have ht : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg hMpos.le hpos.le
    have hpTd_mem : p + t • d ∈ C := hdrec hpC ht
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
        rcases convex_directionalDerivative_monotone_exists_and_sublinear f hfConv x hxFinite' with
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
          (((dotProduct (z - x) (p + t • d) : Real) : EReal)) ≤ (((zr - xr : Real) : EReal)) := by
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

/-- Helper for Theorem 25.6: Rockafellar's boundary argument reduces the extreme-point part of the
Euclideanized fiber to showing that every exposed point of `cl (conv S(x))` already lies in
`closure S(x)`. -/
lemma helperForTheorem_25_6_exposedPoints_closureConvexHull_subset_closure
    {n : Nat} {S : Set (Fin n → Real)}
    (hAbdd : Bornology.IsBounded (closure (convexHull Real S))) :
    (closure (convexHull Real S)).exposedPoints ℝ ⊆ closure S := by
  -- Here `A` is Rockafellar's `cl (conv S(x))`.
  let A : Set (Fin n → Real) := closure (convexHull Real S)
  have hAclosed : IsClosed A := by
    simpa [A] using isClosed_closure
  have hAcompact : IsCompact A := by
    exact (Metric.isCompact_iff_isClosed_bounded).2 ⟨hAclosed, by simpa [A] using hAbdd⟩
  have hSclosed : IsClosed (closure S) := isClosed_closure
  have hSsubA : closure S ⊆ A := by
    exact
      closure_minimal
        (Set.Subset.trans (subset_convexHull Real S) subset_closure)
        hAclosed
  intro p hp
  by_contra hpNotMem
  have hExpSingleton : IsExposed ℝ A ({p} : Set (Fin n → Real)) :=
    (mem_exposedPoints_iff_exposed_singleton (A := A) (x := p)).1 (by simpa [A] using hp)
  have hSingletonNe : ({p} : Set (Fin n → Real)).Nonempty := ⟨p, by simp⟩
  rcases theorem18_6_exposed_eq_toExposed (C := A) hExpSingleton hSingletonNe with ⟨l, hl⟩
  have hpFace : p ∈ l.toExposed A := by
    simpa [hl] using (show p ∈ ({p} : Set (Fin n → Real)) from by simp)
  have hDisj : Disjoint (closure S) (l.toExposed A) := by
    rw [← hl]
    exact Set.disjoint_singleton_right.2 hpNotMem
  rcases
      theorem18_6_exists_uniform_gap_on_closed_disjoint_subset
        (C := A) hAcompact (z := p) hpFace hSclosed hSsubA hDisj with
    ⟨δ, hδpos, hgap⟩
  let H : Set (Fin n → Real) := {x : Fin n → Real | l x ≤ l p - δ}
  have hHclosed : IsClosed H := by
    simpa [H, Set.preimage, Set.Iic] using
      (isClosed_Iic.preimage l.continuous)
  have hHconv : Convex Real H := by
    have hIic : Convex Real (Set.Iic (l p - δ : Real)) := convex_Iic (l p - δ)
    simpa [H, Set.preimage, Set.mem_Iic] using hIic.linear_preimage l.toLinearMap
  have hSsubH : S ⊆ H := by
    intro y hy
    exact hgap y (subset_closure hy)
  have hAsubH : A ⊆ H := by
    refine closure_minimal ?_ hHclosed
    exact (hHconv.convexHull_subset_iff).2 hSsubH
  have hpA : p ∈ A := by
    exact (exposedPoints_subset (A := A) (𝕜 := ℝ)) (by simpa [A] using hp)
  have hpH : p ∈ H := hAsubH hpA
  have hple : l p ≤ l p - δ := by simpa [H] using hpH
  linarith

/-- Helper for Theorem 25.6: Rockafellar's boundary argument reduces the exposed-point part of the
Euclideanized subdifferential to nearby gradient limits. -/
lemma helperForTheorem_25_6_exposedPoints_preimageSubdifferential_subset_closureGradientLimitVectors_of_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    (hdom : (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).Nonempty)
    {x p : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hp :
      p ∈ (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x).exposedPoints ℝ)) :
    p ∈ closure (gradientLimitVectorsAt f x) := by
  by_cases hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
  · simpa using
      helperForTheorem_25_6_exposedPoints_preimageSubdifferential_subset_closure_gradientLimitVectors_of_mem_interior
        (f := f) hf hf_closed hxInt hp
  · -- Rockafellar's Euclideanized fiber `∂f(x)`.
    let C : Set (Fin n → Real) :=
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
    obtain ⟨y, hFace, hyStrict⟩ :=
      helperForTheorem_25_6_exists_exposingDirection_singletonNormalFace_strict_polar_preimageNormalCone_of_mem_exposedPoints
        (f := f) hf hdom hx hp
    obtain ⟨t, ht, hxtInt⟩ :=
      helperForTheorem_25_6_exists_admissibleRay_of_strict_polar_preimageNormalCone
        (f := f) hf hdom hx hyStrict
    have hpGrad :
        p ∈ gradientLimitVectorsAt f x :=
      helperForTheorem_25_6_gradientLimitVector_of_singletonNormalFace_of_mem_effectiveDomain
        (f := f) hf hf_closed hx ⟨t, ht, hxtInt⟩ hFace
    exact subset_closure hpGrad


end Section25
end Chap05
