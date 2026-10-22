/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part8

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- Helper for Theorem 25.6: if a normal face is exposed by a direction that is strictly negative
on every nonzero vector of the vectorized normal cone, then that face is bounded (hence compact,
since it is closed). This is the compact-face input behind the unbounded/no-lines Chapter 18 route.
-/
lemma helperForTheorem_25_6_subdifferentialNormalFace_bounded_of_strict_polar_preimageNormalCone
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x y p : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hpFace : p ∈ subdifferentialNormalFaceAt f x y)
    (hyStrict :
      ∀ v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
          normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x),
        v ≠ 0 → dotProduct v y < 0) :
    Bornology.IsBounded (subdifferentialNormalFaceAt f x y) := by
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  let C : Set (Fin n → Real) := ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
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
  have hFaceEq :
      subdifferentialNormalFaceAt f x y =
        C ∩ {q : Fin n → Real | dotProduct q y = dotProduct p y} := by
    ext q
    constructor
    · intro hq
      refine ⟨hq.1, ?_⟩
      have hpq : dotProduct y (p - q) ≤ 0 := hq.2 p hpFace.1
      have hqp : dotProduct y (q - p) ≤ 0 := hpFace.2 q hq.1
      have hEq : dotProduct y q = dotProduct y p := by
        have h1 : dotProduct y p ≤ dotProduct y q := by
          rw [dotProduct_sub] at hpq
          linarith
        have h2 : dotProduct y q ≤ dotProduct y p := by
          rw [dotProduct_sub] at hqp
          linarith
        exact le_antisymm h2 h1
      simpa [dotProduct_comm] using hEq
    · rintro ⟨hqC, hqEq⟩
      refine ⟨hqC, ?_⟩
      intro z hz
      have hzLe : dotProduct y z ≤ dotProduct y p := by
        have hpz : dotProduct y (z - p) ≤ 0 := hpFace.2 z hz
        rw [dotProduct_sub] at hpz
        linarith
      rw [dotProduct_sub]
      have hqEq' : dotProduct y q = dotProduct y p := by
        simpa [dotProduct_comm] using hqEq
      linarith
  have hFaceClosed : IsClosed (subdifferentialNormalFaceAt f x y) := by
    rw [hFaceEq]
    refine hCclosed.inter ?_
    have hcont : Continuous fun q : Fin n → Real => dotProduct q y := by
      simpa [dotProductEquiv_apply_apply, dotProduct_comm] using
        ((dotProductEquiv Real (Fin n) y).continuous_of_finiteDimensional : Continuous
          (dotProductEquiv Real (Fin n) y))
    exact isClosed_eq hcont continuous_const
  have hFaceConv : Convex Real (subdifferentialNormalFaceAt f x y) := by
    rw [hFaceEq]
    refine hCconv.inter ?_
    intro q hq r hr a b ha hb hab
    change dotProduct (a • q + b • r) y = dotProduct p y
    calc
      dotProduct (a • q + b • r) y = a * dotProduct q y + b * dotProduct r y := by
        simp [dotProduct_add, smul_dotProduct]
      _ = dotProduct p y := by
        rw [hq, hr]
        rw [← add_mul, hab, one_mul]
  have hRecZero :
      Set.recessionCone (subdifferentialNormalFaceAt f x y) = ({0} : Set (Fin n → Real)) := by
    ext v
    constructor
    · intro hv
      have hpvFace : p + (1 : Real) • v ∈ subdifferentialNormalFaceAt f x y := by
        exact hv hpFace (by norm_num)
      have hvyLe : dotProduct v y ≤ 0 := by
        have hpair : dotProduct y ((p + (1 : Real) • v) - p) ≤ 0 := hpFace.2 _ hpvFace.1
        simpa [dotProduct_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hpair
      have h0LeVY : 0 ≤ dotProduct v y := by
        have hpair : dotProduct y (p - (p + (1 : Real) • v)) ≤ 0 := hpvFace.2 p hpFace.1
        simpa [dotProduct_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hpair
      have hvInNormal :
          v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' normalConeAt domf x) := by
        rw [Set.mem_preimage]
        refine (mem_normalConeAt_iff).2 ?_
        constructor
        · simpa [domf] using hx
        · intro z hz
          have hzFinite : f z ≠ ⊤ ∧ f z ≠ ⊥ := by
            exact
              ⟨mem_effectiveDomain_imp_ne_top
                  (S := (Set.univ : Set (Fin n → Real))) (f := f) hz,
                hproper.2.2 z (by simp)⟩
          lift f x to Real using hxFinite with xr hxr
          lift f z to Real using hzFinite with zr hzr
          have hpReal : xr + dotProduct p (z - x) ≤ zr := by
            exact
              EReal.coe_le_coe_iff.mp
                (by simpa [hxr, hzr, dotProductEquiv_apply_apply, EReal.coe_add] using hpFace.1 z)
          have hvLe : dotProduct v (z - x) ≤ 0 := by
            by_contra hvPos
            have hvPos' : 0 < dotProduct v (z - x) := lt_of_not_ge hvPos
            let A : Real := max 0 (zr - xr - dotProduct p (z - x)) + 1
            let a : Real := A / dotProduct v (z - x)
            have hApos : 0 < A := by
              dsimp [A]
              positivity
            have haPos : 0 < a := by
              dsimp [a]
              positivity
            have hpavFace : p + a • v ∈ subdifferentialNormalFaceAt f x y := by
              exact hv hpFace haPos.le
            have hpavReal :
                xr + (dotProduct p (z - x) + a * dotProduct v (z - x)) ≤ zr := by
              exact
                EReal.coe_le_coe_iff.mp
                  (by
                    simpa [hxr, hzr, dotProductEquiv_apply_apply, EReal.coe_add, dotProduct_sub,
                      add_assoc, add_left_comm, add_comm, dotProduct_add, smul_dotProduct] using
                      hpavFace.1 z)
            have haMul : a * dotProduct v (z - x) = A := by
              dsimp [a, A]
              field_simp [hvPos']
            have hgt : zr < xr + (dotProduct p (z - x) + a * dotProduct v (z - x)) := by
              rw [haMul]
              dsimp [A]
              linarith [le_max_right 0 (zr - xr - dotProduct p (z - x))]
            exact (not_lt_of_ge hpavReal) hgt
          simpa [dotProductEquiv_apply_apply] using hvLe
      by_cases hv0 : v = 0
      · simpa [hv0]
      · have hstrict : dotProduct v y < 0 := hyStrict v hvInNormal hv0
        linarith
    · intro hv
      have hv0 : v = 0 := by simpa using hv
      subst hv0
      show (0 : Fin n → Real) ∈ Set.recessionCone (subdifferentialNormalFaceAt f x y)
      intro q hq a ha
      simpa using hq
  exact
    (helperForText_21_3_3_bounded_iff_recessionCone_eq_singleton_zero_fin
      (S := subdifferentialNormalFaceAt f x y) ⟨p, hpFace⟩ hFaceClosed hFaceConv).2 hRecZero

/-- Helper for Theorem 25.6: at an interior-domain point, the support of the closed convex hull of
the gradient-limit vectors is exactly the subdifferential support. -/
lemma helperForTheorem_25_6_support_closureConvexHull_gradientLimitVectors_eq_subdifferentialSupport_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∀ y : Fin n → Real,
      supportFunctionEReal (closure (convexHull Real (gradientLimitVectorsAt f x))) y =
        subdifferentialSupportAt f x y := by
  intro y
  have hSetEq :
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) =
        closure (convexHull Real (gradientLimitVectorsAt f x)) :=
    helperForTheorem_25_6_interior_preimageSubdifferential_eq_closureConvexHull_gradientLimitVectors
      (f := f) hf hf_closed hx
  -- Rewrite the interior gradient-limit hull as the Euclideanized subdifferential and then use
  -- the Chapter 23 support-function identity.
  calc
    supportFunctionEReal (closure (convexHull Real (gradientLimitVectorsAt f x))) y =
        supportFunctionEReal (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) y := by
          rw [hSetEq]
    _ = subdifferentialSupportAt f x y :=
      helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x y

/-- Helper for Theorem 25.6: at an interior-domain point, a support-maximizing exposed point of
the Euclideanized subdifferential already lies in `closure (gradientLimitVectorsAt f x)`, so it
realizes the directional derivative. -/
lemma helperForTheorem_25_6_exists_closureGradientLimitVector_attaining_directionalDerivative_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∀ u : Fin n → Real, ∃ q : Fin n → Real,
      q ∈ closure (gradientLimitVectorsAt f x) ∧
        (((dotProduct q u : Real) : EReal) = upperDirectionalDerivativeAt f x u) := by
  intro u
  let C : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    -- Interior-domain points are finite.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) (interior_subset hx),
        hproper.2.2 x (by simp)⟩
  have hCclosed : IsClosed C := by
    -- Chapter 23 supplies closedness of the Euclideanized subdifferential.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.1
  have hCconv : Convex Real C := by
    -- The same theorem supplies convexity as well.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (f := f) hfConv x hxFinite (dotProductEquiv Real (Fin n) 0)).2.2.1
  have hCne : Set.Nonempty C :=
    (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
      (f := f) hf hx).1
  have hCbdd : Bornology.IsBounded C :=
    (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
      (f := f) hf hx).2
  obtain ⟨q, hqFace, hqExt⟩ :=
    theorem18_8_exists_exposedPoint_maximizer_dotProduct
      (n := n) (C := C) hCclosed hCbdd hCne u
  have hqClosureExposed : q ∈ closure (C.exposedPoints ℝ) := by
    -- Straszewicz upgrades the extreme-point maximizer to a limit of exposed points.
    exact
      (theorem18_6_extremePoints_subset_closure_exposedPoints
        (n := n) (C := C) hCclosed hCbdd hCconv) hqExt
  have hExposedSubset : C.exposedPoints ℝ ⊆ closure (gradientLimitVectorsAt f x) := by
    -- The interior exposed-point theorem turns those exposed points into gradient limits.
    intro p hp
    simpa [C] using
      helperForTheorem_25_6_exposedPoints_preimageSubdifferential_subset_closure_gradientLimitVectors_of_mem_interior
        (f := f) hf hf_closed hx hp
  have hqClosure : q ∈ closure (gradientLimitVectorsAt f x) := by
    -- Closing up the exposed-point inclusion keeps the same target.
    exact (closure_minimal hExposedSubset isClosed_closure) hqClosureExposed
  have hqSupport :
      supportFunctionEReal C u = (((dotProduct q u : Real) : EReal)) := by
    -- A point in the exposed face exactly attains the support in direction `u`.
    rw [supportFunctionEReal]
    apply le_antisymm
    · refine sSup_le ?_
      rintro z ⟨p, hpC, rfl⟩
      exact_mod_cast (hqFace.2 p hpC)
    · exact le_sSup ⟨q, hqFace.1, rfl⟩
  have hDirEq : subdifferentialSupportAt f x u = upperDirectionalDerivativeAt f x u := by
    have hxri :
        x ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      helperForTheorem_23_4_mem_relativeInterior_of_mem_interior (n := n) (C := effectiveDomain Set.univ f) hx
    -- Chapter 23 already identifies the interior directional derivative with the support of `∂f(x)`.
    exact
      (helperForTheorem_23_4_directionalDerivative_regularity_of_mem_relativeInterior
        (f := f) hproper x hxri).2.2.2.2 u |> Eq.symm
  refine ⟨q, hqClosure, ?_⟩
  -- Rewrite the attained support value as the directional derivative.
  calc
    (((dotProduct q u : Real) : EReal)) = supportFunctionEReal C u := by
      symm
      exact hqSupport
    _ = subdifferentialSupportAt f x u := by
      simpa [C] using helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x u
    _ = upperDirectionalDerivativeAt f x u := hDirEq

/-- Helper for Theorem 25.6: on interior fibers, the closed convex hull of the gradient-limit
vectors is bounded because it coincides with the bounded Euclideanized subdifferential. -/
lemma helperForTheorem_25_6_bounded_closureConvexHull_gradientLimitVectors_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    (hf_closed : LowerSemicontinuous f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    Bornology.IsBounded (closure (convexHull Real (gradientLimitVectorsAt f x))) := by
  have hSetEq :
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) =
        closure (convexHull Real (gradientLimitVectorsAt f x)) :=
    helperForTheorem_25_6_interior_preimageSubdifferential_eq_closureConvexHull_gradientLimitVectors
      (f := f) hf hf_closed hx
  have hFiberBounded :
      Bornology.IsBounded
        (((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) :=
    (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
      (f := f) hf hx).2
  -- The interior equality transfers the standard boundedness of the Euclideanized
  -- subdifferential to the gradient-limit hull.
  simpa [hSetEq] using hFiberBounded

/-- Helper for Theorem 25.6: if a positive ray from `x` in the direction `u` enters
`interior (dom f)`, then Chapter 23 already identifies the support of `∂ f(x)` with the upper
directional derivative at `u`. -/
lemma helperForTheorem_25_6_subdifferentialSupport_eq_upperDirectionalDerivative_of_mem_admissibleDirection
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x u : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hu : ∃ t : Real, 0 < t ∧
      x + t • u ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    subdifferentialSupportAt f x u = upperDirectionalDerivativeAt f x u := by
  let D : (Fin n → Real) → EReal := upperDirectionalDerivativeAt f x
  let S : Set (Fin n → Real) :=
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    constructor
    · exact
        mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) hx
    · exact hproper.2.2 x (by simp)
  have hClosureEq : convexFunctionClosure D = subdifferentialSupportAt f x := by
    -- Theorem 23.2 identifies the closure of the directional derivative with the support of the
    -- Euclideanized subdifferential fiber.
    simpa [D] using
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hfConv x hxFinite (0 : Module.Dual ℝ (Fin n → Real))).2.2.2
  rcases hu with ⟨t, ht, htInt⟩
  have htRi :
      x + t • u ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    helperForTheorem_23_4_mem_relativeInterior_of_mem_interior htInt
  have htuRi :
      t • u ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → Real)) D) := by
    -- Theorem 23.3 moves relative-interior domain points of `f` to relative-interior directions
    -- of the upper directional derivative.
    simpa [D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      helperForTheorem_23_3_directionToRi_mem_ri_effectiveDomain_directionalDerivative
        f hfConv x (x + t • u) hxFinite htRi
  have hAtScale : subdifferentialSupportAt f x (t • u) = D (t • u) := by
    by_cases hsub : Set.Nonempty (subdifferentialAt f x)
    · have hDproper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) D :=
        helperForTheorem_23_4_upperDirectionalDerivative_proper_of_subdifferentiable
          f hproper x hsub
      -- On the relative interior of `dom D`, the closed hull agrees with `D` itself.
      calc
        subdifferentialSupportAt f x (t • u) = convexFunctionClosure D (t • u) := by
          symm
          exact congrFun hClosureEq (t • u)
        _ = D (t • u) := by
          have htuRiE :
              (EuclideanSpace.equiv (Fin n) ℝ).symm (t • u) ∈
                euclideanRelativeInterior n
                  ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → Real)) ⁻¹'
                    effectiveDomain (Set.univ : Set (Fin n → Real)) D) := by
            rw [helperForTheorem_23_4_preimage_eq_symmImage]
            exact
              (mem_euclideanRelativeInterior_fin_iff (n := n)
                (C := effectiveDomain (Set.univ : Set (Fin n → Real)) D)
                (x := t • u)).1 htuRi
          simpa using
            (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
              (f := D) hDproper).2
              ((EuclideanSpace.equiv (Fin n) ℝ).symm (t • u)) htuRiE
    · have hDimproper :
          ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) D :=
        helperForTheorem_23_3_directionalDerivative_improper_of_empty_subdifferential
          f hfConv x hxFinite hsub
      -- The same relative-interior agreement is available in the improper branch.
      calc
        subdifferentialSupportAt f x (t • u) = convexFunctionClosure D (t • u) := by
          symm
          exact congrFun hClosureEq (t • u)
        _ = D (t • u) := by
          have htuRiE :
              (EuclideanSpace.equiv (Fin n) ℝ).symm (t • u) ∈
                euclideanRelativeInterior n
                  ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → Real)) ⁻¹'
                    effectiveDomain (Set.univ : Set (Fin n → Real)) D) := by
            rw [helperForTheorem_23_4_preimage_eq_symmImage]
            exact
              (mem_euclideanRelativeInterior_fin_iff (n := n)
                (C := effectiveDomain (Set.univ : Set (Fin n → Real)) D)
                (x := t • u)).1 htuRi
          simpa using
            (convexFunctionClosure_closed_improperConvexFunctionOn_and_agrees_on_ri
              (f := D) hDimproper).2
              ((EuclideanSpace.equiv (Fin n) ℝ).symm (t • u)) htuRiE
  by_cases hsub : Set.Nonempty (subdifferentialAt f x)
  · have hSnonempty : S.Nonempty := by
      rcases hsub with ⟨xStar, hxStar⟩
      refine ⟨(dotProductEquiv Real (Fin n)).symm xStar, ?_⟩
      simpa [S] using hxStar
    have hSconv : Convex Real S := by
      exact
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          f hfConv x hxFinite (0 : Module.Dual ℝ (Fin n → Real))).2.2.1
    have hSuppEq :
        supportFunctionEReal S = subdifferentialSupportAt f x := by
      ext y
      simpa [S] using
        helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x y
    have hSuppPos : PositivelyHomogeneous (subdifferentialSupportAt f x) := by
      rw [← hSuppEq]
      exact
        (section13_supportFunctionEReal_closedProperConvex_posHom
          (C := S) hSnonempty hSconv).2.2
    have hDpos : PositivelyHomogeneous D := by
      rcases convex_directionalDerivative_monotone_exists_and_sublinear f hfConv x hxFinite with
        ⟨_hmono, hpos, _hconv, _hzero, _hsymm⟩
      exact hpos
    have hScaledEq :
        (((t : Real) : EReal) * subdifferentialSupportAt f x u) =
          (((t : Real) : EReal) * D u) := by
      -- Positive homogeneity reduces the equality at `t • u` to the desired equality at `u`.
      calc
        (((t : Real) : EReal) * subdifferentialSupportAt f x u) =
            subdifferentialSupportAt f x (t • u) := by
              symm
              simpa [D] using hSuppPos u t ht
        _ = D (t • u) := hAtScale
        _ = (((t : Real) : EReal) * D u) := by
              simpa [D] using hDpos u t ht
    have hInv :=
      congrArg (fun z : EReal => (((t⁻¹ : Real) : EReal) * z)) hScaledEq
    calc
      subdifferentialSupportAt f x u =
          (((t⁻¹ : Real) : EReal) *
            (((t : Real) : EReal) * subdifferentialSupportAt f x u)) := by
              symm
              exact section13_mul_inv_mul_cancel_pos_real ht _
      _ = (((t⁻¹ : Real) : EReal) * (((t : Real) : EReal) * D u)) := by
            simpa using hInv
      _ = D u := section13_mul_inv_mul_cancel_pos_real ht _
  · have hsubEmpty : subdifferentialAt f x = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hsub
    have hSuppBot : subdifferentialSupportAt f x = fun _ : Fin n → Real => (⊥ : EReal) := by
      -- An empty subdifferential has the constant-`⊥` support function.
      funext y
      simp [subdifferentialSupportAt, hsubEmpty]
    have hDscale : D (t • u) = (((t : Real) : EReal) * D u) := by
      rcases convex_directionalDerivative_monotone_exists_and_sublinear f hfConv x hxFinite with
        ⟨_hmono, hpos, _hconv, _hzero, _hsymm⟩
      simpa [D] using hpos u t ht
    have hDuBot : D u = (⊥ : EReal) := by
      -- Once the scaled direction has value `⊥`, positive scaling forces the base direction to
      -- have value `⊥` as well.
      have hMulBot : (((t : Real) : EReal) * D u) = (⊥ : EReal) := by
        simpa [hSuppBot, hDscale] using hAtScale.symm
      have hInv :=
        congrArg (fun z : EReal => (((t⁻¹ : Real) : EReal) * z)) hMulBot
      calc
        D u = (((t⁻¹ : Real) : EReal) * (((t : Real) : EReal) * D u)) := by
              symm
              exact section13_mul_inv_mul_cancel_pos_real ht _
      _ = (((t⁻¹ : Real) : EReal) * (⊥ : EReal)) := by
              simpa using hInv
        _ = (⊥ : EReal) := by
              simp [EReal.coe_mul_bot_of_pos (inv_pos.2 ht)]
    simpa [D, hSuppBot, hDuBot]

/-- Helper for Theorem 25.6: if `x` is merely in `dom f` and `z` is interior to `dom f`, then
every strict convex combination `a • z + b • x` with `a > 0`, `b ≥ 0`, and `a + b = 1` still
lies in `interior (dom f)`. -/
lemma helperForTheorem_25_6_strictConvexCombo_mem_interior_of_mem_effectiveDomain_and_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x z : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hz : z ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    {a b : Real} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • z + b • x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomConv : Convex Real domf :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hfConv
  have hxClosure : x ∈ closure domf := by
    -- Domain points are of course closure points of the domain.
    exact subset_closure (by simpa [domf] using hx)
  -- A strict convex combination of an interior point and a closure point stays interior.
  exact hdomConv.combo_interior_closure_mem_interior hz hxClosure ha hb hab

/-- Helper for Theorem 25.6: after identifying covectors with Euclidean vectors, the
subdifferential mapping is monotone in the usual dot-product sense. -/
lemma helperForTheorem_25_6_preimageSubdifferential_monotone
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x0 x1 v0 v1 : Fin n → Real}
    (hv0 : v0 ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x0))
    (hv1 : v1 ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x1)) :
    0 ≤ dotProduct (x1 - x0) (v1 - v0) := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hcyclic :
      IsCyclicallyMonotone
        (fun x => ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) :=
    properConvexFunctionOn_isCyclicallyMonotone_subdifferential f hproper
  have hcycle :=
    hcyclic 1 ![x0, x1] ![v0, v1] (by
      intro i
      fin_cases i
      · simpa using hv0
      · simpa using hv1)
  have hraw :
      dotProduct x1 v0 + dotProduct x0 v1 ≤ dotProduct x0 v0 + dotProduct x1 v1 := by
    simpa using hcycle
  have hle :
      dotProduct (x1 - x0) v0 ≤ dotProduct (x1 - x0) v1 := by
    have hdiff :
        dotProduct x1 v0 - dotProduct x0 v0 ≤ dotProduct x1 v1 - dotProduct x0 v1 := by
      linarith
    simpa [dotProduct_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff
  -- Rewrite the comparison into the standard monotonicity form.
  simpa [dotProduct_sub] using hle

/-- Helper for Theorem 25.6: if nearby points `xᵢ` carry closure-gradient witnesses `qᵢ` that
converge to `q`, then a diagonal selection through the defining sequences already realizes `q` as
a limit point of the boundary fiber `gradientLimitVectorsAt f x`. -/
lemma helperForTheorem_25_6_limit_of_closureGradientLimitVectors_mem_closureGradientLimitVectors
    {n : Nat} (f : (Fin n → Real) → EReal)
    {x q : Fin n → Real}
    (xSeq qSeq : ℕ → Fin n → Real)
    (hxSeq_tendsto : Filter.Tendsto xSeq Filter.atTop (nhds x))
    (hqSeq_tendsto : Filter.Tendsto qSeq Filter.atTop (nhds q))
    (hqClosure :
      ∀ i : ℕ, qSeq i ∈ closure (gradientLimitVectorsAt f (xSeq i))) :
    q ∈ closure (gradientLimitVectorsAt f x) := by
  let εSeq : ℕ → Real := fun i => 1 / ((i : Real) + 1)
  have hεpos : ∀ i : ℕ, 0 < εSeq i := by
    intro i
    dsimp [εSeq]
    positivity
  have hApprox :
      ∀ i : ℕ,
        ∃ p : Fin n → Real,
          p ∈ gradientLimitVectorsAt f (xSeq i) ∧ dist p (qSeq i) < εSeq i := by
    intro i
    have hqClosure_i : qSeq i ∈ closure (gradientLimitVectorsAt f (xSeq i)) := hqClosure i
    rw [Metric.mem_closure_iff] at hqClosure_i
    rcases hqClosure_i (εSeq i) (hεpos i) with ⟨p, hp, hpdist⟩
    exact ⟨p, hp, by simpa [dist_comm] using hpdist⟩
  choose p hpMem hpDist using hApprox
  have hεTendsto :
      Filter.Tendsto εSeq Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpSubTendsto :
      Filter.Tendsto (fun i : ℕ => p i - qSeq i) Filter.atTop (nhds 0) := by
    -- The closure approximants `p i` can be chosen so that their error relative to `qSeq i`
    -- decays like `1 / (i + 1)`.
    apply tendsto_iff_dist_tendsto_zero.2
    refine squeeze_zero (fun i => dist_nonneg) ?_ hεTendsto
    intro i
    simpa [dist_eq_norm] using le_of_lt (hpDist i)
  have hpTendsto :
      Filter.Tendsto p Filter.atTop (nhds q) := by
    -- Adding the vanishing error term back to `qSeq i → q` gives `p i → q`.
    have hSumTendsto :
        Filter.Tendsto (fun i : ℕ => (p i - qSeq i) + qSeq i) Filter.atTop (nhds (0 + q)) :=
      hpSubTendsto.add hqSeq_tendsto
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hSumTendsto
  have hpData :
      ∀ i : ℕ,
        ∃ zSeq : ℕ → Fin n → Real,
          ∃ hdiff : ∀ j : ℕ, ERealDifferentiableAt f (zSeq j),
            Filter.Tendsto zSeq Filter.atTop (nhds (xSeq i)) ∧
              Filter.Tendsto (fun j : ℕ => erealGradientAt (hdiff j)) Filter.atTop
                (nhds (p i)) := by
    intro i
    exact hpMem i
  choose zWitness hdiffWitness hzWitnessTendsto hgradWitnessTendsto using hpData
  have hSelect :
      ∀ i : ℕ,
        ∃ j : ℕ,
          dist (zWitness i j) (xSeq i) < εSeq i ∧
            dist (erealGradientAt (hdiffWitness i j)) (p i) < εSeq i := by
    intro i
    have hxNear :
        ∀ᶠ j : ℕ in Filter.atTop, dist (zWitness i j) (xSeq i) < εSeq i := by
      have hdist :
          Filter.Tendsto (fun j : ℕ => dist (zWitness i j) (xSeq i)) Filter.atTop (nhds 0) := by
        simpa using
          (hzWitnessTendsto i).dist
            (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => xSeq i) Filter.atTop
              (nhds (xSeq i)))
      exact hdist.eventually (Iio_mem_nhds (hεpos i))
    have hgradNear :
        ∀ᶠ j : ℕ in Filter.atTop,
          dist (erealGradientAt (hdiffWitness i j)) (p i) < εSeq i := by
      have hdist :
          Filter.Tendsto
            (fun j : ℕ => dist (erealGradientAt (hdiffWitness i j)) (p i))
            Filter.atTop (nhds 0) := by
        simpa using
          (hgradWitnessTendsto i).dist
            (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => p i) Filter.atTop
              (nhds (p i)))
      exact hdist.eventually (Iio_mem_nhds (hεpos i))
    rcases Filter.eventually_atTop.1 hxNear with ⟨Nx, hNx⟩
    rcases Filter.eventually_atTop.1 hgradNear with ⟨Ng, hNg⟩
    refine ⟨max Nx Ng, ?_⟩
    exact ⟨hNx _ (le_max_left _ _), hNg _ (le_max_right _ _)⟩
  choose j hjx hjg using hSelect
  let zSeq : ℕ → Fin n → Real := fun i => zWitness i (j i)
  have hdiff : ∀ i : ℕ, ERealDifferentiableAt f (zSeq i) := by
    intro i
    exact hdiffWitness i (j i)
  have hzClose : ∀ i : ℕ, dist (zSeq i) (xSeq i) < εSeq i := by
    intro i
    simpa [zSeq] using hjx i
  have hGradClose :
      ∀ i : ℕ, dist (erealGradientAt (hdiff i)) (p i) < εSeq i := by
    intro i
    simpa [zSeq] using hjg i
  have hzDistTendsto :
      Filter.Tendsto (fun i : ℕ => dist (zSeq i) x) Filter.atTop (nhds 0) := by
    have hxDistTendsto :
        Filter.Tendsto (fun i : ℕ => dist (xSeq i) x) Filter.atTop (nhds 0) := by
      simpa using
        hxSeq_tendsto.dist
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x))
    have hUpper :
        Filter.Tendsto (fun i : ℕ => εSeq i + dist (xSeq i) x) Filter.atTop (nhds 0) := by
      simpa using hεTendsto.add hxDistTendsto
    -- The selected base points stay within `εᵢ` of `xSeq i`, so they converge to `x`.
    refine squeeze_zero (fun i => dist_nonneg) ?_ hUpper
    intro i
    calc
      dist (zSeq i) x ≤ dist (zSeq i) (xSeq i) + dist (xSeq i) x := dist_triangle _ _ _
      _ ≤ εSeq i + dist (xSeq i) x := by
        exact add_le_add (le_of_lt (hzClose i)) le_rfl
  have hzSeqTendsto :
      Filter.Tendsto zSeq Filter.atTop (nhds x) :=
    tendsto_iff_dist_tendsto_zero.2 hzDistTendsto
  have hGradDistTendsto :
      Filter.Tendsto (fun i : ℕ => dist (erealGradientAt (hdiff i)) q) Filter.atTop (nhds 0) := by
    have hpDistTendsto :
        Filter.Tendsto (fun i : ℕ => dist (p i) q) Filter.atTop (nhds 0) := by
      simpa using
        hpTendsto.dist
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => q) Filter.atTop (nhds q))
    have hUpper :
        Filter.Tendsto (fun i : ℕ => εSeq i + dist (p i) q) Filter.atTop (nhds 0) := by
      simpa using hεTendsto.add hpDistTendsto
    -- The selected gradients stay within `εᵢ` of `p i`, so they inherit the limit `q`.
    refine squeeze_zero (fun i => dist_nonneg) ?_ hUpper
    intro i
    calc
      dist (erealGradientAt (hdiff i)) q ≤
          dist (erealGradientAt (hdiff i)) (p i) + dist (p i) q := dist_triangle _ _ _
      _ ≤ εSeq i + dist (p i) q := by
        exact add_le_add (le_of_lt (hGradClose i)) le_rfl
  have hGradTendsto :
      Filter.Tendsto (fun i : ℕ => erealGradientAt (hdiff i)) Filter.atTop (nhds q) :=
    tendsto_iff_dist_tendsto_zero.2 hGradDistTendsto
  have hqMem : q ∈ gradientLimitVectorsAt f x := by
    -- The diagonal sequence now directly witnesses membership in the boundary gradient-limit set.
    exact ⟨zSeq, hdiff, hzSeqTendsto, hGradTendsto⟩
  -- Membership in the set is stronger than the closure statement needed later.
  exact subset_closure hqMem

/-- Helper for Theorem 25.6: an interior base point admits one common symmetric coordinate box of
interior comparison points, together with chosen Euclidean subgradients at those points. -/
lemma helperForTheorem_25_6_exists_symmetricInteriorComparisonSubgradients
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {z : Fin n → Real}
    (hz : z ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∃ ρ : Real, 0 < ρ ∧
      ∃ vPlus vMinus : Fin n → Fin n → Real,
        (∀ j : Fin n,
          let e : Fin n → Real := Pi.single j (1 : Real)
          z + (ρ / 2) • e ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) ∧
            vPlus j ∈
              ((dotProductEquiv Real (Fin n)) ⁻¹'
                subdifferentialAt f (z + (ρ / 2) • e))) ∧
        (∀ j : Fin n,
          let e : Fin n → Real := Pi.single j (1 : Real)
          z - (ρ / 2) • e ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) ∧
            vMinus j ∈
              ((dotProductEquiv Real (Fin n)) ⁻¹'
                subdifferentialAt f (z - (ρ / 2) • e))) := by
  let domf : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  rcases helperForTheorem_25_1_exists_closedBall_subset_of_isOpen
      (n := n) (C := interior domf) isOpen_interior hz with
    ⟨ρ, hρpos, hρball⟩
  have hplusData :
      ∀ j : Fin n, ∃ v : Fin n → Real,
        let e : Fin n → Real := Pi.single j (1 : Real)
        z + (ρ / 2) • e ∈ interior domf ∧
          v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
            subdifferentialAt f (z + (ρ / 2) • e)) := by
    intro j
    let e : Fin n → Real := Pi.single j (1 : Real)
    have hplusBall : z + (ρ / 2) • e ∈ Metric.closedBall z ρ := by
      -- The positive coordinate perturbation stays inside the common closed ball around `z`.
      change dist (z + (ρ / 2) • e) z ≤ ρ
      rw [dist_eq_norm]
      have hsub : z + (ρ / 2) • e - z = (ρ / 2) • e := by
        abel_nf
      rw [hsub]
      refine (pi_norm_le_iff_of_nonneg (x := (ρ / 2) • e) (r := ρ) hρpos.le).2 ?_
      intro k
      by_cases hk : k = j
      · subst hk
        have hhalf_nonneg : 0 ≤ ρ / 2 := by positivity
        have habs : |ρ| = ρ := abs_of_pos hρpos
        simp [e, habs]
        linarith
      · have hhalf_nonneg : 0 ≤ ρ / 2 := by positivity
        simpa [e, hk] using hρpos.le
    have hplusInt : z + (ρ / 2) • e ∈ interior domf :=
      hρball hplusBall
    rcases
        (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
          (f := f) hf hplusInt).1 with
      ⟨v, hv⟩
    exact ⟨v, hplusInt, hv⟩
  have hminusData :
      ∀ j : Fin n, ∃ v : Fin n → Real,
        let e : Fin n → Real := Pi.single j (1 : Real)
        z - (ρ / 2) • e ∈ interior domf ∧
          v ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
            subdifferentialAt f (z - (ρ / 2) • e)) := by
    intro j
    let e : Fin n → Real := Pi.single j (1 : Real)
    have hminusBall : z - (ρ / 2) • e ∈ Metric.closedBall z ρ := by
      -- The negative coordinate perturbation lies in the same closed ball for the same reason.
      change dist (z - (ρ / 2) • e) z ≤ ρ
      rw [dist_eq_norm]
      have hsub : z - (ρ / 2) • e - z = -((ρ / 2) • e) := by
        abel_nf
      rw [hsub, norm_neg]
      refine (pi_norm_le_iff_of_nonneg (x := (ρ / 2) • e) (r := ρ) hρpos.le).2 ?_
      intro k
      by_cases hk : k = j
      · subst hk
        have hhalf_nonneg : 0 ≤ ρ / 2 := by positivity
        have habs : |ρ| = ρ := abs_of_pos hρpos
        simp [e, habs]
        linarith
      · have hhalf_nonneg : 0 ≤ ρ / 2 := by positivity
        simpa [e, hk] using hρpos.le
    have hminusInt : z - (ρ / 2) • e ∈ interior domf :=
      hρball hminusBall
    rcases
        (helperForTheorem_25_6_preimageSubdifferential_nonempty_bounded_of_mem_interior
          (f := f) hf hminusInt).1 with
      ⟨v, hv⟩
    exact ⟨v, hminusInt, hv⟩
  choose vPlus hvPlus using hplusData
  choose vMinus hvMinus using hminusData
  refine ⟨ρ, hρpos, vPlus, vMinus, ?_, ?_⟩
  · intro j
    simpa [domf] using hvPlus j
  · intro j
    simpa [domf] using hvMinus j

/-- Helper for Theorem 25.6: the fixed interior center secants provide one common coordinate box
for all support realizers chosen along the admissible ray. -/
lemma helperForTheorem_25_6_upperDirectionalDerivative_le_pairing_of_preimageSubgradient_on_positive_rayStep
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x u q : Fin n → Real} {s : Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hs : 0 < s)
    (hqSub :
      q ∈ ((dotProductEquiv Real (Fin n)) ⁻¹'
        subdifferentialAt f (x + s • u))) :
    upperDirectionalDerivativeAt f x u ≤ (((dotProduct q u : Real) : EReal)) := by
  let xs : Fin n → Real := x + s • u
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    constructor
    · exact
        mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin n → Real))) (f := f) hx
    · exact hproper.2.2 x (by simp)
  have hqSub' :
      dotProductEquiv Real (Fin n) q ∈ subdifferentialAt f xs := by
    simpa [xs] using hqSub
  have hxsFinite : f xs ≠ ⊤ ∧ f xs ≠ ⊥ := by
    -- A genuine subgradient forces the point `x + s • u` to be finite.
    exact
      helperForTheorem_23_4_finiteAt_of_subdifferentiable
        f hproper xs ⟨dotProductEquiv Real (Fin n) q, hqSub'⟩
  have hsecLe :
      upperDirectionalDerivativeAt f x u ≤ directionalDifferenceQuotientAt f x u s := by
    rcases convex_directionalDerivative_monotone_exists_and_sublinear f hfConv x hxFinite with
      ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
    rcases hdir u with ⟨_hmono, _htend, hsInfEq⟩
    have hQbdd :
        BddBelow ((Set.Ioi (0 : ℝ)).image fun τ : ℝ => directionalDifferenceQuotientAt f x u τ) := by
      refine ⟨⊥, ?_⟩
      intro r hr
      simp at hr ⊢
    rw [hsInfEq]
    exact csInf_le hQbdd ⟨s, hs, rfl⟩
  lift f x to Real using hxFinite with xr hxr
  lift f xs to Real using hxsFinite with xsr hxsr
  have hsubReal : xr ≥ xsr + dotProduct q (x - xs) := by
    exact
      EReal.coe_le_coe_iff.mp
        (by simpa [hxr, hxsr, xs, dotProductEquiv_apply_apply, EReal.coe_add] using hqSub' x)
  have hdotEq :
      dotProduct q (x - xs) = -s * dotProduct q u := by
    -- Along the positive ray, the return displacement from `x + s • u` back to `x` is `-s • u`.
    calc
      dotProduct q (x - xs) = dotProduct q (-s • u) := by
        congr 1
        ext j
        simp [xs]
      _ = -s * dotProduct q u := by
        rw [dotProduct_smul]
        simp [smul_eq_mul, mul_comm]
  have hquotReal :
      ((xsr - xr) / s) ≤ dotProduct q u := by
    rw [hdotEq] at hsubReal
    have hmul : xsr - xr ≤ s * dotProduct q u := by
      nlinarith
    have hmul' : xsr - xr ≤ dotProduct q u * s := by
      simpa [mul_comm] using hmul
    exact (div_le_iff₀ hs).2 hmul'
  have hdqEq :
      directionalDifferenceQuotientAt f x u s = (((xsr - xr) / s : Real) : EReal) := by
    -- Evaluating the quotient at the step reaching `x + s • u` gives the usual secant slope.
    have hstep : x + s • u = xs := rfl
    simp [directionalDifferenceQuotientAt, hstep, hxr, hxsr, div_eq_mul_inv, EReal.coe_inv]
  have hquotLe :
      directionalDifferenceQuotientAt f x u s ≤ (((dotProduct q u : Real) : EReal)) := by
    simpa [hdqEq] using
      (show (((xsr - xr) / s : Real) : EReal) ≤ (((dotProduct q u : Real) : EReal)) by
        exact_mod_cast hquotReal)
  exact le_trans hsecLe hquotLe

/-- Helper for Theorem 25.6: once the boundary directional derivative in the admissible direction
is not `⊥`, the fixed interior comparison points at `x + t • u ± (ρ/2)eⱼ` give a common
coordinate box for every support realizer chosen along the ray. -/
lemma helperForTheorem_25_6_coordinate_bound_from_monotoneComparison_with_endpoint_and_symmetricInteriorPoints
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x u : Fin n → Real} {t s ρ d : Real}
    {q vPlus vMinus : Fin n → Real} {j : Fin n}
    (hρpos : 0 < ρ) (hsPos : 0 < s) (hsLe : s ≤ t)
    (hqPairLower : d ≤ dotProduct q u)
    (hqSub :
      q ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f (x + s • u)))
    (hvPlus :
      let e : Fin n → Real := Pi.single j (1 : Real)
      vPlus ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          subdifferentialAt f (x + t • u + (ρ / 2) • e)))
    (hvMinus :
      let e : Fin n → Real := Pi.single j (1 : Real)
      vMinus ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          subdifferentialAt f (x + t • u - (ρ / 2) • e))) :
    let BPlus := (2 / ρ) * t * (|dotProduct u vPlus| + |d|)
    let BMinus := (2 / ρ) * t * (|dotProduct u vMinus| + |d|)
    vMinus j - BMinus ≤ q j ∧ q j ≤ vPlus j + BPlus := by
  let e : Fin n → Real := Pi.single j (1 : Real)
  let BPlus : Real := (2 / ρ) * t * (|dotProduct u vPlus| + |d|)
  let BMinus : Real := (2 / ρ) * t * (|dotProduct u vMinus| + |d|)
  have htsNonneg : 0 ≤ t - s := sub_nonneg.mpr hsLe
  have htsLe : t - s ≤ t := by linarith
  have htNonneg : 0 ≤ t := le_trans hsPos.le hsLe
  have hρhalfPos : 0 < ρ / 2 := by positivity
  have hBPlusNonneg : 0 ≤ |dotProduct u vPlus| + |d| := by positivity
  have hBMinusNonneg : 0 ≤ |dotProduct u vMinus| + |d| := by positivity
  have hpairLowerComm : d ≤ dotProduct u q := by
    simpa [dotProduct_comm] using hqPairLower
  have hqSub' :
      q ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f (x + s • u)) := hqSub
  have hvPlus' :
      vPlus ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          subdifferentialAt f (x + t • u + (ρ / 2) • e)) := by
    simpa [e] using hvPlus
  have hvMinus' :
      vMinus ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          subdifferentialAt f (x + t • u - (ρ / 2) • e)) := by
    simpa [e] using hvMinus
  have hmonoPlus :=
    helperForTheorem_25_6_preimageSubdifferential_monotone
      (f := f) hf hqSub' hvPlus'
  have hmonoMinus :=
    helperForTheorem_25_6_preimageSubdifferential_monotone
      (f := f) hf hqSub' hvMinus'
  have hplusRewrite :
      0 ≤
        (t - s) * (dotProduct u vPlus - dotProduct u q) + (ρ / 2) * (vPlus j - q j) := by
    have hdisp :
        x + t • u + (ρ / 2) • e - (x + s • u) = (t - s) • u + (ρ / 2) • e := by
      ext k
      by_cases hk : k = j
      · subst hk
        simp [e]
        ring
      · simp [e, hk]
        ring
    calc
      0 ≤ dotProduct ((t - s) • u + (ρ / 2) • e) (vPlus - q) := by
            simpa [hdisp] using hmonoPlus
      _ =
          (t - s) * (dotProduct u vPlus - dotProduct u q) +
            (ρ / 2) * (vPlus j - q j) := by
            simp [e, dotProduct_add, smul_dotProduct, sub_eq_add_neg]
            ring
  have hminusRewrite :
      0 ≤
        (t - s) * (dotProduct u vMinus - dotProduct u q) - (ρ / 2) * (vMinus j - q j) := by
    have hdisp :
        x + t • u - (ρ / 2) • e - (x + s • u) = (t - s) • u - (ρ / 2) • e := by
      ext k
      by_cases hk : k = j
      · subst hk
        simp [e]
        ring
      · simp [e, hk]
        ring
    calc
      0 ≤ dotProduct ((t - s) • u - (ρ / 2) • e) (vMinus - q) := by
            simpa [hdisp] using hmonoMinus
      _ =
          (t - s) * (dotProduct u vMinus - dotProduct u q) -
            (ρ / 2) * (vMinus j - q j) := by
            simp [e, smul_dotProduct, sub_eq_add_neg]
            ring
  have hplusTermBound :
      (t - s) * (dotProduct u vPlus - dotProduct u q) ≤
        t * (|dotProduct u vPlus| + |d|) := by
    have hraw :
        dotProduct u vPlus - dotProduct u q ≤ |dotProduct u vPlus| + |d| := by
      have hstep : dotProduct u vPlus - dotProduct u q ≤ dotProduct u vPlus - d := by
        linarith
      have hplusAbs : dotProduct u vPlus ≤ |dotProduct u vPlus| := le_abs_self _
      have hdAbs : -d ≤ |d| := by simpa using neg_le_abs d
      linarith
    have hmul :
        (t - s) * (dotProduct u vPlus - dotProduct u q) ≤
          (t - s) * (|dotProduct u vPlus| + |d|) :=
      mul_le_mul_of_nonneg_left hraw htsNonneg
    exact le_trans hmul (mul_le_mul_of_nonneg_right htsLe hBPlusNonneg)
  have hminusTermBound :
      (t - s) * (dotProduct u vMinus - dotProduct u q) ≤
        t * (|dotProduct u vMinus| + |d|) := by
    have hraw :
        dotProduct u vMinus - dotProduct u q ≤ |dotProduct u vMinus| + |d| := by
      have hstep : dotProduct u vMinus - dotProduct u q ≤ dotProduct u vMinus - d := by
        linarith
      have hminusAbs : dotProduct u vMinus ≤ |dotProduct u vMinus| := le_abs_self _
      have hdAbs : -d ≤ |d| := by simpa using neg_le_abs d
      linarith
    have hmul :
        (t - s) * (dotProduct u vMinus - dotProduct u q) ≤
          (t - s) * (|dotProduct u vMinus| + |d|) :=
      mul_le_mul_of_nonneg_left hraw htsNonneg
    exact le_trans hmul (mul_le_mul_of_nonneg_right htsLe hBMinusNonneg)
  have hupperScaled :
      (ρ / 2) * (q j - vPlus j) ≤ t * (|dotProduct u vPlus| + |d|) := by
    linarith
  have hlowerScaled :
      (ρ / 2) * (vMinus j - q j) ≤ t * (|dotProduct u vMinus| + |d|) := by
    linarith
  have hupper :
      q j ≤ vPlus j + BPlus := by
    have hdiv :
        q j - vPlus j ≤ t * (|dotProduct u vPlus| + |d|) / (ρ / 2) := by
      exact (le_div_iff₀ hρhalfPos).2 (by simpa [mul_comm] using hupperScaled)
    have hdiv' :
        q j - vPlus j ≤ BPlus := by
      simpa [BPlus, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    linarith
  have hlower :
      vMinus j - BMinus ≤ q j := by
    have hdiv :
        vMinus j - q j ≤ t * (|dotProduct u vMinus| + |d|) / (ρ / 2) := by
      exact (le_div_iff₀ hρhalfPos).2 (by simpa [mul_comm] using hlowerScaled)
    have hdiv' :
        vMinus j - q j ≤ BMinus := by
      simpa [BMinus, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    linarith
  exact ⟨hlower, hupper⟩


end Section25
end Chap05
