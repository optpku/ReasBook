/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part2

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

/-- The scalar `x : ℝ` viewed as a point of `Fin 1 → ℝ`. -/
def scalarPoint (x : ℝ) : Fin 1 → ℝ :=
  fun _ => x

/-- The effective domain of a one-dimensional extended-real function, viewed as a subset of `ℝ`.
-/
def scalarEffectiveDomain (f : (Fin 1 → ℝ) → EReal) : Set ℝ :=
  {x | scalarPoint x ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f}

/-- A scalar lies strictly to the right of the effective domain when it exceeds every domain
point. -/
def IsRightOfScalarEffectiveDomain (f : (Fin 1 → ℝ) → EReal) (x : ℝ) : Prop :=
  ∀ y ∈ scalarEffectiveDomain f, y < x

/-- A scalar lies strictly to the left of the effective domain when it is smaller than every
domain point. -/
def IsLeftOfScalarEffectiveDomain (f : (Fin 1 → ℝ) → EReal) (x : ℝ) : Prop :=
  ∀ y ∈ scalarEffectiveDomain f, x < y

/-- The extended right derivative of a one-dimensional closed proper convex function: it agrees
with the upper directional derivative in direction `1` on and between domain points, is `⊤` to the
right of the effective domain, and is `⊥` to the left. -/
noncomputable def rightDerivativeExtension (f : (Fin 1 → ℝ) → EReal) (x : ℝ) : EReal :=
  if IsRightOfScalarEffectiveDomain f x then
    (⊤ : EReal)
  else if IsLeftOfScalarEffectiveDomain f x then
    (⊥ : EReal)
  else
    upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint 1)

/-- The extended left derivative of a one-dimensional closed proper convex function: it agrees
with the negative of the upper directional derivative in direction `-1` on and between domain
points, is `⊤` to the right of the effective domain, and is `⊥` to the left. -/
noncomputable def leftDerivativeExtension (f : (Fin 1 → ℝ) → EReal) (x : ℝ) : EReal :=
  if IsRightOfScalarEffectiveDomain f x then
    (⊤ : EReal)
  else if IsLeftOfScalarEffectiveDomain f x then
    (⊥ : EReal)
  else
    -upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint (-1))

/-- Helper for Theorem 5.24.1: the scalar effective domain is convex because it is the
one-dimensional trace of the convex effective domain of `f`. -/
lemma helperForTheorem_5_24_1_scalarEffectiveDomain_convex
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f) :
    Convex ℝ (scalarEffectiveDomain f) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomConv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f)
      (by simpa [ConvexFunction] using hproper.1)
  intro x hx y hy a b ha hb hab
  -- Transport convexity along the scalar embedding `x ↦ scalarPoint x`.
  have hmem :=
    hdomConv hx hy ha hb hab
  have hpoint :
      a • scalarPoint x + b • scalarPoint y = scalarPoint (a * x + b * y) := by
    ext i
    simp [scalarPoint, smul_eq_mul]
  simpa [scalarEffectiveDomain, hpoint]
    using hmem

/-- Helper for Theorem 5.24.1: a point strictly left of the scalar effective domain cannot also be
strictly right of it, because properness gives a domain point. -/
lemma helperForTheorem_5_24_1_not_right_of_left
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x : ℝ} (hxLeft : IsLeftOfScalarEffectiveDomain f x) :
    ¬ IsRightOfScalarEffectiveDomain f x := by
  -- A nonempty effective domain provides a witness contradicting the two strict inequalities.
  rcases properConvexFunctionOn_effectiveDomain_nonempty (f := f) hproper with ⟨y, hy⟩
  have hscalarY : scalarPoint (y 0) = y := by
    ext i
    have hi : i = 0 := Subsingleton.elim i 0
    simpa [scalarPoint, hi]
  have hyScalar : y 0 ∈ scalarEffectiveDomain f := by
    simpa [scalarEffectiveDomain, hscalarY] using hy
  intro hxRight
  exact (lt_irrefl (y 0)) (lt_trans (hxRight (y 0) hyScalar) (hxLeft (y 0) hyScalar))

/-- Helper for Theorem 5.24.1: a point strictly right of the scalar effective domain cannot also
be strictly left of it, again because properness gives a domain point. -/
lemma helperForTheorem_5_24_1_not_left_of_right
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x : ℝ} (hxRight : IsRightOfScalarEffectiveDomain f x) :
    ¬ IsLeftOfScalarEffectiveDomain f x := by
  -- Use the same domain witness as in the previous lemma, but reverse the contradiction.
  rcases properConvexFunctionOn_effectiveDomain_nonempty (f := f) hproper with ⟨y, hy⟩
  have hscalarY : scalarPoint (y 0) = y := by
    ext i
    have hi : i = 0 := Subsingleton.elim i 0
    simpa [scalarPoint, hi]
  have hyScalar : y 0 ∈ scalarEffectiveDomain f := by
    simpa [scalarEffectiveDomain, hscalarY] using hy
  intro hxLeft
  exact (lt_irrefl (y 0)) (lt_trans (hxRight (y 0) hyScalar) (hxLeft (y 0) hyScalar))

/-- Helper for Theorem 5.24.1: if a scalar is neither strictly left nor strictly right of the
effective domain, convexity forces it to lie in the effective domain. -/
lemma helperForTheorem_5_24_1_mem_scalarEffectiveDomain_of_not_left_not_right
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x : ℝ}
    (hxNotLeft : ¬ IsLeftOfScalarEffectiveDomain f x)
    (hxNotRight : ¬ IsRightOfScalarEffectiveDomain f x) :
    x ∈ scalarEffectiveDomain f := by
  have hconv :
      Convex ℝ (scalarEffectiveDomain f) :=
    helperForTheorem_5_24_1_scalarEffectiveDomain_convex f hproper
  -- Negating the left/right predicates yields one domain point on each side of `x`.
  have hleftWitness : ∃ y, y ∈ scalarEffectiveDomain f ∧ y ≤ x := by
    by_contra hleftWitness
    apply hxNotLeft
    intro y hy
    have hyNotLe : ¬ y ≤ x := by
      intro hyx
      exact hleftWitness ⟨y, hy, hyx⟩
    exact lt_of_not_ge hyNotLe
  have hrightWitness : ∃ z, z ∈ scalarEffectiveDomain f ∧ x ≤ z := by
    by_contra hrightWitness
    apply hxNotRight
    intro z hz
    have hzNotLe : ¬ x ≤ z := by
      intro hxz
      exact hrightWitness ⟨z, hz, hxz⟩
    exact lt_of_not_ge hzNotLe
  rcases hleftWitness with ⟨y, hy, hyx⟩
  rcases hrightWitness with ⟨z, hz, hzx⟩
  exact (hconv.ordConnected.out hy hz) ⟨hyx, hzx⟩

/-- Helper for Theorem 5.24.1: a domain point is neither strictly left nor strictly right of the
scalar effective domain. -/
lemma helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain
    (f : (Fin 1 → ℝ) → EReal) {x : ℝ}
    (hx : x ∈ scalarEffectiveDomain f) :
    ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x := by
  constructor
  · intro hxLeft
    exact (lt_irrefl x) (hxLeft x hx)
  · intro hxRight
    exact (lt_irrefl x) (hxRight x hx)

/-- Helper for Theorem 5.24.1: the right-of-domain predicate is monotone in the scalar variable.
-/
lemma helperForTheorem_5_24_1_rightOfScalarEffectiveDomain_mono
    (f : (Fin 1 → ℝ) → EReal) {x y : ℝ} (hxy : x ≤ y)
    (hx : IsRightOfScalarEffectiveDomain f x) :
    IsRightOfScalarEffectiveDomain f y := by
  -- Moving further to the right preserves the "strictly right of every domain point" property.
  intro z hz
  exact lt_of_lt_of_le (hx z hz) hxy

/-- Helper for Theorem 5.24.1: the left-of-domain predicate is antitone in the scalar variable. -/
lemma helperForTheorem_5_24_1_leftOfScalarEffectiveDomain_antitone
    (f : (Fin 1 → ℝ) → EReal) {x y : ℝ} (hxy : x ≤ y)
    (hy : IsLeftOfScalarEffectiveDomain f y) :
    IsLeftOfScalarEffectiveDomain f x := by
  -- Moving further to the left preserves the "strictly left of every domain point" property.
  intro z hz
  exact lt_of_le_of_lt hxy (hy z hz)

/-- Helper for Theorem 5.24.1: interior points of the scalar effective domain have finite right
and left derivative extensions. -/
lemma helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x : ℝ} (hx : x ∈ interior (scalarEffectiveDomain f)) :
    rightDerivativeExtension f x ≠ (⊤ : EReal) ∧
      rightDerivativeExtension f x ≠ (⊥ : EReal) ∧
      leftDerivativeExtension f x ≠ (⊤ : EReal) ∧
      leftDerivativeExtension f x ≠ (⊥ : EReal) := by
  let e : ℝ ≃L[ℝ] (Fin 1 → ℝ) :=
    (ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := ℝ) (M := ℝ)).symm
  have hscalar :
      (fun t : ℝ => e t) = scalarPoint := by
    ext t i
    simp [e, scalarPoint]
  have hdom :
      scalarEffectiveDomain f =
        e ⁻¹' effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f := by
    ext t
    simp [scalarEffectiveDomain, hscalar]
  have hpre :
      e ⁻¹' interior (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f) =
        interior (e ⁻¹' effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f) := by
    simpa using
      (e.toHomeomorph.preimage_interior
        (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f))
  have hxIntPreimage :
      x ∈ e ⁻¹' interior (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f) := by
    -- Transport the interior statement across the one-dimensional homeomorphism.
    rw [hpre]
    simpa [hdom] using hx
  have hxInt :
      scalarPoint x ∈ interior (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f) := by
    simpa [hscalar] using hxIntPreimage
  have hxDom : x ∈ scalarEffectiveDomain f :=
    interior_subset hx
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hxDom
  rcases
      subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        f hproper (scalarPoint x) with
    ⟨_hoff, _hri, _hiff, hfinite⟩
  have hrightFinite := hfinite hxInt (scalarPoint 1)
  have hleftFinite := hfinite hxInt (scalarPoint (-1))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- On the interior, the right derivative is the finite directional derivative in direction `1`.
    simpa [rightDerivativeExtension, hxNot.2, hxNot.1] using hrightFinite.1
  · simpa [rightDerivativeExtension, hxNot.2, hxNot.1] using hrightFinite.2
  · -- The left derivative is `-f'(x; -1)`, so avoiding `⊥` for `f'(x; -1)` avoids `⊤` after negation.
    simpa [leftDerivativeExtension, hxNot.2, hxNot.1] using hleftFinite.2
  · simpa [leftDerivativeExtension, hxNot.2, hxNot.1] using hleftFinite.1

/-- Helper for Theorem 5.24.1: at a domain point, the left derivative extension does not exceed
the right derivative extension. -/
lemma helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension_at_domain
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x : ℝ} (hx : x ∈ scalarEffectiveDomain f) :
    leftDerivativeExtension f x ≤ rightDerivativeExtension f x := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
    exact ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hx,
      hproper.2.2 (scalarPoint x) (by simp)⟩
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hx
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      f hf (scalarPoint x) hxFinite with
    ⟨_hdir, _hpos, _hconv, _hzero, hsymm⟩
  -- The symmetric-direction inequality from Theorem 23.1 is exactly `f'_-(x) ≤ f'_+(x)`.
  simpa [leftDerivativeExtension, rightDerivativeExtension, hxNot.2, hxNot.1, scalarPoint]
    using hsymm (scalarPoint 1)

/-- Helper for Theorem 5.24.1: for domain points `x < y`, the secant slope from `x` to `y` sits
between the right derivative at `x` and the left derivative at `y`. -/
lemma helperForTheorem_5_24_1_secantSlope_between_rightAndLeftDerivatives
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x y : ℝ} (hxy : x < y)
    (hx : x ∈ scalarEffectiveDomain f) (hy : y ∈ scalarEffectiveDomain f) :
    rightDerivativeExtension f x ≤
        (f (scalarPoint y) - f (scalarPoint x)) / (((y - x : ℝ)) : EReal) ∧
      (f (scalarPoint y) - f (scalarPoint x)) / (((y - x : ℝ)) : EReal) ≤
        leftDerivativeExtension f y := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
    exact ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hx,
      hproper.2.2 (scalarPoint x) (by simp)⟩
  have hyFinite : f (scalarPoint y) ≠ (⊤ : EReal) ∧ f (scalarPoint y) ≠ (⊥ : EReal) := by
    exact ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hy,
      hproper.2.2 (scalarPoint y) (by simp)⟩
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hx
  have hyNot :
      ¬ IsLeftOfScalarEffectiveDomain f y ∧ ¬ IsRightOfScalarEffectiveDomain f y :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hy
  have ht : 0 < y - x := sub_pos.mpr hxy
  have hstepToY :
      scalarPoint x + (y - x) • scalarPoint 1 = scalarPoint y := by
    ext i
    simp [scalarPoint]
  have hstepToX :
      scalarPoint y + (y - x) • scalarPoint (-1) = scalarPoint x := by
    ext i
    simp [scalarPoint]
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      f hf (scalarPoint x) hxFinite with
    ⟨hdirRight, _hposRight, _hconvRight, _hzeroRight, _hsymmRight⟩
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      f hf (scalarPoint y) hyFinite with
    ⟨hdirLeft, _hposLeft, _hconvLeft, _hzeroLeft, _hsymmLeft⟩
  have hRightBdd :
      BddBelow
        ((Set.Ioi (0 : ℝ)).image
          fun t : ℝ => directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t) := by
    refine ⟨⊥, ?_⟩
    intro q hq
    simp
  have hLeftBdd :
      BddBelow
        ((Set.Ioi (0 : ℝ)).image
          fun t : ℝ => directionalDifferenceQuotientAt f (scalarPoint y) (scalarPoint (-1)) t) := by
    refine ⟨⊥, ?_⟩
    intro q hq
    simp
  have hRightLeQuot :
      upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint 1) ≤
        directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) (y - x) := by
    rw [(hdirRight (scalarPoint 1)).2.2]
    exact csInf_le hRightBdd ⟨y - x, ht, rfl⟩
  have hLeftLeNegQuot :
      upperDirectionalDerivativeAt f (scalarPoint y) (scalarPoint (-1)) ≤
        directionalDifferenceQuotientAt f (scalarPoint y) (scalarPoint (-1)) (y - x) := by
    rw [(hdirLeft (scalarPoint (-1))).2.2]
    exact csInf_le hLeftBdd ⟨y - x, ht, rfl⟩
  constructor
  · -- Evaluate the positive-step quotient at `t = y - x`.
    simpa [rightDerivativeExtension, hxNot.2, hxNot.1, directionalDifferenceQuotientAt, hstepToY]
      using hRightLeQuot
  · have hQuotLeLeft :
        -directionalDifferenceQuotientAt f (scalarPoint y) (scalarPoint (-1)) (y - x) ≤
          -upperDirectionalDerivativeAt f (scalarPoint y) (scalarPoint (-1)) := by
      rw [EReal.neg_le_neg_iff]
      exact hLeftLeNegQuot
    have hnegQuot :
        -directionalDifferenceQuotientAt f (scalarPoint y) (scalarPoint (-1)) (y - x) =
          (f (scalarPoint y) - f (scalarPoint x)) / (((y - x : ℝ)) : EReal) := by
      have htmp :
          -((f (scalarPoint x) - f (scalarPoint y)) / (((y - x : ℝ)) : EReal)) =
            (f (scalarPoint y) - f (scalarPoint x)) / (((y - x : ℝ)) : EReal) := by
        rw [EReal.div_eq_inv_mul, EReal.div_eq_inv_mul, neg_mul_eq_mul_neg]
        rw [EReal.neg_sub (Or.inl hxFinite.2) (Or.inl hxFinite.1)]
        simp [sub_eq_add_neg, add_comm]
      simpa [directionalDifferenceQuotientAt, hstepToX] using htmp
    -- Negating the left-point quotient identifies it with the secant slope from `x` to `y`.
    calc
      (f (scalarPoint y) - f (scalarPoint x)) / (((y - x : ℝ)) : EReal) =
          -directionalDifferenceQuotientAt f (scalarPoint y) (scalarPoint (-1)) (y - x) := by
            symm
            exact hnegQuot
      _ ≤ -upperDirectionalDerivativeAt f (scalarPoint y) (scalarPoint (-1)) :=
        hQuotLeLeft
      _ = leftDerivativeExtension f y := by
        simp [leftDerivativeExtension, hyNot.2, hyNot.1]

/-- Helper for Theorem 5.24.1: whenever `x < y`, the extended right derivative at `x` is bounded
above by the extended left derivative at `y`. -/
lemma helperForTheorem_5_24_1_rightDerivativeExtension_le_leftDerivativeExtension_of_lt
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x y : ℝ} (hxy : x < y) :
    rightDerivativeExtension f x ≤ leftDerivativeExtension f y := by
  by_cases hxLeft : IsLeftOfScalarEffectiveDomain f x
  · have hxNotRight :
      ¬ IsRightOfScalarEffectiveDomain f x :=
      helperForTheorem_5_24_1_not_right_of_left f hproper hxLeft
    -- Strictly left of the domain, the right derivative extension is `⊥`.
    simp [rightDerivativeExtension, hxNotRight, hxLeft]
  by_cases hyRight : IsRightOfScalarEffectiveDomain f y
  · have hyNotLeft :
      ¬ IsLeftOfScalarEffectiveDomain f y :=
      helperForTheorem_5_24_1_not_left_of_right f hproper hyRight
    -- Strictly right of the domain, the left derivative extension is `⊤`.
    simp [leftDerivativeExtension, hyRight, hyNotLeft]
  have hxNotRight : ¬ IsRightOfScalarEffectiveDomain f x := by
    intro hxRight
    exact hyRight
      (helperForTheorem_5_24_1_rightOfScalarEffectiveDomain_mono f (le_of_lt hxy) hxRight)
  have hyNotLeft : ¬ IsLeftOfScalarEffectiveDomain f y := by
    intro hyLeft
    exact hxLeft
      (helperForTheorem_5_24_1_leftOfScalarEffectiveDomain_antitone f (le_of_lt hxy) hyLeft)
  have hxDom :
      x ∈ scalarEffectiveDomain f :=
    helperForTheorem_5_24_1_mem_scalarEffectiveDomain_of_not_left_not_right
      f hproper hxLeft hxNotRight
  have hyDom :
      y ∈ scalarEffectiveDomain f :=
    helperForTheorem_5_24_1_mem_scalarEffectiveDomain_of_not_left_not_right
      f hproper hyNotLeft hyRight
  exact
    (helperForTheorem_5_24_1_secantSlope_between_rightAndLeftDerivatives
      f hproper hxy hxDom hyDom).1.trans
      (helperForTheorem_5_24_1_secantSlope_between_rightAndLeftDerivatives
        f hproper hxy hxDom hyDom).2

/-- Helper for Theorem 5.24.1: the extended left derivative never exceeds the extended right
derivative at the same point. -/
lemma helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    (x : ℝ) :
    leftDerivativeExtension f x ≤ rightDerivativeExtension f x := by
  by_cases hxLeft : IsLeftOfScalarEffectiveDomain f x
  · have hxNotRight :
      ¬ IsRightOfScalarEffectiveDomain f x :=
      helperForTheorem_5_24_1_not_right_of_left f hproper hxLeft
    -- On the left exterior region both extensions take the value `⊥`.
    simp [leftDerivativeExtension, rightDerivativeExtension, hxNotRight, hxLeft]
  by_cases hxRight : IsRightOfScalarEffectiveDomain f x
  · have hxNotLeft :
      ¬ IsLeftOfScalarEffectiveDomain f x :=
      helperForTheorem_5_24_1_not_left_of_right f hproper hxRight
    -- On the right exterior region both extensions take the value `⊤`.
    simp [leftDerivativeExtension, rightDerivativeExtension, hxRight, hxNotLeft]
  have hxDom :
      x ∈ scalarEffectiveDomain f :=
    helperForTheorem_5_24_1_mem_scalarEffectiveDomain_of_not_left_not_right
      f hproper hxLeft hxRight
  exact
    helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension_at_domain
      f hproper hxDom

/-- Helper for Theorem 5.24.1: the three-term order chain
`f'_+(z₁) ≤ f'_-(x) ≤ f'_+(x) ≤ f'_-(z₂)` holds whenever `z₁ < x < z₂`. -/
lemma helperForTheorem_5_24_1_derivativeExtensions_orderChain
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {z1 x z2 : ℝ} (hz1x : z1 < x) (hxz2 : x < z2) :
    rightDerivativeExtension f z1 ≤ leftDerivativeExtension f x ∧
      leftDerivativeExtension f x ≤ rightDerivativeExtension f x ∧
      rightDerivativeExtension f x ≤ leftDerivativeExtension f z2 := by
  -- Combine the off-diagonal comparison with the same-point inequality.
  refine ⟨?_, ?_, ?_⟩
  · exact
      helperForTheorem_5_24_1_rightDerivativeExtension_le_leftDerivativeExtension_of_lt
        f hproper hz1x
  · exact
      helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
        f hproper x
  · exact
      helperForTheorem_5_24_1_rightDerivativeExtension_le_leftDerivativeExtension_of_lt
        f hproper hxz2

/-- Helper for Theorem 5.24.1: the derivative extensions are monotone once the strict-order
comparison and same-point inequality are known. -/
lemma helperForTheorem_5_24_1_monotoneDerivativeExtensions
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f) :
    Monotone (rightDerivativeExtension f) ∧ Monotone (leftDerivativeExtension f) := by
  constructor
  · intro x y hxy
    rcases lt_or_eq_of_le hxy with hlt | rfl
    · -- Insert the left derivative at `y` as an intermediate value.
      exact
        le_trans
          (helperForTheorem_5_24_1_rightDerivativeExtension_le_leftDerivativeExtension_of_lt
            f hproper hlt)
          (helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
            f hproper y)
    · exact le_rfl
  · intro x y hxy
    rcases lt_or_eq_of_le hxy with hlt | rfl
    · -- Insert the right derivative at `x` as an intermediate value.
      exact
        le_trans
          (helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
            f hproper x)
          (helperForTheorem_5_24_1_rightDerivativeExtension_le_leftDerivativeExtension_of_lt
            f hproper hlt)
    · exact le_rfl

/-- Helper for Theorem 5.24.1: reflecting the scalar variable sends the scalar effective domain
of `f` to its negated preimage. -/
lemma helperForTheorem_5_24_1_reflectedFunction_mem_scalarEffectiveDomain_iff
    (f : (Fin 1 → ℝ) → EReal) (x : ℝ) :
    x ∈ scalarEffectiveDomain (fun u => f (-u)) ↔ -x ∈ scalarEffectiveDomain f := by
  constructor
  · intro hx
    rcases hx with ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    simpa [scalarEffectiveDomain, scalarPoint] using hμ
  · intro hx
    rcases hx with ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    simpa [scalarEffectiveDomain, scalarPoint] using hμ

/-- Helper for Theorem 5.24.1: after reflection, being strictly right of the effective domain is
equivalent to the original point being strictly left of it. -/
lemma helperForTheorem_5_24_1_reflectedFunction_rightOf_iff
    (f : (Fin 1 → ℝ) → EReal) (x : ℝ) :
    IsRightOfScalarEffectiveDomain (fun u => f (-u)) (-x) ↔ IsLeftOfScalarEffectiveDomain f x := by
  constructor
  · intro hx y hy
    -- Pull an original-domain point `y` back to the reflected point `-y`.
    have hmem : -y ∈ scalarEffectiveDomain (fun u => f (-u)) :=
      (helperForTheorem_5_24_1_reflectedFunction_mem_scalarEffectiveDomain_iff f (-y)).2
        (by simpa)
    have hlt : -y < -x := hx (-y) hmem
    linarith
  · intro hx y hy
    -- Push a reflected-domain point `y` forward to the original-domain point `-y`.
    have hmem : -y ∈ scalarEffectiveDomain f :=
      (helperForTheorem_5_24_1_reflectedFunction_mem_scalarEffectiveDomain_iff f y).1 hy
    have hlt : x < -y := hx (-y) hmem
    linarith

/-- Helper for Theorem 5.24.1: after reflection, being strictly left of the effective domain is
equivalent to the original point being strictly right of it. -/
lemma helperForTheorem_5_24_1_reflectedFunction_leftOf_iff
    (f : (Fin 1 → ℝ) → EReal) (x : ℝ) :
    IsLeftOfScalarEffectiveDomain (fun u => f (-u)) (-x) ↔ IsRightOfScalarEffectiveDomain f x := by
  constructor
  · intro hx y hy
    -- Pull an original-domain point `y` back to the reflected point `-y`.
    have hmem : -y ∈ scalarEffectiveDomain (fun u => f (-u)) :=
      (helperForTheorem_5_24_1_reflectedFunction_mem_scalarEffectiveDomain_iff f (-y)).2
        (by simpa)
    have hlt : -x < -y := hx (-y) hmem
    linarith
  · intro hx y hy
    -- Push a reflected-domain point `y` forward to the original-domain point `-y`.
    have hmem : -y ∈ scalarEffectiveDomain f :=
      (helperForTheorem_5_24_1_reflectedFunction_mem_scalarEffectiveDomain_iff f y).1 hy
    have hlt : -y < x := hx (-y) hmem
    linarith

/-- Helper for Theorem 5.24.1: reflecting a closed convex function preserves closed convexity. -/
lemma helperForTheorem_5_24_1_reflectedFunction_closed
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f) :
    ClosedConvexFunction (fun u => f (-u)) := by
  -- Reflection is linear and continuous, so both convexity and lower semicontinuity transport.
  refine ⟨?_, ?_⟩
  · simpa using
      (convexFunctionOn_precomp_linearMap
        (A := (ContinuousLinearEquiv.neg ℝ : (Fin 1 → ℝ) ≃L[ℝ] (Fin 1 → ℝ)).toLinearMap)
        (g := f) hclosed.1)
  · simpa using
      hclosed.2.comp_continuous (show Continuous (fun u : Fin 1 → ℝ => -u) by fun_prop)

/-- Helper for Theorem 5.24.1: reflecting a proper convex function preserves properness. -/
lemma helperForTheorem_5_24_1_reflectedFunction_proper
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (fun u => f (-u)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Proper convexity keeps the convexity clause under linear precomposition.
    simpa using
      (convexFunctionOn_precomp_linearMap
        (A := (ContinuousLinearEquiv.neg ℝ : (Fin 1 → ℝ) ≃L[ℝ] (Fin 1 → ℝ)).toLinearMap)
        (g := f) hproper.1)
  · -- A finite witness for `f` gives a concrete point in the reflected epigraph.
    rcases properConvexFunctionOn_exists_finite_point (n := 1) (f := f) hproper with ⟨y, r, hy⟩
    refine ⟨(-y, r), ?_⟩
    refine (mem_epigraph_univ_iff (f := fun u => f (-u))).2 ?_
    simpa [hy]
  · -- Properness still excludes the value `⊥` after reflection.
    intro u hu
    simpa using hproper.2.2 (-u) (by simp)

/-- Helper for Theorem 5.24.1: the reflected positive-step quotient in direction `1` is the
original positive-step quotient in direction `-1`. -/
lemma helperForTheorem_5_24_1_reflectedDifferenceQuotient_dirOne
    (f : (Fin 1 → ℝ) → EReal) (x t : ℝ) :
    (f (scalarPoint x + t • scalarPoint (-1)) - f (scalarPoint x)) / (t : EReal) =
      ((fun u => f (-u)) (scalarPoint (-x) + t • scalarPoint 1) -
          (fun u => f (-u)) (scalarPoint (-x))) / (t : EReal) := by
  have harg0 : -(scalarPoint (-x)) = scalarPoint x := by
    ext i
    simp [scalarPoint]
  have harg1 : -(scalarPoint (-x) + t • scalarPoint 1) = scalarPoint x + t • scalarPoint (-1) := by
    ext i
    simp [scalarPoint, add_comm, add_left_comm]
  -- After rewriting the reflected arguments, the two quotients are identical.
  simpa [harg0, harg1]

/-- Helper for Theorem 5.24.1: the reflected positive-step quotient in direction `-1` is the
original positive-step quotient in direction `1`. -/
lemma helperForTheorem_5_24_1_reflectedDifferenceQuotient_dirNegOne
    (f : (Fin 1 → ℝ) → EReal) (x t : ℝ) :
    (f (scalarPoint x + t • scalarPoint 1) - f (scalarPoint x)) / (t : EReal) =
      ((fun u => f (-u)) (scalarPoint (-x) + t • scalarPoint (-1)) -
          (fun u => f (-u)) (scalarPoint (-x))) / (t : EReal) := by
  have harg0 : -(scalarPoint (-x)) = scalarPoint x := by
    ext i
    simp [scalarPoint]
  have harg1 : -(scalarPoint (-x) + t • scalarPoint (-1)) = scalarPoint x + t • scalarPoint 1 := by
    ext i
    simp [scalarPoint, add_comm, add_left_comm]
  -- After rewriting the reflected arguments, the two quotients are identical.
  simpa [harg0, harg1]

/-- Helper for Theorem 5.24.1: reflection swaps the two derivative extensions up to sign. -/
lemma helperForTheorem_5_24_1_reflectedFunction_derivativeIdentities
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f) (x : ℝ) :
    rightDerivativeExtension (fun u => f (-u)) (-x) = - leftDerivativeExtension f x ∧
      leftDerivativeExtension (fun u => f (-u)) (-x) = - rightDerivativeExtension f x := by
  have hRightRef :
      IsRightOfScalarEffectiveDomain (fun u => f (-u)) (-x) ↔
        IsLeftOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_reflectedFunction_rightOf_iff f x
  have hLeftRef :
      IsLeftOfScalarEffectiveDomain (fun u => f (-u)) (-x) ↔
        IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_reflectedFunction_leftOf_iff f x
  constructor
  · by_cases hxLeft : IsLeftOfScalarEffectiveDomain f x
    · have hxNotRight :
        ¬ IsRightOfScalarEffectiveDomain f x :=
          helperForTheorem_5_24_1_not_right_of_left f hproper hxLeft
      have hRefRight : IsRightOfScalarEffectiveDomain (fun u => f (-u)) (-x) :=
        hRightRef.2 hxLeft
      have hRefNotLeft :
          ¬ IsLeftOfScalarEffectiveDomain (fun u => f (-u)) (-x) := by
        simpa [hLeftRef] using hxNotRight
      -- Exterior values reduce to direct simplification.
      simp [rightDerivativeExtension, leftDerivativeExtension, hxLeft, hxNotRight,
        hRefRight, hRefNotLeft]
    · by_cases hxRight : IsRightOfScalarEffectiveDomain f x
      · have hxNotLeft :
          ¬ IsLeftOfScalarEffectiveDomain f x :=
            helperForTheorem_5_24_1_not_left_of_right f hproper hxRight
        have hRefLeft : IsLeftOfScalarEffectiveDomain (fun u => f (-u)) (-x) :=
          hLeftRef.2 hxRight
        have hRefNotRight :
            ¬ IsRightOfScalarEffectiveDomain (fun u => f (-u)) (-x) := by
          simpa [hRightRef] using hxNotLeft
        -- Exterior values reduce to direct simplification.
        simp [rightDerivativeExtension, leftDerivativeExtension, hxRight, hxNotLeft,
          hRefLeft, hRefNotRight]
      · have hRefNotRight :
          ¬ IsRightOfScalarEffectiveDomain (fun u => f (-u)) (-x) := by
          simpa [hRightRef] using hxLeft
        have hRefNotLeft :
          ¬ IsLeftOfScalarEffectiveDomain (fun u => f (-u)) (-x) := by
          simpa [hLeftRef] using hxRight
        have hudd :
            upperDirectionalDerivativeAt (fun u => f (-u)) (scalarPoint (-x)) (scalarPoint 1) =
              upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint (-1)) := by
          unfold upperDirectionalDerivativeAt
          apply congrArg sInf
          ext b
          constructor <;> intro hb
          · rcases hb with ⟨a, ha, rfl⟩
            refine ⟨a, ha, ?_⟩
            apply congrArg sSup
            ext q
            constructor <;> intro hq
            · rcases hq with ⟨t, ht0, hta, rfl⟩
              refine ⟨t, ht0, hta, ?_⟩
              exact helperForTheorem_5_24_1_reflectedDifferenceQuotient_dirOne f x t
            · rcases hq with ⟨t, ht0, hta, rfl⟩
              refine ⟨t, ht0, hta, ?_⟩
              exact (helperForTheorem_5_24_1_reflectedDifferenceQuotient_dirOne f x t).symm
          · rcases hb with ⟨a, ha, rfl⟩
            refine ⟨a, ha, ?_⟩
            apply congrArg sSup
            ext q
            constructor <;> intro hq
            · rcases hq with ⟨t, ht0, hta, rfl⟩
              refine ⟨t, ht0, hta, ?_⟩
              exact (helperForTheorem_5_24_1_reflectedDifferenceQuotient_dirOne f x t).symm
            · rcases hq with ⟨t, ht0, hta, rfl⟩
              refine ⟨t, ht0, hta, ?_⟩
              exact helperForTheorem_5_24_1_reflectedDifferenceQuotient_dirOne f x t
        -- In the domain regime, the reflected right quotient is the original left quotient.
        simp [rightDerivativeExtension, leftDerivativeExtension, hxLeft, hxRight, hRefNotRight,
          hRefNotLeft, hudd]
  · by_cases hxLeft : IsLeftOfScalarEffectiveDomain f x
    · have hxNotRight :
        ¬ IsRightOfScalarEffectiveDomain f x :=
          helperForTheorem_5_24_1_not_right_of_left f hproper hxLeft
      have hRefRight : IsRightOfScalarEffectiveDomain (fun u => f (-u)) (-x) :=
        hRightRef.2 hxLeft
      have hRefNotLeft :
          ¬ IsLeftOfScalarEffectiveDomain (fun u => f (-u)) (-x) := by
        simpa [hLeftRef] using hxNotRight
      -- Exterior values reduce to direct simplification.
      simp [rightDerivativeExtension, leftDerivativeExtension, hxLeft, hxNotRight,
        hRefRight, hRefNotLeft]
    · by_cases hxRight : IsRightOfScalarEffectiveDomain f x
      · have hxNotLeft :
          ¬ IsLeftOfScalarEffectiveDomain f x :=
            helperForTheorem_5_24_1_not_left_of_right f hproper hxRight
        have hRefLeft : IsLeftOfScalarEffectiveDomain (fun u => f (-u)) (-x) :=
          hLeftRef.2 hxRight
        have hRefNotRight :
            ¬ IsRightOfScalarEffectiveDomain (fun u => f (-u)) (-x) := by
          simpa [hRightRef] using hxNotLeft
        -- Exterior values reduce to direct simplification.
        simp [rightDerivativeExtension, leftDerivativeExtension, hxRight, hxNotLeft,
          hRefLeft, hRefNotRight]
      · have hRefNotRight :
          ¬ IsRightOfScalarEffectiveDomain (fun u => f (-u)) (-x) := by
          simpa [hRightRef] using hxLeft
        have hRefNotLeft :
          ¬ IsLeftOfScalarEffectiveDomain (fun u => f (-u)) (-x) := by
          simpa [hLeftRef] using hxRight
        have hudd :
            upperDirectionalDerivativeAt (fun u => f (-u)) (scalarPoint (-x)) (scalarPoint (-1)) =
              upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint 1) := by
          unfold upperDirectionalDerivativeAt
          apply congrArg sInf
          ext b
          constructor <;> intro hb
          · rcases hb with ⟨a, ha, rfl⟩
            refine ⟨a, ha, ?_⟩
            apply congrArg sSup
            ext q
            constructor <;> intro hq
            · rcases hq with ⟨t, ht0, hta, rfl⟩
              refine ⟨t, ht0, hta, ?_⟩
              exact helperForTheorem_5_24_1_reflectedDifferenceQuotient_dirNegOne f x t
            · rcases hq with ⟨t, ht0, hta, rfl⟩
              refine ⟨t, ht0, hta, ?_⟩
              exact (helperForTheorem_5_24_1_reflectedDifferenceQuotient_dirNegOne f x t).symm
          · rcases hb with ⟨a, ha, rfl⟩
            refine ⟨a, ha, ?_⟩
            apply congrArg sSup
            ext q
            constructor <;> intro hq
            · rcases hq with ⟨t, ht0, hta, rfl⟩
              refine ⟨t, ht0, hta, ?_⟩
              exact (helperForTheorem_5_24_1_reflectedDifferenceQuotient_dirNegOne f x t).symm
            · rcases hq with ⟨t, ht0, hta, rfl⟩
              refine ⟨t, ht0, hta, ?_⟩
              exact helperForTheorem_5_24_1_reflectedDifferenceQuotient_dirNegOne f x t
        -- In the domain regime, the reflected left quotient is the original right quotient.
        simp [rightDerivativeExtension, leftDerivativeExtension, hxLeft, hxRight, hRefNotRight,
          hRefNotLeft, hudd]

/-- Helper for Theorem 5.24.1: the affine parameter sending `z ∈ Ioo x y` to the segment
coefficient approaching `1` is well behaved on the right-neighborhood filter. -/
lemma helperForTheorem_5_24_1_affineParameter_tendsto_one
    {x y : ℝ} (hxy : x < y) :
    Filter.Tendsto (fun z : ℝ => (y - z) / (y - x))
      (nhdsWithin x (Set.Ioo x y))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    (f := fun z : ℝ => (y - z) / (y - x)) ?_ ?_
  · have hcont : Continuous (fun z : ℝ => (y - z) / (y - x)) := by
      fun_prop
    have hlim :
        Filter.Tendsto (fun z : ℝ => (y - z) / (y - x))
          (nhds x)
          (nhds (((y - x) / (y - x) : ℝ))) := by
      simpa [sub_eq_add_neg] using hcont.continuousAt.tendsto
    have hone : ((y - x) / (y - x) : ℝ) = 1 := by
      exact div_self (sub_ne_zero.mpr hxy.ne')
    exact tendsto_nhdsWithin_of_tendsto_nhds (hone ▸ hlim)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hden : 0 < y - x := sub_pos.mpr hxy
    -- Right-neighborhood points correspond to segment parameters below `1`.
    show (y - z) / (y - x) < 1
    field_simp [hden.ne']
    linarith [hz.1, hz.2]

/-- Helper for Theorem 5.24.1: the affine segment parametrization used near `x` really lands on
the scalar point `z`. -/
lemma helperForTheorem_5_24_1_segmentParameterization_eq_scalarPoint
    {x y z : ℝ} (hxy : x < y) :
    (1 - (y - z) / (y - x)) • scalarPoint y + ((y - z) / (y - x)) • scalarPoint x =
      scalarPoint z := by
  ext i
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
  simp [scalarPoint]
  -- Clearing the affine denominator reduces the segment identity to a scalar ring calculation.
  field_simp [scalarPoint, hne]
  ring


end Section24
end Chap05
