/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part4

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

-- Proof sketch: combine Theorem 26.1, which identifies essential smoothness with
-- single-valuedness of the subdifferential of a closed proper convex function, with the dual
-- characterization from Theorem 23.5 relating subdifferentials of `f` and `f*`, and then invoke
-- the Chapter 26 definition of essential strict convexity in terms of injectivity of the
-- subdifferential on its effective domain.
/-- Helper for Theorem 26.3: a Euclidean subgradient inequality converts to a real lower bound
once the comparison point is finite. -/
lemma helperForTheorem_26_3_realLowerBound_of_euclideanSubgradient
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x w xStar : Fin n → ℝ}
    (hxSub : IsEuclideanSubgradientAt f x xStar)
    (hwTop : f w ≠ ⊤) :
    (f w).toReal ≥ (f x).toReal + dotProduct xStar (w - x) := by
  -- The Chapter 23 finiteness lemma lets us rewrite the base-point value in `ℝ`.
  have hfxFinite :=
    helperForTheorem_23_5_finiteAt_of_euclideanSubgradient f hproper x xStar hxSub
  have hwBot : f w ≠ ⊥ := hproper.2.2 w (by simp)
  have hE : f w ≥ f x + ((dotProduct xStar (w - x) : ℝ) : EReal) := by
    simpa [IsEuclideanSubgradientAt, dotProduct_sub] using hxSub w
  have hRight :
      f x + ((dotProduct xStar (w - x) : ℝ) : EReal) =
        (((f x).toReal + dotProduct xStar (w - x) : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hfxFinite.1 hfxFinite.2]
    simp
  have hE' :
      f w ≥ (((f x).toReal + dotProduct xStar (w - x) : ℝ) : EReal) := by
    rw [hRight] at hE
    exact hE
  have hCast :
      (((f w).toReal : ℝ) : EReal) ≥
        (((f x).toReal + dotProduct xStar (w - x) : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hwTop hwBot] using hE'
  exact_mod_cast hCast

/-- Helper for Theorem 26.3: convexity bounds the real-valued restriction of `f` above every
convex combination of two finite points. -/
lemma helperForTheorem_26_3_convexCombination_toReal_le
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x y : Fin n → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hfxTop : f x ≠ ⊤) (hfyTop : f y ≠ ⊤) :
    f (a • x + b • y) ≠ ⊤ ∧
      (f (a • x + b • y)).toReal ≤ a * (f x).toReal + b * (f y).toReal := by
  let z : Fin n → ℝ := a • x + b • y
  have hnotBot : ∀ u : Fin n → ℝ, f u ≠ ⊥ := by
    intro u
    exact hproper.2.2 u (by simp)
  have hfxBot : f x ≠ ⊥ := hnotBot x
  have hfyBot : f y ≠ ⊥ := hnotBot y
  have hConvE :
      f z ≤ ((a : ℝ) : EReal) * f x + ((b : ℝ) : EReal) * f y := by
    by_cases hbZero : b = 0
    · have haOne : a = 1 := by linarith
      simp [z, hbZero, haOne]
    · by_cases haZero : a = 0
      · have hbOne : b = 1 := by linarith
        simp [z, haZero, hbOne]
      · have hbPos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hbZero)
        have haPos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using haZero)
        have hbLt : b < 1 := by linarith
        have hconvSeg :=
            (convexFunctionOn_iff_segment_inequality
              (C := (Set.univ : Set (Fin n → ℝ))) (f := f) convex_univ
              (by intro u _; exact hnotBot u)).1 hproper.1
              x (by simp) y (by simp) b hbPos hbLt
        have haEq : a = 1 - b := by linarith
        simpa [z, haEq] using hconvSeg
  have hRhsEq :
      ((a : ℝ) : EReal) * f x + ((b : ℝ) : EReal) * f y =
        (((a * (f x).toReal + b * (f y).toReal : ℝ)) : EReal) := by
    rw [← EReal.coe_toReal hfxTop hfxBot, ← EReal.coe_toReal hfyTop hfyBot]
    simp
  have hConvE' :
      f z ≤ (((a * (f x).toReal + b * (f y).toReal : ℝ)) : EReal) := by
    rw [hRhsEq] at hConvE
    exact hConvE
  have hzTop : f z ≠ ⊤ := by
    intro hzTop
    have : (((a * (f x).toReal + b * (f y).toReal : ℝ)) : EReal) = ⊤ := by
      simpa [hzTop] using hConvE'
    exact EReal.coe_ne_top (a * (f x).toReal + b * (f y).toReal) this
  have hzBot : f z ≠ ⊥ := hnotBot z
  have hCast :
      (((f z).toReal : ℝ) : EReal) ≤
        (((a * (f x).toReal + b * (f y).toReal : ℝ)) : EReal) := by
    simpa [EReal.coe_toReal hzTop hzBot] using hConvE'
  refine ⟨hzTop, ?_⟩
  exact_mod_cast hCast

/-- Helper for Theorem 26.3: if the same Euclidean dual vector supports `f` at two points, then
it supports `f` at every convex combination of those points, and `f` is affine there. -/
lemma helperForTheorem_26_3_segment_subgradient_and_affine_of_commonSubgradient
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x y xStar : Fin n → ℝ}
    (hxSub : IsEuclideanSubgradientAt f x xStar)
    (hySub : IsEuclideanSubgradientAt f y xStar)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    let z : Fin n → ℝ := a • x + b • y
    IsEuclideanSubgradientAt f z xStar ∧
      (f z).toReal = a * (f x).toReal + b * (f y).toReal := by
  let z : Fin n → ℝ := a • x + b • y
  have hfxFinite :=
    helperForTheorem_23_5_finiteAt_of_euclideanSubgradient f hproper x xStar hxSub
  have hfyFinite :=
    helperForTheorem_23_5_finiteAt_of_euclideanSubgradient f hproper y xStar hySub
  have hzTop :
      f z ≠ ⊤ :=
    (helperForTheorem_26_3_convexCombination_toReal_le
      hproper ha hb hab hfxFinite.1 hfyFinite.1).1
  have hzUpper :
      (f z).toReal ≤ a * (f x).toReal + b * (f y).toReal :=
    (helperForTheorem_26_3_convexCombination_toReal_le
      hproper ha hb hab hfxFinite.1 hfyFinite.1).2
  have hzBot : f z ≠ ⊥ := hproper.2.2 z (by simp)
  have hxAtZ :
      (f z).toReal ≥ (f x).toReal + dotProduct xStar (z - x) :=
    helperForTheorem_26_3_realLowerBound_of_euclideanSubgradient hproper hxSub hzTop
  have hyAtZ :
      (f z).toReal ≥ (f y).toReal + dotProduct xStar (z - y) :=
    helperForTheorem_26_3_realLowerBound_of_euclideanSubgradient hproper hySub hzTop
  have hdotZero :
      a * dotProduct xStar (z - x) + b * dotProduct xStar (z - y) = 0 := by
    have haEq : a = 1 - b := by linarith
    simp [z, haEq, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  have hzLower :
      (f z).toReal ≥ a * (f x).toReal + b * (f y).toReal := by
    have hxScaled := mul_le_mul_of_nonneg_left hxAtZ ha
    have hyScaled := mul_le_mul_of_nonneg_left hyAtZ hb
    have haux : a * (f x).toReal + b * (f y).toReal ≤
        a * (f z).toReal + b * (f z).toReal := by
      calc
        a * (f x).toReal + b * (f y).toReal =
            a * (f x).toReal + b * (f y).toReal +
              (a * dotProduct xStar (z - x) + b * dotProduct xStar (z - y)) := by
                rw [hdotZero]
                ring
        _ = a * ((f x).toReal + dotProduct xStar (z - x)) +
              b * ((f y).toReal + dotProduct xStar (z - y)) := by
                ring
        _ ≤ a * (f z).toReal + b * (f z).toReal := by
              linarith
    have hsum : a * (f z).toReal + b * (f z).toReal = (f z).toReal := by
      rw [← add_mul, hab, one_mul]
    linarith
  have hzEqReal :
      (f z).toReal = a * (f x).toReal + b * (f y).toReal :=
    le_antisymm hzUpper hzLower
  constructor
  · -- Combine the two endpoint subgradient inequalities and use the affine value equality at `z`.
    intro w
    by_cases hwTop : f w = ⊤
    · simp [hwTop]
    · have hwBot : f w ≠ ⊥ := hproper.2.2 w (by simp)
      have hxAtW :
          (f w).toReal ≥ (f x).toReal + dotProduct xStar (w - x) :=
        helperForTheorem_26_3_realLowerBound_of_euclideanSubgradient hproper hxSub hwTop
      have hyAtW :
          (f w).toReal ≥ (f y).toReal + dotProduct xStar (w - y) :=
        helperForTheorem_26_3_realLowerBound_of_euclideanSubgradient hproper hySub hwTop
      have hxScaled := mul_le_mul_of_nonneg_left hxAtW ha
      have hyScaled := mul_le_mul_of_nonneg_left hyAtW hb
      have hdotCombine :
          a * dotProduct xStar (w - x) + b * dotProduct xStar (w - y) =
            dotProduct xStar (w - z) := by
        have haEq : a = 1 - b := by linarith
        simp [z, haEq, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
        ring
      have haux :
          a * (f x).toReal + b * (f y).toReal + dotProduct xStar (w - z) ≤
            a * (f w).toReal + b * (f w).toReal := by
        calc
          a * (f x).toReal + b * (f y).toReal + dotProduct xStar (w - z) =
              a * (f x).toReal + b * (f y).toReal +
                (a * dotProduct xStar (w - x) + b * dotProduct xStar (w - y)) := by
                  rw [hdotCombine]
          _ = a * ((f x).toReal + dotProduct xStar (w - x)) +
                b * ((f y).toReal + dotProduct xStar (w - y)) := by
                  ring
          _ ≤ a * (f w).toReal + b * (f w).toReal := by
                linarith
      have hsum : a * (f w).toReal + b * (f w).toReal = (f w).toReal := by
        rw [← add_mul, hab, one_mul]
      have hReal :
          (f w).toReal ≥ (f z).toReal + dotProduct xStar (w - z) := by
        have haux' :
            (f z).toReal + dotProduct xStar (w - z) ≤
              a * (f w).toReal + b * (f w).toReal := by
          simpa [hzEqReal] using haux
        linarith
      have hCast :
          (((f w).toReal : ℝ) : EReal) ≥
            (((f z).toReal + dotProduct xStar (w - z) : ℝ) : EReal) := by
        exact_mod_cast hReal
      have hRight :
          (((f z).toReal + dotProduct xStar (w - z) : ℝ) : EReal) =
            f z + ((dotProduct xStar (w - z) : ℝ) : EReal) := by
        rw [← EReal.coe_toReal hzTop hzBot]
        simp
      have hFinal :
          (((f w).toReal : ℝ) : EReal) ≥
            f z + ((dotProduct xStar (w - z) : ℝ) : EReal) := by
        rwa [hRight] at hCast
      change f w ≥ f z + ((dotProduct xStar (w - z) : ℝ) : EReal)
      simpa [EReal.coe_toReal hwTop hwBot] using hFinal
  · exact hzEqReal

/-- Helper for Theorem 26.3: on the set where a fixed Euclidean subgradient is present, essential
strict convexity forces the supporting point to be unique. -/
lemma helperForTheorem_26_3_primalSubdifferential_injective_of_essentiallyStrictlyConvex
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hEss : IsEssentiallyStrictlyConvex f) :
    ∀ ⦃x y xStar : Fin n → ℝ⦄,
      IsEuclideanSubgradientAt f x xStar →
      IsEuclideanSubgradientAt f y xStar →
      x = y := by
  rcases hEss with ⟨hproper, hstrict⟩
  intro x y xStar hxSub hySub
  let C : Set (Fin n → ℝ) := {z | IsEuclideanSubgradientAt f z xStar}
  have hCSubset : C ⊆ subdifferentialEffectiveDomain f := by
    intro z hz
    exact
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty f z).2
        ⟨dotProductEquiv ℝ (Fin n) xStar, hz⟩
  have hCConv : Convex ℝ C := by
    intro u hu v hv a b ha hb hab
    -- The common subgradient persists along convex combinations of its support set.
    exact
      (helperForTheorem_26_3_segment_subgradient_and_affine_of_commonSubgradient
        hproper hu hv ha hb hab).1
  have hStrictC : StrictConvexOn ℝ C (fun z => (f z).toReal) := hstrict hCSubset hCConv
  by_contra hxy
  have hxC : x ∈ C := hxSub
  have hyC : y ∈ C := hySub
  have hmidC :
      (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ C :=
    hCConv hxC hyC (by norm_num) (by norm_num) (by ring)
  have hmidStrict :
      (f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)).toReal <
        (1 / 2 : ℝ) * (f x).toReal + (1 / 2 : ℝ) * (f y).toReal :=
    hStrictC.2 hxC hyC hxy (by norm_num) (by norm_num) (by ring)
  have hmidEq :
      (f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)).toReal =
        (1 / 2 : ℝ) * (f x).toReal + (1 / 2 : ℝ) * (f y).toReal :=
    (helperForTheorem_26_3_segment_subgradient_and_affine_of_commonSubgradient
      hproper hxSub hySub (by norm_num) (by norm_num) (by ring)).2
  exact (lt_irrefl _ ) (hmidEq ▸ hmidStrict)

/-- Helper for Theorem 26.3: if convexity is attained with equality at a strict convex
combination, then every subgradient at the middle point is also a subgradient at the endpoints. -/
lemma helperForTheorem_26_3_endpoint_subgradients_of_convexCombinationEquality
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x y : Fin n → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hxDom : x ∈ subdifferentialEffectiveDomain f)
    (hyDom : y ∈ subdifferentialEffectiveDomain f)
    {xStar : Fin n → ℝ}
    (hzSub : IsEuclideanSubgradientAt f (a • x + b • y) xStar)
    (hEq :
      (f (a • x + b • y)).toReal = a * (f x).toReal + b * (f y).toReal) :
    IsEuclideanSubgradientAt f x xStar ∧ IsEuclideanSubgradientAt f y xStar := by
  let z : Fin n → ℝ := a • x + b • y
  have hzFinite :
      f z ≠ ⊤ ∧ f z ≠ ⊥ := by
    simpa [z] using
      helperForTheorem_23_5_finiteAt_of_euclideanSubgradient
        f hproper z xStar hzSub
  have hxTop : f x ≠ ⊤ :=
    mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → ℝ))) (f := f)
      ((relativeInterior_subset_subdifferentialEffectiveDomain_subset_effectiveDomain
        (f := f) hproper).2 hxDom)
  have hyTop : f y ≠ ⊤ :=
    mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → ℝ))) (f := f)
      ((relativeInterior_subset_subdifferentialEffectiveDomain_subset_effectiveDomain
        (f := f) hproper).2 hyDom)
  have hxBot : f x ≠ ⊥ := hproper.2.2 x (by simp)
  have hyBot : f y ≠ ⊥ := hproper.2.2 y (by simp)
  have hzx :
      (f x).toReal ≥ (f z).toReal + dotProduct xStar (x - z) :=
    helperForTheorem_26_3_realLowerBound_of_euclideanSubgradient
      hproper hzSub hxTop
  have hzy :
      (f y).toReal ≥ (f z).toReal + dotProduct xStar (y - z) :=
    helperForTheorem_26_3_realLowerBound_of_euclideanSubgradient
      hproper hzSub hyTop
  have hzero :
      a * dotProduct xStar (x - z) + b * dotProduct xStar (y - z) = 0 := by
    have haEq : a = 1 - b := by linarith
    simp [z, haEq, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  have hzxScaled := mul_le_mul_of_nonneg_left hzx ha.le
  have hzyScaled := mul_le_mul_of_nonneg_left hzy hb.le
  have hweighted_eq :
      a * ((f z).toReal + dotProduct xStar (x - z)) +
        b * ((f z).toReal + dotProduct xStar (y - z)) =
        a * (f x).toReal + b * (f y).toReal := by
    calc
      a * ((f z).toReal + dotProduct xStar (x - z)) +
          b * ((f z).toReal + dotProduct xStar (y - z)) =
          (a + b) * (f z).toReal +
            (a * dotProduct xStar (x - z) + b * dotProduct xStar (y - z)) := by
            ring
      _ = (f z).toReal := by rw [hab, hzero]; ring
      _ = a * (f x).toReal + b * (f y).toReal := by simpa [z] using hEq
  have hEqX :
      (f x).toReal = (f z).toReal + dotProduct xStar (x - z) := by
    have hDiff :
        a * ((f x).toReal - ((f z).toReal + dotProduct xStar (x - z))) +
          b * ((f y).toReal - ((f z).toReal + dotProduct xStar (y - z))) = 0 := by
      linarith [hweighted_eq]
    have hxDiffNonneg :
        0 ≤ (f x).toReal - ((f z).toReal + dotProduct xStar (x - z)) := by linarith
    have hyDiffNonneg :
        0 ≤ (f y).toReal - ((f z).toReal + dotProduct xStar (y - z)) := by linarith
    have hax :
        a * ((f x).toReal - ((f z).toReal + dotProduct xStar (x - z))) = 0 := by
      linarith
    have hxDiffZero :
        (f x).toReal - ((f z).toReal + dotProduct xStar (x - z)) = 0 := by
      exact (mul_eq_zero.mp hax).resolve_left ha.ne'
    linarith
  have hEqY :
      (f y).toReal = (f z).toReal + dotProduct xStar (y - z) := by
    have hDiff :
        a * ((f x).toReal - ((f z).toReal + dotProduct xStar (x - z))) +
          b * ((f y).toReal - ((f z).toReal + dotProduct xStar (y - z))) = 0 := by
      linarith [hweighted_eq]
    have hxDiffNonneg :
        0 ≤ (f x).toReal - ((f z).toReal + dotProduct xStar (x - z)) := by linarith
    have hyDiffNonneg :
        0 ≤ (f y).toReal - ((f z).toReal + dotProduct xStar (y - z)) := by linarith
    have hby :
        b * ((f y).toReal - ((f z).toReal + dotProduct xStar (y - z))) = 0 := by
      linarith
    have hyDiffZero :
        (f y).toReal - ((f z).toReal + dotProduct xStar (y - z)) = 0 := by
      exact (mul_eq_zero.mp hby).resolve_left hb.ne'
    linarith
  constructor
  · -- Once equality holds at `x`, the middle-point subgradient inequality translates to `x`.
    intro w
    change f w ≥ f x + ((dotProduct xStar (w - x) : ℝ) : EReal)
    have hzIneq : f w ≥ f z + ((dotProduct xStar (w - z) : ℝ) : EReal) := by
      simpa [z, IsEuclideanSubgradientAt, dotProduct_sub, dotProduct_add, dotProduct_smul,
        smul_eq_mul] using hzSub w
    have hEqXE' :
        (((f x).toReal : ℝ) : EReal) =
          (((f z).toReal + dotProduct xStar (x - z) : ℝ) : EReal) := by
      exact_mod_cast hEqX
    have hEqXE :
        f x = f z + ((dotProduct xStar (x - z) : ℝ) : EReal) := by
      calc
        f x = (((f x).toReal : ℝ) : EReal) := by
          symm
          exact EReal.coe_toReal hxTop hxBot
        _ = (((f z).toReal + dotProduct xStar (x - z) : ℝ) : EReal) := hEqXE'
        _ = f z + ((dotProduct xStar (x - z) : ℝ) : EReal) := by
          rw [← EReal.coe_toReal hzFinite.1 hzFinite.2]
          simp
    have hLinear :
        dotProduct xStar (w - z) =
          dotProduct xStar (w - x) + dotProduct xStar (x - z) := by
      simp [z, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hRewritten :
        f z + ((dotProduct xStar (w - z) : ℝ) : EReal) =
          f x + ((dotProduct xStar (w - x) : ℝ) : EReal) := by
      have hLinearE :
          ((dotProduct xStar (w - z) : ℝ) : EReal) =
            ((dotProduct xStar (w - x) : ℝ) : EReal) +
              ((dotProduct xStar (x - z) : ℝ) : EReal) := by
        exact congrArg (fun r : ℝ => ((r : ℝ) : EReal)) hLinear
      calc
        f z + ((dotProduct xStar (w - z) : ℝ) : EReal) =
            f z + ((dotProduct xStar (w - x) : ℝ) : EReal) +
              ((dotProduct xStar (x - z) : ℝ) : EReal) := by
                rw [hLinearE, add_assoc]
        _ = (f z + ((dotProduct xStar (x - z) : ℝ) : EReal)) +
              ((dotProduct xStar (w - x) : ℝ) : EReal) := by
                abel
        _ = f x + ((dotProduct xStar (w - x) : ℝ) : EReal) := by rw [hEqXE]
    exact hRewritten ▸ hzIneq
  · -- The same translation argument works symmetrically for `y`.
    intro w
    change f w ≥ f y + ((dotProduct xStar (w - y) : ℝ) : EReal)
    have hzIneq : f w ≥ f z + ((dotProduct xStar (w - z) : ℝ) : EReal) := by
      simpa [z, IsEuclideanSubgradientAt, dotProduct_sub, dotProduct_add, dotProduct_smul,
        smul_eq_mul] using hzSub w
    have hEqYE' :
        (((f y).toReal : ℝ) : EReal) =
          (((f z).toReal + dotProduct xStar (y - z) : ℝ) : EReal) := by
      exact_mod_cast hEqY
    have hEqYE :
        f y = f z + ((dotProduct xStar (y - z) : ℝ) : EReal) := by
      calc
        f y = (((f y).toReal : ℝ) : EReal) := by
          symm
          exact EReal.coe_toReal hyTop hyBot
        _ = (((f z).toReal + dotProduct xStar (y - z) : ℝ) : EReal) := hEqYE'
        _ = f z + ((dotProduct xStar (y - z) : ℝ) : EReal) := by
          rw [← EReal.coe_toReal hzFinite.1 hzFinite.2]
          simp
    have hLinear :
        dotProduct xStar (w - z) =
          dotProduct xStar (w - y) + dotProduct xStar (y - z) := by
      simp [z, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hRewritten :
        f z + ((dotProduct xStar (w - z) : ℝ) : EReal) =
          f y + ((dotProduct xStar (w - y) : ℝ) : EReal) := by
      have hLinearE :
          ((dotProduct xStar (w - z) : ℝ) : EReal) =
            ((dotProduct xStar (w - y) : ℝ) : EReal) +
              ((dotProduct xStar (y - z) : ℝ) : EReal) := by
        exact congrArg (fun r : ℝ => ((r : ℝ) : EReal)) hLinear
      calc
        f z + ((dotProduct xStar (w - z) : ℝ) : EReal) =
            f z + ((dotProduct xStar (w - y) : ℝ) : EReal) +
              ((dotProduct xStar (y - z) : ℝ) : EReal) := by
                rw [hLinearE, add_assoc]
        _ = (f z + ((dotProduct xStar (y - z) : ℝ) : EReal)) +
              ((dotProduct xStar (w - y) : ℝ) : EReal) := by
                abel
        _ = f y + ((dotProduct xStar (w - y) : ℝ) : EReal) := by rw [hEqYE]
    exact hRewritten ▸ hzIneq

/-- Theorem 26.3: a closed proper convex function is essentially strictly convex if and only if
its Fenchel conjugate is essentially smooth. -/
theorem essentiallyStrictlyConvex_iff_conjugate_essentiallySmooth
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f) :
    IsEssentiallyStrictlyConvex f ↔ IsEssentiallySmooth (fenchelConjugate n f) := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hclosed : ClosedConvexFunction f := ⟨hfConv, hf_closed⟩
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hfStar : ProperConvexERealFunction (F := (Fin n → ℝ)) (fenchelConjugate n f) :=
    helperForLemma_26_2_properConvexERealFunction hproperStar
  have hfenchelClosedConvex := fenchelConjugate_closedConvex (n := n) (f := f)
  have hfStarClosed : LowerSemicontinuous (fenchelConjugate n f) := hfenchelClosedConvex.1
  have hclosedStar : ClosedConvexFunction (fenchelConjugate n f) :=
    ⟨hfenchelClosedConvex.2, hfenchelClosedConvex.1⟩
  constructor
  · intro hEss
    have hInj :
        ∀ ⦃x y xStar : Fin n → ℝ⦄,
          IsEuclideanSubgradientAt f x xStar →
          IsEuclideanSubgradientAt f y xStar →
          x = y :=
      helperForTheorem_26_3_primalSubdifferential_injective_of_essentiallyStrictlyConvex hEss
    have hSVStar :
        IsSingleValuedMultivaluedMap (subdifferentialAt (fenchelConjugate n f)) := by
      intro xStar g₁ hg₁ g₂ hg₂
      let x₁ : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g₁
      let x₂ : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g₂
      have hx₁Star :
          IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x₁ := by
        simpa [x₁, IsEuclideanSubgradientAt] using hg₁
      have hx₂Star :
          IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x₂ := by
        simpa [x₂, IsEuclideanSubgradientAt] using hg₂
      have hx₁ :
          IsEuclideanSubgradientAt f x₁ xStar :=
        (euclidean_subgradient_fenchelConjugate_iff
          (f := f) hclosed hproper x₁ xStar).1 hx₁Star
      have hx₂ :
          IsEuclideanSubgradientAt f x₂ xStar :=
        (euclidean_subgradient_fenchelConjugate_iff
          (f := f) hclosed hproper x₂ xStar).1 hx₂Star
      have hEq : x₁ = x₂ := hInj hx₁ hx₂
      calc
        g₁ = dotProductEquiv ℝ (Fin n) x₁ := by simp [x₁]
        _ = dotProductEquiv ℝ (Fin n) x₂ := by rw [hEq]
        _ = g₂ := by simp [x₂]
    -- Route correction: combine the endpoint strict-convexity argument with Theorem 23.5 only
    -- at the final transport step from `∂f` to `∂(f*)`.
    exact
      (subdifferential_singleValued_iff_essentiallySmooth
        (f := fenchelConjugate n f) hfStar hfStarClosed).1.1 hSVStar
  · intro hSmoothStar
    have hSVStar :
        IsSingleValuedMultivaluedMap (subdifferentialAt (fenchelConjugate n f)) :=
      (subdifferential_singleValued_iff_essentiallySmooth
        (f := fenchelConjugate n f) hfStar hfStarClosed).1.2 hSmoothStar
    refine ⟨hproper, ?_⟩
    intro C hCSubset hCConv
    refine ⟨hCConv, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    let z : Fin n → ℝ := a • x + b • y
    have hz : z ∈ C := hCConv hx hy ha.le hb.le hab
    have hzDom : z ∈ subdifferentialEffectiveDomain f := hCSubset hz
    rcases
        (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
          f z).1 hzDom with
      ⟨g, hgSub⟩
    have hxDom : x ∈ subdifferentialEffectiveDomain f := hCSubset hx
    have hyDom : y ∈ subdifferentialEffectiveDomain f := hCSubset hy
    have hxTop : f x ≠ ⊤ :=
      mem_effectiveDomain_imp_ne_top
        (S := (Set.univ : Set (Fin n → ℝ))) (f := f)
        ((relativeInterior_subset_subdifferentialEffectiveDomain_subset_effectiveDomain
          (f := f) hproper).2 hxDom)
    have hyTop : f y ≠ ⊤ :=
      mem_effectiveDomain_imp_ne_top
        (S := (Set.univ : Set (Fin n → ℝ))) (f := f)
        ((relativeInterior_subset_subdifferentialEffectiveDomain_subset_effectiveDomain
          (f := f) hproper).2 hyDom)
    have hConvLe :
        (f z).toReal ≤ a * (f x).toReal + b * (f y).toReal :=
      (helperForTheorem_26_3_convexCombination_toReal_le
        hproper ha.le hb.le hab hxTop hyTop).2
    by_contra hNotStrict
    have hEqReal :
        (f z).toReal = a * (f x).toReal + b * (f y).toReal :=
      le_antisymm hConvLe (not_lt.mp hNotStrict)
    let xStar : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g
    have hzSubVec : IsEuclideanSubgradientAt f z xStar := by
      simpa [xStar, IsEuclideanSubgradientAt] using hgSub
    have hEnds :
        IsEuclideanSubgradientAt f x xStar ∧ IsEuclideanSubgradientAt f y xStar :=
      helperForTheorem_26_3_endpoint_subgradients_of_convexCombinationEquality
        hproper ha hb hab hxDom hyDom hzSubVec hEqReal
    have hxStar : IsEuclideanSubgradientAt f x xStar := hEnds.1
    have hyStar : IsEuclideanSubgradientAt f y xStar := hEnds.2
    have hxConj :
        IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hclosed hproper x xStar).2 hxStar
    have hyConj :
        IsEuclideanSubgradientAt (fenchelConjugate n f) xStar y :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hclosed hproper y xStar).2 hyStar
    have hEqDual :
        dotProductEquiv ℝ (Fin n) x = dotProductEquiv ℝ (Fin n) y :=
      hSVStar xStar (by simpa [IsEuclideanSubgradientAt] using hxConj)
        (by simpa [IsEuclideanSubgradientAt] using hyConj)
    exact hxy ((dotProductEquiv ℝ (Fin n)).injective hEqDual)

end Section26
end Chap05
