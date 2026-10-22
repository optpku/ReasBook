/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part5

section Chap05
section Section23

open scoped ConvexAnalysis Pointwise

/-- The one-variable function `g(ξ₁) = 1 - √ξ₁` on the nonnegative half-line and `+∞` on the
negative half-line. -/
noncomputable def rightHalfLineSquareRootGap (ξ₁ : ℝ) : EReal :=
  if 0 ≤ ξ₁ then ((1 - Real.sqrt ξ₁ : ℝ) : EReal) else ⊤

/-- The `ℝ²` example `f(ξ₁, ξ₂) = max {g(ξ₁), |ξ₂|}` used to show that the set of
subdifferentiability points of a proper convex function need not be convex. -/
noncomputable def nonconvexSubdifferentiabilityExampleFunction (ξ : Fin 2 → ℝ) : EReal :=
  max (rightHalfLineSquareRootGap (ξ 0)) (((|ξ 1| : ℝ)) : EReal)

/-- The closed right half-plane in `ℝ²`. -/
def closedRightHalfPlane : Set (Fin 2 → ℝ) :=
  {ξ | 0 ≤ ξ 0}

/-- The relative interior of the vertical line segment joining `(0, 1)` and `(0, -1)`. -/
def openVerticalUnitSegment : Set (Fin 2 → ℝ) :=
  {ξ | ξ 0 = 0 ∧ |ξ 1| < 1}

/-- The `g`-branch is convex on the nonnegative half-line. -/
lemma helperForExample_23_4_2_rightHalfLineSquareRootGap_branch_convex :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => 1 - Real.sqrt t) := by
  have hneg :
      ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => -Real.sqrt t) :=
    (neg_convexOn_iff).2 Real.strictConcaveOn_sqrt.concaveOn
  have hconst :
      ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun _ : ℝ => (1 : ℝ)) :=
    convexOn_const (c := (1 : ℝ)) (hs := convex_Ici (0 : ℝ))
  have hadd :
      ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => (1 : ℝ) + -Real.sqrt t) :=
    hconst.add hneg
  simpa [sub_eq_add_neg] using hadd

/-- The epigraph of the right-half-line square-root gap function is convex. -/
lemma helperForExample_23_4_2_rightHalfLineSquareRootGap_convex :
    ConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
      (fun ξ : Fin 2 → ℝ => rightHalfLineSquareRootGap (ξ 0)) := by
  let C : Set (Fin 2 → ℝ) := closedRightHalfPlane
  have hbranch :
      ConvexOn ℝ C (fun ξ : Fin 2 → ℝ => 1 - Real.sqrt (ξ 0)) := by
    let proj0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0
    have hcomp :
        ConvexOn ℝ (proj0 ⁻¹' Set.Ici (0 : ℝ))
          (fun ξ : Fin 2 → ℝ => (fun t : ℝ => 1 - Real.sqrt t) (proj0 ξ)) := by
      simpa [Function.comp, proj0, LinearMap.proj_apply] using
        helperForExample_23_4_2_rightHalfLineSquareRootGap_branch_convex.comp_linearMap proj0
    simpa [C, closedRightHalfPlane, proj0] using hcomp
  have hconv :=
    convexFunctionOn_univ_if_top (C := C) (g := fun ξ : Fin 2 → ℝ => 1 - Real.sqrt (ξ 0)) hbranch
  simpa [C, rightHalfLineSquareRootGap, closedRightHalfPlane] using hconv

/-- The epigraph of the absolute-value branch is convex. -/
lemma helperForExample_23_4_2_absBranch_convex :
    ConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
      (fun ξ : Fin 2 → ℝ => (((|ξ 1| : ℝ)) : EReal)) := by
  change Convex ℝ (epigraph (Set.univ : Set (Fin 2 → ℝ))
    (fun ξ : Fin 2 → ℝ => (((|ξ 1| : ℝ)) : EReal)))
  intro x hx y hy a b ha hb hab
  have hxR : |x.1 1| ≤ x.2 := (EReal.coe_le_coe_iff).1 hx.2
  have hyR : |y.1 1| ≤ y.2 := (EReal.coe_le_coe_iff).1 hy.2
  have hcoord : ((a • x + b • y).1 1) = a * x.1 1 + b * y.1 1 := by
    simp [smul_eq_mul]
  have habs :
      |a * x.1 1 + b * y.1 1| ≤ a * |x.1 1| + b * |y.1 1| := by
    calc
      |a * x.1 1 + b * y.1 1| ≤ |a * x.1 1| + |b * y.1 1| := abs_add_le _ _
      _ = a * |x.1 1| + b * |y.1 1| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hweighted : a * |x.1 1| + b * |y.1 1| ≤ a * x.2 + b * y.2 := by
    exact add_le_add (mul_le_mul_of_nonneg_left hxR ha) (mul_le_mul_of_nonneg_left hyR hb)
  have hfinal : |a * x.1 1 + b * y.1 1| ≤ a * x.2 + b * y.2 := le_trans habs hweighted
  exact ⟨by exact Set.mem_univ (a • x.1 + b • y.1),
    (EReal.coe_le_coe_iff).2 (by simpa [hcoord, smul_eq_mul] using hfinal)⟩

/-- The full `max` example is a proper convex function. -/
lemma helperForExample_23_4_2_properConvex :
    ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
      nonconvexSubdifferentiabilityExampleFunction := by
  have hgapConv :
      ConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
        (fun ξ : Fin 2 → ℝ => rightHalfLineSquareRootGap (ξ 0)) :=
    helperForExample_23_4_2_rightHalfLineSquareRootGap_convex
  have habsConv :
      ConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
        (fun ξ : Fin 2 → ℝ => (((|ξ 1| : ℝ)) : EReal)) :=
    helperForExample_23_4_2_absBranch_convex
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
        nonconvexSubdifferentiabilityExampleFunction := by
    have hEpi :
        epigraph (Set.univ : Set (Fin 2 → ℝ)) nonconvexSubdifferentiabilityExampleFunction =
          epigraph (Set.univ : Set (Fin 2 → ℝ)) (fun ξ : Fin 2 → ℝ => rightHalfLineSquareRootGap (ξ 0)) ∩
            epigraph (Set.univ : Set (Fin 2 → ℝ)) (fun ξ : Fin 2 → ℝ => (((|ξ 1| : ℝ)) : EReal)) := by
      ext p
      constructor
      · intro hp
        exact ⟨⟨hp.1, le_trans (le_max_left _ _) hp.2⟩,
          ⟨hp.1, le_trans (le_max_right _ _) hp.2⟩⟩
      · rintro ⟨hpGap, hpAbs⟩
        exact ⟨hpGap.1, max_le_iff.2 ⟨hpGap.2, hpAbs.2⟩⟩
    simpa [ConvexFunctionOn, hEpi] using hgapConv.inter habsConv
  have hnonempty :
      Set.Nonempty (epigraph (Set.univ : Set (Fin 2 → ℝ))
        nonconvexSubdifferentiabilityExampleFunction) := by
    refine ⟨((0 : Fin 2 → ℝ), 1), ?_⟩
    constructor
    · exact Set.mem_univ (0 : Fin 2 → ℝ)
    · simp [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap]
  have hneBot :
      ∀ ξ ∈ (Set.univ : Set (Fin 2 → ℝ)),
        nonconvexSubdifferentiabilityExampleFunction ξ ≠ (⊥ : EReal) := by
    intro ξ hξ
    by_cases h0 : 0 ≤ ξ 0
    · simp [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap, h0]
    · simp [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap, h0]
  exact ⟨hconv, hnonempty, hneBot⟩

/-- The effective domain of the example is exactly the closed right half-plane. -/
lemma helperForExample_23_4_2_effectiveDomain :
    effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) nonconvexSubdifferentiabilityExampleFunction =
      closedRightHalfPlane := by
  ext ξ
  constructor
  · intro hξ
    by_contra hneg
    have hξ0neg : ¬ 0 ≤ ξ 0 := by simpa [closedRightHalfPlane] using hneg
    have htop : nonconvexSubdifferentiabilityExampleFunction ξ = (⊤ : EReal) := by
      simp [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap, hξ0neg]
    rcases hξ with ⟨μ, hμ⟩
    exact not_top_le_coe μ (by simpa [htop] using hμ.2)
  · intro hξ
    have hξ0 : 0 ≤ ξ 0 := by simpa [closedRightHalfPlane] using hξ
    refine ⟨(nonconvexSubdifferentiabilityExampleFunction ξ).toReal, ?_⟩
    exact epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin 2 → ℝ))) (x := ξ)
      (μ := (nonconvexSubdifferentiabilityExampleFunction ξ).toReal) (by simp)
      (by
        have hneTop : nonconvexSubdifferentiabilityExampleFunction ξ ≠ (⊤ : EReal) := by
          rw [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap, if_pos hξ0]
          exact max_ne_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)
        have hneBot : nonconvexSubdifferentiabilityExampleFunction ξ ≠ (⊥ : EReal) := by
          simp [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap, hξ0]
        rw [EReal.coe_toReal hneTop hneBot])

/-- Points with positive first coordinate lie in the interior of the closed right half-plane. -/
lemma helperForExample_23_4_2_mem_interior_closedRightHalfPlane {ξ : Fin 2 → ℝ}
    (hξ : 0 < ξ 0) :
    ξ ∈ interior closedRightHalfPlane := by
  refine mem_interior_iff_mem_nhds.mpr ?_
  let U : Set (Fin 2 → ℝ) := {z | 0 < z 0}
  have hU : U ∈ nhds ξ := by
    exact (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hξ
  show closedRightHalfPlane ∈ nhds ξ
  refine Filter.mem_of_superset hU ?_
  · intro z hz
    simpa [U, closedRightHalfPlane] using hz.le

/-- Boundary points `(0,t)` with `|t| < 1` have empty subdifferential. -/
lemma helperForExample_23_4_2_subdifferential_empty_on_openVerticalUnitSegment
    {ξ : Fin 2 → ℝ} (hξ0 : ξ 0 = 0) (hξ1 : |ξ 1| < 1) :
    subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  intro xStar hxStar
  let v : Fin 2 → ℝ := (dotProductEquiv ℝ (Fin 2)).symm xStar
  let a : ℝ := v 0
  have hxval : nonconvexSubdifferentiabilityExampleFunction ξ = (1 : EReal) := by
    have hξabsle : ((|ξ 1| : ℝ) : EReal) ≤ (1 : EReal) := by
      exact (EReal.coe_le_coe_iff).2 (le_of_lt hξ1)
    simp [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap, hξ0,
      max_eq_left hξabsle]
  by_cases ha : 0 ≤ a
  · let r : ℝ := (1 - |ξ 1|) / 2
    have hrpos : 0 < r := by
      have : 0 < 1 - |ξ 1| := by linarith
      dsimp [r]
      positivity
    let z : Fin 2 → ℝ := ξ + Pi.single 0 (r ^ 2)
    have hz0 : 0 ≤ z 0 := by
      simp [z, hξ0, sq_nonneg]
    have hz1 : z 1 = ξ 1 := by
      simp [z]
    have hrlt : r < 1 - |ξ 1| := by
      dsimp [r]
      linarith
    have hmaxLeft : |z 1| < 1 - Real.sqrt (z 0) := by
      have hz0eq : z 0 = r ^ 2 := by simp [z, hξ0]
      have hrnonneg : 0 ≤ r := le_of_lt hrpos
      have hsqrt : Real.sqrt (z 0) = r := by
        rw [hz0eq, Real.sqrt_sq_eq_abs, abs_of_nonneg hrnonneg]
      rw [hz1, hsqrt]
      linarith
    have hzval :
        nonconvexSubdifferentiabilityExampleFunction z = ((1 - r : ℝ) : EReal) := by
      have hz0eq : z 0 = r ^ 2 := by simp [z, hξ0]
      have hrnonneg : 0 ≤ r := le_of_lt hrpos
      have hsqrt : Real.sqrt (z 0) = r := by
        rw [hz0eq, Real.sqrt_sq_eq_abs, abs_of_nonneg hrnonneg]
      have habsle : ((|z 1| : ℝ) : EReal) ≤ ((1 - r : ℝ) : EReal) := by
        exact (EReal.coe_le_coe_iff).2 (le_of_lt (by simpa [hz1, hsqrt] using hmaxLeft))
      rw [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap, if_pos hz0, hsqrt]
      exact max_eq_left habsle
    have hxineq := hxStar z
    have hlin : xStar (z - ξ) = a * r ^ 2 := by
      calc
        xStar (z - ξ) = dotProduct v (z - ξ) := by
          rw [show xStar = dotProductEquiv ℝ (Fin 2) v by simp [v]]
          rfl
        _ = a * r ^ 2 := by
          simp [a, v, z, hξ0, dotProduct, Fin.sum_univ_two]
    have hxineqR : 1 + a * r ^ 2 ≤ 1 - r := by
      have hxineqE : ((1 - r : ℝ) : EReal) ≥ (1 : EReal) + ((a * r ^ 2 : ℝ) : EReal) := by
        simpa [hxval, hzval, hlin] using hxineq
      have : ((1 : ℝ) : EReal) + ((a * r ^ 2 : ℝ) : EReal) ≤ ((1 - r : ℝ) : EReal) := hxineqE
      have : (((1 + a * r ^ 2 : ℝ)) : EReal) ≤ ((1 - r : ℝ) : EReal) := by
        simpa [EReal.coe_add] using this
      exact (EReal.coe_le_coe_iff).1 this
    have har_nonneg : 0 ≤ a * r ^ 2 := mul_nonneg ha (sq_nonneg r)
    have : ¬ (1 + a * r ^ 2 ≤ 1 - r) := by
      have : 1 < 1 + a * r ^ 2 := by linarith
      linarith
    exact this hxineqR
  · have hlt : a < 0 := lt_of_not_ge ha
    let r : ℝ := min ((1 - |ξ 1|) / 2) ((-a)⁻¹ / 2)
    have hrpos1 : 0 < (1 - |ξ 1|) / 2 := by
      have : 0 < 1 - |ξ 1| := by linarith
      positivity
    have hrpos2 : 0 < (-a)⁻¹ / 2 := by
      have hapos : 0 < -a := by linarith
      positivity
    have hrpos : 0 < r := lt_min hrpos1 hrpos2
    let z : Fin 2 → ℝ := ξ + Pi.single 0 (r ^ 2)
    have hz0 : 0 ≤ z 0 := by
      simp [z, hξ0, sq_nonneg]
    have hz1 : z 1 = ξ 1 := by
      simp [z]
    have hrlt : r < 1 - |ξ 1| := by
      dsimp [r]
      have : r ≤ (1 - |ξ 1|) / 2 := min_le_left _ _
      linarith
    have hmaxLeft : |z 1| < 1 - Real.sqrt (z 0) := by
      have hz0eq : z 0 = r ^ 2 := by simp [z, hξ0]
      have hrnonneg : 0 ≤ r := le_of_lt hrpos
      have hsqrt : Real.sqrt (z 0) = r := by
        rw [hz0eq, Real.sqrt_sq_eq_abs, abs_of_nonneg hrnonneg]
      rw [hz1, hsqrt]
      linarith
    have hzval :
        nonconvexSubdifferentiabilityExampleFunction z = ((1 - r : ℝ) : EReal) := by
      have hz0eq : z 0 = r ^ 2 := by simp [z, hξ0]
      have hrnonneg : 0 ≤ r := le_of_lt hrpos
      have hsqrt : Real.sqrt (z 0) = r := by
        rw [hz0eq, Real.sqrt_sq_eq_abs, abs_of_nonneg hrnonneg]
      have habsle : ((|z 1| : ℝ) : EReal) ≤ ((1 - r : ℝ) : EReal) := by
        exact (EReal.coe_le_coe_iff).2 (le_of_lt (by simpa [hz1, hsqrt] using hmaxLeft))
      rw [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap, if_pos hz0, hsqrt]
      exact max_eq_left habsle
    have hxineq := hxStar z
    have hlin :
        xStar (z - ξ) = a * r ^ 2 := by
      calc
        xStar (z - ξ) = dotProduct v (z - ξ) := by
          rw [show xStar = dotProductEquiv ℝ (Fin 2) v by simp [v]]
          rfl
        _ = a * r ^ 2 := by
              simp [a, v, z, hξ0, dotProduct, Fin.sum_univ_two]
    have hrltInv : r < (-a)⁻¹ := by
      have : r ≤ (-a)⁻¹ / 2 := min_le_right _ _
      linarith [hrpos2]
    have hcontra : ¬ (a * r ^ 2 ≤ -r) := by
      have hapos : 0 < -a := by linarith
      have hmul : (-a) * r < 1 := by
        have hmul' := mul_lt_mul_of_pos_left hrltInv hapos
        have hane : (-a : ℝ) ≠ 0 := by linarith
        calc
          (-a) * r < (-a) * ((-a)⁻¹) := by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
          _ = 1 := by simpa using mul_inv_cancel₀ hane
      nlinarith [hrpos, hmul]
    have hxineqR : a * r ^ 2 ≤ -r := by
      have hxineqE : ((1 - r : ℝ) : EReal) ≥ (1 : EReal) + ((a * r ^ 2 : ℝ) : EReal) := by
        simpa [hxval, hzval, hlin] using hxineq
      have : ((1 : ℝ) : EReal) + ((a * r ^ 2 : ℝ) : EReal) ≤ ((1 - r : ℝ) : EReal) := hxineqE
      have : (((1 + a * r ^ 2 : ℝ)) : EReal) ≤ ((1 - r : ℝ) : EReal) := by
        simpa [EReal.coe_add] using this
      have hreal : 1 + a * r ^ 2 ≤ 1 - r := (EReal.coe_le_coe_iff).1 this
      linarith
    exact hcontra hxineqR

/-- Boundary points `(0,t)` with `t ≥ 1` admit the upward vertical subgradient. -/
lemma helperForExample_23_4_2_subgradient_of_boundary_ge_one
    {ξ : Fin 2 → ℝ} (hξ0 : ξ 0 = 0) (hξ1 : 1 ≤ ξ 1) :
    dotProductEquiv ℝ (Fin 2) (Pi.single 1 (1 : ℝ)) ∈
      subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ := by
  intro z
  have hξ1nonneg : 0 ≤ ξ 1 := le_trans (by norm_num) hξ1
  have hξval : nonconvexSubdifferentiabilityExampleFunction ξ = ((ξ 1 : ℝ) : EReal) := by
    calc
      nonconvexSubdifferentiabilityExampleFunction ξ
          = max ((1 : ℝ) : EReal) ((ξ 1 : ℝ) : EReal) := by
              simp [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap, hξ0,
                abs_of_nonneg hξ1nonneg]
      _ = ((ξ 1 : ℝ) : EReal) := by
          rw [max_eq_right]
          exact_mod_cast hξ1
  have hzabs : ((z 1 : ℝ) : EReal) ≤ (((|z 1| : ℝ)) : EReal) := by
    exact_mod_cast le_abs_self (z 1)
  have hdot :
      ((dotProductEquiv ℝ (Fin 2) (Pi.single 1 (1 : ℝ))) (z - ξ) : ℝ) = z 1 - ξ 1 := by
    simp [dotProductEquiv_apply_apply, dotProduct, Fin.sum_univ_two]
  calc
    nonconvexSubdifferentiabilityExampleFunction z
        ≥ (((|z 1| : ℝ)) : EReal) := le_max_right _ _
    _ ≥ ((z 1 : ℝ) : EReal) := hzabs
    _ = nonconvexSubdifferentiabilityExampleFunction ξ +
          (((dotProductEquiv ℝ (Fin 2) (Pi.single 1 (1 : ℝ))) (z - ξ) : ℝ) : EReal) := by
          calc
            ((z 1 : ℝ) : EReal) = (((ξ 1 + (z 1 - ξ 1) : ℝ)) : EReal) := by
              exact congrArg (fun r : ℝ => (r : EReal)) (by ring : z 1 = ξ 1 + (z 1 - ξ 1))
            _ = ((ξ 1 : ℝ) : EReal) + (((z 1 - ξ 1 : ℝ)) : EReal) := by
              rw [EReal.coe_add]
            _ = nonconvexSubdifferentiabilityExampleFunction ξ +
                  (((dotProductEquiv ℝ (Fin 2) (Pi.single 1 (1 : ℝ))) (z - ξ) : ℝ) : EReal) := by
              rw [hξval, hdot]

/-- Boundary points `(0,t)` with `t ≤ -1` admit the downward vertical subgradient. -/
lemma helperForExample_23_4_2_subgradient_of_boundary_le_neg_one
    {ξ : Fin 2 → ℝ} (hξ0 : ξ 0 = 0) (hξ1 : ξ 1 ≤ -1) :
    dotProductEquiv ℝ (Fin 2) (Pi.single 1 (-1 : ℝ)) ∈
      subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ := by
  intro z
  have hξ1nonpos : ξ 1 ≤ 0 := by linarith
  have hξval : nonconvexSubdifferentiabilityExampleFunction ξ = ((-ξ 1 : ℝ) : EReal) := by
    calc
      nonconvexSubdifferentiabilityExampleFunction ξ
          = max ((1 : ℝ) : EReal) ((-ξ 1 : ℝ) : EReal) := by
              simp [nonconvexSubdifferentiabilityExampleFunction, rightHalfLineSquareRootGap, hξ0,
                abs_of_nonpos hξ1nonpos]
      _ = ((-ξ 1 : ℝ) : EReal) := by
          rw [max_eq_right]
          exact_mod_cast (show 1 ≤ -ξ 1 by linarith)
  have hzabs : ((-z 1 : ℝ) : EReal) ≤ (((|z 1| : ℝ)) : EReal) := by
    exact_mod_cast neg_le_abs (z 1)
  have hdot :
      ((dotProductEquiv ℝ (Fin 2) (Pi.single 1 (-1 : ℝ))) (z - ξ) : ℝ) = ξ 1 - z 1 := by
    simp [dotProductEquiv_apply_apply, dotProduct, Fin.sum_univ_two]
  calc
    nonconvexSubdifferentiabilityExampleFunction z
        ≥ (((|z 1| : ℝ)) : EReal) := le_max_right _ _
    _ ≥ ((-z 1 : ℝ) : EReal) := hzabs
    _ = nonconvexSubdifferentiabilityExampleFunction ξ +
          (((dotProductEquiv ℝ (Fin 2) (Pi.single 1 (-1 : ℝ))) (z - ξ) : ℝ) : EReal) := by
          calc
            ((-z 1 : ℝ) : EReal) = (((-ξ 1 + (ξ 1 - z 1) : ℝ)) : EReal) := by
              exact congrArg (fun r : ℝ => (r : EReal)) (by ring : -z 1 = -ξ 1 + (ξ 1 - z 1))
            _ = ((-ξ 1 : ℝ) : EReal) + (((ξ 1 - z 1 : ℝ)) : EReal) := by
              rw [EReal.coe_add]
            _ = nonconvexSubdifferentiabilityExampleFunction ξ +
                  (((dotProductEquiv ℝ (Fin 2) (Pi.single 1 (-1 : ℝ))) (z - ξ) : ℝ) : EReal) := by
              rw [hξval, hdot]

/-- Example 23.4.2 (Nonconvexity of Subdifferentiability Set): For the function
`f(ξ₁, ξ₂) = max {g(ξ₁), |ξ₂|}` with `g(ξ₁) = 1 - √ξ₁` for `ξ₁ ≥ 0` and `g(ξ₁) = +∞` for
`ξ₁ < 0`, the effective domain is the closed right half-plane, the set of points where `f` is
subdifferentiable is the closed right half-plane with the open vertical segment
`{(0, t) | |t| < 1}` removed, and hence this subdifferentiability set is not convex. -/
theorem subdifferentiableSet_nonconvex_for_halfPlaneSquareRootMaxExample :
    ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ)) nonconvexSubdifferentiabilityExampleFunction ∧
      effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) nonconvexSubdifferentiabilityExampleFunction =
        closedRightHalfPlane ∧
      {ξ | Set.Nonempty (subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ)} =
        closedRightHalfPlane \ openVerticalUnitSegment ∧
      ¬ Convex ℝ {ξ | Set.Nonempty (subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ)} := by
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
        nonconvexSubdifferentiabilityExampleFunction :=
    helperForExample_23_4_2_properConvex
  have hdom :
      effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) nonconvexSubdifferentiabilityExampleFunction =
        closedRightHalfPlane :=
    helperForExample_23_4_2_effectiveDomain
  have hsub :
      {ξ | Set.Nonempty (subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ)} =
        closedRightHalfPlane \ openVerticalUnitSegment := by
    ext ξ
    constructor
    · intro hξ
      refine ⟨?_, ?_⟩
      · by_contra hnot
        have hOff :
            subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ = ∅ :=
          (subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
            nonconvexSubdifferentiabilityExampleFunction hproper ξ).1 (by simpa [hdom] using hnot)
        exact hξ.ne_empty hOff
      · by_contra hopen
        rcases hopen with ⟨hξ0, hξ1⟩
        have hempty :=
          helperForExample_23_4_2_subdifferential_empty_on_openVerticalUnitSegment hξ0 hξ1
        exact hξ.ne_empty hempty
    · rintro ⟨hξHalf, hξNotSeg⟩
      by_cases hpos : 0 < ξ 0
      · have hξInt :
            ξ ∈ interior
              (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
                nonconvexSubdifferentiabilityExampleFunction) := by
          simpa [hdom] using helperForExample_23_4_2_mem_interior_closedRightHalfPlane hpos
        exact
          (subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
            nonconvexSubdifferentiabilityExampleFunction hproper ξ).2.2.1.2 hξInt |>.1
      · have hξ0le : 0 ≤ ξ 0 := by simpa [closedRightHalfPlane] using hξHalf
        have hξ0 : ξ 0 = 0 := le_antisymm (le_of_not_gt hpos) hξ0le
        have habsge : 1 ≤ |ξ 1| := by
          by_contra hlt
          exact hξNotSeg ⟨hξ0, lt_of_not_ge hlt⟩
        by_cases hξ1nonneg : 0 ≤ ξ 1
        · have hξ1ge : 1 ≤ ξ 1 := by
            simpa [abs_of_nonneg hξ1nonneg] using habsge
          refine ⟨dotProductEquiv ℝ (Fin 2) (Pi.single 1 (1 : ℝ)),
            helperForExample_23_4_2_subgradient_of_boundary_ge_one hξ0 hξ1ge⟩
        · have hξ1le : ξ 1 ≤ -1 := by
            have hlt0 : ξ 1 < 0 := lt_of_not_ge hξ1nonneg
            have : 1 ≤ -ξ 1 := by simpa [abs_of_neg hlt0] using habsge
            linarith
          refine ⟨dotProductEquiv ℝ (Fin 2) (Pi.single 1 (-1 : ℝ)),
            helperForExample_23_4_2_subgradient_of_boundary_le_neg_one hξ0 hξ1le⟩
  have hnonconvex :
      ¬ Convex ℝ {ξ | Set.Nonempty (subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ)} := by
    intro hconv
    let p : Fin 2 → ℝ := Pi.single 1 (1 : ℝ)
    let q : Fin 2 → ℝ := Pi.single 1 (-1 : ℝ)
    let m : Fin 2 → ℝ := 0
    have hp :
        p ∈ {ξ | Set.Nonempty (subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ)} := by
      rw [hsub]
      refine ⟨by simp [closedRightHalfPlane, p], ?_⟩
      simp [openVerticalUnitSegment, p]
    have hq :
        q ∈ {ξ | Set.Nonempty (subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ)} := by
      rw [hsub]
      refine ⟨by simp [closedRightHalfPlane, q], ?_⟩
      simp [openVerticalUnitSegment, q]
    have hm :
        m ∈ {ξ | Set.Nonempty (subdifferentialAt nonconvexSubdifferentiabilityExampleFunction ξ)} := by
      have hmid :=
        hconv hp hq (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
          (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
      have hpq : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q = m := by
        ext i
        fin_cases i <;> simp [p, q, m]
      rw [hpq] at hmid
      exact hmid
    rw [hsub] at hm
    exact hm.2 (by simp [openVerticalUnitSegment, m])
  exact ⟨hproper, hdom, hsub, hnonconvex⟩

/-- Qualification by an intersection of the range of `A` with the relative interior of the
effective domain of `h`. -/
def RangeMeetsRelativeInteriorEffectiveDomain {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (h : (Fin m → ℝ) → EReal) : Prop :=
  ∃ z : Fin m → ℝ,
    z ∈ Set.range A ∧ z ∈ euclideanRelativeInterior_fin m (effectiveDomain Set.univ h)

/-- Qualification by a singleton intersection of the range of `A` with the effective domain of
`h`. -/
def RangeMeetsEffectiveDomainInOnePoint {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (h : (Fin m → ℝ) → EReal) : Prop :=
  ∃ z : Fin m → ℝ,
    Set.range A ∩ effectiveDomain Set.univ h = {z}

/-- A dual vector `xStar` decomposes at `x` as a sum of subgradients of `f₁, …, fₘ` when there is
a family `parts i ∈ ∂ fᵢ(x)` whose sum is `xStar`. -/
def IsSubdifferentialSumDecompositionAt {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (xStar : Module.Dual ℝ (Fin n → ℝ)) : Prop :=
  ∃ parts : Fin m → Module.Dual ℝ (Fin n → ℝ),
    (∀ i : Fin m, parts i ∈ subdifferentialAt (f i) x) ∧ xStar = ∑ i, parts i

/-- The qualification condition for the subdifferential sum rule: either all relative interiors of
the effective domains meet, or a distinguished polyhedral subfamily has a common point in its
effective domains while the remaining summands still meet in relative interior. -/
def SubdifferentialSumQualification {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m)) : Prop :=
  (∃ z : Fin n → ℝ, ∀ i : Fin m, z ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (f i))) ∨
  ∃ z : Fin n → ℝ, (∀ i ∈ Ipoly, z ∈ effectiveDomain Set.univ (f i)) ∧
    ∀ i ∉ Ipoly, z ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (f i))

/-- Helper for Theorem 23.8: evaluating the sum of a family of dual vectors on `z - x` is the same
as summing the individual evaluations. -/
lemma helperForTheorem_23_8_sum_dual_apply_sub_eq_ereal_sum {m n : ℕ}
    (parts : Fin m → Module.Dual ℝ (Fin n → ℝ)) (x z : Fin n → ℝ) :
    ∑ i, ((((parts i) (z - x) : ℝ) : EReal)) =
      ((((∑ i, parts i) (z - x) : ℝ) : EReal)) := by
  -- Rewrite the common argument `z - x` using linearity, then collapse the finite real sum.
  calc
    ∑ i, ((((parts i) (z - x) : ℝ) : EReal))
        = ∑ i, ((((parts i) z - (parts i) x : ℝ) : EReal)) := by
            simp [LinearMap.map_sub]
    _ = (((∑ i, ((parts i) z - (parts i) x)) : ℝ) : EReal) := by
          symm
          exact section16_coe_finset_sum (s := Finset.univ)
            (b := fun i : Fin m => (parts i) z - (parts i) x)
    _ = ((((∑ i, parts i) z - (∑ i, parts i) x : ℝ) : EReal)) := by
          simp [Finset.sum_sub_distrib]
    _ = ((((∑ i, parts i) (z - x) : ℝ) : EReal)) := by
          simp [LinearMap.map_sub]

/-- Helper for Theorem 23.8: every explicit decomposition of `xStar` into summand subgradients
produces a subgradient of the pointwise sum. -/
lemma helperForTheorem_23_8_subgradient_of_sum_of_decomposition {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    IsSubdifferentialSumDecompositionAt f x xStar →
      xStar ∈ subdifferentialAt (fun y => ∑ i, f i y) x := by
  rintro ⟨parts, hparts, rfl⟩
  intro z
  -- Sum the componentwise subgradient inequalities at the common test point `z`.
  have hsum :
      ∑ i, (f i x + (((parts i) (z - x) : ℝ) : EReal)) ≤ ∑ i, f i z := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hparts i z
  -- Reassemble the linear term into the dual sum that appears in the target subgradient.
  calc
    (∑ i, f i z) ≥ ∑ i, (f i x + (((parts i) (z - x) : ℝ) : EReal)) := hsum
    _ = (∑ i, f i x) + ∑ i, ((((parts i) (z - x) : ℝ) : EReal)) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i, f i x) + ((((∑ i, parts i) (z - x) : ℝ) : EReal)) := by
      rw [helperForTheorem_23_8_sum_dual_apply_sub_eq_ereal_sum]

/-- Theorem 23.8(1), inclusion direction in notation form:
every finite sum of summand subgradients belongs to the subdifferential of the summed function. -/
lemma subgradient_sum_mem_subdifferential_sum {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (parts : Fin m → Module.Dual ℝ (Fin n → ℝ))
    (hparts : ∀ i : Fin m, parts i ∈ ∂ (f i) (x)) :
    (∑ i, parts i) ∈ ∂ (fun y => ∑ i, f i y) (x) := by
  exact
    helperForTheorem_23_8_subgradient_of_sum_of_decomposition
      f x (∑ i, parts i) ⟨parts, hparts, rfl⟩

/-- Theorem 23.8(1), inclusion direction in set form:
the Minkowski sum of the summand subdifferentials is contained in the subdifferential of the summed
function. -/
lemma subdifferential_sum_subset_subdifferential_sum {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    (∑ i, (∂ (f i) (x) : Set (Module.Dual ℝ (Fin n → ℝ)))) ⊆
      ∂ (fun y => ∑ i, f i y) (x) := by
  classical
  intro xStar hxStar
  rcases
      (Set.mem_fintype_sum
        (f := fun i : Fin m => (∂ (f i) (x) : Set (Module.Dual ℝ (Fin n → ℝ))))
        (a := xStar)).1 hxStar with
    ⟨parts, hparts, hsum⟩
  have hmem : (∑ i, parts i) ∈ ∂ (fun y => ∑ i, f i y) (x) :=
    subgradient_sum_mem_subdifferential_sum f x parts hparts
  simpa [hsum] using hmem

/-- Helper for Theorem 23.8: the qualification hypothesis supplies a point where the full sum is
finite, so the summed function is again proper convex. -/
lemma helperForTheorem_23_8_sum_proper_of_qualification {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn Set.univ (f i)) (Ipoly : Set (Fin m))
    (hqual : SubdifferentialSumQualification f Ipoly) :
    ProperConvexFunctionOn Set.univ (fun y => ∑ i, f i y) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  -- Extract a witness where every summand is finite, then invoke the finite-sum properness lemma.
  refine properConvexFunctionOn_sum_of_exists_ne_top (f := f) hproper ?_
  rcases hqual with hriAll | hmixed
  · rcases hriAll with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hzTerm :
        ∀ i : Fin m, f i z ≠ (⊤ : EReal) := by
      intro i
      have hzDom :
          z ∈ effectiveDomain Set.univ (f i) := by
        have hzriE :
            e.symm z ∈
              euclideanRelativeInterior n (e.symm '' effectiveDomain Set.univ (f i)) :=
          (mem_euclideanRelativeInterior_fin_iff
            (n := n) (C := effectiveDomain Set.univ (f i)) (x := z)).1 (hz i)
        have hzImg :
            e.symm z ∈ e.symm '' effectiveDomain Set.univ (f i) :=
          (euclideanRelativeInterior_subset_closure n (e.symm '' effectiveDomain Set.univ (f i))).1
            hzriE
        rcases hzImg with ⟨w, hw, hwEq⟩
        have hwz : w = z := by
          simpa [e] using congrArg e hwEq
        simpa [hwz] using hw
      exact mem_effectiveDomain_imp_ne_top (S := Set.univ) (f := f i) hzDom
    refine finset_sum_ne_top_of_forall (s := Finset.univ) (f := fun i : Fin m => f i z) ?_
    intro i hi
    exact hzTerm i
  · rcases hmixed with ⟨z, hzPoly, hzRest⟩
    refine ⟨z, ?_⟩
    have hzTerm :
        ∀ i : Fin m, f i z ≠ (⊤ : EReal) := by
      intro i
      by_cases hi : i ∈ Ipoly
      · exact mem_effectiveDomain_imp_ne_top (S := Set.univ) (f := f i) (hzPoly i hi)
      · have hzDom :
            z ∈ effectiveDomain Set.univ (f i) := by
          have hzriE :
              e.symm z ∈
                euclideanRelativeInterior n (e.symm '' effectiveDomain Set.univ (f i)) :=
            (mem_euclideanRelativeInterior_fin_iff
              (n := n) (C := effectiveDomain Set.univ (f i)) (x := z)).1 (hzRest i hi)
          have hzImg :
              e.symm z ∈ e.symm '' effectiveDomain Set.univ (f i) :=
            (euclideanRelativeInterior_subset_closure n
              (e.symm '' effectiveDomain Set.univ (f i))).1 hzriE
          rcases hzImg with ⟨w, hw, hwEq⟩
          have hwz : w = z := by
            simpa [e] using congrArg e hwEq
          simpa [hwz] using hw
        exact mem_effectiveDomain_imp_ne_top (S := Set.univ) (f := f i) hzDom
    refine finset_sum_ne_top_of_forall (s := Finset.univ) (f := fun i : Fin m => f i z) ?_
    intro i hi
    exact hzTerm i

/-- Helper for Theorem 23.8: a subgradient of the full sum yields the corresponding
Fenchel-Young equality for that full sum. -/
lemma helperForTheorem_23_8_fullFenchelYoung_of_sumSubgradient {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hsumProper : ProperConvexFunctionOn Set.univ (fun y => ∑ i, f i y))
    (x : Fin n → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ))
    (hxStar : xStar ∈ subdifferentialAt (fun y => ∑ i, f i y) x) :
    FenchelYoungEqualityAt (fun y => ∑ i, f i y) x ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
  -- Rewrite the dual witness through `dotProductEquiv`, then read off condition `(d)` from
  -- Theorem 23.5.
  have hxStarE :
      IsEuclideanSubgradientAt (fun y => ∑ i, f i y) x ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
    change
      dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm xStar) ∈
        subdifferentialAt (fun y => ∑ i, f i y) x
    simpa using hxStar
  exact
    ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
      (fun y => ∑ i, f i y) hsumProper x ((dotProductEquiv ℝ (Fin n)).symm xStar)).1.out 0 3).1
      hxStarE

/-- Helper for Theorem 23.8: once each Euclidean summand satisfies Fenchel-Young equality and the
summands add up to `xStar`, the corresponding dual vectors give the required decomposition. -/
lemma helperForTheorem_23_8_dualDecomposition_of_summandFenchelYoung {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn Set.univ (f i))
    (x : Fin n → ℝ) (xStar : Fin n → ℝ) (parts : Fin m → Fin n → ℝ)
    (hsum : ∑ i, parts i = xStar)
    (hfy : ∀ i : Fin m, FenchelYoungEqualityAt (f i) x (parts i)) :
    IsSubdifferentialSumDecompositionAt f x (dotProductEquiv ℝ (Fin n) xStar) := by
  -- Convert each Fenchel-Young equality back to a Euclidean subgradient, then package the dual
  -- witnesses and collapse their sum through linearity of `dotProductEquiv`.
  refine ⟨fun i => dotProductEquiv ℝ (Fin n) (parts i), ?_, ?_⟩
  · intro i
    have hsubE :
        IsEuclideanSubgradientAt (f i) x (parts i) :=
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        (f i) (hproper i) x (parts i)).1.out 3 0).1 (hfy i)
    simpa [IsEuclideanSubgradientAt] using hsubE
  · -- Route correction: linearity of `dotProductEquiv` collapses the family sum back to the
    -- dual vector corresponding to `xStar`.
    calc
      dotProductEquiv ℝ (Fin n) xStar = dotProductEquiv ℝ (Fin n) (∑ i, parts i) := by
        exact by simp [hsum]
      _ = ∑ i, dotProductEquiv ℝ (Fin n) (parts i) := by
            exact by
              simpa using
                (LinearMap.map_sum (dotProductEquiv ℝ (Fin n)).toLinearMap
                  (fun i : Fin m => parts i))

/-- Helper for Theorem 23.8: a full Fenchel-Young equality for the summed function forces the
full conjugate value to be finite. -/
lemma helperForTheorem_23_8_fullConjugate_ne_top_of_fullFenchelYoung {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hsumProper : ProperConvexFunctionOn Set.univ (fun y => ∑ i, f i y))
    (x xStarE : Fin n → ℝ)
    (hfullFY : FenchelYoungEqualityAt (fun y => ∑ i, f i y) x xStarE) :
    fenchelConjugate n (fun y => ∑ i, f i y) xStarE ≠ (⊤ : EReal) := by
  -- Read the equality first as a weak Fenchel-Young inequality to recover finiteness of the
  -- primal sum at `x`.
  have hsumFinite :=
    helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality
      (f := fun y => ∑ i, f i y) hsumProper x xStarE (le_of_eq hfullFY)
  intro htop
  -- A finite right-hand side cannot equal a left-hand side containing `⊤`.
  rw [FenchelYoungEqualityAt] at hfullFY
  have hleft_top :
      (fun y => ∑ i, f i y) x + fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
        (⊤ : EReal) := by
    simpa [htop] using (EReal.add_top_of_ne_bot hsumFinite.2)
  exact EReal.coe_ne_top (dotProduct x xStarE) (hfullFY.symm.trans hleft_top)

/-- Helper for Theorem 23.8: an all-relative-interior qualification gives an attained
Fenchel-conjugate split for the full family. -/
lemma helperForTheorem_23_8_attainedFenchelSplit_of_allRiQualification {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hmPos : 0 < m)
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn Set.univ (f i))
    (hsumProper : ProperConvexFunctionOn Set.univ (fun y => ∑ i, f i y))
    (x xStarE : Fin n → ℝ)
    (hallri : ∃ z : Fin n → ℝ,
      ∀ i : Fin m, z ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (f i)))
    (hfullFY : FenchelYoungEqualityAt (fun y => ∑ i, f i y) x xStarE) :
    ∃ parts : Fin m → Fin n → ℝ,
      (∑ i, parts i) = xStarE ∧
        fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
          ∑ i, fenchelConjugate n (f i) (parts i) := by
  rcases hallri with ⟨z, hz⟩
  -- Transport the `Fin n → ℝ` witness into the Euclidean-space relative-interior statement used
  -- by Section 16.
  have hri :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun y : EuclideanSpace ℝ (Fin n) => (y : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
    refine ⟨(EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm z, Set.mem_iInter.2 ?_⟩
    intro i
    have hz' :
        (EuclideanSpace.equiv (Fin n) ℝ).symm z ∈
          euclideanRelativeInterior n
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' effectiveDomain Set.univ (f i)) :=
      (mem_euclideanRelativeInterior_fin_iff
        (n := n) (C := effectiveDomain Set.univ (f i)) (x := z)).1 (hz i)
    simpa [helperForTheorem_23_4_preimage_eq_symmImage
      (C := effectiveDomain Set.univ (f i))] using hz'
  have hsec16 :=
    section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
      (f := f) hproper hri
  have hconj_ne_top :
      fenchelConjugate n (fun y => ∑ i, f i y) xStarE ≠ (⊤ : EReal) :=
    helperForTheorem_23_8_fullConjugate_ne_top_of_fullFenchelYoung
      f hsumProper x xStarE hfullFY
  have hEqAt :
      fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStarE := by
    simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g xStarE) hsec16.1
  -- The finite full Fenchel-Young equality rules out the `= ⊤` alternative in Section 16.
  rcases hsec16.2 xStarE with htop | ⟨parts, hsum, hval⟩
  · exact False.elim (hconj_ne_top (hEqAt.trans htop))
  · exact ⟨parts, hsum, hEqAt.trans hval.symm⟩

/-- Helper for Theorem 23.8: the polyhedral filtered block over `Ipoly` attains its conjugate
value by a decomposition over the corresponding subtype. -/
lemma helperForTheorem_23_8_polyFilter_conjugate_attained_by_subtypeFamily {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hIpolyNonempty : Ipoly ≠ ∅)
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn Set.univ (f i))
    (hdomPoly : ∃ z : Fin n → ℝ,
      ∀ i : Fin m, i ∈ Ipoly → z ∈ effectiveDomain Set.univ (f i))
    (xHead : Fin n → ℝ) :
    ∃ headFamily : {i : Fin m // i ∈ Ipoly} → Fin n → ℝ,
      (∑ i, headFamily i) = xHead ∧
        fenchelConjugate n
            (fun y => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i y) xHead =
          ∑ i : {i : Fin m // i ∈ Ipoly}, fenchelConjugate n (f i.1) (headFamily i) := by
  classical
  let J : Type := {i : Fin m // i ∈ Ipoly}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let k : ℕ := Fintype.card J
  let eJ : J ≃ Fin k := Fintype.equivFin J
  let fFin : Fin k → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  -- Reindex the filtered block by a contiguous finite type and invoke the polyhedral attainment
  -- theorem there.
  have hpolyFin : ∀ i : Fin k, IsPolyhedralConvexFunction n (fFin i) := by
    intro i
    simpa [fFin, fJ] using (hpoly (eJ.symm i).1).1 (eJ.symm i).2
  have hproperFin :
      ∀ i : Fin k, ProperConvexFunctionOn Set.univ (fFin i) := by
    intro i
    simpa [fFin, fJ] using hproper (eJ.symm i).1
  have hdomFin :
      Set.Nonempty (⋂ i : Fin k, effectiveDomain Set.univ (fFin i)) := by
    rcases hdomPoly with ⟨z, hz⟩
    refine ⟨z, Set.mem_iInter.2 ?_⟩
    intro i
    simpa [fFin, fJ] using hz (eJ.symm i).1 (eJ.symm i).2
  have hkPos : 0 < k := by
    rcases Set.nonempty_iff_ne_empty.mpr hIpolyNonempty with ⟨i0, hi0⟩
    simpa [k] using (Fintype.card_pos_iff.mpr ⟨⟨i0, hi0⟩⟩)
  have hpolyAtt :=
    polyhedral_refinement_fenchelConjugate_sum_eq_infimalConvolutionFamily_and_attainment
      (f := fFin) hpolyFin hproperFin hdomFin hkPos
  rcases hpolyAtt.2 xHead with ⟨headFinFamily, hsumFin, hvalFin⟩
  let headFamily : J → Fin n → ℝ := fun j => headFinFamily (eJ j)
  have hsumJ : (∑ j : J, headFamily j) = xHead := by
    calc
      (∑ j : J, headFamily j) = ∑ i : Fin k, headFamily (eJ.symm i) := by
        simpa [headFamily] using
          (Fintype.sum_equiv eJ
            (fun j : J => headFamily j)
            (fun i : Fin k => headFamily (eJ.symm i))
            (by intro j; simp [headFamily]))
      _ = ∑ i : Fin k, headFinFamily i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [headFamily]
      _ = xHead := hsumFin
  have hsumConjJ :
      (∑ j : J, fenchelConjugate n (f j.1) (headFamily j)) =
        ∑ i : Fin k, fenchelConjugate n (fFin i) (headFinFamily i) := by
    calc
      (∑ j : J, fenchelConjugate n (f j.1) (headFamily j)) =
          ∑ i : Fin k, fenchelConjugate n (f (eJ.symm i).1) (headFamily (eJ.symm i)) := by
            simpa using
              (Fintype.sum_equiv eJ
                (fun j : J => fenchelConjugate n (f j.1) (headFamily j))
                (fun i : Fin k =>
                  fenchelConjugate n (f (eJ.symm i).1) (headFamily (eJ.symm i)))
                (by intro j; simp))
      _ = ∑ i : Fin k, fenchelConjugate n (fFin i) (headFinFamily i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [fFin, fJ, headFamily]
  have hsumFinToJ :
      (fun y => ∑ i : Fin k, fFin i y) = (fun y => ∑ j : J, fJ j y) := by
    funext y
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => fJ j y)
        (fun i : Fin k => fJ (eJ.symm i) y)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hsumJToFilter :
      (fun y => ∑ j : J, fJ j y) =
        (fun y => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i y) := by
    funext y
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∈ Ipoly)
        (f := fun i : Fin m => f i y))
  have hsumFinToFilter :
      (fun y => ∑ i : Fin k, fFin i y) =
        (fun y => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i y) :=
    hsumFinToJ.trans hsumJToFilter
  have hconjFin :
      fenchelConjugate n (fun y => ∑ i : Fin k, fFin i y) xHead =
        ∑ i : Fin k, fenchelConjugate n (fFin i) (headFinFamily i) := by
    calc
      fenchelConjugate n (fun y => ∑ i : Fin k, fFin i y) xHead =
          infimalConvolutionFamily (fun i : Fin k => fenchelConjugate n (fFin i)) xHead := by
            simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g xHead) hpolyAtt.1
      _ = ∑ i : Fin k, fenchelConjugate n (fFin i) (headFinFamily i) := hvalFin
  refine ⟨headFamily, hsumJ, ?_⟩
  calc
    fenchelConjugate n
        (fun y => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i y) xHead =
      fenchelConjugate n (fun y => ∑ i : Fin k, fFin i y) xHead := by
        simpa [hsumFinToFilter] using
          congrArg (fun g : (Fin n → ℝ) → EReal => g xHead) hsumFinToFilter.symm
    _ = ∑ i : Fin k, fenchelConjugate n (fFin i) (headFinFamily i) := hconjFin
    _ = ∑ i : J, fenchelConjugate n (f i.1) (headFamily i) := hsumConjJ.symm

/-- Helper for Theorem 23.8: the nonpolyhedral filtered block over `Ipolyᶜ` attains its conjugate
value by a decomposition over the complement subtype, provided that block is nonempty. -/
lemma helperForTheorem_23_8_nonpolyFilter_conjugate_attained_by_subtypeFamily {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hnonpolyNonempty : {i : Fin m | i ∉ Ipoly} ≠ ∅)
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn Set.univ (f i))
    (hriNonpoly : ∃ z : Fin n → ℝ,
      ∀ i : Fin m, i ∉ Ipoly →
        z ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (f i)))
    (xTail : Fin n → ℝ) :
    ∃ tailFamily : {i : Fin m // i ∉ Ipoly} → Fin n → ℝ,
      (∑ i, tailFamily i) = xTail ∧
        fenchelConjugate n
            (fun y => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i y) xTail =
          ∑ i : {i : Fin m // i ∉ Ipoly}, fenchelConjugate n (f i.1) (tailFamily i) := by
  classical
  let J : Type := {i : Fin m // i ∉ Ipoly}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let k : ℕ := Fintype.card J
  let eJ : J ≃ Fin k := Fintype.equivFin J
  let fFin : Fin k → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  -- Reindex the nonpolyhedral block and apply Section 16 together with the standard
  -- top-case attainment when the block cardinality is positive.
  have hproperFin :
      ∀ i : Fin k, ProperConvexFunctionOn Set.univ (fFin i) := by
    intro i
    simpa [fFin, fJ] using hproper (eJ.symm i).1
  have hriFin :
      Set.Nonempty
        (⋂ i : Fin k,
          euclideanRelativeInterior n
            ((fun y : EuclideanSpace ℝ (Fin n) => (y : Fin n → ℝ)) ⁻¹'
              effectiveDomain Set.univ (fFin i))) := by
    rcases hriNonpoly with ⟨z, hz⟩
    refine ⟨(EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm z, Set.mem_iInter.2 ?_⟩
    intro i
    have hz' :
        (EuclideanSpace.equiv (Fin n) ℝ).symm z ∈
          euclideanRelativeInterior n
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' effectiveDomain Set.univ (f (eJ.symm i).1)) :=
      (mem_euclideanRelativeInterior_fin_iff
        (n := n) (C := effectiveDomain Set.univ (f (eJ.symm i).1)) (x := z)).1
        (hz (eJ.symm i).1 (eJ.symm i).2)
    simpa [fFin, fJ, helperForTheorem_23_4_preimage_eq_symmImage
      (C := effectiveDomain Set.univ (f (eJ.symm i).1))] using hz'
  have hkPos : 0 < k := by
    rcases Set.nonempty_iff_ne_empty.mpr hnonpolyNonempty with ⟨i0, hi0⟩
    simpa [k] using (Fintype.card_pos_iff.mpr ⟨⟨i0, hi0⟩⟩)
  have hsec16 :=
    section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
      (f := fFin) hproperFin hriFin
  have htailFinWitness :
      ∃ tailFinFamily : Fin k → Fin n → ℝ,
        (∑ i, tailFinFamily i) = xTail ∧
          (∑ i, fenchelConjugate n (fFin i) (tailFinFamily i)) =
            infimalConvolutionFamily (fun i : Fin k => fenchelConjugate n (fFin i)) xTail := by
    rcases hsec16.2 xTail with htop | hatt
    · exact
        section16_attainment_when_infimalConvolutionFamily_eq_top_of_pos
          (n := n) (m := k) hkPos
          (g := fun i : Fin k => fenchelConjugate n (fFin i))
          (xStar := xTail) htop
    · exact hatt
  rcases htailFinWitness with ⟨tailFinFamily, hsumFin, hvalFin⟩
  let tailFamily : J → Fin n → ℝ := fun j => tailFinFamily (eJ j)
  have hsumJ : (∑ j : J, tailFamily j) = xTail := by
    calc
      (∑ j : J, tailFamily j) = ∑ i : Fin k, tailFamily (eJ.symm i) := by
        simpa [tailFamily] using
          (Fintype.sum_equiv eJ
            (fun j : J => tailFamily j)
            (fun i : Fin k => tailFamily (eJ.symm i))
            (by intro j; simp [tailFamily]))
      _ = ∑ i : Fin k, tailFinFamily i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [tailFamily]
      _ = xTail := hsumFin
  have hsumConjJ :
      (∑ j : J, fenchelConjugate n (f j.1) (tailFamily j)) =
        ∑ i : Fin k, fenchelConjugate n (fFin i) (tailFinFamily i) := by
    calc
      (∑ j : J, fenchelConjugate n (f j.1) (tailFamily j)) =
          ∑ i : Fin k, fenchelConjugate n (f (eJ.symm i).1) (tailFamily (eJ.symm i)) := by
            simpa using
              (Fintype.sum_equiv eJ
                (fun j : J => fenchelConjugate n (f j.1) (tailFamily j))
                (fun i : Fin k =>
                  fenchelConjugate n (f (eJ.symm i).1) (tailFamily (eJ.symm i)))
                (by intro j; simp))
      _ = ∑ i : Fin k, fenchelConjugate n (fFin i) (tailFinFamily i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [fFin, fJ, tailFamily]
  have hsumFinToJ :
      (fun y => ∑ i : Fin k, fFin i y) = (fun y => ∑ j : J, fJ j y) := by
    funext y
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => fJ j y)
        (fun i : Fin k => fJ (eJ.symm i) y)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hsumJToFilter :
      (fun y => ∑ j : J, fJ j y) =
        (fun y => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i y) := by
    funext y
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∉ Ipoly)
        (f := fun i : Fin m => f i y))
  have hsumFinToFilter :
      (fun y => ∑ i : Fin k, fFin i y) =
        (fun y => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i y) :=
    hsumFinToJ.trans hsumJToFilter
  have hconjFin :
      fenchelConjugate n (fun y => ∑ i : Fin k, fFin i y) xTail =
        ∑ i : Fin k, fenchelConjugate n (fFin i) (tailFinFamily i) := by
    rcases hsec16.2 xTail with htop | hatt
    · calc
        fenchelConjugate n (fun y => ∑ i : Fin k, fFin i y) xTail =
            infimalConvolutionFamily (fun i : Fin k => fenchelConjugate n (fFin i)) xTail := by
              simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g xTail) hsec16.1
        _ = ∑ i : Fin k, fenchelConjugate n (fFin i) (tailFinFamily i) := hvalFin.symm
    · calc
        fenchelConjugate n (fun y => ∑ i : Fin k, fFin i y) xTail =
            infimalConvolutionFamily (fun i : Fin k => fenchelConjugate n (fFin i)) xTail := by
              simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g xTail) hsec16.1
        _ = ∑ i : Fin k, fenchelConjugate n (fFin i) (tailFinFamily i) := hvalFin.symm
  refine ⟨tailFamily, hsumJ, ?_⟩
  calc
    fenchelConjugate n
        (fun y => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i y) xTail =
      fenchelConjugate n (fun y => ∑ i : Fin k, fFin i y) xTail := by
        simpa [hsumFinToFilter] using
          congrArg (fun g : (Fin n → ℝ) → EReal => g xTail) hsumFinToFilter.symm
    _ = ∑ i : Fin k, fenchelConjugate n (fFin i) (tailFinFamily i) := hconjFin
    _ = ∑ i : J, fenchelConjugate n (f i.1) (tailFamily i) := hsumConjJ.symm

/-- Helper for Theorem 23.8: summing a piecewise family over `Ipoly` and its complement splits
into the corresponding subtype sums. -/
lemma helperForTheorem_23_8_sum_piecewise_membership
    {m : ℕ} {α : Type*} [AddCommMonoid α]
    (Ipoly : Set (Fin m)) [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (headVal : {i : Fin m // i ∈ Ipoly} → α)
    (tailVal : {i : Fin m // i ∉ Ipoly} → α) :
    (∑ i : Fin m,
        if hi : i ∈ Ipoly then headVal ⟨i, hi⟩ else tailVal ⟨i, hi⟩) =
      (∑ i : {i : Fin m // i ∈ Ipoly}, headVal i) +
      (∑ i : {i : Fin m // i ∉ Ipoly}, tailVal i) := by
  classical
  let splitVal : Fin m → α := fun i =>
    if hi : i ∈ Ipoly then headVal ⟨i, hi⟩ else tailVal ⟨i, hi⟩
  -- Split the full sum into a filtered sum over `Ipoly` and another over its complement.
  have hsplit :
      (∑ i : Fin m, splitVal i) =
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), splitVal i) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), splitVal i) := by
    simpa [splitVal] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∈ Ipoly)
        (f := splitVal)).symm
  have hheadFilter :
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), splitVal i) =
        ∑ i : {i : Fin m // i ∈ Ipoly}, headVal i := by
    calc
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), splitVal i) =
          ∑ i : {i : Fin m // i ∈ Ipoly}, splitVal i.1 := by
            symm
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (Fin m)))
                (p := fun i : Fin m => i ∈ Ipoly)
                (f := splitVal))
      _ = ∑ i : {i : Fin m // i ∈ Ipoly}, headVal i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [splitVal, i.2]
  have htailFilter :
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), splitVal i) =
        ∑ i : {i : Fin m // i ∉ Ipoly}, tailVal i := by
    calc
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), splitVal i) =
          ∑ i : {i : Fin m // i ∉ Ipoly}, splitVal i.1 := by
            symm
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (Fin m)))
                (p := fun i : Fin m => i ∉ Ipoly)
                (f := splitVal))
      _ = ∑ i : {i : Fin m // i ∉ Ipoly}, tailVal i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [splitVal, i.2]
  calc
    (∑ i : Fin m, splitVal i) =
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), splitVal i) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), splitVal i) := hsplit
    _ = (∑ i : {i : Fin m // i ∈ Ipoly}, headVal i) +
        (∑ i : {i : Fin m // i ∉ Ipoly}, tailVal i) := by
          rw [hheadFilter, htailFilter]

/-- Helper for Theorem 23.8: the mixed qualification yields an attained conjugate split after
first separating the polyhedral and nonpolyhedral filtered blocks. -/
lemma helperForTheorem_23_8_attainedFenchelSplit_of_mixedQualification_via_filteredBinaryBridge
    {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hmPos : 0 < m)
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn Set.univ (f i))
    (hsumProper : ProperConvexFunctionOn Set.univ (fun y => ∑ i, f i y))
    (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hmixed : ∃ z : Fin n → ℝ,
      (∀ i ∈ Ipoly, z ∈ effectiveDomain Set.univ (f i)) ∧
        ∀ i ∉ Ipoly, z ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (f i)))
    (x xStarE : Fin n → ℝ)
    (hfullFY : FenchelYoungEqualityAt (fun y => ∑ i, f i y) x xStarE) :
    ∃ parts : Fin m → Fin n → ℝ,
      (∑ i, parts i) = xStarE ∧
        fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
          ∑ i, fenchelConjugate n (f i) (parts i) := by
  classical
  by_cases hIpolyEmpty : Ipoly = ∅
  · rcases hmixed with ⟨z, _hzPoly, hzRest⟩
    -- If `Ipoly = ∅`, the mixed qualification is exactly the all-`ri` qualification.
    have hallri :
        ∃ z : Fin n → ℝ,
          ∀ i : Fin m, z ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (f i)) := by
      refine ⟨z, ?_⟩
      intro i
      exact hzRest i (by simpa [hIpolyEmpty])
    exact
      helperForTheorem_23_8_attainedFenchelSplit_of_allRiQualification
        f hmPos hproper hsumProper x xStarE hallri hfullFY
  by_cases hnonpoly : Set.Nonempty {i : Fin m | i ∉ Ipoly}
  · rcases hmixed with ⟨z, hzPoly, hzRest⟩
    let p : (Fin n → ℝ) → EReal :=
      fun y => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i y
    let q : (Fin n → ℝ) → EReal :=
      fun y => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i y
    -- Translate the textbook mixed witness into the Chapter 20 filtered-block witness.
    have hdom_ri :
        Set.Nonempty
          ((⋂ i : {i : Fin m // i ∈ Ipoly},
              ((fun y : EuclideanSpace ℝ (Fin n) => (y : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
            ∩
            (⋂ i : {i : Fin m // i ∉ Ipoly},
              euclideanRelativeInterior n
                ((fun y : EuclideanSpace ℝ (Fin n) => (y : Fin n → ℝ)) ⁻¹'
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) := by
      refine ⟨(EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm z, ?_⟩
      refine And.intro ?_ ?_
      · refine Set.mem_iInter.2 ?_
        intro i
        simpa [Set.mem_preimage] using hzPoly i.1 i.2
      · refine Set.mem_iInter.2 ?_
        intro i
        have hz' :
            (EuclideanSpace.equiv (Fin n) ℝ).symm z ∈
              euclideanRelativeInterior n
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' effectiveDomain Set.univ (f i.1)) :=
          (mem_euclideanRelativeInterior_fin_iff
            (n := n) (C := effectiveDomain Set.univ (f i.1)) (x := z)).1
            (hzRest i.1 i.2)
        simpa [helperForTheorem_23_4_preimage_eq_symmImage
          (C := effectiveDomain Set.univ (f i.1))] using hz'
    have hconj_ne_top :
        fenchelConjugate n (fun y => ∑ i, f i y) xStarE ≠ (⊤ : EReal) :=
      helperForTheorem_23_8_fullConjugate_ne_top_of_fullFenchelYoung
        f hsumProper x xStarE hfullFY
    have hIpolyNonempty : Ipoly ≠ ∅ := hIpolyEmpty
    have hpolyMem :
        ∀ i : Fin m, i ∈ Ipoly → IsPolyhedralConvexFunction n (f i) := by
      intro i hi
      exact (hpoly i).1 hi
    have hdomPoly :
        ∃ z : Fin n → ℝ,
          ∀ i : Fin m, i ∈ Ipoly → z ∈ effectiveDomain Set.univ (f i) := by
      exact ⟨z, hzPoly⟩
    have hriNonpoly :
        ∃ z : Fin n → ℝ,
          ∀ i : Fin m, i ∉ Ipoly →
            z ∈ euclideanRelativeInterior_fin n (effectiveDomain Set.univ (f i)) := by
      exact ⟨z, hzRest⟩
    have hpolyP :
        IsPolyhedralConvexFunction n p := by
      simpa [p] using
        helperForTheorem_20_1_polyhedral_filteredBlock_of_membership_polyhedral
          (f := f) (Ipoly := Ipoly) hpolyMem hproper
          (hdom := by
            refine ⟨z, Set.mem_iInter.2 ?_⟩
            intro i
            exact hzPoly i.1 i.2)
          hIpolyNonempty
    have hproperP :
        ProperConvexFunctionOn Set.univ p := by
      exact
        (helperForTheorem_20_0_4_poly_filter_block_proper_and_dom_witness
          (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)).1
    have hproperQ :
        ProperConvexFunctionOn Set.univ q := by
      simpa [q] using
        helperForTheorem_20_0_4_nonpoly_filter_block_proper
          (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
    have hdomRiWitnessBlock :
        ∃ x0 : Fin n → ℝ,
          x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p ∧
            (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
              euclideanRelativeInterior n
                ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
      simpa [p, q] using
        helperForTheorem_20_0_4_exists_dom_poly_and_ri_nonpoly_filtered_sum_witness
          (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
    have hnonemptyDomInterRi :
        Set.Nonempty
          (((fun y : EuclideanSpace ℝ (Fin n) => (y : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun y : EuclideanSpace ℝ (Fin n) => (y : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) :=
      helperForTheorem_20_1_nonempty_preimageDom_inter_riPreimage_of_domRiWitnessBlock
        (p := p) (q := q) hdomRiWitnessBlock
    have hbinaryBridge :
        (fenchelConjugate n (fun y => p y + q y) =
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
          (∀ xStar : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
              ∃ y : Fin n → ℝ,
                infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                  fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :=
      _root_.helperForTheorem_20_1_mixed_two_block_exact_topOrAttained_of_polyLeft_domRi_without_riInter
        (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi
    have hsumSplit :
        (fun y => ∑ i, f i y) = (fun y => p y + q y) := by
      funext y
      simpa [p, q] using
        (Finset.sum_filter_add_sum_filter_not
          (s := (Finset.univ : Finset (Fin m)))
          (p := fun i : Fin m => i ∈ Ipoly)
          (f := fun i : Fin m => f i y)).symm
    have hEqAt :
        fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStarE := by
      calc
        fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
            fenchelConjugate n (fun y => p y + q y) xStarE := by
              simp [hsumSplit]
        _ = infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStarE := by
              simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g xStarE) hbinaryBridge.1
    rcases hbinaryBridge.2 xStarE with htop | ⟨y, hy⟩
    · exact False.elim (hconj_ne_top (hEqAt.trans htop))
    · rcases
          helperForTheorem_23_8_polyFilter_conjugate_attained_by_subtypeFamily
            (f := f) (Ipoly := Ipoly) hIpolyNonempty hpoly hproper hdomPoly (xStarE - y) with
        ⟨headFamily, hHeadSum, hHeadVal⟩
      rcases
          helperForTheorem_23_8_nonpolyFilter_conjugate_attained_by_subtypeFamily
            (f := f) (Ipoly := Ipoly)
            (hnonpolyNonempty := by
              simpa [Set.nonempty_iff_ne_empty] using hnonpoly)
            hproper hriNonpoly y with
        ⟨tailFamily, hTailSum, hTailVal⟩
      let parts : Fin m → Fin n → ℝ := fun i =>
        if hi : i ∈ Ipoly then headFamily ⟨i, hi⟩ else tailFamily ⟨i, hi⟩
      have hsumPartsSplit :
          (∑ i : Fin m, parts i) =
            (∑ i : {i : Fin m // i ∈ Ipoly}, headFamily i) +
            (∑ i : {i : Fin m // i ∉ Ipoly}, tailFamily i) := by
        simpa [parts] using
          helperForTheorem_23_8_sum_piecewise_membership
            (Ipoly := Ipoly) (headVal := headFamily) (tailVal := tailFamily)
      have hsumParts : (∑ i, parts i) = xStarE := by
        calc
          (∑ i, parts i) =
              (∑ i : {i : Fin m // i ∈ Ipoly}, headFamily i) +
              (∑ i : {i : Fin m // i ∉ Ipoly}, tailFamily i) := hsumPartsSplit
          _ = (xStarE - y) + y := by rw [hHeadSum, hTailSum]
          _ = xStarE := by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have hvalPartsSplit :
          (∑ i : Fin m,
              if hi : i ∈ Ipoly then fenchelConjugate n (f i) (headFamily ⟨i, hi⟩)
              else fenchelConjugate n (f i) (tailFamily ⟨i, hi⟩)) =
            (∑ i : {i : Fin m // i ∈ Ipoly},
              fenchelConjugate n (f i.1) (headFamily i)) +
            (∑ i : {i : Fin m // i ∉ Ipoly},
              fenchelConjugate n (f i.1) (tailFamily i)) := by
        exact
          helperForTheorem_23_8_sum_piecewise_membership
            (Ipoly := Ipoly)
            (headVal := fun i => fenchelConjugate n (f i.1) (headFamily i))
            (tailVal := fun i => fenchelConjugate n (f i.1) (tailFamily i))
      have hvalParts :
          (∑ i : Fin m, fenchelConjugate n (f i) (parts i)) =
            (∑ i : {i : Fin m // i ∈ Ipoly},
              fenchelConjugate n (f i.1) (headFamily i)) +
            (∑ i : {i : Fin m // i ∉ Ipoly},
              fenchelConjugate n (f i.1) (tailFamily i)) := by
        calc
          (∑ i : Fin m, fenchelConjugate n (f i) (parts i)) =
              ∑ i : Fin m,
                if hi : i ∈ Ipoly then fenchelConjugate n (f i) (headFamily ⟨i, hi⟩)
                else fenchelConjugate n (f i) (tailFamily ⟨i, hi⟩) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  by_cases hmem : i ∈ Ipoly <;> simp [parts, hmem]
          _ =
              (∑ i : {i : Fin m // i ∈ Ipoly},
                fenchelConjugate n (f i.1) (headFamily i)) +
              (∑ i : {i : Fin m // i ∉ Ipoly},
                fenchelConjugate n (f i.1) (tailFamily i)) := hvalPartsSplit
      refine ⟨parts, hsumParts, ?_⟩
      calc
        fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStarE := hEqAt
        _ = fenchelConjugate n p (xStarE - y) + fenchelConjugate n q y := hy
        _ =
            (∑ i : {i : Fin m // i ∈ Ipoly},
              fenchelConjugate n (f i.1) (headFamily i)) +
            (∑ i : {i : Fin m // i ∉ Ipoly},
              fenchelConjugate n (f i.1) (tailFamily i)) := by
              rw [hHeadVal, hTailVal]
        _ = ∑ i : Fin m, fenchelConjugate n (f i) (parts i) := hvalParts.symm
  · rcases hmixed with ⟨z, hzPoly, _hzRest⟩
    -- If the complement is empty, every index is polyhedral and the whole family is covered by
    -- the polyhedral attainment theorem directly.
    have hmemAll : ∀ i : Fin m, i ∈ Ipoly := by
      intro i
      by_contra hi
      exact hnonpoly ⟨i, hi⟩
    have hpolyAll : ∀ i : Fin m, IsPolyhedralConvexFunction n (f i) := by
      intro i
      exact (hpoly i).1 (hmemAll i)
    have hdomAll :
        Set.Nonempty (⋂ i : Fin m, effectiveDomain Set.univ (f i)) := by
      refine ⟨z, Set.mem_iInter.2 ?_⟩
      intro i
      exact hzPoly i (hmemAll i)
    have hpolyAtt :=
      polyhedral_refinement_fenchelConjugate_sum_eq_infimalConvolutionFamily_and_attainment
        (f := f) hpolyAll hproper hdomAll hmPos
    rcases hpolyAtt.2 xStarE with ⟨parts, hsum, hval⟩
    have hEqAt :
        fenchelConjugate n (fun y => ∑ i, f i y) xStarE =
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStarE := by
      simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g xStarE) hpolyAtt.1
    exact ⟨parts, hsum, hEqAt.trans hval⟩

end Section23
end Chap05
