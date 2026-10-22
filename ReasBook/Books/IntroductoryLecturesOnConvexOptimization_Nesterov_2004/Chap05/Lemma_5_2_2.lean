/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient NewtonDecrement AuxiliaryCentralPathNewtonDecrement DikinEllipsoidNotation
  HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear tilt preserves the positive-definite-Hessian owner on `dom`. -/
instance auxiliaryCentralPathObjective_hasPositiveDefiniteHessianOn
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) :
    HasPositiveDefiniteHessianOn dom (auxiliaryCentralPathObjective f y0 t) where
  isPositive {x} hx := by
    simpa [auxiliaryCentralPathObjective_hessian_eq] using
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx : (hessian f x).IsPositive)
  posdef {x} hx {u} hu := by
    simpa [auxiliaryCentralPathObjective_hessian_eq] using
      (HasPositiveDefiniteHessianOn.posdef hx hu : 0 < inner ℝ u (hessian f x u))

/-- The Hessian of the tilted objective `ψ(t; ·)` is nondegenerate at every domain point once the
ambient objective carries the chapter's positive-definite-Hessian owner. -/
theorem auxiliaryCentralPathObjective_hessian_det_ne_zero
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) {y : E} (hy : y ∈ dom) :
    (hessian (auxiliaryCentralPathObjective f y0 t) y).det ≠ 0 := by
  have hdet : (hessian f y).det ≠ 0 := HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy
  simpa [auxiliaryCentralPathObjective_hessian_eq] using hdet

/-- The approximate centering condition for the tilted objective `ψ(t; ·)` at `y`, expressed as
the bound `λ_{ψ(t; ·)}(y) ≤ β / M_f` on the canonical domain-membership Newton-decrement surface
for the tilted objective, with the positive self-concordance parameter carried on the canonical
`NNRealˣ` surface. -/
def satisfies_approximate_centering_condition
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ)
    (β : ℝ) : Prop :=
  λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤ β / (Mf : ℝ)

-- Proof sketch: unfold `satisfies_approximate_centering_condition`.
/-- Expanding `satisfies_approximate_centering_condition` recovers the inequality
`λ_{ψ(t; ·)}(y) ≤ β / M_f`. -/
theorem satisfies_approximate_centering_condition_iff
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ) (β : ℝ) :
    satisfies_approximate_centering_condition f y0 t y hy Mf β ↔
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤ β / (Mf : ℝ) := Iff.rfl

variable {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ}

/-- Helper for Lemma 5.2.2: the Hessian operator induces the positive-definite bilinear form
used by the Chapter 5 dual local norm. -/
private theorem hessianBilinPosDefOfIsPositiveOfIsInvertible
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    ((((innerSL ℝ).comp (hessian F x)).toBilinForm).toQuadraticMap).PosDef := by
  -- Expand the Hessian bilinear form and read positive definiteness off the Hessian owner.
  rw [QuadraticMap.posDef_iff_nonneg]
  refine ⟨?_, ?_⟩
  · intro u
    change 0 ≤ inner ℝ (hessian F x u) u
    simpa [real_inner_comm] using hPos.inner_nonneg_right u
  · intro u hu
    change inner ℝ (hessian F x u) u = 0 at hu
    have hHu : hessian F x u = 0 := by
      obtain ⟨m, w, hA⟩ := (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).mp hPos
      rw [hA] at hu ⊢
      have hsum : ∑ j : Fin m, (inner ℝ (w j) u) ^ (2 : ℕ) = 0 := by
        simpa [Finset.sum_apply, InnerProductSpace.rankOne_apply, sum_inner, real_inner_smul_left,
          pow_two] using hu
      have hw : ∀ i : Fin m, inner ℝ (w i) u = 0 := by
        intro i
        exact sq_eq_zero_iff.mp <|
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ ↦ sq_nonneg (inner ℝ (w j) u))).mp hsum i (by simp)
      simp [Finset.sum_apply, InnerProductSpace.rankOne_apply, hw]
    simpa using hInv.injective (by simpa using hHu)

/-- Helper for Lemma 5.2.2: the Chapter 2 dual norm is bounded above on the image of the
closed primal unit ball, so `le_csSup` can be used pointwise. -/
private theorem seminormDualNormBddAboveInnerImageClosedBall
    (p : Seminorm ℝ E) [p.IsNorm] (g : E) :
    BddAbove ((fun y : E ↦ inner ℝ g y) '' p.closedBall 0 1) := by
  -- A global norm bound on the primal unit ball gives a uniform upper bound on the image.
  obtain ⟨C, hC_pos, hnorm_le⟩ := p.exists_norm_le_mul
  refine ⟨‖g‖ * C, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hy_norm : ‖y‖ ≤ C := by
    have hpy : p y ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hy
    calc
      ‖y‖ ≤ C * p y := hnorm_le y
      _ ≤ C * 1 := by
        gcongr
      _ = C := by
        ring
  calc
    inner ℝ g y ≤ ‖g‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖g‖ * C := by
      gcongr

/-- Helper for Lemma 5.2.2: the Chapter 2 dual norm is subadditive after passing through the
Riesz identification. -/
private theorem seminormDualNormAddLe
    (p : Seminorm ℝ E) [p.IsNorm] (g h : E) :
    Seminorm.dualNorm p (g + h) ≤ Seminorm.dualNorm p g + Seminorm.dualNorm p h := by
  -- Evaluate the sum on a shared unit-ball witness and bound each term separately.
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⟨0, by simp, by simp⟩⟩
  · rintro z ⟨u, hu, rfl⟩
    have hu_ball : u ∈ p.closedBall 0 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hu
    have hg_le : inner ℝ g u ≤ Seminorm.dualNorm p g := by
      have hmem : inner ℝ g u ∈ ((fun y : E ↦ inner ℝ g y) '' p.closedBall 0 1) :=
        ⟨u, hu_ball, rfl⟩
      exact le_csSup (seminormDualNormBddAboveInnerImageClosedBall p g) hmem
    have hh_le : inner ℝ h u ≤ Seminorm.dualNorm p h := by
      have hmem : inner ℝ h u ∈ ((fun y : E ↦ inner ℝ h y) '' p.closedBall 0 1) :=
        ⟨u, hu_ball, rfl⟩
      exact le_csSup (seminormDualNormBddAboveInnerImageClosedBall p h) hmem
    calc
      inner ℝ (g + h) u = inner ℝ g u + inner ℝ h u := by
        rw [inner_add_left]
      _ ≤ Seminorm.dualNorm p g + Seminorm.dualNorm p h := add_le_add hg_le hh_le

/-- Helper for Lemma 5.2.2: at a fixed domain point, the Hessian dual local norm is subadditive
on covectors. -/
private theorem hessianDualLocalNorm_ofPosDefMem_add_le
    {dom : Set E} {F : E → ℝ} [HasPositiveDefiniteHessianOn dom F]
    {x : E} (hx : x ∈ dom) (g₁ g₂ : StrongDual ℝ E) :
    HessianDualLocalNorm.ofPosDefMem F hx (g₁ + g₂) ≤
      HessianDualLocalNorm.ofPosDefMem F hx g₁ +
        HessianDualLocalNorm.ofPosDefMem F hx g₂ := by
  let hPos : (hessian F x).IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx
  let hInv : (hessian F x).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx)
  let B : LinearMap.BilinForm ℝ E := ((innerSL ℝ).comp (hessian F x)).toBilinForm
  let hBPos : B.toQuadraticMap.PosDef :=
    hessianBilinPosDefOfIsPositiveOfIsInvertible hPos hInv
  let p : Seminorm ℝ E := B.primalSeminorm hBPos
  let v₁ : E := (InnerProductSpace.toDual ℝ E).symm g₁
  let v₂ : E := (InnerProductSpace.toDual ℝ E).symm g₂
  have hBPos_eq :
      hessianBilinPosDefOfIsPositiveOfIsInvertible hPos hInv = hBPos :=
    Subsingleton.elim _ _
  have hsum :
      Seminorm.dualNorm p (v₁ + v₂) ≤ Seminorm.dualNorm p v₁ + Seminorm.dualNorm p v₂ :=
    seminormDualNormAddLe p v₁ v₂
  have hleft :
      HessianDualLocalNorm.ofPosDefMem F hx (g₁ + g₂) =
        Seminorm.dualNorm p (v₁ + v₂) := by
    trans B.dualNorm hBPos ((g₁ + g₂).toLinearMap)
    · simp [HessianDualLocalNorm.ofPosDefMem, dualLocalNorm, B]
      change
        B.dualNorm (hessianBilinPosDefOfIsPositiveOfIsInvertible hPos hInv)
            ((g₁ + g₂).toLinearMap) =
          B.dualNorm hBPos ((g₁ + g₂).toLinearMap)
      rw [hBPos_eq]
    · symm
      simpa [p, v₁, v₂] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos (v₁ + v₂))
  have hg₁ :
      HessianDualLocalNorm.ofPosDefMem F hx g₁ =
        Seminorm.dualNorm p v₁ := by
    trans B.dualNorm hBPos g₁.toLinearMap
    · simp [HessianDualLocalNorm.ofPosDefMem, dualLocalNorm, B]
      change
        B.dualNorm (hessianBilinPosDefOfIsPositiveOfIsInvertible hPos hInv) g₁.toLinearMap =
          B.dualNorm hBPos g₁.toLinearMap
      rw [hBPos_eq]
    · symm
      simpa [p, v₁] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos v₁)
  have hg₂ :
      HessianDualLocalNorm.ofPosDefMem F hx g₂ =
        Seminorm.dualNorm p v₂ := by
    trans B.dualNorm hBPos g₂.toLinearMap
    · simp [HessianDualLocalNorm.ofPosDefMem, dualLocalNorm, B]
      change
        B.dualNorm (hessianBilinPosDefOfIsPositiveOfIsInvertible hPos hInv) g₂.toLinearMap =
          B.dualNorm hBPos g₂.toLinearMap
      rw [hBPos_eq]
    · symm
      simpa [p, v₂] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos v₂)
  calc
    HessianDualLocalNorm.ofPosDefMem F hx (g₁ + g₂) =
        Seminorm.dualNorm p (v₁ + v₂) := hleft
    _ ≤ Seminorm.dualNorm p v₁ + Seminorm.dualNorm p v₂ := hsum
    _ = HessianDualLocalNorm.ofPosDefMem F hx g₁ +
          HessianDualLocalNorm.ofPosDefMem F hx g₂ := by
      rw [← hg₁, ← hg₂]

/-- Helper for Lemma 5.2.2: the Hessian dual local norm is even on covectors at a fixed domain
point. -/
private theorem hessianDualLocalNorm_ofPosDefMem_neg
    {dom : Set E} {F : E → ℝ} [HasPositiveDefiniteHessianOn dom F]
    {x : E} (hx : x ∈ dom) (g : StrongDual ℝ E) :
    HessianDualLocalNorm.ofPosDefMem F hx (-g) =
      HessianDualLocalNorm.ofPosDefMem F hx g := by
  -- Expanding both sides shows that the two minus signs cancel inside the inverse-Hessian pairing.
  rw [HessianDualLocalNorm.ofPosDefMem_def, HessianDualLocalNorm.ofPosDefMem_def]
  simp

/-- Helper for Lemma 5.2.2: fixed-point Hessian dual local norms pull out absolute scalar
factors. -/
private theorem hessianDualLocalNorm_ofPosDefMem_smul
    {dom : Set E} {F : E → ℝ} [HasPositiveDefiniteHessianOn dom F]
    {x : E} (hx : x ∈ dom) (v : E) (a : ℝ) :
    HessianDualLocalNorm.ofPosDefMem F hx ((toDual ℝ E) (a • v)) =
      |a| * HessianDualLocalNorm.ofPosDefMem F hx ((toDual ℝ E) v) := by
  let hPos : (hessian F x).IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx
  let hInv : (hessian F x).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx)
  by_cases ha : 0 ≤ a
  · -- Nonnegative scalars pull out directly by positive homogeneity.
    simpa [HessianDualLocalNorm.ofPosDefMem, smul_eq_mul, abs_of_nonneg ha] using
      dualLocalNorm_smul_nonneg F x hPos hInv ((toDual ℝ E) v) ha
  · have ha_lt : a < 0 := lt_of_not_ge ha
    have hneg_nonneg : 0 ≤ -a := by linarith
    calc
      HessianDualLocalNorm.ofPosDefMem F hx ((toDual ℝ E) (a • v)) =
          HessianDualLocalNorm.ofPosDefMem F hx (((-a : ℝ)) • (toDual ℝ E (-v))) := by
        simp
      _ = (-a) * HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E (-v)) := by
        simpa [HessianDualLocalNorm.ofPosDefMem, smul_eq_mul] using
          dualLocalNorm_smul_nonneg F x hPos hInv (toDual ℝ E (-v)) hneg_nonneg
      _ = (-a) * HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) := by
        have hneg :
            HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E (-v)) =
              HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) := by
          simpa using hessianDualLocalNorm_ofPosDefMem_neg hx ((toDual ℝ E) v)
        rw [hneg]
      _ = |a| * HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) := by
        simp [abs_of_neg ha_lt]

/-- Helper for Lemma 5.2.2: a quadratic family bounded above by `c` yields the discriminant
estimate `a² ≤ b c`. -/
private theorem sq_le_mul_of_quadratic_family
    {a b c : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ c) :
    a ^ (2 : ℕ) ≤ b * c := by
  -- Split on the degenerate quadratic coefficient and test the family at the critical point.
  by_cases hb_zero : b = 0
  · by_cases ha_zero : a = 0
    · simp [ha_zero, hb_zero]
    · have ha_eq_zero : a = 0 := by
        by_contra ha_ne
        have htest := hline ((|c| + 1) / a)
        have hcontr : 2 * (|c| + 1) ≤ c := by
          have hrew : 2 * ((|c| + 1) / a) * a ≤ c := by
            simpa [hb_zero] using htest
          field_simp [ha_ne] at hrew
          linarith
        have habs : c ≤ |c| := le_abs_self c
        have hbad : |c| + 2 ≤ 0 := by
          nlinarith
        have hpos : 0 < |c| + 2 := by
          nlinarith [abs_nonneg c]
        exact (not_le_of_gt hpos) hbad
      exact (ha_zero ha_eq_zero).elim
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_zero)
    have htest := hline (a / b)
    have hrewrite :
        2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
      field_simp [hb_zero]
      ring
    have hquot : a ^ (2 : ℕ) / b ≤ c := by
      simpa [hrewrite] using htest
    simpa [mul_comm] using (div_le_iff₀ hb_pos).1 hquot

/-- Helper for Lemma 5.2.2: the Euclidean pairing is controlled by the Hessian dual local norm
times the Hessian local norm at a positive-definite domain point. -/
private theorem abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm_ofPosDefMem
    {dom : Set E} {F : E → ℝ} [HasPositiveDefiniteHessianOn dom F]
    {x : E} (hx : x ∈ dom) (v z : E) :
    |inner ℝ v z| ≤
      HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) * ‖z‖[F; x] := by
  let H := hessian F x
  let w := H.inverse v
  have hPos : H.IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx
  have hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero
    (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx)
  have hHw : H w = v := by
    dsimp [w, H]
    exact hInv.self_apply_inverse v
  have hquad : 0 ≤ inner ℝ z (H z) := hPos.inner_nonneg_right z
  have hpair_nonneg : 0 ≤ inner ℝ v w := by
    -- Rewrite the positive Hessian quadratic form of `w` as the inverse-Hessian pairing.
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ v w := by rw [hHw, real_inner_comm]
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ v z - t ^ (2 : ℕ) * inner ℝ z (H z) ≤ inner ℝ v w := by
    intro t
    have hnonneg : 0 ≤ inner ℝ (t • z - w) (H (t • z - w)) := hPos.inner_nonneg_right (t • z - w)
    have hcross :
        inner ℝ w (H z) = inner ℝ v z := by
      calc
        inner ℝ w (H z) = inner ℝ (H w) z := by
          simpa [real_inner_comm] using hPos.isSymmetric z w
        _ = inner ℝ v z := by rw [hHw]
    have hrewrite :
        inner ℝ (t • z - w) (H (t • z - w)) =
          t ^ (2 : ℕ) * inner ℝ z (H z) - 2 * t * inner ℝ v z + inner ℝ v w := by
      -- Expand the quadratic form and rewrite the mixed terms using `H w = v`.
      have hleft :
          inner ℝ (t • z) (H w) = t * inner ℝ v z := by
        rw [hHw, real_inner_comm, inner_smul_right]
      have hright :
          inner ℝ w (t • H z) = t * inner ℝ v z := by
        rw [inner_smul_right, hcross]
      have hdiag :
          inner ℝ w (H w) = inner ℝ v w := by
        rw [hHw, real_inner_comm]
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
      rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
      rw [hleft, hright, hdiag]
      have hstar_t : (starRingEnd ℝ) t = t := by simp
      rw [hstar_t]
      ring_nf
    rw [hrewrite] at hnonneg
    nlinarith
  have hsq_raw :
      (inner ℝ v z) ^ (2 : ℕ) ≤ inner ℝ z (H z) * inner ℝ v w := by
    have hsq : (inner ℝ v z) ^ (2 : ℕ) ≤ inner ℝ z (H z) * inner ℝ v w :=
      sq_le_mul_of_quadratic_family hquad hline
    simpa [mul_comm] using hsq
  have hdual_sq :
      (HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v)) ^ (2 : ℕ) = inner ℝ v w := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    simpa [w, H, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      Real.sq_sqrt hpair_nonneg
  have hlocal_sq : ‖z‖[F; x] ^ (2 : ℕ) = inner ℝ z (H z) := by
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt hquad
  have hsq_abs :
      |inner ℝ v z| ^ (2 : ℕ) ≤
        (HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) * ‖z‖[F; x]) ^ (2 : ℕ) := by
    calc
      |inner ℝ v z| ^ (2 : ℕ) = (inner ℝ v z) ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ inner ℝ z (H z) * inner ℝ v w := hsq_raw
      _ =
          (HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v)) ^ (2 : ℕ) *
            ‖z‖[F; x] ^ (2 : ℕ) := by rw [hdual_sq, hlocal_sq, mul_comm]
      _ =
          (HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) * ‖z‖[F; x]) ^ (2 : ℕ) := by
        ring
  have hdual_nonneg : 0 ≤ HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    exact Real.sqrt_nonneg _
  exact le_of_sq_le_sq hsq_abs
    (mul_nonneg hdual_nonneg (hessianLocalNorm_nonneg F x z))

/-- Helper for Lemma 5.2.2: a Loewner upper bound on Hessians yields the corresponding local-norm
comparison after taking square roots. -/
private theorem hessianLocalNorm_le_mul_of_loewner_upper
    {F : E → ℝ} {x y v : E} {c : ℝ}
    (hc : 0 ≤ c) (hcmp : hessian F y ≤ c • hessian F x) :
    ‖v‖[F; y] ≤ Real.sqrt c * ‖v‖[F; x] := by
  have hgap_pos :
      (c • hessian F x - hessian F y).IsPositive := by
    rw [← ContinuousLinearMap.le_def]
    exact hcmp
  have hinner_le :
      inner ℝ v (hessian F y v) ≤ c * inner ℝ v (hessian F x v) := by
    have hquad_gap :
        0 ≤ inner ℝ v ((c • hessian F x - hessian F y) v) :=
      hgap_pos.inner_nonneg_right v
    simpa [inner_sub_right, inner_smul_right] using hquad_gap
  -- Scalarize the Loewner comparison on the test vector and then take square roots.
  rw [hessianLocalNorm_def, hessianLocalNorm_def]
  calc
    Real.sqrt (inner ℝ v (hessian F y v))
        ≤ Real.sqrt (c * inner ℝ v (hessian F x v)) := by
          exact Real.sqrt_le_sqrt hinner_le
    _ = Real.sqrt c * Real.sqrt (inner ℝ v (hessian F x v)) := by
          rw [Real.sqrt_mul hc]

/-- Helper for Lemma 5.2.2: along an admissible Dikin segment, the endpoint dual local norm is at
most the base dual local norm multiplied by the standard transport factor
`(1 - M_f ‖y - x‖_x)⁻¹`. -/
private theorem hessianDualLocalNorm_ofPosDefMem_le_mul_of_mem_openDikinEllipsoid
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y v : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ))) :
    HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E v) ≤
      (1 / (1 - (Mf : ℝ) * ‖y - x‖[F; x])) *
        HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let a : ℝ := (Mf : ℝ) * ‖y - x‖[F; x]
  let coeff : ℝ := ((1 - a) ^ (2 : ℕ))⁻¹
  let Hy := hessian F y
  let w : E := Hy.inverse v
  let δx := HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v)
  let δy := HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E v)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hnorm_lt : ‖y - x‖[F; x] < 1 / (Mf : ℝ) := by
    simpa using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hnorm_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hcoeff_nonneg : 0 ≤ coeff := by
    positivity
  let rmid : ℝ := (‖y - x‖[F; x] + 1 / (Mf : ℝ)) / 2
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    -- Place the exact local radius below `1 / M_f` by inserting the midpoint witness.
    dsimp [rmid]
    nlinarith
  have hxy_mid : y ∈ W⁰[F; x](rmid) := by
    -- The exact local radius is strictly below the midpoint radius.
    refine (mem_openDikinEllipsoid_iff F x y rmid).2 ?_
    dsimp [rmid]
    nlinarith
  have hloewner :=
    hself.hessian_loewner_bounds_of_exact_local_radius hx hy hrmid_lt hxy_mid
  have hcoeff_eq : coeff = (1 / (1 - a)) ^ (2 : ℕ) := by
    dsimp [coeff]
    field_simp [hfactor_pos.ne']
  have hcmp : hessian F x ≤ coeff • hessian F y := by
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · intro u₁ u₂
      have hsymmX :
          inner ℝ (hessian F x u₁) u₂ = inner ℝ u₁ (hessian F x u₂) := by
        simpa using (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx).isSymmetric u₁ u₂
      have hsymmY :
          inner ℝ (hessian F y u₁) u₂ = inner ℝ u₁ (hessian F y u₂) := by
        simpa using (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hy).isSymmetric u₁ u₂
      calc
        inner ℝ ((coeff • hessian F y - hessian F x) u₁) u₂ =
            coeff * inner ℝ (hessian F y u₁) u₂ - inner ℝ (hessian F x u₁) u₂ := by
              simp [inner_sub_left, inner_smul_left]
        _ = coeff * inner ℝ u₁ (hessian F y u₂) - inner ℝ u₁ (hessian F x u₂) := by
              rw [hsymmY, hsymmX]
        _ = inner ℝ u₁ ((coeff • hessian F y - hessian F x) u₂) := by
              simp [inner_sub_right, inner_smul_right]
    · intro u
      have hloewner_lower :
          ((1 - a) ^ (2 : ℕ)) • hessian F x ≤ hessian F y := by
        simpa [a, mul_comm, mul_left_comm, mul_assoc] using hloewner.1
      rw [ContinuousLinearMap.le_def] at hloewner_lower
      have hdiag :
          ((1 - a) ^ (2 : ℕ)) * inner ℝ u (hessian F x u) ≤ inner ℝ u (hessian F y u) := by
        have hraw :
            0 ≤ inner ℝ u (hessian F y u - (((1 - a) ^ (2 : ℕ)) • hessian F x) u) := by
          simpa [sub_eq_add_neg] using hloewner_lower.inner_nonneg_right u
        simpa [inner_sub_right, inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hraw
      have hpow_pos : 0 < (1 - a) ^ (2 : ℕ) := by
        positivity
      have hscalar :
          inner ℝ u (hessian F x u) ≤ coeff * inner ℝ u (hessian F y u) := by
        have hdiv :
            inner ℝ u (hessian F x u) ≤ inner ℝ u (hessian F y u) / ((1 - a) ^ (2 : ℕ)) := by
          exact (le_div_iff₀ hpow_pos).2 (by simpa [mul_comm] using hdiag)
        simpa [hcoeff_eq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
      have hgoal :
          0 ≤ inner ℝ ((coeff • hessian F y - hessian F x) u) u := by
        simpa [real_inner_comm, inner_sub_left, inner_smul_left, mul_comm, mul_left_comm,
          mul_assoc] using sub_nonneg.mpr hscalar
      exact hgoal
  have hInvY : Hy.IsInvertible := hessian_isInvertible_of_det_ne_zero
    (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy)
  have hHyw : Hy w = v := by
    dsimp [w, Hy]
    exact hInvY.self_apply_inverse v
  have hpair_nonneg : 0 ≤ inner ℝ v w := by
    have hPosY : Hy.IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hy
    calc
      0 ≤ inner ℝ w (Hy w) := hPosY.inner_nonneg_right w
      _ = inner ℝ v w := by rw [hHyw, real_inner_comm]
  have hw_base_le :
      ‖w‖[F; x] ≤ (1 / (1 - a)) * ‖w‖[F; y] := by
    have hsqrt : Real.sqrt coeff = 1 / (1 - a) := by
      have hfactor_nonneg : 0 ≤ 1 / (1 - a) := by
        positivity
      rw [hcoeff_eq, Real.sqrt_sq_eq_abs, abs_of_nonneg hfactor_nonneg]
    -- Compare the same witness `w = ∇²F(y)⁻¹ v` in the base and endpoint Hessian metrics.
    calc
      ‖w‖[F; x] ≤ Real.sqrt coeff * ‖w‖[F; y] := by
        exact hessianLocalNorm_le_mul_of_loewner_upper hcoeff_nonneg hcmp
      _ = (1 / (1 - a)) * ‖w‖[F; y] := by
        rw [hsqrt]
  have hw_endpoint_eq : ‖w‖[F; y] = δy := by
    -- Compare the endpoint local norm of `w` with the endpoint dual norm of `v`.
    have hcore : ‖w‖[F; y] = HessianDualLocalNorm.ofPosDefMem F hy ((toDual ℝ E) v) := by
      rw [hessianLocalNorm_def, HessianDualLocalNorm.ofPosDefMem_def]
      have hinner : inner ℝ w (Hy w) = inner ℝ v w := by
        rw [hHyw, real_inner_comm]
      simpa [w, Hy, InnerProductSpace.toDual_apply_apply] using congrArg Real.sqrt hinner
    simpa [δy] using hcore
  have hdual_sq : δy ^ (2 : ℕ) = inner ℝ v w := by
    -- Squaring the endpoint dual norm recovers the inverse-Hessian witness pairing.
    have hcore :
        (HessianDualLocalNorm.ofPosDefMem F hy ((toDual ℝ E) v)) ^ (2 : ℕ) = inner ℝ v w := by
      rw [HessianDualLocalNorm.ofPosDefMem_def]
      simpa [w, Hy, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
        Real.sq_sqrt hpair_nonneg
    simpa [δy] using hcore
  have hδx_nonneg : 0 ≤ δx := by
    -- Expand `δx` once so the base dual norm is visibly a square root.
    simp [δx, HessianDualLocalNorm.ofPosDefMem_def]
  have hδy_nonneg : 0 ≤ δy := by
    -- Expand `δy` once so the endpoint dual norm is visibly a square root.
    simp [δy, HessianDualLocalNorm.ofPosDefMem_def]
  have hpair_bound : |inner ℝ v w| ≤ δx * ‖w‖[F; x] := by
    have hpair_bound_raw :
        |inner ℝ v w| ≤
          HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) * ‖w‖[F; x] :=
      abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm_ofPosDefMem hx v w
    simpa [δx] using hpair_bound_raw
  have hmain : δy ^ (2 : ℕ) ≤ (1 / (1 - a)) * δx * δy := by
    have hpair_step : inner ℝ v w ≤ δx * ‖w‖[F; x] := by
      simpa [abs_of_nonneg hpair_nonneg] using hpair_bound
    have hw_scaled :
        δx * ‖w‖[F; x] ≤ δx * ((1 / (1 - a)) * ‖w‖[F; y]) := by
      exact mul_le_mul_of_nonneg_left hw_base_le hδx_nonneg
    have hpair_step' :
        inner ℝ v w ≤ δx * ((1 / (1 - a)) * ‖w‖[F; y]) := by
      exact le_trans hpair_step hw_scaled
    rw [hw_endpoint_eq] at hpair_step'
    have hpair_to_sq : inner ℝ v w = δy ^ (2 : ℕ) := by
      simpa using hdual_sq.symm
    rw [hpair_to_sq] at hpair_step'
    ring_nf at hpair_step' ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm] using hpair_step'
  have hfactor_nonneg : 0 ≤ 1 / (1 - a) := by
    positivity
  have hgoal : δy ≤ (1 / (1 - a)) * δx := by
    by_cases hzero : δy = 0
    · rw [hzero]
      exact mul_nonneg hfactor_nonneg hδx_nonneg
    · have hpos : 0 < δy := lt_of_le_of_ne hδy_nonneg (by simpa [eq_comm] using hzero)
      nlinarith [hmain, hpos, hfactor_nonneg, hδx_nonneg]
  simpa [a, δx, δy] using hgoal

/-- A linear tilt preserves the Chapter 5 self-concordance owner, so the updated path parameter
`t₊` determines a canonical intermediate Newton step for `ψ(t₊; ·)` on the same domain. -/
theorem auxiliaryCentralPathObjective_isSelfConcordantOnWith
    (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (y0 : dom) (t : ℝ) :
    IsSelfConcordantOnWith dom Mf (auxiliaryCentralPathObjective f y0 t) := by
  -- Recast the tilt as a zero-quadratic affine perturbation and invoke Corollary 5.1.2.
  let hf : IsSelfConcordantOnWith dom Mf f := inferInstance
  simpa [auxiliaryCentralPathObjective, quadraticAffineObjective_zero_operator, add_comm,
    add_left_comm, add_assoc, sub_eq_add_neg, inner_smul_left, mul_comm, mul_left_comm,
    mul_assoc] using
    hf.add_quadraticAffineObjective 0 (-(t : ℝ) • ∇ f (y0 : E)) (0 : E →L[ℝ] E)
      ContinuousLinearMap.isPositive_zero

private instance auxiliaryCentralPathObjective_instIsSelfConcordantOnWith
    (y0 : dom) (t : ℝ) [IsSelfConcordantOnWith dom (Mf : NNReal) f] :
    IsSelfConcordantOnWith dom (Mf : NNReal) (auxiliaryCentralPathObjective f y0 t) :=
  auxiliaryCentralPathObjective_isSelfConcordantOnWith f (Mf : NNReal) y0 t

/-- Helper for Lemma 5.2.2: the fixed-point Hessian dual local norm for a tilted objective does
not depend on the path parameter because the tilt leaves the Hessian unchanged. -/
private theorem auxiliaryCentralPathObjective_dualLocalNorm_eq
    (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) {y : E} (hy : y ∈ dom) (t t' : ℝ) (g : StrongDual ℝ E) :
    HessianDualLocalNorm.ofPosDefMem (auxiliaryCentralPathObjective f y0 t') hy g =
      HessianDualLocalNorm.ofPosDefMem (auxiliaryCentralPathObjective f y0 t) hy g := by
  -- Both sides expand to the same inverse-Hessian pairing because the Hessian is unchanged.
  rw [HessianDualLocalNorm.ofPosDefMem_def, HessianDualLocalNorm.ofPosDefMem_def]
  simp [auxiliaryCentralPathObjective_hessian_eq]

/-- Helper for Lemma 5.2.2: the determinant-based decrement from Theorem 5.2.2 agrees with the
domain-membership centering decrement on the same tilted objective. -/
private theorem auxiliaryCentralPathObjective_ndec_eq_centeringDecrement
    [IsSelfConcordantOnWith dom (Mf : NNReal) f] [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) {y : E} (hy : y ∈ dom)
    (hH : (hessian (auxiliaryCentralPathObjective f y0 t) y).det ≠ 0) :
    ndec((auxiliaryCentralPathObjective f y0 t), y, (Mf : NNReal), hy, hH) =
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] := by
  -- Both decrement owners reduce to the same inverse-Hessian quadratic form.
  rw [NewtonDecrement.ofDetNeZero_def, NewtonDecrement.ofPosDefMem_def]

/-- Helper for Lemma 5.2.2: the base dual local norm of `∇ f (y₀)` at `y`. -/
private abbrev pathFollowingObjectiveNorm
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (y : E) (hy : y ∈ dom) : ℝ :=
  HessianDualLocalNorm.ofPosDefMem f hy
    ((toDual ℝ E) (∇ f (y0 : E)))

/-- Helper for Lemma 5.2.2: changing the path parameter from `t` to `t'` changes the centering
decrement at the fixed point `y` by at most `|t' - t| ‖∇ f(y₀)‖*_y`. -/
private theorem auxiliaryCentralPathObjective_decrement_le_add_objectiveNorm_mul_abs_sub
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) {y : E} (hy : y ∈ dom) (t t' : ℝ) :
    λ[auxiliaryCentralPathObjective f y0 t'; y | hy] ≤
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] +
        |t' - t| * pathFollowingObjectiveNorm f y0 y hy := by
  let ψ := auxiliaryCentralPathObjective f y0 t
  let g0 := ∇ f (y0 : E)
  have ht' :
      λ[auxiliaryCentralPathObjective f y0 t'; y | hy] =
        HessianDualLocalNorm.ofPosDefMem ψ hy
          ((toDual ℝ E) (∇ f y - (t' : ℝ) • g0)) := by
    -- Rewrite the new decrement on the fixed Hessian surface of `ψ(t; ·)`.
    change
      HessianDualLocalNorm.ofPosDefMem (auxiliaryCentralPathObjective f y0 t') hy
        ((toDual ℝ E) (∇ (auxiliaryCentralPathObjective f y0 t') y)) = _
    rw [auxiliaryCentralPathObjective_dualLocalNorm_eq f y0 hy t t']
    simp [auxiliaryCentralPathObjective_gradient_eq, ψ, g0]
  have ht :
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] =
        HessianDualLocalNorm.ofPosDefMem ψ hy
          ((toDual ℝ E) (∇ f y - (t : ℝ) • g0)) := by
    -- Expand the old decrement on the same fixed Hessian surface.
    simp [NewtonDecrement.ofPosDefMem, auxiliaryCentralPathObjective_gradient_eq, ψ, g0]
  have hsplit :
      ∇ f y - (t' : ℝ) • g0 =
        (∇ f y - (t : ℝ) • g0) + (t - t') • g0 := by
    -- The shifted gradients differ by the single affine perturbation term.
    rw [sub_smul]
    abel
  have hnorm_eq :
      HessianDualLocalNorm.ofPosDefMem ψ hy ((toDual ℝ E) g0) =
        pathFollowingObjectiveNorm f y0 y hy := by
    -- Setting the tilt parameter to `0` identifies the fixed Hessian surface with the original one.
    rw [auxiliaryCentralPathObjective_dualLocalNorm_eq f y0 hy 0 t]
    simp [g0, pathFollowingObjectiveNorm, auxiliaryCentralPathObjective_hessian_eq]
  calc
    λ[auxiliaryCentralPathObjective f y0 t'; y | hy] =
        HessianDualLocalNorm.ofPosDefMem ψ hy
          (((toDual ℝ E) (∇ f y - (t : ℝ) • g0)) +
            ((toDual ℝ E) ((t - t') • g0))) := by
      rw [ht']
      congr 1
      rw [← map_add]
      simp [hsplit]
    _ ≤ HessianDualLocalNorm.ofPosDefMem ψ hy
          ((toDual ℝ E) (∇ f y - (t : ℝ) • g0)) +
        HessianDualLocalNorm.ofPosDefMem ψ hy
          ((toDual ℝ E) ((t - t') • g0)) := by
      exact hessianDualLocalNorm_ofPosDefMem_add_le hy _ _
    _ = λ[auxiliaryCentralPathObjective f y0 t; y | hy] +
        HessianDualLocalNorm.ofPosDefMem ψ hy
          ((toDual ℝ E) ((t - t') • g0)) := by
      rw [← ht]
    _ = λ[auxiliaryCentralPathObjective f y0 t; y | hy] +
        |t - t'| * HessianDualLocalNorm.ofPosDefMem ψ hy ((toDual ℝ E) g0) := by
      rw [hessianDualLocalNorm_ofPosDefMem_smul hy g0 (t - t')]
    _ = λ[auxiliaryCentralPathObjective f y0 t; y | hy] +
        |t' - t| * pathFollowingObjectiveNorm f y0 y hy := by
      rw [abs_sub_comm, hnorm_eq]

private instance pathFollowingUpdate_auxiliaryCentralPathObjective_isSelfConcordantOnWith
    (y0 : dom) (t : ℝ) [IsSelfConcordantOnWith dom (Mf : NNReal) f] :
    IsSelfConcordantOnWith dom (Mf : NNReal) (auxiliaryCentralPathObjective f y0 t) :=
  auxiliaryCentralPathObjective_isSelfConcordantOnWith f (Mf : NNReal) y0 t

/-- The path-following map sending `(t, y)` to the intermediate Newton update `(t₊, y₊)` for the
tilted objective based at `y₀` and path increment parameter `γ`, defined on the canonical
positive-definite-Hessian owner over `dom`. The scalar update is the ordinary expression
`t₊ = t - γ / (M_f ‖∇ f(y₀)‖*_y)`, so the denominator positivity is kept explicit as part of the
input data. The vector update is the canonical intermediate Newton next point for the tilted
objective at the updated parameter `t₊`. -/
def pathFollowingUpdate
    {dom : Set E} (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) : ℝ × E :=
  let hMf : 0 < (Mf : ℝ) := by
    have hMfNNReal : 0 < (Mf : NNReal) := by
      exact pos_iff_ne_zero.mpr (Units.ne_zero Mf)
    exact_mod_cast hMfNNReal
  let denominator : Set.Ioi (0 : ℝ) :=
    ⟨(Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy, mul_pos hMf hObjectiveNorm⟩
  let tPlus :=
    (t : ℝ) - gamma / (denominator : ℝ)
  (tPlus,
    selfConcordantNewtonNextPoint
      (auxiliaryCentralPathObjective f y0 tPlus)
      (Mf : NNReal) .intermediate y hy
      (auxiliaryCentralPathObjective_hessian_det_ne_zero f y0 tPlus hy))

namespace PathFollowingUpdate

/-- Source-facing notation for the path-following map `𝒫_γ`, with the ambient objective data
kept explicit because they are not inferable from `(t, y)` alone. -/
scoped notation:max
  "𝒫[" f "; " Mf "; " y0 " | " hy "; " hObjectiveNorm "; " gamma "](" t ", " y ")" =>
  pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma

end PathFollowingUpdate

open scoped PathFollowingUpdate

-- Proof sketch: unfold `pathFollowingUpdate`.
/-- The first coordinate of `pathFollowingUpdate` is the scalar update
`t₊ = t - γ / (M_f ‖∇ f(y₀)‖*_y)`. -/
theorem pathFollowingUpdate_fst
    (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) :
    (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1 =
      (t : ℝ) - gamma / ((Mf : ℝ) *
        HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E)))) := by
  simp [pathFollowingUpdate, pathFollowingObjectiveNorm]

/-- The second coordinate of `pathFollowingUpdate` is the canonical intermediate Newton next
point for the tilted objective at the updated parameter `t₊`. -/
theorem pathFollowingUpdate_snd
    (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) :
    (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).2 =
      selfConcordantNewtonNextPoint
        (auxiliaryCentralPathObjective f y0
          (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1)
        (Mf : NNReal) .intermediate y hy
        (auxiliaryCentralPathObjective_hessian_det_ne_zero f y0
          (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1 hy) := by
  simp only [pathFollowingUpdate, pathFollowingObjectiveNorm]

/-- The centering threshold `β = τ² (1 + τ + τ / (1 + τ + τ²))` used in the path-following
small-step estimate. -/
def pathFollowingCenteringBeta (τ : ℝ) : ℝ :=
  τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ)))

-- Proof sketch: unfold `pathFollowingCenteringBeta`.
/-- Expanding `pathFollowingCenteringBeta τ` recovers the textbook formula
`τ² (1 + τ + τ / (1 + τ + τ²))`. -/
theorem pathFollowingCenteringBeta_def (τ : ℝ) :
    pathFollowingCenteringBeta τ =
      τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := rfl

/-- The admissible path-parameter increment bound
`τ - τ² (1 + τ + τ / (1 + τ + τ²))` from `(5.2.15)`. -/
def pathFollowingGammaRadius (τ : ℝ) : ℝ :=
  τ - pathFollowingCenteringBeta τ

-- Proof sketch: unfold `pathFollowingGammaRadius` and then rewrite with
-- `pathFollowingCenteringBeta_def`.
/-- Expanding `pathFollowingGammaRadius τ` gives the bound from `(5.2.15)`. -/
theorem pathFollowingGammaRadius_def (τ : ℝ) :
    pathFollowingGammaRadius τ =
      τ - τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := by
  simp [pathFollowingGammaRadius, pathFollowingCenteringBeta]

/-- Helper for Lemma 5.2.2: the bound `λ₁ ≤ τ / M_f` with `τ ≤ 1 / 2` implies the cubic
smallness condition required by Theorem 5.2.2(5) and (6). -/
private theorem pathFollowingIntermediateSmallness_of_scaled_le_half
    {δ τ : ℝ} (hδ_nonneg : 0 ≤ δ) (hscaled : (Mf : ℝ) * δ ≤ τ) (htau : τ ≤ 1 / 2) :
    (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
      (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤ 1 := by
  let s : ℝ := (Mf : ℝ) * δ
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hs_nonneg : 0 ≤ s := by
    exact mul_nonneg (le_of_lt hMf_pos) hδ_nonneg
  have hs_le_half : s ≤ 1 / 2 := le_trans hscaled htau
  have hcore : s + s ^ (2 : ℕ) + s ^ (3 : ℕ) ≤ 1 := by
    nlinarith
  have hs_eq :
      s + s ^ (2 : ℕ) + s ^ (3 : ℕ) =
        (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
          (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) := by
    simp [s]
    ring
  rw [hs_eq] at hcore
  exact hcore

/-- Helper for Lemma 5.2.2: the explicit intermediate-step decrement coefficient from
Theorem 5.2.2(6) is bounded by `β(τ) / M_f` once `(M_f) δ ≤ τ ≤ 1 / 2`. -/
private theorem pathFollowingExplicitIntermediateBound_le_centeringBeta_div
    {δ τ : ℝ} (hδ_nonneg : 0 ≤ δ) (hscaled : (Mf : ℝ) * δ ≤ τ) (htau : τ ≤ 1 / 2) :
    ((Mf : ℝ) * δ ^ (2 : ℕ)) *
        (1 + (Mf : ℝ) * δ +
          ((Mf : ℝ) * δ) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) ≤
      pathFollowingCenteringBeta τ / (Mf : ℝ) := by
  let s : ℝ := (Mf : ℝ) * δ
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hs_nonneg : 0 ≤ s := by
    exact mul_nonneg (le_of_lt hMf_pos) hδ_nonneg
  have hs_le : s ≤ τ := by
    simpa [s] using hscaled
  have hτ_nonneg : 0 ≤ τ := le_trans hs_nonneg hs_le
  have hden_s_pos : 0 < 1 + s + s ^ (2 : ℕ) := by positivity
  have hden_τ_pos : 0 < 1 + τ + τ ^ (2 : ℕ) := by positivity
  have hs_sq_le : s ^ (2 : ℕ) ≤ τ ^ (2 : ℕ) := by
    nlinarith
  have hfrac_le :
      s / (1 + s + s ^ (2 : ℕ)) ≤ τ / (1 + τ + τ ^ (2 : ℕ)) := by
    field_simp [hden_s_pos.ne', hden_τ_pos.ne']
    nlinarith
  have hbracket_le :
      1 + s + s / (1 + s + s ^ (2 : ℕ)) ≤
        1 + τ + τ / (1 + τ + τ ^ (2 : ℕ)) := by
    linarith
  have hbracket_nonneg :
      0 ≤ 1 + τ + τ / (1 + τ + τ ^ (2 : ℕ)) := by
    positivity
  have hmain :
      s ^ (2 : ℕ) * (1 + s + s / (1 + s + s ^ (2 : ℕ))) ≤
        τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := by
    calc
      s ^ (2 : ℕ) * (1 + s + s / (1 + s + s ^ (2 : ℕ))) ≤
          s ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := by
            gcongr
      _ ≤ τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := by
            gcongr
  have hrewrite :
      ((Mf : ℝ) * δ ^ (2 : ℕ)) *
          (1 + (Mf : ℝ) * δ +
            ((Mf : ℝ) * δ) /
              (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) =
        (s ^ (2 : ℕ) * (1 + s + s / (1 + s + s ^ (2 : ℕ)))) / (Mf : ℝ) := by
    -- Rewrite the coefficient in terms of the scaled decrement `s = M_f δ`.
    dsimp [s]
    field_simp [hMf_pos.ne']
  rw [hrewrite, pathFollowingCenteringBeta_def]
  exact div_le_div_of_nonneg_right hmain (le_of_lt hMf_pos)

/-- Helper for Lemma 5.2.2: nonnegative scalar dilations scale the Hessian local norm at a
positive-definite domain point. -/
private theorem hessianLocalNorm_smul_of_nonneg_ofPosDefMem
    {F : E → ℝ} {x u : E} (hPos : (hessian F x).IsPositive) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖τ • u‖[F; x] = τ * ‖u‖[F; x] := by
  have hquad : 0 ≤ inner ℝ u (hessian F x u) := hPos.inner_nonneg_right u
  calc
    ‖τ • u‖[F; x] = Real.sqrt ((τ * τ) * inner ℝ u (hessian F x u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian F x u)) * Real.sqrt (τ * τ) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = τ * ‖u‖[F; x] := by
      rw [show τ * τ = τ ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hτ,
        hessianLocalNorm_def]
      ring

/-- Helper for Lemma 5.2.2: the Newton displacement is the negative step size times the inverse
Hessian applied to the gradient. -/
private theorem nextPointSubEqNegStepSizeSmulInverseGradient
    {dom : Set E} {Mf : NNReal} {F : E → ℝ} [IsSelfConcordantOnWith dom Mf F]
    (variant : SelfConcordantNewtonVariant) {x : E} (hx : x ∈ dom)
    (hH : (hessian F x).det ≠ 0) :
    let α := selfConcordantNewtonStepSize F Mf variant x hx hH
    selfConcordantNewtonNextPoint F Mf variant x hx hH - x =
      -(α • (hessian F x).inverse (∇ F x)) := by
  dsimp [selfConcordantNewtonStepSize]
  rw [selfConcordantNewtonNextPoint_def]
  simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Lemma 5.2.2: the base local norm of a Newton displacement equals the step size
times the Newton decrement. -/
private theorem nextPointSubLocalNormEqStepSizeMulNdec
    {dom : Set E} {Mf : NNReal} {F : E → ℝ} [IsSelfConcordantOnWith dom Mf F]
    (variant : SelfConcordantNewtonVariant) {x : E} (hx : x ∈ dom)
    (hH : (hessian F x).det ≠ 0) :
    let δ := ndec(F, x, Mf, hx, hH)
    let α := selfConcordantNewtonStepSize F Mf variant x hx hH
    ‖selfConcordantNewtonNextPoint F Mf variant x hx hH - x‖[F; x] = α * δ := by
  let δ := ndec(F, x, Mf, hx, hH)
  let α := selfConcordantNewtonStepSize F Mf variant x hx hH
  let v : E := (hessian F x).inverse (∇ F x)
  let hPos : (hessian F x).IsPositive := IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx
  let hInv : (hessian F x).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hα_nonneg : 0 ≤ α := le_of_lt (selfConcordantNewtonStepSize_pos F Mf variant x hx hH)
  have hv_eq : hessian F x v = ∇ F x := hInv.self_apply_inverse (∇ F x)
  have hv_norm : ‖v‖[F; x] = δ := by
    rw [hessianLocalNorm_def]
    calc
      Real.sqrt (inner ℝ v (hessian F x v)) = Real.sqrt (inner ℝ (∇ F x) v) := by
        rw [hv_eq, real_inner_comm]
      _ = δ := by
        simpa [δ, v] using (NewtonDecrement.ofDetNeZero_def Mf F hx hH).symm
  calc
    ‖selfConcordantNewtonNextPoint F Mf variant x hx hH - x‖[F; x] = ‖α • v‖[F; x] := by
      rw [nextPointSubEqNegStepSizeSmulInverseGradient variant hx hH]
      rw [hessianLocalNorm_neg]
    _ = α * ‖v‖[F; x] := hessianLocalNorm_smul_of_nonneg_ofPosDefMem hPos hα_nonneg
    _ = α * δ := by rw [hv_norm]

/-- Helper for Lemma 5.2.2: the intermediate Newton step size has the simplified rational form
used in the centering update. -/
private theorem intermediateStepSize_eq
    {dom : Set E} {Mf : NNRealˣ} {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    {x : E} (hx : x ∈ dom) (hH : (hessian F x).det ≠ 0) :
    let δ := ndec(F, x, (Mf : NNReal), hx, hH)
    selfConcordantNewtonStepSize F (Mf : NNReal) .intermediate x hx hH =
      (1 + (Mf : ℝ) * δ) /
        (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) := by
  let δ := ndec(F, x, (Mf : NNReal), hx, hH)
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg (Mf : NNReal) F hx hH
  have hshift_den_pos : 0 < 1 + (Mf : ℝ) * δ := by
    nlinarith
  rw [selfConcordantNewtonStepSize]
  simp [selfConcordantNewtonShift, δ]
  field_simp [hshift_den_pos.ne']

/-- Helper for Lemma 5.2.2: the intermediate-step local norm stays strictly below the reciprocal
radius `1 / M_f`. -/
private theorem intermediateStepLocalNorm_lt_inv
    {Mf : NNRealˣ} {δ : ℝ} (hδ_nonneg : 0 ≤ δ) :
    δ * (1 + (Mf : ℝ) * δ) /
        (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) <
      1 / (Mf : ℝ) := by
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hden_pos :
      0 < 1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) := by
    positivity
  refine (lt_div_iff₀ hMf_pos).2 ?_
  have hscaled_lt :
      (((Mf : ℝ) * δ) * (1 + (Mf : ℝ) * δ)) /
          (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) <
        1 := by
    refine (div_lt_iff₀ hden_pos).2 ?_
    nlinarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled_lt

/-- Helper for Lemma 5.2.2: under the cubic smallness condition, the intermediate Newton next
point stays in `dom`. -/
private theorem intermediateNewtonNextPoint_mem_of_smallness
    {dom : Set E} {Mf : NNRealˣ} {F : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) F] [HasPositiveDefiniteHessianOn dom F]
    {x : E} (hx : x ∈ dom) (hH : (hessian F x).det ≠ 0)
    (hsmall :
      let δ := ndec(F, x, (Mf : NNReal), hx, hH)
      (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤ 1) :
    let xPlus := selfConcordantNewtonNextPoint F (Mf : NNReal) .intermediate x hx hH
    xPlus ∈ dom := by
  dsimp
  let δ := ndec(F, x, (Mf : NNReal), hx, hH)
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg (Mf : NNReal) F hx hH
  have hstep_mem :
      selfConcordantNewtonNextPoint F (Mf : NNReal) .intermediate x hx hH ∈
        W⁰[F; x](1 / ((Mf : NNReal) : ℝ)) := by
    refine (mem_openDikinEllipsoid_iff F x
        (selfConcordantNewtonNextPoint F (Mf : NNReal) .intermediate x hx hH)
        (1 / ((Mf : NNReal) : ℝ))).2 ?_
    rw [show
        ‖selfConcordantNewtonNextPoint F (Mf : NNReal) .intermediate x hx hH - x‖[F; x] =
          δ * (1 + (Mf : ℝ) * δ) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) by
        have hstep :
            ‖selfConcordantNewtonNextPoint F (Mf : NNReal) .intermediate x hx hH - x‖[F; x] =
              selfConcordantNewtonStepSize F (Mf : NNReal) .intermediate x hx hH *
                ndec(F, x, (Mf : NNReal), hx, hH) :=
          nextPointSubLocalNormEqStepSizeMulNdec .intermediate hx hH
        rw [intermediateStepSize_eq hx hH] at hstep
        simpa [δ, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hstep]
    exact intermediateStepLocalNorm_lt_inv hδ_nonneg
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  exact hself.openDikinEllipsoid_inv_constant_subset hx hstep_mem

/-- Under the hypotheses of Lemma 5.2.2, the updated point produced by `pathFollowingUpdate`
belongs to `dom`; this is derived from the canonical intermediate Newton step for
`ψ(t₊; ·)`, not taken as primitive path-following data. -/
theorem pathFollowingUpdate_snd_mem
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) {y : E} (hy : y ∈ dom) {τ gamma : ℝ}
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (htau : τ ≤ 1 / 2)
    (hcenter : satisfies_approximate_centering_condition f y0 t y hy Mf
      (pathFollowingCenteringBeta τ))
    (hgamma : |gamma| ≤ pathFollowingGammaRadius τ) :
    (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).2 ∈ dom := by
  let tPlus := (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1
  let ψ := auxiliaryCentralPathObjective f y0 tPlus
  have hH : (hessian ψ y).det ≠ 0 := by
    simpa [ψ] using auxiliaryCentralPathObjective_hessian_det_ne_zero f y0 tPlus hy
  let δ := ndec(ψ, y, (Mf : NNReal), hy, hH)
  have hδ_eq : δ = λ[ψ; y | hy] := by
    simpa [δ] using
      (auxiliaryCentralPathObjective_ndec_eq_centeringDecrement y0 tPlus hy hH)
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg (Mf : NNReal) ψ hy hH
  have hcenter_old :
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤
        pathFollowingCenteringBeta τ / (Mf : ℝ) := by
    exact (satisfies_approximate_centering_condition_iff f y0 t y hy Mf
      (pathFollowingCenteringBeta τ)).1 hcenter
  have hδ_le_shifted :
      δ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
        |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
    rw [hδ_eq]
    calc
      λ[ψ; y | hy] ≤ λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
            have hshift_raw :
                λ[auxiliaryCentralPathObjective f y0 tPlus; y | hy] ≤
                  λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
                    |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy :=
              auxiliaryCentralPathObjective_decrement_le_add_objectiveNorm_mul_abs_sub
                y0 hy (t : ℝ) tPlus
            simpa [ψ, tPlus] using hshift_raw
      _ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
            gcongr
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hstep_eq :
      |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy =
        |gamma| / (Mf : ℝ) := by
    dsimp [tPlus]
    rw [pathFollowingUpdate_fst]
    have hObjectiveNorm_nonneg : 0 ≤ pathFollowingObjectiveNorm f y0 y hy := le_of_lt hObjectiveNorm
    calc
      |(t : ℝ) - gamma / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy) - (t : ℝ)| *
          pathFollowingObjectiveNorm f y0 y hy =
          |(-gamma) / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy)| *
            pathFollowingObjectiveNorm f y0 y hy := by
              congr 1
              ring
      _ = (|gamma| / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy)) *
            pathFollowingObjectiveNorm f y0 y hy := by
              rw [abs_div, abs_neg, abs_mul, abs_of_pos hMf_pos,
                abs_of_nonneg hObjectiveNorm_nonneg]
      _ = |gamma| / (Mf : ℝ) := by
              field_simp [hMf_pos.ne', hObjectiveNorm.ne']
  have hδ_le_tau_div :
      δ ≤ τ / (Mf : ℝ) := by
    calc
      δ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := hδ_le_shifted
      _ = pathFollowingCenteringBeta τ / (Mf : ℝ) + |gamma| / (Mf : ℝ) := by
            rw [hstep_eq]
      _ ≤ τ / (Mf : ℝ) := by
            have hsum :
                pathFollowingCenteringBeta τ + |gamma| ≤ τ := by
              calc
                pathFollowingCenteringBeta τ + |gamma| ≤
                    pathFollowingCenteringBeta τ + pathFollowingGammaRadius τ := by
                      gcongr
                _ = τ := by
                      simp [pathFollowingGammaRadius]
            simpa [add_div] using
              (div_le_div_of_nonneg_right hsum (le_of_lt hMf_pos))
  have hscaled : (Mf : ℝ) * δ ≤ τ := by
    simpa [mul_comm] using (le_div_iff₀ hMf_pos).mp hδ_le_tau_div
  have hsmall :
      let δ := ndec(ψ, y, (Mf : NNReal), hy, hH)
      (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤ 1 := by
    simpa [δ] using
      pathFollowingIntermediateSmallness_of_scaled_le_half hδ_nonneg hscaled htau
  rw [pathFollowingUpdate_snd]
  simpa [tPlus, ψ] using
    (intermediateNewtonNextPoint_mem_of_smallness hy hH hsmall)

/-- Helper for Lemma 5.2.2: each affine interpolation point `x + τ • (y - x)` belongs to the
closed segment from `x` to `y`. -/
private theorem segmentPoint_mem_segment
    {x y : E} {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    x + τ • (y - x) ∈ segment ℝ x y := by
  -- Rewrite the affine segment point into the canonical convex-combination parameterization.
  rw [segment_eq_image_lineMap]
  refine ⟨τ, hτ, ?_⟩
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Lemma 5.2.2: affine lines differentiate to their direction vector. -/
private theorem line_hasDerivAt
    (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Lemma 5.2.2: self-concordance provides continuity of the Hessian on `dom`. -/
private theorem hessianContinuousOn
    {F : E → ℝ} (hself : IsSelfConcordantOnWith dom (Mf : NNReal) F) :
    ContinuousOn (hessian F) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ F) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ F) dom :=
      (hself.contDiffOn.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_of_isOpen
          hself.isOpen_domain
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  -- Differentiate the gradient once more on the open domain to reach the Hessian field.
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen
      hself.isOpen_domain
      (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn

/-- Helper for Lemma 5.2.2: scalarizing the gradient along an affine line differentiates to the
corresponding Hessian pairing. -/
private theorem scalarizedGradientLine_hasDerivAt
    {F : E → ℝ} (hself : IsSelfConcordantOnWith dom (Mf : NNReal) F)
    {x d u : E} {t : ℝ} (hxt : x + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ F (x + s • d)) u)
      (inner ℝ (hessian F (x + t • d) d) u) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ F) (x + t • d) := by
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ F) (x + t • d) :=
      (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hxt)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 3)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ F) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ F (x + s • d))
        ((hessian F (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the gradient derivative with the affine-line derivative.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ F (x + s • d)))
        (φ.comp ((hessian F (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional to obtain the one-dimensional derivative.
    simpa [φ] using (φ.hasFDerivAt.comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Lemma 5.2.2: integrating the Hessian along the segment from `x` to `y` recovers
the scalarized gradient increment. -/
private theorem gradientDifferencePairing_eq_averageHessianStep
    {F : E → ℝ} (hself : IsSelfConcordantOnWith dom (Mf : NNReal) F)
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    let d := y - x
    let G := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • d)
    inner ℝ (∇ F y - ∇ F x) u = inner ℝ (G d) u := by
  let d : E := y - x
  let H : ℝ → E →L[ℝ] E := fun τ ↦ hessian F (x + τ • d)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, H τ
  have hHessCont : ContinuousOn (hessian F) dom := hessianContinuousOn hself
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hline_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • d) (Set.Icc (0 : ℝ) 1) dom := by
    intro τ hτ
    exact hsegment_dom (segmentPoint_mem_segment hτ)
  have hH_cont : ContinuousOn H (Set.Icc (0 : ℝ) 1) := by
    -- Restrict the continuous Hessian field to the affine segment joining `x` and `y`.
    simpa [H, d] using
      hHessCont.comp
        (show Continuous (fun τ : ℝ ↦ x + τ • d) by continuity).continuousOn
        hline_maps
  have hH_int : IntervalIntegrable H MeasureTheory.volume 0 1 :=
    hH_cont.intervalIntegrable_of_Icc (by norm_num)
  have hH_apply_cont (v : E) : ContinuousOn (fun τ : ℝ ↦ H τ v) (Set.Icc (0 : ℝ) 1) := by
    let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E v
    simpa [H, ev] using ev.continuous.comp_continuousOn hH_cont
  have hH_apply_int (v : E) :
      IntervalIntegrable (fun τ : ℝ ↦ H τ v) MeasureTheory.volume 0 1 :=
    (hH_apply_cont v).intervalIntegrable_of_Icc (by norm_num)
  let g : ℝ → ℝ := fun τ ↦ inner ℝ (∇ F (x + τ • d)) u
  let θ : ℝ → ℝ := fun τ ↦ inner ℝ (H τ d) u
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    exact
      (scalarizedGradientLine_hasDerivAt hself (hline_maps hτ)).continuousAt.continuousWithinAt
  have hθ_int : IntervalIntegrable θ MeasureTheory.volume 0 1 := by
    have hθ_cont : ContinuousOn θ (Set.Icc (0 : ℝ) 1) := by
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
      simpa [θ, H, φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
        φ.continuous.comp_continuousOn (hH_apply_cont d)
    exact hθ_cont.intervalIntegrable_of_Icc (by norm_num)
  have hderiv :
      ∀ τ ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (θ τ) τ := by
    intro τ hτ
    simpa [g, θ, H] using
      scalarizedGradientLine_hasDerivAt hself (hline_maps (Set.mem_Icc_of_Ioo hτ))
  have hftc : ∫ τ in (0 : ℝ)..1, θ τ = g 1 - g 0 := by
    simpa using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (show (0 : ℝ) ≤ 1 by norm_num) hg_cont hderiv hθ_int
  have hpair_integral : ∫ τ in (0 : ℝ)..1, θ τ = inner ℝ u (G d) := by
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
    calc
      ∫ τ in (0 : ℝ)..1, θ τ = ∫ τ in (0 : ℝ)..1, φ (H τ d) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro τ
        simp [θ, φ, InnerProductSpace.toDual_apply_apply, real_inner_comm]
      _ = φ (∫ τ in (0 : ℝ)..1, H τ d) := by
        exact ContinuousLinearMap.intervalIntegral_comp_comm φ (hH_apply_int d)
      _ = inner ℝ u (∫ τ in (0 : ℝ)..1, H τ d) := by
        simp [φ, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ u (G d) := by
        rw [ContinuousLinearMap.intervalIntegral_apply hH_int d]
  -- The scalar fundamental theorem of calculus turns the gradient increment into the average
  -- Hessian applied to the segment displacement.
  calc
    inner ℝ (∇ F y - ∇ F x) u = g 1 - g 0 := by
      rw [inner_sub_left]
      simp [g, d]
    _ = ∫ τ in (0 : ℝ)..1, θ τ := by
      symm
      exact hftc
    _ = inner ℝ u (G d) := hpair_integral
    _ = inner ℝ (G d) u := real_inner_comm _ _

/-- Helper for Lemma 5.2.2: subtracting symmetric operators preserves symmetry. -/
private theorem hessianDifference_isSymmetric
    {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (A - B).IsSymmetric := by
  -- Rewrite the pairing of the difference termwise and use symmetry on each summand.
  intro s t
  calc
    inner ℝ ((A - B) s) t = inner ℝ (A s) t - inner ℝ (B s) t := by
      simp [inner_sub_left]
    _ = inner ℝ s (A t) - inner ℝ s (B t) := by
      rw [show inner ℝ (A s) t = inner ℝ s (A t) by simpa using hA s t]
      rw [show inner ℝ (B s) t = inner ℝ s (B t) by simpa using hB s t]
    _ = inner ℝ s ((A - B) t) := by
      simp [inner_sub_right]

/-- Helper for Lemma 5.2.2: Loewner order is preserved after adding the same operator on the
right. -/
private theorem loewnerAddRight
    {A B C : E →L[ℝ] E} (h : A ≤ B) :
    A + C ≤ B + C := by
  -- Move to the positivity definition and cancel the common right summand.
  have h' : (B - A).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using h
  change ((B + C) - (A + C)).IsPositive
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'

/-- Helper for Lemma 5.2.2: a nonnegative scalar preserves Loewner order on Hessian-type
operators. -/
private theorem loewnerSmul_mono_of_nonneg
    {A : E →L[ℝ] E} (hA : 0 ≤ A) {a b : ℝ} (hab : a ≤ b) :
    a • A ≤ b • A := by
  have hA' : A.IsPositive := by
    simpa [ContinuousLinearMap.le_def] using hA
  have hba_nonneg : 0 ≤ b - a := by
    linarith
  -- Scale the positive operator `A` by the nonnegative gap `b - a`.
  rw [ContinuousLinearMap.le_def]
  simpa [sub_smul] using hA'.smul_of_nonneg hba_nonneg

/-- Helper for Lemma 5.2.2: an operator sandwiched between `± c ∇²F(x)` has Hessian-metric
operator norm at most `c`. -/
private theorem absInner_le_mul_localNorm_ofOperatorSandwich
    {F : E → ℝ} {x u v : E} (hPos : (hessian F x).IsPositive) (K : E →L[ℝ] E) {c : ℝ}
    (hc : 0 ≤ c) (hK_symm : K.IsSymmetric)
    (hlower : -(c • hessian F x) ≤ K) (hupper : K ≤ c • hessian F x) :
    |inner ℝ v (K u)| ≤ c * ‖v‖[F; x] * ‖u‖[F; x] := by
  let H := hessian F x
  have hH_symm : H.IsSymmetric := hPos.isSymmetric
  have hminus_pos : (c • H - K).IsPositive := by
    rw [← ContinuousLinearMap.le_def]
    exact hupper
  have hplus_pos : (c • H + K).IsPositive := by
    have htmp : (K - -(c • H)).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hlower
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
  have hu_quad_nonneg : 0 ≤ c * inner ℝ u (H u) := by
    exact mul_nonneg hc (hPos.inner_nonneg_right u)
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ v (K u) - t ^ (2 : ℕ) * (c * inner ℝ u (H u)) ≤
          c * inner ℝ v (H v) := by
    intro t
    have hsum_nonneg :
        0 ≤
          inner ℝ (v - t • u) ((c • H + K) (v - t • u)) +
            inner ℝ (v + t • u) ((c • H - K) (v + t • u)) := by
      exact add_nonneg (hplus_pos.inner_nonneg_right (v - t • u))
        (hminus_pos.inner_nonneg_right (v + t • u))
    have hHu : inner ℝ u (H v) = inner ℝ v (H u) := by
      simpa [real_inner_comm] using hH_symm v u
    have hKu : inner ℝ u (K v) = inner ℝ v (K u) := by
      simpa [real_inner_comm] using hK_symm v u
    have hsum_formula :
        inner ℝ (v - t • u) ((c • H + K) (v - t • u)) +
            inner ℝ (v + t • u) ((c • H - K) (v + t • u)) =
          2 * c * inner ℝ v (H v) - 4 * t * inner ℝ v (K u) +
            2 * t ^ (2 : ℕ) * (c * inner ℝ u (H u)) := by
      simp [H, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, ContinuousLinearMap.map_add,
        ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul, hHu, hKu, pow_two]
      ring
    rw [hsum_formula] at hsum_nonneg
    nlinarith
  have hsq_raw :
      (inner ℝ v (K u)) ^ (2 : ℕ) ≤
        (c * inner ℝ u (H u)) * (c * inner ℝ v (H v)) := by
    have hsq :
        (inner ℝ v (K u)) ^ (2 : ℕ) ≤
          (c * inner ℝ u (H u)) * (c * inner ℝ v (H v)) :=
      sq_le_mul_of_quadratic_family hu_quad_nonneg hline
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsq
  have hu_sq : ‖u‖[F; x] ^ (2 : ℕ) = inner ℝ u (H u) := by
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt (hPos.inner_nonneg_right u)
  have hv_sq : ‖v‖[F; x] ^ (2 : ℕ) = inner ℝ v (H v) := by
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt (hPos.inner_nonneg_right v)
  have hsq_abs :
      |inner ℝ v (K u)| ^ (2 : ℕ) ≤
        (c * ‖v‖[F; x] * ‖u‖[F; x]) ^ (2 : ℕ) := by
    calc
      |inner ℝ v (K u)| ^ (2 : ℕ) = (inner ℝ v (K u)) ^ (2 : ℕ) := by
        rw [sq_abs]
      _ ≤ (c * inner ℝ u (H u)) * (c * inner ℝ v (H v)) := hsq_raw
      _ = c ^ (2 : ℕ) * (‖v‖[F; x] ^ (2 : ℕ) * ‖u‖[F; x] ^ (2 : ℕ)) := by
        rw [hu_sq, hv_sq]
        ring
      _ = (c * ‖v‖[F; x] * ‖u‖[F; x]) ^ (2 : ℕ) := by
        ring
  have hright_nonneg : 0 ≤ c * ‖v‖[F; x] * ‖u‖[F; x] := by
    exact mul_nonneg (mul_nonneg hc (hessianLocalNorm_nonneg F x v))
      (hessianLocalNorm_nonneg F x u)
  exact le_of_sq_le_sq hsq_abs hright_nonneg

/-- Helper for Lemma 5.2.2: the inverse-Hessian witness simultaneously realizes the local norm
and the squared dual norm on the same positive-definite Hessian surface. -/
private theorem inverseHessianWitness_localNorm_eq_dual_and_pairing_ofPosDefMem
    {F : E → ℝ} [HasPositiveDefiniteHessianOn dom F]
    {x : E} (hx : x ∈ dom) (k : E) :
    let H := hessian F x
    let w := H.inverse k
    ‖w‖[F; x] = HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E k) ∧
      inner ℝ k w =
        (HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E k)) ^ (2 : ℕ) := by
  let H := hessian F x
  let w := H.inverse k
  let hPos : H.IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx
  let hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero
    (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx)
  have hHw : H w = k := by
    dsimp [H, w]
    exact hInv.self_apply_inverse k
  have hpair_nonneg : 0 ≤ inner ℝ k w := by
    -- Rewrite the positive Hessian quadratic form of `w` as the inverse-Hessian pairing.
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ k w := by
        rw [hHw, real_inner_comm]
  refine ⟨?_, ?_⟩
  · -- The local norm of the inverse-Hessian witness is the corresponding dual norm.
    rw [hessianLocalNorm_def, HessianDualLocalNorm.ofPosDefMem_def]
    have hinner : inner ℝ w (H w) = inner ℝ k w := by
      rw [hHw, real_inner_comm]
    simpa [H, w, InnerProductSpace.toDual_apply_apply] using congrArg Real.sqrt hinner
  · -- Squaring that dual norm recovers the same inverse-Hessian pairing.
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    simpa [H, w, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      (Real.sq_sqrt hpair_nonneg).symm

/-- Helper for Lemma 5.2.2: once the next point stays in the domain, the new gradient splits into
the transported old gradient plus the averaged-Hessian residual. -/
private theorem nextGradient_eq_oldGradient_plus_averageResidual
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    (variant : SelfConcordantNewtonVariant) {x : E} (hx : x ∈ dom)
    (hH : (hessian F x).det ≠ 0)
    (hxPlus :
      let xPlus := selfConcordantNewtonNextPoint F (Mf : NNReal) variant x hx hH
      xPlus ∈ dom) :
    let α := selfConcordantNewtonStepSize F (Mf : NNReal) variant x hx hH
    let xPlus := selfConcordantNewtonNextPoint F (Mf : NNReal) variant x hx hH
    let H := hessian F x
    let u := H.inverse (∇ F x)
    let G := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (xPlus - x))
    ∇ F xPlus = (1 - α) • ∇ F x + α • ((H - G) u) := by
  let α := selfConcordantNewtonStepSize F (Mf : NNReal) variant x hx hH
  let xPlus := selfConcordantNewtonNextPoint F (Mf : NNReal) variant x hx hH
  let H : E →L[ℝ] E := hessian F x
  let u : E := H.inverse (∇ F x)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (xPlus - x))
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  have hxPlus' : xPlus ∈ dom := by
    simpa [xPlus] using hxPlus
  have hu : H u = ∇ F x := by
    -- The Newton direction is defined by the inverse Hessian at `x`.
    let hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero hH
    exact hInv.self_apply_inverse (∇ F x)
  have hsub :
      xPlus - x = -(α • u) := by
    -- Rewrite the canonical next point into the standard Newton displacement form.
    have hsub_raw :
        selfConcordantNewtonNextPoint F (Mf : NNReal) variant x hx hH - x =
          -(selfConcordantNewtonStepSize F (Mf : NNReal) variant x hx hH •
            (hessian F x).inverse (∇ F x)) :=
      nextPointSubEqNegStepSizeSmulInverseGradient variant hx hH
    simpa [α, xPlus, H, u] using hsub_raw
  apply (InnerProductSpace.toDual ℝ E).injective
  ext v
  have hpair :
      inner ℝ (∇ F xPlus - ∇ F x) v = inner ℝ (G (xPlus - x)) v := by
    simpa [xPlus, G] using
      gradientDifferencePairing_eq_averageHessianStep hself hx hxPlus'
  have hpair' :
      inner ℝ (∇ F xPlus) v = inner ℝ (∇ F x - α • (G u)) v := by
    have hpair_eq :
        inner ℝ (∇ F xPlus) v =
          inner ℝ (∇ F x) v + inner ℝ (G (xPlus - x)) v := by
      have hpair_expanded :
          inner ℝ (∇ F xPlus) v - inner ℝ (∇ F x) v = inner ℝ (G (xPlus - x)) v := by
        simpa [inner_sub_left] using hpair
      linarith
    -- Expand the gradient increment and replace the displacement by `-α • u`.
    calc
      inner ℝ (∇ F xPlus) v =
          inner ℝ (∇ F x) v + inner ℝ (G (xPlus - x)) v := hpair_eq
      _ = inner ℝ (∇ F x) v + inner ℝ (G (-(α • u))) v := by
        rw [hsub]
      _ = inner ℝ (∇ F x) v + inner ℝ (-α • (G u)) v := by
        simp
      _ = inner ℝ (∇ F x - α • (G u)) v := by
        simp [sub_eq_add_neg, inner_add_left, inner_smul_left, add_comm, add_left_comm,
          add_assoc]
  -- Identify the scalarized equality with the desired vector identity.
  calc
    inner ℝ (∇ F xPlus) v = inner ℝ (∇ F x - α • (G u)) v := hpair'
    _ = inner ℝ ((1 - α) • ∇ F x + α • ((H - G) u)) v := by
      rw [ContinuousLinearMap.sub_apply, hu]
      simp [sub_eq_add_neg, inner_add_left, inner_smul_left, add_comm, add_left_comm,
        add_assoc]
      ring

/-- Helper for Lemma 5.2.2: the averaged-Hessian residual is controlled in scalar pairings by the
standard factor `a / (1 - a)` along an admissible Dikin segment. -/
private theorem averageHessianResidual_pairingBound
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u v : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let G := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (y - x))
    |inner ℝ v ((hessian F x - G) u)| ≤
      (a / (1 - a)) * ‖v‖[F; x] * ‖u‖[F; x] := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let hy : y ∈ dom := hself.openDikinEllipsoid_inv_constant_subset hx hxy
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian F x
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (y - x))
  let K : E →L[ℝ] E := H - G
  let c : ℝ := a / (1 - a)
  have hHessCont : ContinuousOn (hessian F) dom := hessianContinuousOn hself
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg F x (y - x)
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hH_nonneg : 0 ≤ H := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive H).2
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx)
  have hG_lower :
      (1 - a + a ^ (2 : ℕ) / 3) • H ≤ G := by
    -- Rewrite the averaged-Hessian lower bound into the fixed `H/G/a` spelling.
    simpa [a, r, G, H, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      hself.segmentAverageHessian_lower_bound hx hxy
  have hG_upper : G ≤ (1 / (1 - a)) • H := by
    -- Rewrite the averaged-Hessian upper bound into the same normal form.
    simpa [a, r, G, H, mul_assoc, mul_left_comm, mul_comm] using
      hself.segmentAverageHessian_upper_bound hx hxy
  have hG_symm : G.IsSymmetric := by
    let d : E := y - x
    let Hτ : ℝ → E →L[ℝ] E := fun τ ↦ hessian F (x + τ • d)
    have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
    have hHτ_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • d) (Set.Icc (0 : ℝ) 1) dom := by
      intro τ hτ
      exact hsegment_dom (segmentPoint_mem_segment hτ)
    have hHτ_cont : ContinuousOn Hτ (Set.Icc (0 : ℝ) 1) := by
      -- Restrict the continuous Hessian field to the affine segment used in the average.
      simpa [Hτ, d] using
        hHessCont.comp
          (show Continuous (fun τ : ℝ ↦ x + τ • d) by continuity).continuousOn
          hHτ_maps
    have hHτ_int : IntervalIntegrable Hτ MeasureTheory.volume 0 1 :=
      hHτ_cont.intervalIntegrable_of_Icc (by norm_num)
    have hHτ_apply_cont (w : E) : ContinuousOn (fun τ : ℝ ↦ Hτ τ w) (Set.Icc (0 : ℝ) 1) := by
      let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E w
      simpa [Hτ, ev] using ev.continuous.comp_continuousOn hHτ_cont
    have hHτ_apply_int (w : E) :
        IntervalIntegrable (fun τ : ℝ ↦ Hτ τ w) MeasureTheory.volume 0 1 :=
      (hHτ_apply_cont w).intervalIntegrable_of_Icc (by norm_num)
    have hpair_integral (s t : E) :
        ∫ τ in (0 : ℝ)..1, inner ℝ s (Hτ τ t) = inner ℝ s (G t) := by
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) s
      calc
        ∫ τ in (0 : ℝ)..1, inner ℝ s (Hτ τ t) =
            ∫ τ in (0 : ℝ)..1, φ (Hτ τ t) := by
              refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro τ
              simp [φ, Hτ, InnerProductSpace.toDual_apply_apply]
        _ = φ (∫ τ in (0 : ℝ)..1, Hτ τ t) := by
              exact ContinuousLinearMap.intervalIntegral_comp_comm φ (hHτ_apply_int t)
        _ = inner ℝ s (∫ τ in (0 : ℝ)..1, Hτ τ t) := by
              simp [φ, InnerProductSpace.toDual_apply_apply]
        _ = inner ℝ s (G t) := by
              rw [ContinuousLinearMap.intervalIntegral_apply hHτ_int t]
    intro s t
    calc
      inner ℝ (G s) t = inner ℝ t (G s) := real_inner_comm _ _
      _ = ∫ τ in (0 : ℝ)..1, inner ℝ t (Hτ τ s) := (hpair_integral t s).symm
      _ = ∫ τ in (0 : ℝ)..1, inner ℝ s (Hτ τ t) := by
            refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro τ hτ
            have hτIoc : τ ∈ Set.Ioc (0 : ℝ) 1 := by
              simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hτ
            have hτ' : τ ∈ Set.Icc (0 : ℝ) 1 := by
              exact ⟨le_of_lt hτIoc.1, hτIoc.2⟩
            have hz : x + τ • d ∈ dom := hHτ_maps hτ'
            have hzPos : (Hτ τ).IsPositive := by
              simpa [Hτ] using
                HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hz
            simpa [Hτ, real_inner_comm] using hzPos.isSymmetric s t
      _ = inner ℝ s (G t) := hpair_integral s t
  have hK_symm : K.IsSymmetric := by
    -- Symmetry is preserved when the symmetric Hessian average is subtracted from the symmetric
    -- base Hessian.
    exact hessianDifference_isSymmetric
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx).isSymmetric hG_symm
  have hlower : -(c • H) ≤ K := by
    -- The upper averaged-Hessian bound supplies the negative side of the symmetric sandwich.
    have hsum : H + c • H = (1 / (1 - a)) • H := by
      have hscalar : (1 : ℝ) + c = 1 / (1 - a) := by
        dsimp [c]
        field_simp [hfactor_pos.ne']
        ring
      calc
        H + c • H = ((1 : ℝ) + c) • H := by
          rw [add_smul, one_smul]
        _ = (1 / (1 - a)) • H := by
          rw [hscalar]
    have hmain : G ≤ H + c • H := by
      rw [hsum]
      exact hG_upper
    rw [ContinuousLinearMap.le_def]
    have hmain' : ((H + c • H) - G).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hmain
    simpa [K, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain'
  have hupper : K ≤ c • H := by
    -- The lower averaged-Hessian bound controls the positive side after one scalar comparison.
    have hscalar_le : (1 : ℝ) ≤ (1 - a + a ^ (2 : ℕ) / 3) + c := by
      dsimp [c]
      field_simp [hfactor_pos.ne']
      nlinarith [ha_nonneg, ha_lt_one]
    have hstep1 :
        (1 : ℝ) • H ≤ ((1 - a + a ^ (2 : ℕ) / 3) + c) • H := by
      exact loewnerSmul_mono_of_nonneg hH_nonneg hscalar_le
    have hstep2 :
        ((1 - a + a ^ (2 : ℕ) / 3) + c) • H =
          (1 - a + a ^ (2 : ℕ) / 3) • H + c • H := by
      rw [add_smul]
    have hstep3 :
        (1 - a + a ^ (2 : ℕ) / 3) • H + c • H ≤ G + c • H := by
      exact loewnerAddRight hG_lower
    have hmain : H ≤ G + c • H := by
      calc
        H = (1 : ℝ) • H := by simp
        _ ≤ ((1 - a + a ^ (2 : ℕ) / 3) + c) • H := hstep1
        _ = (1 - a + a ^ (2 : ℕ) / 3) • H + c • H := hstep2
        _ ≤ G + c • H := hstep3
    rw [ContinuousLinearMap.le_def]
    have hmain' : (G + c • H - H).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hmain
    simpa [K, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain'
  -- Reduce the averaged-Hessian residual to the operator sandwich estimate at the base point.
  simpa [a, r, G, H, K, c] using
    absInner_le_mul_localNorm_ofOperatorSandwich
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx) K hc_nonneg hK_symm
      hlower hupper

/-- Helper for Lemma 5.2.2: the averaged-Hessian residual is controlled in the base dual local
norm by the standard factor `a / (1 - a)`. -/
private theorem averageHessianResidual_baseDualBound
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let H := hessian F x
    let G := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (y - x))
    HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E ((H - G) u)) ≤
      (a / (1 - a)) * ‖u‖[F; x] := by
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian F x
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (y - x))
  let k : E := (H - G) u
  let δ : ℝ := HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E k)
  let w : E := H.inverse k
  have hw_realize : ‖w‖[F; x] = δ ∧ inner ℝ k w = δ ^ (2 : ℕ) := by
    -- The inverse-Hessian witness at `x` realizes both the base dual norm and its square.
    have hw_realize_raw :
        ‖H.inverse k‖[F; x] = HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E k) ∧
          inner ℝ k (H.inverse k) =
            (HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E k)) ^ (2 : ℕ) :=
      inverseHessianWitness_localNorm_eq_dual_and_pairing_ofPosDefMem hx k
    simpa [H, w, k, δ] using hw_realize_raw
  have hw_norm : ‖w‖[F; x] = δ := hw_realize.1
  have hpair_sq : inner ℝ k w = δ ^ (2 : ℕ) := hw_realize.2
  have hδ_nonneg : 0 ≤ δ := by
    rw [show δ = HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E k) by rfl]
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    exact Real.sqrt_nonneg _
  have hpair_nonneg : 0 ≤ inner ℝ k w := by
    rw [hpair_sq]
    positivity
  have hpair_bound :
      |inner ℝ w k| ≤ (a / (1 - a)) * ‖w‖[F; x] * ‖u‖[F; x] := by
    -- Apply the averaged-Hessian residual pairing estimate to the inverse-Hessian witness `w`.
    have hpair_bound_raw :
        |inner ℝ w ((hessian F x - ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (y - x))) u)| ≤
          ((Mf : ℝ) * ‖y - x‖[F; x] / (1 - (Mf : ℝ) * ‖y - x‖[F; x])) *
            ‖w‖[F; x] * ‖u‖[F; x] :=
      averageHessianResidual_pairingBound hx hxy
    simpa [H, G, k, a, r, real_inner_comm] using hpair_bound_raw
  by_cases hδ_zero : δ = 0
  · -- If the base dual norm vanishes, the desired bound is immediate.
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := by positivity
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg hMf_nonneg (hessianLocalNorm_nonneg F x (y - x))
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
    have ha_lt_one : a < 1 := by
      by_cases hMf_zero : (Mf : ℝ) = 0
      · simp [a, hMf_zero]
      · have hMf_pos : 0 < (Mf : ℝ) :=
            lt_of_le_of_ne hMf_nonneg (by simpa [eq_comm] using hMf_zero)
        dsimp [a]
        simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
    have hfactor_nonneg : 0 ≤ (a / (1 - a)) * ‖u‖[F; x] := by
      have hden_pos : 0 < 1 - a := by
        linarith
      exact mul_nonneg (div_nonneg ha_nonneg (le_of_lt hden_pos)) (hessianLocalNorm_nonneg F x u)
    change δ ≤ (a / (1 - a)) * ‖u‖[F; x]
    simpa [hδ_zero] using hfactor_nonneg
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (by simpa [eq_comm] using hδ_zero)
    have hsq_bound : δ ^ (2 : ℕ) ≤ (a / (1 - a)) * (δ * ‖u‖[F; x]) := by
      calc
        δ ^ (2 : ℕ) = inner ℝ k w := by
          symm
          exact hpair_sq
        _ = |inner ℝ k w| := by
          rw [abs_of_nonneg hpair_nonneg]
        _ = |inner ℝ w k| := by
          rw [real_inner_comm]
        _ ≤ (a / (1 - a)) * ‖w‖[F; x] * ‖u‖[F; x] := hpair_bound
        _ = (a / (1 - a)) * (δ * ‖u‖[F; x]) := by
          rw [hw_norm]
          ring
    -- Cancel the positive witness norm from the squared dual-norm bound.
    change δ ≤ (a / (1 - a)) * ‖u‖[F; x]
    nlinarith

/-- Helper for Lemma 5.2.2: pairing the averaged-Hessian residual against a fixed endpoint
witness is exactly the scalar segment integral of the pointwise residual. -/
private theorem averageHessianResidual_endpointWitnessIntegralRewrite
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) F)
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    let H := hessian F x
    let G := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (y - x))
    let k := (H - G) u
    inner ℝ w k =
      ∫ τ in (0 : ℝ)..1, inner ℝ w ((H - hessian F (x + τ • (y - x))) u) := by
  let d : E := y - x
  let H : E →L[ℝ] E := hessian F x
  let Hτ : ℝ → E →L[ℝ] E := fun τ ↦ hessian F (x + τ • d)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, Hτ τ
  let θ : ℝ → ℝ := fun τ ↦ inner ℝ w (Hτ τ u)
  have hHessCont : ContinuousOn (hessian F) dom := hessianContinuousOn hself
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hHτ_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • d) (Set.Icc (0 : ℝ) 1) dom := by
    intro τ hτ
    exact hsegment_dom (segmentPoint_mem_segment hτ)
  have hHτ_cont : ContinuousOn Hτ (Set.Icc (0 : ℝ) 1) := by
    -- Restrict the continuous Hessian field to the affine segment from `x` to `y`.
    simpa [Hτ, d] using
      hHessCont.comp
        (show Continuous (fun τ : ℝ ↦ x + τ • d) by continuity).continuousOn
        hHτ_maps
  have hHτ_int : IntervalIntegrable Hτ MeasureTheory.volume 0 1 :=
    hHτ_cont.intervalIntegrable_of_Icc (by norm_num)
  have hHτ_apply_cont (v : E) : ContinuousOn (fun τ : ℝ ↦ Hτ τ v) (Set.Icc (0 : ℝ) 1) := by
    let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E v
    simpa [Hτ, ev] using ev.continuous.comp_continuousOn hHτ_cont
  have hHτ_apply_int (v : E) :
      IntervalIntegrable (fun τ : ℝ ↦ Hτ τ v) MeasureTheory.volume 0 1 :=
    (hHτ_apply_cont v).intervalIntegrable_of_Icc (by norm_num)
  have hθ_int : IntervalIntegrable θ MeasureTheory.volume 0 1 := by
    -- Evaluating the Hessian field on `u` and pairing with `w` preserves integrability.
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
    simpa [θ, φ, InnerProductSpace.toDual_apply_apply] using
      φ.continuous.comp_continuousOn (hHτ_apply_cont u) |>.intervalIntegrable_of_Icc (by norm_num)
  have hpair_integral : ∫ τ in (0 : ℝ)..1, θ τ = inner ℝ w (G u) := by
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
    calc
      ∫ τ in (0 : ℝ)..1, θ τ = ∫ τ in (0 : ℝ)..1, φ (Hτ τ u) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro τ
        simp [θ, φ, InnerProductSpace.toDual_apply_apply]
      _ = φ (∫ τ in (0 : ℝ)..1, Hτ τ u) := by
        exact ContinuousLinearMap.intervalIntegral_comp_comm φ (hHτ_apply_int u)
      _ = inner ℝ w (∫ τ in (0 : ℝ)..1, Hτ τ u) := by
        simp [φ, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ w (G u) := by
        rw [ContinuousLinearMap.intervalIntegral_apply hHτ_int u]
  -- Expand the residual once so the endpoint witness pairing becomes a scalar integral.
  calc
    inner ℝ w ((H - G) u) = inner ℝ w (H u) - inner ℝ w (G u) := by
      simp [ContinuousLinearMap.sub_apply, inner_sub_right]
    _ = inner ℝ w (H u) - ∫ τ in (0 : ℝ)..1, θ τ := by
      rw [hpair_integral]
    _ = ∫ τ in (0 : ℝ)..1, (inner ℝ w (H u) - θ τ) := by
      symm
      simpa using
        intervalIntegral.integral_sub intervalIntegrable_const hθ_int
    _ = ∫ τ in (0 : ℝ)..1, inner ℝ w ((H - Hτ τ) u) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro τ
      simp [θ, ContinuousLinearMap.sub_apply, inner_sub_right]

/-- Helper for Lemma 5.2.2: the reciprocal-square scalar majorant integrates explicitly on
`[0, τ]`. -/
private theorem segmentReciprocalSquareIntegralUpto
    {a τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ha : a < 1) :
    ∫ s in (0 : ℝ)..τ, a * ((1 - s * a) ^ (2 : ℕ))⁻¹ = (τ * a) / (1 - τ * a) := by
  have hden : ∀ s ∈ Set.Icc (0 : ℝ) τ, 0 < 1 - s * a := by
    intro s hs
    by_cases ha_nonneg : 0 ≤ a
    · have hsa_le_ta : s * a ≤ τ * a := mul_le_mul_of_nonneg_right hs.2 ha_nonneg
      have hta_le_a : τ * a ≤ a := by
        simpa using (show τ * a ≤ 1 * a from mul_le_mul_of_nonneg_right hτ.2 ha_nonneg)
      linarith
    · have hsa_le_zero : s * a ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs.1 (le_of_not_ge ha_nonneg)
      linarith
  have hnum :
      ContinuousOn (fun s : ℝ ↦ (s * a) / (1 - s * a)) (Set.Icc (0 : ℝ) τ) := by
    refine
      (show ContinuousOn (fun s : ℝ ↦ s * a) (Set.Icc (0 : ℝ) τ) by
        exact (show Continuous (fun s : ℝ ↦ s * a) by continuity).continuousOn).div ?_ ?_
    · exact (show Continuous (fun s : ℝ ↦ 1 - s * a) by continuity).continuousOn
    · intro s hs
      exact (hden s hs).ne'
  have hint :
      IntervalIntegrable (fun s : ℝ ↦ a * ((1 - s * a) ^ (2 : ℕ))⁻¹)
        MeasureTheory.volume 0 τ := by
    have hcontInv :
        ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) τ) := by
      have hbase :
          ContinuousOn (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) τ) := by
        refine continuousOn_const.div ?_ ?_
        · exact (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
        · intro s hs
          exact pow_ne_zero 2 (hden s hs).ne'
      simpa [one_div] using hbase
    have hcont :
        ContinuousOn (fun s : ℝ ↦ a * ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) τ) := by
      simpa [mul_assoc] using continuous_const.continuousOn.mul hcontInv
    exact hcont.intervalIntegrable_of_Icc hτ.1
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) τ,
        HasDerivAt (fun s : ℝ ↦ (s * a) / (1 - s * a))
          (a * ((1 - t * a) ^ (2 : ℕ))⁻¹) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) τ := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 - t * a ≠ 0 := (hden t ht').ne'
    have hnum_deriv : HasDerivAt (fun s : ℝ ↦ s * a) a t := by
      simpa [mul_comm] using (hasDerivAt_id t).mul_const a
    have hden_deriv : HasDerivAt (fun s : ℝ ↦ 1 - s * a) (-a) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot := hnum_deriv.div hden_deriv hden_ne
    have hslope :
        (a * (1 - t * a) - (t * a) * (-a)) / (1 - t * a) ^ (2 : ℕ) =
          a * ((1 - t * a) ^ (2 : ℕ))⁻¹ := by
      rw [show a * (1 - t * a) - (t * a) * (-a) = a by ring]
      rw [div_eq_mul_inv]
    exact hquot.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1 hnum hderiv hint
  calc
    ∫ s in (0 : ℝ)..τ, a * ((1 - s * a) ^ (2 : ℕ))⁻¹ =
        ((τ * a) / (1 - τ * a)) - ((0 : ℝ) * a / (1 - 0 * a)) := by
          simpa using hftc
    _ = (τ * a) / (1 - τ * a) := by ring

/-- Helper for Lemma 5.2.2: the same reciprocal-square kernel integrates explicitly on a short
interval `[s, τ]`, which is the scalar normalization needed by the primitive-drop route. -/
private theorem segmentReciprocalSquareIntegralBetween
    {a τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) (ha : a < 1) :
    ∫ t in s..τ, a * ((1 - t * a) ^ (2 : ℕ))⁻¹ =
      ((τ - s) * a) / ((1 - τ * a) * (1 - s * a)) := by
  have hden : ∀ t ∈ Set.Icc s τ, 0 < 1 - t * a := by
    intro t ht
    by_cases ha_nonneg : 0 ≤ a
    · have hta_le_τa : t * a ≤ τ * a := mul_le_mul_of_nonneg_right ht.2 ha_nonneg
      have hτa_le_a : τ * a ≤ a := by
        simpa using (show τ * a ≤ 1 * a from mul_le_mul_of_nonneg_right hτ.2 ha_nonneg)
      linarith
    · have hta_le_zero : t * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_trans hs.1 ht.1)
        (le_of_not_ge ha_nonneg)
      linarith
  have hnum :
      ContinuousOn (fun t : ℝ ↦ (t * a) / (1 - t * a)) (Set.Icc s τ) := by
    refine
      (show ContinuousOn (fun t : ℝ ↦ t * a) (Set.Icc s τ) by
        exact (show Continuous (fun t : ℝ ↦ t * a) by continuity).continuousOn).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 - t * a) by continuity).continuousOn
    · intro t ht
      exact (hden t ht).ne'
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ a * ((1 - t * a) ^ (2 : ℕ))⁻¹)
        MeasureTheory.volume s τ := by
    have hcontInv :
        ContinuousOn (fun t : ℝ ↦ ((1 - t * a) ^ (2 : ℕ))⁻¹) (Set.Icc s τ) := by
      have hbase :
          ContinuousOn (fun t : ℝ ↦ (1 : ℝ) / (1 - t * a) ^ (2 : ℕ)) (Set.Icc s τ) := by
        refine continuousOn_const.div ?_ ?_
        · exact (show Continuous (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) by continuity).continuousOn
        · intro t ht
          exact pow_ne_zero 2 (hden t ht).ne'
      simpa [one_div] using hbase
    have hcont :
        ContinuousOn (fun t : ℝ ↦ a * ((1 - t * a) ^ (2 : ℕ))⁻¹) (Set.Icc s τ) := by
      simpa [mul_assoc] using continuous_const.continuousOn.mul hcontInv
    exact hcont.intervalIntegrable_of_Icc hs.2
  have hderiv :
      ∀ t ∈ Set.Ioo s τ,
        HasDerivAt (fun t : ℝ ↦ (t * a) / (1 - t * a))
          (a * ((1 - t * a) ^ (2 : ℕ))⁻¹) t := by
    intro t ht
    have ht' : t ∈ Set.Icc s τ := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 - t * a ≠ 0 := (hden t ht').ne'
    have hnum_deriv : HasDerivAt (fun x : ℝ ↦ x * a) a t := by
      simpa [mul_comm] using (hasDerivAt_id t).mul_const a
    have hden_deriv : HasDerivAt (fun x : ℝ ↦ 1 - x * a) (-a) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot := hnum_deriv.div hden_deriv hden_ne
    have hslope :
        (a * (1 - t * a) - (t * a) * (-a)) / (1 - t * a) ^ (2 : ℕ) =
          a * ((1 - t * a) ^ (2 : ℕ))⁻¹ := by
      field_simp [hden_ne]
      ring
    exact hquot.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.2 hnum hderiv hint
  have hτden : 1 - τ * a ≠ 0 := (hden τ ⟨hs.2, le_rfl⟩).ne'
  have hsden : 1 - s * a ≠ 0 := (hden s ⟨le_rfl, hs.2⟩).ne'
  have hsden' : 1 - a * s ≠ 0 := by
    simpa [mul_comm] using hsden
  calc
    ∫ t in s..τ, a * ((1 - t * a) ^ (2 : ℕ))⁻¹ =
        (τ * a) / (1 - τ * a) - (s * a) / (1 - s * a) := by
          simpa using hftc
    _ = ((τ - s) * a) / ((1 - τ * a) * (1 - s * a)) := by
          field_simp [hτden, hsden, hsden']
          ring

/-- Helper for Lemma 5.2.2: scalarizing the Hessian along an affine segment is continuous on
every closed subinterval of that segment. -/
private theorem scalarizedHessianLineContinuousOn
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) F)
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let d := y - x
    let ψ : ℝ → ℝ := fun t ↦ inner ℝ w (hessian F (x + t • d) u)
    ContinuousOn ψ (Set.Icc s τ) := by
  dsimp
  let d : E := y - x
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ w (hessian F (x + t • d) u)
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hline_maps : Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Icc s τ) dom := by
    intro t ht
    exact hsegment_dom <|
      segmentPoint_mem_segment
        ⟨le_trans hs.1 ht.1, le_trans ht.2 hτ.2⟩
  let Hs : ℝ → E →L[ℝ] E := fun t ↦ hessian F (x + t • d)
  have hHs_cont : ContinuousOn Hs (Set.Icc s τ) := by
    -- Restrict the continuous Hessian field to the affine tail segment.
    simpa [Hs, d] using
      (hessianContinuousOn (F := F) hself).comp
        (show Continuous (fun t : ℝ ↦ x + t • d) by continuity).continuousOn
        hline_maps
  let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E u
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
  -- Evaluating at `u` and pairing with the fixed witness preserves continuity.
  simpa [ψ, Hs, ev, φ, InnerProductSpace.toDual_apply_apply] using
    φ.continuous.comp_continuousOn (ev.continuous.comp_continuousOn hHs_cont)

/-- Helper for Lemma 5.2.2: a `C³` objective yields a Fréchet derivative for the Hessian field at
every point. -/
private theorem hessianHasFDerivAtOfContDiffAt
    {F : E → ℝ} {x : E} (hcontAt : ContDiffAt ℝ 3 F x) :
    HasFDerivAt (hessian F) (fderiv ℝ (hessian F) x) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ F) x := by
    -- First differentiate `F` once and keep the two remaining derivatives.
    exact hcontAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ F) x := by
    -- Rewrite the gradient through the Riesz map before differentiating again.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp x hfderiv_C2
  have hhessian_C1 : ContDiffAt ℝ 1 (hessian F) x := by
    -- One more derivative of the gradient is exactly the Hessian owner.
    simpa [hessian] using
      hgrad_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  -- Convert the `C¹` regularity of the Hessian map into the required Fréchet derivative.
  exact (hhessian_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt

/-- Helper for Lemma 5.2.2: scalarizing the third-derivative line along an affine segment is
continuous on every closed subinterval of that segment. -/
private theorem scalarizedHessianLineDerivContinuousOn
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) F)
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let d := y - x
    let θ : ℝ → ℝ := fun t ↦ inner ℝ w ((fderiv ℝ (hessian F) (x + t • d) d) u)
    ContinuousOn θ (Set.Icc s τ) := by
  dsimp
  let d : E := y - x
  let θ : ℝ → ℝ := fun t ↦ inner ℝ w ((fderiv ℝ (hessian F) (x + t • d) d) u)
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hline_maps : Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Icc s τ) dom := by
    intro t ht
    exact hsegment_dom <|
      segmentPoint_mem_segment
        ⟨le_trans hs.1 ht.1, le_trans ht.2 hτ.2⟩
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfd_C2 : ContDiffOn ℝ 2 (fderiv ℝ F) dom :=
    hself.contDiffOn.fderiv_of_isOpen
      hself.isOpen_domain
      (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffOn ℝ 2 (∇ F) dom := by
    -- Rewrite the gradient through the Riesz map before differentiating again on `dom`.
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd_C2
  have hhessian_C1 : ContDiffOn ℝ 1 (hessian F) dom := by
    -- One more derivative produces a `C¹` Hessian field on the self-concordant domain.
    simpa [hessian] using
      hgrad_C2.fderiv_of_isOpen
        hself.isOpen_domain
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hhessianDeriv_cont : ContinuousOn (fderiv ℝ (hessian F)) dom := by
    -- The derivative of the Hessian field is continuous because the Hessian is `C¹`.
    exact
      (hhessian_C1.fderiv_of_isOpen
        hself.isOpen_domain
        (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn
  have hlineDeriv_cont :
      ContinuousOn (fun t : ℝ ↦ fderiv ℝ (hessian F) (x + t • d)) (Set.Icc s τ) := by
    -- Pull the continuous Hessian derivative back to the same affine tail segment.
    simpa [d] using
      hhessianDeriv_cont.comp
        (show Continuous (fun t : ℝ ↦ x + t • d) by continuity).continuousOn
        hline_maps
  let evd : (E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
    ContinuousLinearMap.apply ℝ (E →L[ℝ] E) d
  let evu : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E u
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
  -- Evaluate the third-derivative operator on `d`, then on `u`, then pair with `w`.
  change
    ContinuousOn
      (fun t : ℝ ↦ inner ℝ w ((fderiv ℝ (hessian F) (x + t • d) d) u))
      (Set.Icc s τ)
  simpa [θ, evd, evu, φ, InnerProductSpace.toDual_apply_apply] using
    φ.continuous.comp_continuousOn
      (evu.continuous.comp_continuousOn (evd.continuous.comp_continuousOn hlineDeriv_cont))

/-- Helper for Lemma 5.2.2: scalarizing the Hessian along an affine line differentiates to the
corresponding third-derivative pairing. -/
private theorem scalarizedHessianLineHasDerivAt
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) F)
    {x d u w : E} {t : ℝ} (hxt : x + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ w (hessian F (x + s • d) u))
      (inner ℝ w ((fderiv ℝ (hessian F) (x + t • d) d) u)) t := by
  have hcontAt : ContDiffAt ℝ 3 F (x + t • d) := by
    exact hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hxt)
  have hhessianDeriv :
      HasFDerivAt (hessian F) (fderiv ℝ (hessian F) (x + t • d)) (x + t • d) := by
    -- Upgrade the pointwise `C³` regularity of `F` to a derivative of the Hessian field.
    exact hessianHasFDerivAtOfContDiffAt (F := F) (x := x + t • d) hcontAt
  have happly :
      HasDerivAt (fun s : ℝ ↦ hessian F (x + s • d) u)
        ((fderiv ℝ (hessian F) (x + t • d) d) u) t := by
    -- Differentiate the Hessian field along the affine line and then evaluate it on `u`.
    have happlyF :
        HasFDerivAt (fun z : E ↦ hessian F z u)
          ((ContinuousLinearMap.apply ℝ E u).comp (fderiv ℝ (hessian F) (x + t • d)))
          (x + t • d) := by
      exact (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp (x + t • d) hhessianDeriv
    simpa using happlyF.comp_hasDerivAt t (line_hasDerivAt x d t)
  have hinnerF :
      HasFDerivAt (fun z : E ↦ inner ℝ w z) ((innerSL ℝ) w) (hessian F (x + t • d) u) := by
    -- Postcompose the vector-valued Hessian slice with the fixed linear functional `inner w`.
    simpa using ((innerSL ℝ) w).hasFDerivAt
  simpa using hinnerF.comp_hasDerivAt t happly

/-- Helper for Lemma 5.2.2: differentiating the fixed-endpoint weighted tail gap produces the
normalized numerator used by the sharp fixed-`τ` endpoint route. -/
private theorem weightedEndpointWitnessTailGapHasDerivAt
    {a τ s : ℝ} {ψ : ℝ → ℝ} {ψ' : ℝ}
    (hden : 1 - s * a ≠ 0)
    (hψ : HasDerivAt ψ ψ' s) :
    HasDerivAt
      (fun t : ℝ ↦ ((1 - τ * a) / (1 - t * a)) * (ψ t - ψ τ))
      (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
        (a * (ψ s - ψ τ) + (1 - s * a) * ψ')) s := by
  have hnum_deriv : HasDerivAt (fun t : ℝ ↦ (1 - τ * a)) 0 s := by
    -- The numerator of the rational weight is constant in the differentiation variable.
    simpa using (hasDerivAt_const s (1 - τ * a))
  have hden_deriv : HasDerivAt (fun t : ℝ ↦ 1 - t * a) (-a) s := by
    -- Differentiate the affine denominator before the single quotient-rule step.
    convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).mul_const a) using 1
    ring
  have hweight :
      HasDerivAt (fun t : ℝ ↦ ((1 - τ * a) / (1 - t * a)))
        (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) s := by
    have hquot := hnum_deriv.div hden_deriv hden
    have hslope :
        (0 * (1 - s * a) - (1 - τ * a) * (-a)) / (1 - s * a) ^ (2 : ℕ) =
          (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
      field_simp [hden]
      ring
    exact hquot.congr_deriv hslope
  have hgap :
      HasDerivAt (fun t : ℝ ↦ ψ t - ψ τ) ψ' s := by
    -- The weighted tail gap subtracts a fixed endpoint value.
    exact hψ.sub_const (ψ τ)
  have hmul := hweight.mul hgap
  have hslope :
      (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ s - ψ τ) +
          ((1 - τ * a) / (1 - s * a)) * ψ' =
        (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
          (a * (ψ s - ψ τ) + (1 - s * a) * ψ')) := by
    field_simp [hden]
  -- Rewrite the product-rule slope into the single weighted tail-gap numerator.
  exact hmul.congr_deriv hslope

/-- Helper for Lemma 5.2.2: integrating the derivative of the scalar weight
`((1 - τ * a) * (s * a)) / (1 - s * a)` against a tail-gap primitive collapses to a single live
integrand on `[0, τ]`. -/
private theorem scalarTailKernelByParts
    {a τ : ℝ} {Θ J : ℝ → ℝ} (hτ : 0 ≤ τ)
    (hJ_cont : ContinuousOn J (Set.Icc (0 : ℝ) τ))
    (hJ_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) τ, HasDerivAt J (-Θ s) s)
    (hJτ : J τ = 0)
    (hΘ_int : IntervalIntegrable Θ MeasureTheory.volume 0 τ)
    (hden : ∀ s ∈ Set.Icc (0 : ℝ) τ, 0 < 1 - s * a) :
    ∫ s in (0 : ℝ)..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
      =
        ∫ s in (0 : ℝ)..τ, (((1 - τ * a) * (s * a)) / (1 - s * a)) * Θ s := by
  let g : ℝ → ℝ := fun s ↦ (((1 - τ * a) * (s * a)) / (1 - s * a))
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) τ) := by
    refine ((continuous_const.mul (continuous_id.mul_const a)).continuousOn).div ?_ ?_
    · exact (show Continuous (fun s : ℝ ↦ 1 - s * a) by continuity).continuousOn
    · intro s hs
      exact (hden s hs).ne'
  have hg_deriv :
      ∀ s ∈ Set.Ioo (0 : ℝ) τ,
        HasDerivAt g ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) s := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) τ := Set.mem_Icc_of_Ioo hs
    have hden_ne : 1 - s * a ≠ 0 := (hden s hs').ne'
    have hnum_deriv :
        HasDerivAt (fun t : ℝ ↦ (1 - τ * a) * (t * a)) ((1 - τ * a) * a) s := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ((hasDerivAt_id s).mul_const a).const_mul (1 - τ * a)
    have hden_deriv : HasDerivAt (fun t : ℝ ↦ 1 - t * a) (-a) s := by
      -- Differentiate the affine denominator before the single quotient-rule step.
      convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).mul_const a) using 1
      ring
    have hquot := hnum_deriv.div hden_deriv hden_ne
    have hslope :
        (((1 - τ * a) * a) * (1 - s * a) - ((1 - τ * a) * (s * a)) * (-a)) /
            (1 - s * a) ^ (2 : ℕ)
          =
            (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
      field_simp [hden_ne]
      ring
    -- Collapse the quotient-rule numerator to the reciprocal-square scalar kernel.
    exact hquot.congr_deriv hslope
  have hkernel_int :
      IntervalIntegrable
        (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s)
        MeasureTheory.volume 0 τ := by
    have hcont :
        ContinuousOn
          (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s)
          (Set.Icc (0 : ℝ) τ) := by
      have hinv :
          ContinuousOn
            (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
            (Set.Icc (0 : ℝ) τ) := by
        have hpow_inv :
            ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) τ) := by
          have hbase :
              ContinuousOn
                (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) τ) := by
            refine continuousOn_const.div ?_ ?_
            · exact
                (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
            · intro s hs
              exact pow_ne_zero 2 ((hden s hs).ne')
          simpa [one_div] using hbase
        simpa [mul_assoc] using ((continuous_const.mul continuous_const).continuousOn.mul hpow_inv)
      exact hinv.mul hJ_cont
    exact hcont.intervalIntegrable_of_Icc hτ
  have hJ_deriv' :
      ∀ s ∈ Set.Ioo (min (0 : ℝ) τ) (max (0 : ℝ) τ), HasDerivAt J (-Θ s) s := by
    simpa [min_eq_left hτ, max_eq_right hτ] using hJ_deriv
  have hg_cont' : ContinuousOn g (Set.uIcc (0 : ℝ) τ) := by
    simpa [Set.uIcc_of_le hτ] using hg_cont
  have hJ_cont' : ContinuousOn J (Set.uIcc (0 : ℝ) τ) := by
    simpa [Set.uIcc_of_le hτ] using hJ_cont
  have hg_deriv' :
      ∀ s ∈ Set.Ioo (min (0 : ℝ) τ) (max (0 : ℝ) τ),
        HasDerivAt g ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) s := by
    simpa [min_eq_left hτ, max_eq_right hτ] using hg_deriv
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hg_cont' hJ_cont' hg_deriv' hJ_deriv'
      (by
        have hcont :
            ContinuousOn (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
              (Set.Icc (0 : ℝ) τ) := by
          have hpow_inv :
              ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) τ) := by
            have hbase :
                ContinuousOn
                  (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) τ) := by
              refine continuousOn_const.div ?_ ?_
              · exact
                  (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
              · intro s hs
                exact pow_ne_zero 2 ((hden s hs).ne')
            simpa [one_div] using hbase
          simpa [mul_assoc] using
            ((continuous_const.mul continuous_const).continuousOn.mul hpow_inv)
        exact hcont.intervalIntegrable_of_Icc hτ)
      hΘ_int.neg
  have hg0 : g 0 = 0 := by
    simp [g]
  have hparts' :
      ∫ s in (0 : ℝ)..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
        =
          -∫ s in (0 : ℝ)..τ, g s * (-Θ s) := by
    -- The boundary terms vanish because the scalar weight is zero at `0` and the tail gap is
    -- zero at the fixed endpoint `τ`.
    have hτterm : g τ * J τ = 0 := by
      simp [g, hJτ]
    have hparts_zero :
        ∫ s in (0 : ℝ)..τ, g s * (-Θ s) =
          -∫ s in (0 : ℝ)..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s := by
      simpa [g, hg0, hτterm] using hparts
    simpa using (congrArg Neg.neg hparts_zero).symm
  calc
    ∫ s in (0 : ℝ)..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
        = -∫ s in (0 : ℝ)..τ, g s * (-Θ s) := hparts'
    _ = ∫ s in (0 : ℝ)..τ, g s * Θ s := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr ?_
      intro s hs
      ring
    _ = ∫ s in (0 : ℝ)..τ, (((1 - τ * a) * (s * a)) / (1 - s * a)) * Θ s := by
      rfl

/-- Helper for Lemma 5.2.2: evaluating the weighted tail gap at `0` rewrites the fixed endpoint
residual as one explicit integral shell before any sharp majorization is applied. -/
private theorem weightedTailGapEndpointIdentityAtZero
    {a τ : ℝ} {ψ θ : ℝ → ℝ}
    (hτ : 0 ≤ τ)
    (hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) τ))
    (hθ_cont : ContinuousOn θ (Set.Icc (0 : ℝ) τ))
    (hψ_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) τ, HasDerivAt ψ (θ s) s)
    (hden_pos : ∀ s ∈ Set.Icc (0 : ℝ) τ, 0 < 1 - s * a) :
    let ω : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * θ s
    (1 - τ * a) * (ψ 0 - ψ τ) =
      ∫ s in (0 : ℝ)..τ,
        ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s := by
  dsimp
  let ω : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * θ s
  let F : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * (ψ s - ψ τ)
  let integrand : ℝ → ℝ := fun s ↦
    ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s
  have hweight_cont :
      ContinuousOn (fun s : ℝ ↦ ((1 - τ * a) / (1 - s * a))) (Set.Icc (0 : ℝ) τ) := by
    -- The rational weight is continuous on the closed interval because the affine denominator
    -- never vanishes there.
    refine continuousOn_const.div ?_ ?_
    · exact (show Continuous (fun s : ℝ ↦ 1 - s * a) by continuity).continuousOn
    · intro s hs
      exact (hden_pos s hs).ne'
  have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) τ) := by
    -- Multiply the continuous weight by the continuous tail gap `ψ s - ψ τ`.
    exact hweight_cont.mul (hψ_cont.sub continuous_const.continuousOn)
  have hintegrand_cont : ContinuousOn integrand (Set.Icc (0 : ℝ) τ) := by
    have hkernel_cont :
        ContinuousOn
          (fun s : ℝ ↦
            (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s))
          (Set.Icc (0 : ℝ) τ) := by
      have hpow_inv :
          ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) τ) := by
        have hbase :
            ContinuousOn
              (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) τ) := by
          refine continuousOn_const.div ?_ ?_
          · exact
              (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
          · intro s hs
            exact pow_ne_zero 2 ((hden_pos s hs).ne')
        simpa [one_div] using hbase
      have hkernel_weight :
          ContinuousOn
            (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
            (Set.Icc (0 : ℝ) τ) := by
        simpa [mul_assoc] using
          (show ContinuousOn
            (fun s : ℝ ↦ ((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)
              (Set.Icc (0 : ℝ) τ) from continuous_const.continuousOn.mul hpow_inv)
      exact hkernel_weight.mul (continuous_const.continuousOn.sub hψ_cont)
    have hω_cont : ContinuousOn ω (Set.Icc (0 : ℝ) τ) := by
      -- The weighted derivative shell uses the same denominator control as `F`.
      exact hweight_cont.mul hθ_cont
    exact hkernel_cont.sub hω_cont
  have hintegrand_int : IntervalIntegrable integrand MeasureTheory.volume 0 τ :=
    hintegrand_cont.intervalIntegrable_of_Icc hτ
  have hF_deriv :
      ∀ s ∈ Set.Ioo (0 : ℝ) τ, HasDerivAt F (-integrand s) s := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) τ := Set.mem_Icc_of_Ioo hs
    have hbase :
        HasDerivAt F
          ((((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
            (a * (ψ s - ψ τ) + (1 - s * a) * θ s))) s := by
      simpa [F] using
        weightedEndpointWitnessTailGapHasDerivAt
          (a := a) (τ := τ) (s := s) (ψ := ψ) (ψ' := θ s)
          (hden_pos s hs').ne' (hψ_deriv s hs)
    have hslope :
        (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
            (a * (ψ s - ψ τ) + (1 - s * a) * θ s)) =
          -integrand s := by
      dsimp [integrand, ω]
      field_simp [(hden_pos s hs').ne']
      ring
    exact hbase.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ hF_cont hF_deriv hintegrand_int.neg
  -- Evaluate `F` at the endpoints `0` and `τ` so the weighted tail gap becomes the desired
  -- residual identity at `0`.
  calc
    (1 - τ * a) * (ψ 0 - ψ τ) = F 0 := by
      simp [F]
    _ = F 0 - F τ := by
      simp [F]
    _ = -∫ s in (0 : ℝ)..τ, -integrand s := by
      linarith [hftc]
    _ = ∫ s in (0 : ℝ)..τ, integrand s := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr ?_
      intro s hs
      ring
    _ = ∫ s in (0 : ℝ)..τ,
          ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s := by
      rfl

/-- Helper for Lemma 5.2.2: the same weighted tail-gap identity holds on an arbitrary short
interval `[s0, τ]`, so the primitive drop from `s0` to the fixed endpoint `τ` stays in the same
scalar normal form as the basepoint case. -/
private theorem weightedTailGapEndpointIdentityOnIcc
    {a τ s0 : ℝ} {ψ θ : ℝ → ℝ}
    (hsτ : s0 ≤ τ)
    (hψ_cont : ContinuousOn ψ (Set.Icc s0 τ))
    (hθ_cont : ContinuousOn θ (Set.Icc s0 τ))
    (hψ_deriv : ∀ s ∈ Set.Ioo s0 τ, HasDerivAt ψ (θ s) s)
    (hden_pos : ∀ s ∈ Set.Icc s0 τ, 0 < 1 - s * a) :
    let ω : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * θ s
    ((1 - τ * a) / (1 - s0 * a)) * (ψ s0 - ψ τ) =
      ∫ s in s0..τ,
        ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s := by
  dsimp
  let ω : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * θ s
  let F : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * (ψ s - ψ τ)
  let integrand : ℝ → ℝ := fun s ↦
    ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s
  have hweight_cont :
      ContinuousOn (fun s : ℝ ↦ ((1 - τ * a) / (1 - s * a))) (Set.Icc s0 τ) := by
    -- The rational weight is continuous on `[s0, τ]` because the affine denominator never
    -- vanishes there.
    refine continuousOn_const.div ?_ ?_
    · exact (show Continuous (fun s : ℝ ↦ 1 - s * a) by continuity).continuousOn
    · intro s hs
      exact (hden_pos s hs).ne'
  have hF_cont : ContinuousOn F (Set.Icc s0 τ) := by
    -- Multiply the continuous weight by the continuous tail gap `ψ s - ψ τ`.
    exact hweight_cont.mul (hψ_cont.sub continuous_const.continuousOn)
  have hintegrand_cont : ContinuousOn integrand (Set.Icc s0 τ) := by
    have hkernel_cont :
        ContinuousOn
          (fun s : ℝ ↦
            ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)))
          (Set.Icc s0 τ) := by
      have hpow_inv :
          ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc s0 τ) := by
        have hbase :
            ContinuousOn
              (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc s0 τ) := by
          refine continuousOn_const.div ?_ ?_
          · exact
              (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
          · intro s hs
            exact pow_ne_zero 2 ((hden_pos s hs).ne')
        simpa [one_div] using hbase
      have hkernel_weight :
          ContinuousOn
            (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
            (Set.Icc s0 τ) := by
        simpa [mul_assoc] using
          (show ContinuousOn
            (fun s : ℝ ↦ ((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)
              (Set.Icc s0 τ) from continuous_const.continuousOn.mul hpow_inv)
      exact hkernel_weight.mul (continuous_const.continuousOn.sub hψ_cont)
    have hω_cont : ContinuousOn ω (Set.Icc s0 τ) := by
      -- The weighted derivative shell uses the same denominator control as `F`.
      exact hweight_cont.mul hθ_cont
    exact hkernel_cont.sub hω_cont
  have hintegrand_int : IntervalIntegrable integrand MeasureTheory.volume s0 τ :=
    hintegrand_cont.intervalIntegrable_of_Icc hsτ
  have hF_deriv :
      ∀ s ∈ Set.Ioo s0 τ, HasDerivAt F (-integrand s) s := by
    intro s hs
    have hs' : s ∈ Set.Icc s0 τ := Set.mem_Icc_of_Ioo hs
    have hbase :
        HasDerivAt F
          ((((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
            (a * (ψ s - ψ τ) + (1 - s * a) * θ s))) s := by
      simpa [F] using
        weightedEndpointWitnessTailGapHasDerivAt
          (a := a) (τ := τ) (s := s) (ψ := ψ) (ψ' := θ s)
          (hden_pos s hs').ne' (hψ_deriv s hs)
    have hslope :
        (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
            (a * (ψ s - ψ τ) + (1 - s * a) * θ s)) =
          -integrand s := by
      dsimp [integrand, ω]
      field_simp [(hden_pos s hs').ne']
      ring
    exact hbase.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsτ hF_cont hF_deriv hintegrand_int.neg
  -- Evaluate `F` at `s0` and at `τ` so the weighted short-interval tail gap becomes the desired
  -- primitive identity.
  calc
    ((1 - τ * a) / (1 - s0 * a)) * (ψ s0 - ψ τ) = F s0 := by
      simp [F]
    _ = F s0 - F τ := by
      simp [F]
    _ = -∫ s in s0..τ, -integrand s := by
      linarith [hftc]
    _ = ∫ s in s0..τ, integrand s := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr ?_
      intro s hs
      ring
    _ = ∫ s in s0..τ,
          ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s := by
      rfl

/-- Helper for Lemma 5.2.2: integrating the reciprocal-square tail kernel by parts on an
arbitrary short interval `[s0, τ]` collapses the tail primitive to the live scalar shell at the
same endpoint `τ`. -/
private theorem scalarTailKernelByPartsOnIcc
    {a τ s0 : ℝ} {Θ J : ℝ → ℝ} (hsτ : s0 ≤ τ)
    (hJ_cont : ContinuousOn J (Set.Icc s0 τ))
    (hJ_deriv : ∀ s ∈ Set.Ioo s0 τ, HasDerivAt J (-Θ s) s)
    (hJτ : J τ = 0)
    (hΘ_int : IntervalIntegrable Θ MeasureTheory.volume s0 τ)
    (hden : ∀ s ∈ Set.Icc s0 τ, 0 < 1 - s * a) :
    ∫ s in s0..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
      =
        ∫ s in s0..τ,
          ((((1 - τ * a) * ((s - s0) * a)) / ((1 - s0 * a) * (1 - s * a))) * Θ s) := by
  let g : ℝ → ℝ := fun s ↦
    (((1 - τ * a) * ((s - s0) * a)) / ((1 - s0 * a) * (1 - s * a)))
  have hg_cont : ContinuousOn g (Set.Icc s0 τ) := by
    refine
      ((continuous_const.mul (((continuous_id.sub continuous_const).mul_const a))).continuousOn).div
        ?_ ?_
    · exact
        (show Continuous (fun s : ℝ ↦ (1 - s0 * a) * (1 - s * a)) by continuity).continuousOn
    · intro s hs
      exact mul_ne_zero ((hden s0 ⟨le_rfl, hsτ⟩).ne') ((hden s hs).ne')
  have hg_deriv :
      ∀ s ∈ Set.Ioo s0 τ,
        HasDerivAt g ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) s := by
    intro s hs
    have hs' : s ∈ Set.Icc s0 τ := Set.mem_Icc_of_Ioo hs
    have hs0' : s0 ∈ Set.Icc s0 τ := ⟨le_rfl, hsτ⟩
    have hden_s0_ne : 1 - s0 * a ≠ 0 := (hden s0 hs0').ne'
    have hden_s_ne : 1 - s * a ≠ 0 := (hden s hs').ne'
    have hden_s0_ne' : 1 - a * s0 ≠ 0 := by
      simpa [mul_comm] using hden_s0_ne
    have hden_s_ne' : 1 - a * s ≠ 0 := by
      simpa [mul_comm] using hden_s_ne
    have hnum_deriv :
        HasDerivAt (fun t : ℝ ↦ (1 - τ * a) * ((t - s0) * a)) (((1 - τ * a) * a)) s := by
      -- Differentiate the affine numerator once before the quotient-rule simplification.
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
        (((hasDerivAt_id s).sub_const s0).mul_const a).const_mul (1 - τ * a)
    have hbase_den :
        HasDerivAt (fun t : ℝ ↦ 1 - t * a) (-a) s := by
      -- Differentiate the affine denominator factor.
      convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).mul_const a) using 1
      ring
    have hden_deriv :
        HasDerivAt (fun t : ℝ ↦ (1 - s0 * a) * (1 - t * a)) (-(1 - s0 * a) * a) s := by
      -- Keep the constant live-endpoint factor outside the affine denominator derivative.
      convert hbase_den.const_mul (1 - s0 * a) using 1 <;> ring
    have hquot := hnum_deriv.div hden_deriv (mul_ne_zero hden_s0_ne hden_s_ne)
    have hslope :
        (((1 - τ * a) * a) * ((1 - s0 * a) * (1 - s * a)) -
            ((1 - τ * a) * ((s - s0) * a)) * (-(1 - s0 * a) * a)) /
            (((1 - s0 * a) * (1 - s * a)) ^ (2 : ℕ))
          =
            (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
      field_simp [hden_s0_ne, hden_s_ne, hden_s0_ne', hden_s_ne']
      ring_nf
    -- Collapse the quotient-rule numerator to the reciprocal-square kernel on `[s0, τ]`.
    exact hquot.congr_deriv hslope
  have hkernel_int :
      IntervalIntegrable
        (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
        MeasureTheory.volume s0 τ := by
    have hcont :
        ContinuousOn
          (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
          (Set.Icc s0 τ) := by
      have hpow_inv :
          ContinuousOn
            (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹)
            (Set.Icc s0 τ) := by
        have hbase :
            ContinuousOn
              (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ))
              (Set.Icc s0 τ) := by
          refine continuousOn_const.div ?_ ?_
          · exact
              (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
          · intro s hs
            exact pow_ne_zero 2 ((hden s hs).ne')
        simpa [one_div] using hbase
      simpa [mul_assoc] using ((continuous_const.mul continuous_const).continuousOn.mul hpow_inv)
    exact hcont.intervalIntegrable_of_Icc hsτ
  have hJ_deriv' :
      ∀ s ∈ Set.Ioo (min s0 τ) (max s0 τ), HasDerivAt J (-Θ s) s := by
    simpa [min_eq_left hsτ, max_eq_right hsτ] using hJ_deriv
  have hg_cont' : ContinuousOn g (Set.uIcc s0 τ) := by
    simpa [Set.uIcc_of_le hsτ] using hg_cont
  have hJ_cont' : ContinuousOn J (Set.uIcc s0 τ) := by
    simpa [Set.uIcc_of_le hsτ] using hJ_cont
  have hg_deriv' :
      ∀ s ∈ Set.Ioo (min s0 τ) (max s0 τ),
        HasDerivAt g ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) s := by
    simpa [min_eq_left hsτ, max_eq_right hsτ] using hg_deriv
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hg_cont' hJ_cont' hg_deriv' hJ_deriv'
      hkernel_int hΘ_int.neg
  have hg_s0 : g s0 = 0 := by
    simp [g]
  have hparts' :
      ∫ s in s0..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
        =
          -∫ s in s0..τ, g s * (-Θ s) := by
    -- The boundary terms vanish because `g s0 = 0` and the tail primitive itself vanishes at
    -- the fixed endpoint `τ`.
    have hτterm : g τ * J τ = 0 := by
      simp [g, hJτ]
    have hs0term : g s0 * J s0 = 0 := by
      simp [hg_s0]
    have hparts_zero :
        ∫ s in s0..τ, g s * (-Θ s) =
          -∫ s in s0..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s := by
      simpa [hτterm, hs0term] using hparts
    simpa using (congrArg Neg.neg hparts_zero).symm
  calc
    ∫ s in s0..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
        = -∫ s in s0..τ, g s * (-Θ s) := hparts'
    _ = ∫ s in s0..τ, g s * Θ s := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr ?_
      intro s hs
      ring
    _ =
        ∫ s in s0..τ,
          ((((1 - τ * a) * ((s - s0) * a)) / ((1 - s0 * a) * (1 - s * a))) * Θ s) := by
      rfl

/-- Helper for Lemma 5.2.2: the single transport from a segment point back to the endpoint
cancels the temporary factor `1 - τ a`. -/
private theorem segmentPointResidualTransportCoefficientEq
    {a τ : ℝ} (hτfactor_pos : 0 < 1 - τ * a) (hfactor_pos : 0 < 1 - a) :
    ((1 - τ * a) / (1 - a)) * ((2 * τ * a) / (1 - τ * a)) = (2 * τ * a) / (1 - a) := by
  -- Cancel the shared factor `1 - τ * a` before the last endpoint comparison.
  field_simp [hτfactor_pos.ne', hfactor_pos.ne']

/-- Helper for Lemma 5.2.2: each affine segment point inherits the pointwise Hessian comparison
with the base point Hessian. -/
private theorem segmentPointHessianBounds
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) F)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    ((1 - τ * a) ^ (2 : ℕ)) • hessian F x ≤ hessian F z ∧
      hessian F z ≤ ((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian F x := by
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  have hτ_nonneg : 0 ≤ τ := hτ.1
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg F x (y - x)
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have hy : y ∈ dom := hself.openDikinEllipsoid_inv_constant_subset hx hxy
  have hz : z ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy (segmentPoint_mem_segment hτ)
  have hxPos : (hessian F x).IsPositive := hself.hessian_isPositive hx
  have hz_norm : ‖z - x‖[F; x] = τ * r := by
    have hz_sub : z - x = τ • (y - x) := by
      dsimp [z]
      abel
    rw [hz_sub, hessianLocalNorm_smul_of_nonneg_ofPosDefMem hxPos hτ_nonneg]
  have hτr_le : τ * r ≤ r := by
    have hmul_le : τ * r ≤ 1 * r := mul_le_mul_of_nonneg_right hτ.2 hr_nonneg
    simpa using hmul_le
  let rmid : ℝ := (r + 1 / (Mf : ℝ)) / 2
  have hr_lt_rmid : r < rmid := by
    dsimp [rmid]
    linarith
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    dsimp [rmid]
    linarith
  have hz_mem_rmid : z ∈ W⁰[F; x](rmid) := by
    rw [mem_openDikinEllipsoid_iff]
    have hz_norm_le_r : ‖z - x‖[F; x] ≤ r := by
      rw [hz_norm]
      simpa using hτr_le
    exact lt_of_le_of_lt hz_norm_le_r hr_lt_rmid
  -- Compare `∇²F(z)` to `∇²F(x)` at the exact segment radius, using `rmid` only to discharge
  -- the strict Dikin-radius side condition.
  simpa [a, hz_norm, mul_assoc, mul_left_comm, mul_comm] using
    hself.hessian_loewner_bounds_of_exact_local_radius
      (x := x) (y := z) (r := rmid) hx hz hrmid_lt hz_mem_rmid

/-- Helper for Lemma 5.2.2: scaling both sides of a Loewner inequality by the same nonnegative
scalar preserves the inequality. -/
private theorem loewnerSmulBridge
    {A B : E →L[ℝ] E} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  have h' : (B - A).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using h
  -- Move to the positivity definition and factor the common scalar through the difference.
  change (c • B - c • A).IsPositive
  simpa [smul_sub] using h'.smul_of_nonneg hc

/-- Helper for Lemma 5.2.2: the tail of an admissible Dikin segment has the transported local
norm bound at the intermediate point. -/
private theorem segmentTailLocalNormLe
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    ‖y - z‖[F; z] ≤ ((1 - τ) * r) / (1 - τ * a) := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  have hτ_nonneg : 0 ≤ τ := hτ.1
  have h1τ_nonneg : 0 ≤ 1 - τ := by
    linarith [hτ.2]
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - τ * a := by
    have hτa_le_a : τ * a ≤ a := by
      have ha_nonneg : 0 ≤ a := by
        dsimp [a]
        exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    linarith
  have hz_norm : ‖y - z‖[F; x] = (1 - τ) * r := by
    -- Rewrite the tail displacement as the remaining scalar multiple of `y - x`.
    have hyz : y - z = (1 - τ) • (y - x) := by
      calc
        y - z = y - (x + τ • (y - x)) := by rfl
        _ = y - x - τ • (y - x) := by abel
        _ = (1 - τ) • (y - x) := by
              rw [sub_smul, one_smul]
    rw [hyz, hessianLocalNorm_smul_of_nonneg_ofPosDefMem
      (hself.hessian_isPositive hx) h1τ_nonneg]
  have hz_bound :
      hessian F z ≤ ((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian F x := by
    simpa [r, a, z] using
      (segmentPointHessianBounds (F := F) hself (x := x) (y := y) hx hxy (τ := τ) hτ).2
  have hsqrt :
      Real.sqrt (((1 - τ * a) ^ (2 : ℕ))⁻¹) = 1 / (1 - τ * a) := by
    have hfactor_nonneg : 0 ≤ 1 / (1 - τ * a) := by positivity
    rw [show ((((1 - τ * a) ^ (2 : ℕ))⁻¹ : ℝ)) = (1 / (1 - τ * a)) ^ (2 : ℕ) by
      field_simp [hfactor_pos.ne']]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hfactor_nonneg]
  -- Compare the tail displacement in the intermediate and base metrics, then rewrite the base
  -- metric using the scalar tail factor `1 - τ`.
  calc
    ‖y - z‖[F; z] ≤ Real.sqrt (((1 - τ * a) ^ (2 : ℕ))⁻¹) * ‖y - z‖[F; x] := by
      exact hessianLocalNorm_le_mul_of_loewner_upper (F := F) (x := x) (y := z) (v := y - z)
        (by positivity) hz_bound
    _ = (1 / (1 - τ * a)) * ‖y - z‖[F; x] := by
      rw [hsqrt]
    _ = ((1 - τ) * r) / (1 - τ * a) := by
      rw [hz_norm]
      field_simp [hfactor_pos.ne']

/-- Helper for Lemma 5.2.2: along an admissible Dikin segment, the segment-point metric compares
back to the base metric with the standard factor `(1 - τ a)⁻¹`. -/
private theorem segmentPointLocalNorm_le_baseFactor
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (v : E) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    ‖v‖[F; z] ≤ (1 / (1 - τ * a)) * ‖v‖[F; x] := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hτa_le_a : τ * a ≤ a := by
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hfactor_pos : 0 < 1 - τ * a := by
    linarith
  have hz_bound :
      hessian F z ≤ ((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian F x := by
    simpa [r, a, z] using
      (segmentPointHessianBounds (F := F) hself (x := x) (y := y) hx hxy (τ := τ) hτ).2
  have hsqrt :
      Real.sqrt (((1 - τ * a) ^ (2 : ℕ))⁻¹) = 1 / (1 - τ * a) := by
    have hfactor_nonneg : 0 ≤ 1 / (1 - τ * a) := by positivity
    rw [show ((((1 - τ * a) ^ (2 : ℕ))⁻¹ : ℝ)) = (1 / (1 - τ * a)) ^ (2 : ℕ) by
      field_simp [hfactor_pos.ne']]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hfactor_nonneg]
  -- Compare the live point metric directly back to the base point metric.
  calc
    ‖v‖[F; z] ≤ Real.sqrt (((1 - τ * a) ^ (2 : ℕ))⁻¹) * ‖v‖[F; x] := by
      exact hessianLocalNorm_le_mul_of_loewner_upper (F := F) (x := x) (y := z) (v := v)
        (by positivity) hz_bound
    _ = (1 / (1 - τ * a)) * ‖v‖[F; x] := by
      rw [hsqrt]

/-- Helper for Lemma 5.2.2: an intermediate segment point compares to the endpoint Hessian
metric with the exact transport factor `((1 - τ * a) / (1 - a))`. -/
private theorem segmentPointLocalNorm_le_endpointFactor
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (v : E) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    ‖v‖[F; z] ≤ ((1 - τ * a) / (1 - a)) * ‖v‖[F; y] := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hz : z ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy (segmentPoint_mem_segment hτ)
  have htail :
      ‖y - z‖[F; z] ≤ ((1 - τ) * r) / (1 - τ * a) := by
    simpa [r, a, z] using
      segmentTailLocalNormLe (F := F) (x := x) (y := y) hx hy hxy (τ := τ) hτ
  let ρ : ℝ := ‖y - z‖[F; z]
  let rmid : ℝ := (ρ + 1 / (Mf : ℝ)) / 2
  have hρ_lt : ρ < 1 / (Mf : ℝ) := by
    have htail_lt : ((1 - τ) * r) / (1 - τ * a) < 1 / (Mf : ℝ) := by
      have hτa_le_a : τ * a ≤ a := by
        have ha_nonneg : 0 ≤ a := by
          dsimp [a]
          exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
        simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
      have hfactor_posτ : 0 < 1 - τ * a := by
        linarith
      have hmul :
          (Mf : ℝ) * (((1 - τ) * r) / (1 - τ * a)) < 1 := by
        have hrew :
            (Mf : ℝ) * (((1 - τ) * r) / (1 - τ * a)) =
              ((1 - τ) * a) / (1 - τ * a) := by
          dsimp [a]
          field_simp [hfactor_posτ.ne']
        rw [hrew]
        have hnum_lt_den : (1 - τ) * a < 1 - τ * a := by
          linarith
        exact (div_lt_iff₀ hfactor_posτ).2 (by simpa using hnum_lt_den)
      exact (lt_div_iff₀ hMf_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    exact lt_of_le_of_lt htail htail_lt
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    dsimp [rmid]
    linarith
  have hy_mem_rmid : y ∈ W⁰[F; z](rmid) := by
    rw [mem_openDikinEllipsoid_iff]
    dsimp [rmid, ρ]
    linarith
  have hloewner :
      ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ)) • hessian F z ≤ hessian F y := by
    simpa [ρ] using
      (hself.hessian_loewner_bounds_of_exact_local_radius
        (x := z) (y := y) (r := rmid) hz hy hrmid_lt hy_mem_rmid).1
  have hcmp : hessian F z ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ • hessian F y := by
    have hcoeff_nonneg : 0 ≤ ((((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ : ℝ)) := by positivity
    have hscaled := loewnerSmulBridge hloewner hcoeff_nonneg
    have hpow_ne : (1 - (Mf : ℝ) * ρ) ^ (2 : ℕ) ≠ 0 := by
      have hfac : 0 < 1 - (Mf : ℝ) * ρ := by
        have hmul_lt_one : (Mf : ℝ) * ρ < 1 := by
          simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
        linarith
      exact pow_ne_zero 2 hfac.ne'
    have hone :
        ((((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ : ℝ) * (1 - (Mf : ℝ) * ρ) ^ (2 : ℕ)) = 1 := by
      exact inv_mul_cancel₀ hpow_ne
    calc
      hessian F z =
          ((((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ : ℝ) * (1 - (Mf : ℝ) * ρ) ^ (2 : ℕ)) •
            hessian F z := by
              simp [hone]
      _ ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ • hessian F y := by
            simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hρ_factor :
      1 / (1 - (Mf : ℝ) * ρ) ≤ (1 - τ * a) / (1 - a) := by
    have hden_posρ : 0 < 1 - (Mf : ℝ) * ρ := by
      have hmul_lt_one : (Mf : ℝ) * ρ < 1 := by
        simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
      linarith
    have hτa_factor_pos : 0 < 1 - τ * a := by
      have hτa_le_a : τ * a ≤ a := by
        have ha_nonneg : 0 ≤ a := by
          dsimp [a]
          exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
        simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
      linarith
    have hρ_upper : (Mf : ℝ) * ρ ≤ ((1 - τ) * a) / (1 - τ * a) := by
      have hMf_nonneg : 0 ≤ (Mf : ℝ) := le_of_lt hMf_pos
      have hρ_upper_raw := mul_le_mul_of_nonneg_left htail hMf_nonneg
      dsimp [ρ, a] at hρ_upper_raw ⊢
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hρ_upper_raw
    have hfactor_lower :
        (1 - a) / (1 - τ * a) ≤ 1 - (Mf : ℝ) * ρ := by
      have hrewrite :
          1 - ((1 - τ) * a) / (1 - τ * a) = (1 - a) / (1 - τ * a) := by
        field_simp [hτa_factor_pos.ne']
        ring
      rw [← hrewrite]
      linarith
    have hleft_pos : 0 < (1 - a) / (1 - τ * a) := by
      positivity
    have hrecip :
        1 / (1 - (Mf : ℝ) * ρ) ≤ 1 / ((1 - a) / (1 - τ * a)) := by
      exact (one_div_le_one_div hden_posρ hleft_pos).2 hfactor_lower
    simpa [div_eq_mul_inv] using hrecip
  have hsqrt :
      Real.sqrt (((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹) ≤ (1 - τ * a) / (1 - a) := by
    have hden_posρ : 0 < 1 - (Mf : ℝ) * ρ := by
      have hmul_lt_one : (Mf : ℝ) * ρ < 1 := by
        simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
      linarith
    have hsqrt_eq :
        Real.sqrt (((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹) = 1 / (1 - (Mf : ℝ) * ρ) := by
      have hfactor_nonneg : 0 ≤ 1 / (1 - (Mf : ℝ) * ρ) := by positivity
      rw [show ((((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ : ℝ)) =
          (1 / (1 - (Mf : ℝ) * ρ)) ^ (2 : ℕ) by
            field_simp [hden_posρ.ne']]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hfactor_nonneg]
    rw [hsqrt_eq]
    exact hρ_factor
  -- Route correction: compare the tail metric at `(z, y)` directly instead of pushing the
  -- witness through an extra coarse residual estimate.
  calc
    ‖v‖[F; z] ≤ Real.sqrt (((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹) * ‖v‖[F; y] := by
      exact hessianLocalNorm_le_mul_of_loewner_upper (F := F) (x := y) (y := z) (v := v)
        (by positivity) hcmp
    _ ≤ ((1 - τ * a) / (1 - a)) * ‖v‖[F; y] := by
      exact mul_le_mul_of_nonneg_right hsqrt (hessianLocalNorm_nonneg F y v)

/-- Helper for Lemma 5.2.2: reparameterizing a short subsegment transports the live point metric
directly to the fixed endpoint metric. -/
private theorem subsegmentPointLocalNorm_le_endpointFactor
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ))) {τ s : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) (v : E) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    ‖v‖[F; x + s • (y - x)] ≤ ((1 - s * a) / (1 - τ * a)) * ‖v‖[F; z] := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  let d : E := y - x
  have hz_mem : z ∈ W⁰[F; x](1 / (Mf : ℝ)) := by
    -- Keep the shorter endpoint inside the original Dikin ellipsoid before reparameterizing.
    refine (mem_openDikinEllipsoid_iff F x z (1 / (Mf : ℝ))).2 ?_
    have hz_sub : z - x = τ • d := by
      dsimp [z, d]
      abel
    rw [hz_sub, hessianLocalNorm_smul_of_nonneg_ofPosDefMem (hself.hessian_isPositive hx) hτ.1]
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
    have hr_nonneg : 0 ≤ r := by
      simpa [r] using hessianLocalNorm_nonneg F x d
    have hτr_le : τ * r ≤ r := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hτ.2 hr_nonneg
    exact lt_of_le_of_lt hτr_le hr_lt
  have hz : z ∈ dom := hself.openDikinEllipsoid_inv_constant_subset hx hz_mem
  by_cases hτ0 : τ = 0
  · have hs0 : s = 0 := by linarith [hs.1, hs.2, hτ0]
    subst hτ0
    subst hs0
    -- When `τ = 0`, the shorter segment degenerates to the base point.
    simp [z, d, a]
  · let σ : ℝ := s / τ
    have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (by simpa [eq_comm] using hτ0)
    have hσ : σ ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · dsimp [σ]
        exact div_nonneg hs.1 hτ.1
      · dsimp [σ]
        exact (div_le_iff₀ hτpos).2 (by simpa using hs.2)
    have hz_norm : ‖z - x‖[F; x] = τ * r := by
      have hz_sub : z - x = τ • d := by
        dsimp [z, d]
        abel
      rw [hz_sub, hessianLocalNorm_smul_of_nonneg_ofPosDefMem (hself.hessian_isPositive hx) hτ.1]
    have hs_point : x + σ • (z - x) = x + s • d := by
      have hz_sub : z - x = τ • d := by
        dsimp [z, d]
        abel
      dsimp [σ]
      rw [hz_sub, smul_smul]
      congr 1
      field_simp [hτ0]
    have hcoeff :
        (1 - σ * ((Mf : ℝ) * ‖z - x‖[F; x])) / (1 - (Mf : ℝ) * ‖z - x‖[F; x]) =
          (1 - s * a) / (1 - τ * a) := by
      dsimp [σ, a]
      rw [hz_norm]
      field_simp [hτ0]
    -- Apply the already-proved endpoint transport formula to the shorter segment `x → z`.
    have htransport :
        ‖v‖[F; x + σ • (z - x)] ≤
          (1 - σ * ((Mf : ℝ) * ‖z - x‖[F; x])) / (1 - (Mf : ℝ) * ‖z - x‖[F; x]) *
            ‖v‖[F; z] := by
      simpa using
        segmentPointLocalNorm_le_endpointFactor (F := F) (x := x) (y := z)
          hx hz hz_mem (τ := σ) hσ v
    calc
      ‖v‖[F; x + s • (y - x)] = ‖v‖[F; x + σ • (z - x)] := by
        rw [hs_point.symm]
      _ ≤ (1 - σ * ((Mf : ℝ) * ‖z - x‖[F; x])) / (1 - (Mf : ℝ) * ‖z - x‖[F; x]) *
            ‖v‖[F; z] := htransport
      _ = ((1 - s * a) / (1 - τ * a)) * ‖v‖[F; z] := by
        rw [hcoeff]
      _ = ((1 - s * a) / (1 - τ * a)) * ‖v‖[F; x + τ • (y - x)] := by
        rfl

/-- Helper for Lemma 5.2.2: the short subsegment from the live point
`p = x + s • (y - x)` to the fixed endpoint `z = x + τ • (y - x)` has the expected local-norm
radius in the live metric at `p`. -/
private theorem shortSubsegmentEndpointLocalNorm_leLiveFactor
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    ‖z - p‖[F; p] ≤ ((τ - s) * r) / (1 - s * a) := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_trans hs.2 hτ.2⟩
  have hp : p ∈ dom := by
    -- Keep the live point on the original admissible segment before measuring the tail from `p`.
    exact hself.convex_domain.segment_subset hx hy (segmentPoint_mem_segment hs01)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsfactor_pos : 0 < 1 - s * a := by
    have hsa_le_a : s * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hs01.2 ha_nonneg
    linarith
  by_cases hs1 : s = 1
  · have hτ1 : τ = 1 := by linarith [hs.2, hτ.2, hs1]
    subst hs1
    subst hτ1
    -- The short subsegment collapses at the endpoint, so the live displacement is zero.
    simpa [p, z, d, hessianLocalNorm_def] using (le_rfl : (0 : ℝ) ≤ 0)
  · let η : ℝ := (τ - s) / (1 - s)
    have hs_lt_one : s < 1 := lt_of_le_of_ne hs01.2 (by simpa [eq_comm] using hs1)
    have hone_sub_s_pos : 0 < 1 - s := by linarith
    have hone_sub_s_ne : 1 - s ≠ 0 := hone_sub_s_pos.ne'
    have hη : η ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · dsimp [η]
        exact div_nonneg (sub_nonneg.mpr hs.2) (le_of_lt hone_sub_s_pos)
      · dsimp [η]
        have hnum_le : τ - s ≤ 1 - s := by
          linarith [hτ.2]
        exact (div_le_iff₀ hone_sub_s_pos).2 (by simpa [one_mul] using hnum_le)
    have hy_tail :
        ‖y - p‖[F; p] ≤ ((1 - s) * r) / (1 - s * a) := by
      -- Route correction: measure the remaining tail from the live point `p` instead of
      -- transporting first to the fixed endpoint `z`.
      simpa [r, a, p, d] using
        segmentTailLocalNormLe (F := F) (x := x) (y := y) hx hy hxy (τ := s) hs01
    have hzp_eq : z - p = η • (y - p) := by
      have hy_tail_eq : y - p = (1 - s) • d := by
        calc
          y - p = y - (x + s • d) := by rfl
          _ = y - x - s • d := by abel
          _ = d - s • d := by simp [d]
          _ = (1 - s) • d := by rw [sub_smul, one_smul]
      have hz_tail_eq : z - p = (τ - s) • d := by
        calc
          z - p = (x + τ • d) - (x + s • d) := by rfl
          _ = τ • d - s • d := by abel
          _ = (τ - s) • d := by rw [sub_smul]
      rw [hz_tail_eq, hy_tail_eq, smul_smul]
      dsimp [η]
      have hη_mul : ((τ - s) / (1 - s)) * (1 - s) = τ - s := by
        field_simp [hone_sub_s_ne]
      rw [hη_mul]
    have hη_nonneg : 0 ≤ η := hη.1
    have hscale :
        ‖z - p‖[F; p] = η * ‖y - p‖[F; p] := by
      -- Rewrite the short tail as a nonnegative rescaling of the full tail from `p` to `y`.
      rw [hzp_eq]
      exact hessianLocalNorm_smul_of_nonneg_ofPosDefMem (hself.hessian_isPositive hp) hη_nonneg
    have hscaled :
        η * ‖y - p‖[F; p] ≤ η * (((1 - s) * r) / (1 - s * a)) := by
      exact mul_le_mul_of_nonneg_left hy_tail hη_nonneg
    calc
      ‖z - p‖[F; p] = η * ‖y - p‖[F; p] := hscale
      _ ≤ η * (((1 - s) * r) / (1 - s * a)) := hscaled
      _ = ((τ - s) * r) / (1 - s * a) := by
        have hη_mul :
            η * (((1 - s) * r) / (1 - s * a)) = ((τ - s) * r) / (1 - s * a) := by
          dsimp [η]
          field_simp [hone_sub_s_ne, hsfactor_pos.ne']
        simpa using hη_mul

/-- Helper for Lemma 5.2.2: the short subsegment from the live point `p` to the fixed endpoint
`z` inherits the same exact Hessian comparison, now expressed in the live metric at `p`. -/
private theorem shortSubsegmentEndpointHessianBoundsFromLivePoint
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    (((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ)) • hessian F p ≤ hessian F z ∧
      hessian F z ≤ ((((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ))⁻¹) • hessian F p := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let ρ : ℝ := ‖z - p‖[F; p]
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_trans hs.2 hτ.2⟩
  have hp : p ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy (segmentPoint_mem_segment hs01)
  have hz : z ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy (segmentPoint_mem_segment hτ)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsfactor_pos : 0 < 1 - s * a := by
    have hsa_le_a : s * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hs01.2 ha_nonneg
    linarith
  have hzp_le :
      ρ ≤ ((τ - s) * r) / (1 - s * a) := by
    simpa [ρ, r, a, d, p, z] using
      shortSubsegmentEndpointLocalNorm_leLiveFactor
        (F := F) (x := x) (y := y) hx hy hxy (τ := τ) (s := s) hτ hs
  have hρ_lt : ρ < 1 / (Mf : ℝ) := by
    have hupper_lt :
        ((τ - s) * r) / (1 - s * a) < 1 / (Mf : ℝ) := by
      have hβ_lt_one :
          ((τ - s) * a) / (1 - s * a) < 1 := by
        have hτsa_lt_one_minus_sa : (τ - s) * a < 1 - s * a := by
          have hτa_le_a : τ * a ≤ a := by
            simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
          linarith
        exact (div_lt_iff₀ hsfactor_pos).2 (by simpa [one_mul] using hτsa_lt_one_minus_sa)
      have hrew :
          (Mf : ℝ) * (((τ - s) * r) / (1 - s * a)) = ((τ - s) * a) / (1 - s * a) := by
        dsimp [a]
        field_simp [hsfactor_pos.ne']
      have hscaled_lt :
          (((τ - s) * r) / (1 - s * a)) * (Mf : ℝ) < 1 := by
        calc
          (((τ - s) * r) / (1 - s * a)) * (Mf : ℝ)
              = (Mf : ℝ) * (((τ - s) * r) / (1 - s * a)) := by ring
          _ = ((τ - s) * a) / (1 - s * a) := hrew
          _ < 1 := hβ_lt_one
      exact (lt_div_iff₀ hMf_pos).2 hscaled_lt
    exact lt_of_le_of_lt hzp_le hupper_lt
  let rmid : ℝ := (ρ + 1 / (Mf : ℝ)) / 2
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    dsimp [rmid]
    linarith
  have hz_mem_rmid : z ∈ W⁰[F; p](rmid) := by
    rw [mem_openDikinEllipsoid_iff]
    dsimp [rmid, ρ]
    linarith
  have hloewner :
      ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ)) • hessian F p ≤ hessian F z ∧
        hessian F z ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ • hessian F p := by
    simpa [ρ] using
      hself.hessian_loewner_bounds_of_exact_local_radius
        (x := p) (y := z) (r := rmid) hp hz hrmid_lt hz_mem_rmid
  have hβ_bound :
      (Mf : ℝ) * ρ ≤ ((τ - s) * a) / (1 - s * a) := by
    have hscaled := mul_le_mul_of_nonneg_left hzp_le (le_of_lt hMf_pos)
    dsimp [ρ, a] at hscaled ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hscaled
  have hratio_nonneg : 0 ≤ (1 - τ * a) / (1 - s * a) := by
    have hτa_le_a : τ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    exact div_nonneg (by linarith) (le_of_lt hsfactor_pos)
  have hratio_sq_le :
      ((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ) ≤ (1 - (Mf : ℝ) * ρ) ^ (2 : ℕ) := by
    have hsfactor_pos' : 0 < 1 - a * s := by
      simpa [mul_comm] using hsfactor_pos
    have hratio_le :
        (1 - τ * a) / (1 - s * a) ≤ 1 - (Mf : ℝ) * ρ := by
      have hrewrite :
          (1 - τ * a) / (1 - s * a) = 1 - (((τ - s) * a) / (1 - s * a)) := by
        field_simp [hsfactor_pos.ne', hsfactor_pos'.ne']
        ring
      rw [hrewrite]
      linarith
    have hρfactor_nonneg : 0 ≤ 1 - (Mf : ℝ) * ρ := by
      have hρfactor_pos : 0 < 1 - (Mf : ℝ) * ρ := by
        have hscaled_lt : (Mf : ℝ) * ρ < 1 := by
          simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
        linarith
      exact le_of_lt hρfactor_pos
    nlinarith [hratio_le, hratio_nonneg, hρfactor_nonneg]
  have hρfactor_pos : 0 < 1 - (Mf : ℝ) * ρ := by
    have hscaled_lt : (Mf : ℝ) * ρ < 1 := by
      simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
    linarith
  have hρfactor_sq_nonneg : 0 ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ := by positivity
  constructor
  · -- Compare the exact live-point factor to the canonical Dikin-radius factor at `p`.
    calc
      ((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ) • hessian F p
          ≤ (1 - (Mf : ℝ) * ρ) ^ (2 : ℕ) • hessian F p := by
              exact loewnerSmul_mono_of_nonneg
                (show 0 ≤ hessian F p by
                  exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 (hself.hessian_isPositive hp))
                hratio_sq_le
      _ ≤ hessian F z := hloewner.1
  · -- The reciprocal comparison follows from the same exact-radius bound after one scalar
    -- monotonicity step.
    have hinv_mono :
        ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ ≤
          (((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ))⁻¹ := by
      exact inv_le_inv₀ (by positivity) hratio_sq_le
    calc
      hessian F z ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ • hessian F p := hloewner.2
      _ ≤ ((((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ))⁻¹) • hessian F p := by
            exact loewnerSmul_mono_of_nonneg
              (show 0 ≤ hessian F p by
                exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 (hself.hessian_isPositive hp))
              hinv_mono

/-- Helper for Lemma 5.2.2: the live third-derivative operator is symmetric in its operator
slots. -/
private theorem thirdDerivativeOperator_isSymmetric
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) F)
    {x d : E} (hx : x ∈ dom) :
    (fderiv ℝ (hessian F) x d).IsSymmetric := by
  have hcontAt : ContDiffAt ℝ 3 F x := by
    exact hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx)
  intro v w
  -- Normalize both pairings to the same third iterated derivative and swap the final slots.
  calc
    inner ℝ ((fderiv ℝ (hessian F) x d) v) w = inner ℝ w ((fderiv ℝ (hessian F) x d) v) := by
      rw [real_inner_comm]
    _ = iteratedFDeriv ℝ 3 F x ![d, v, w] :=
      hessian_direction_pairing_eq_iteratedFDeriv
        (f := F) (x := x) (d := d) (w := v) (v := w) hcontAt
    _ = iteratedFDeriv ℝ 3 F x ![d, w, v] :=
      iteratedFDeriv_three_swap23_at
        (f := F) (x := x) (u₁ := d) (u₂ := v) (u₃ := w) hcontAt
    _ = inner ℝ v ((fderiv ℝ (hessian F) x d) w) :=
      (hessian_direction_pairing_eq_iteratedFDeriv
        (f := F) (x := x) (d := d) (w := w) (v := v) hcontAt).symm

/-- Helper for Lemma 5.2.2: at a live segment point, the scalar third-derivative pairing is
controlled in the fixed endpoint metric at `z = x + τ • (y - x)`. -/
private theorem pointwiseSegmentHessianDerivPairingBoundAtSegmentPoint
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    let d := y - x
    let p := x + s • d
    |inner ℝ w ((fderiv ℝ (hessian F) p d) u)| ≤
      ((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[F; z] * ‖u‖[F; x] := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  let d : E := y - x
  let p : E := x + s • d
  let K : E →L[ℝ] E := fderiv ℝ (hessian F) p d
  let c : ℝ := 2 * (Mf : ℝ) * ‖d‖[F; p]
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_trans hs.2 hτ.2⟩
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hp : p ∈ dom := by
    exact hsegment_dom (segmentPoint_mem_segment hs01)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x d)
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsa_le_ta : s * a ≤ τ * a := by
    simpa using mul_le_mul_of_nonneg_right hs.2 ha_nonneg
  have hτa_le_a : τ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hτfactor_pos : 0 < 1 - τ * a := by
    linarith
  have hsfactor_pos : 0 < 1 - s * a := by
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) (by positivity : 0 ≤ (Mf : ℝ)))
      (hessianLocalNorm_nonneg F p d)
  have hupper : K ≤ c • hessian F p := by
    -- Apply the operator third-derivative bound in the live metric at `p`.
    simpa [K, c] using IsSelfConcordantOnWith.thirdDerivative_operator_le hself hp d
  have hneg_upper : -K ≤ c • hessian F p := by
    -- Replacing `d` by `-d` gives the opposite side of the symmetric sandwich.
    simpa [K, c, map_neg, hessianLocalNorm_neg] using
      IsSelfConcordantOnWith.thirdDerivative_operator_le hself hp (-d)
  have hlower : -(c • hessian F p) ≤ K := by
    rw [ContinuousLinearMap.le_def]
    rw [ContinuousLinearMap.le_def] at hneg_upper
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg_upper
  have hK_symm : K.IsSymmetric := by
    have hgap_pos : (c • hessian F p - K).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hupper
    have hscalar_symm : (c • hessian F p).IsSymmetric := by
      intro v₁ v₂
      calc
        inner ℝ ((c • hessian F p) v₁) v₂ = c * inner ℝ (hessian F p v₁) v₂ := by
          simp [inner_smul_left]
        _ = c * inner ℝ v₁ (hessian F p v₂) := by
          rw [show inner ℝ (hessian F p v₁) v₂ = inner ℝ v₁ (hessian F p v₂) by
            simpa using (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hp).isSymmetric v₁ v₂]
        _ = inner ℝ v₁ ((c • hessian F p) v₂) := by
          simp [inner_smul_right]
    have hrepr : K = c • hessian F p - (c • hessian F p - K) := by
      ext v
      simp
    rw [hrepr]
    exact hessianDifference_isSymmetric hscalar_symm hgap_pos.isSymmetric
  have hpair :
      |inner ℝ w (K u)| ≤ c * ‖w‖[F; p] * ‖u‖[F; p] := by
    -- Package the live-point third-derivative control as a scalar pairing estimate.
    simpa [K, c] using
      absInner_le_mul_localNorm_ofOperatorSandwich
        (F := F) (x := p) (u := u) (v := w)
        (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hp)
        K hc_nonneg hK_symm hlower hupper
  have hd_transport :
      ‖d‖[F; p] ≤ (1 / (1 - s * a)) * ‖d‖[F; x] := by
    -- Compare the full segment direction back to the base metric at `x`.
    simpa [r, a, p, d] using
      segmentPointLocalNorm_le_baseFactor (F := F) (x := x) (y := y)
        hx hy hxy (τ := s) hs01 d
  have hw_transport :
      ‖w‖[F; p] ≤ ((1 - s * a) / (1 - τ * a)) * ‖w‖[F; z] := by
    -- Transport the witness from the live point `p` to the fixed endpoint `z`.
    simpa [r, a, z, p, d] using
      subsegmentPointLocalNorm_le_endpointFactor (F := F) (x := x) (y := y)
        hx hy hxy (τ := τ) hτ (s := s) hs w
  have hu_transport :
      ‖u‖[F; p] ≤ (1 / (1 - s * a)) * ‖u‖[F; x] := by
    -- Compare the test direction back to the base metric at `x`.
    simpa [r, a, p, d] using
      segmentPointLocalNorm_le_baseFactor (F := F) (x := x) (y := y)
        hx hy hxy (τ := s) hs01 u
  have hc_le :
      c ≤ (2 * a) / (1 - s * a) := by
    have hscaled := mul_le_mul_of_nonneg_left hd_transport (by positivity : 0 ≤ 2 * (Mf : ℝ))
    simpa [c, a, r, d, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hscaled
  have htransport_step :
      c * ‖w‖[F; p] * ‖u‖[F; p] ≤
        ((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[F; z] * ‖u‖[F; x] := by
    have hw_bound_nonneg : 0 ≤ ((1 - s * a) / (1 - τ * a)) * ‖w‖[F; z] := by
      exact mul_nonneg (div_nonneg (le_of_lt hsfactor_pos) (le_of_lt hτfactor_pos))
        (hessianLocalNorm_nonneg F z w)
    have hwu :
        ‖w‖[F; p] * ‖u‖[F; p] ≤
          (((1 - s * a) / (1 - τ * a)) * ‖w‖[F; z]) *
            ((1 / (1 - s * a)) * ‖u‖[F; x]) := by
      exact mul_le_mul hw_transport hu_transport
        (hessianLocalNorm_nonneg F p u) hw_bound_nonneg
    have hscaled :
        c * (‖w‖[F; p] * ‖u‖[F; p]) ≤
          c * ((((1 - s * a) / (1 - τ * a)) * ‖w‖[F; z]) *
            ((1 / (1 - s * a)) * ‖u‖[F; x])) := by
      exact mul_le_mul_of_nonneg_left hwu hc_nonneg
    have htransport_nonneg :
        0 ≤
          (((1 - s * a) / (1 - τ * a)) * ‖w‖[F; z]) *
            ((1 / (1 - s * a)) * ‖u‖[F; x]) := by
      exact mul_nonneg hw_bound_nonneg
        (mul_nonneg (by positivity) (hessianLocalNorm_nonneg F x u))
    have hmono :
        c * ((((1 - s * a) / (1 - τ * a)) * ‖w‖[F; z]) *
            ((1 / (1 - s * a)) * ‖u‖[F; x])) ≤
          ((2 * a) / (1 - s * a)) *
            ((((1 - s * a) / (1 - τ * a)) * ‖w‖[F; z]) *
              ((1 / (1 - s * a)) * ‖u‖[F; x])) := by
      exact mul_le_mul_of_nonneg_right hc_le htransport_nonneg
    calc
      c * ‖w‖[F; p] * ‖u‖[F; p] = c * (‖w‖[F; p] * ‖u‖[F; p]) := by ring
      _ ≤ c * ((((1 - s * a) / (1 - τ * a)) * ‖w‖[F; z]) *
            ((1 / (1 - s * a)) * ‖u‖[F; x])) := hscaled
      _ ≤ ((2 * a) / (1 - s * a)) *
            ((((1 - s * a) / (1 - τ * a)) * ‖w‖[F; z]) *
              ((1 / (1 - s * a)) * ‖u‖[F; x])) := hmono
      _ = ((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[F; z] * ‖u‖[F; x] := by
        field_simp [hτfactor_pos.ne', hsfactor_pos.ne']
  -- Combine the live-point third-derivative sandwich with the two transport estimates.
  calc
    |inner ℝ w (K u)| ≤ c * ‖w‖[F; p] * ‖u‖[F; p] := hpair
    _ ≤ ((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[F; z] * ‖u‖[F; x] :=
      htransport_step

/-- Helper for Lemma 5.2.2: the weighted live Hessian-derivative integrand admits the reciprocal-
square short-segment majorant in the fixed endpoint metric `z = x + τ • (y - x)`. -/
private theorem weightedEndpointWitnessScaledDerivPairingBound
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    let d := y - x
    let p := x + s • d
    |(((1 - τ * a) / (1 - s * a)) * inner ℝ w ((fderiv ℝ (hessian F) p d) u))| ≤
      ((2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖w‖[F; z] * ‖u‖[F; x] := by
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  let d : E := y - x
  let p : E := x + s • d
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x d)
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsa_le_ta : s * a ≤ τ * a := by
    simpa using mul_le_mul_of_nonneg_right hs.2 ha_nonneg
  have hτa_le_a : τ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hsfactor_pos : 0 < 1 - s * a := by
    linarith
  have hτfactor_pos : 0 < 1 - τ * a := by
    linarith
  have hraw :
      |inner ℝ w ((fderiv ℝ (hessian F) p d) u)| ≤
        ((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[F; z] * ‖u‖[F; x] := by
    simpa [r, a, z, d, p] using
      pointwiseSegmentHessianDerivPairingBoundAtSegmentPoint
        (F := F) (x := x) (y := y) (u := u) (w := w) hx hy hxy (τ := τ) hτ (s := s) hs
  have hcoeff_nonneg : 0 ≤ (1 - τ * a) / (1 - s * a) := by
    exact div_nonneg (le_of_lt hτfactor_pos) (le_of_lt hsfactor_pos)
  have hscaled := mul_le_mul_of_nonneg_left hraw hcoeff_nonneg
  have habs :
      |((1 - τ * a) / (1 - s * a))| *
          |inner ℝ w ((fderiv ℝ (hessian F) p d) u)| ≤
        ((1 - τ * a) / (1 - s * a)) *
          (((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[F; z] * ‖u‖[F; x]) := by
    simpa [abs_of_nonneg hcoeff_nonneg] using hscaled
  -- Keep the extra scalar weight separate so only the reciprocal-square kernel survives.
  calc
    |(((1 - τ * a) / (1 - s * a)) * inner ℝ w ((fderiv ℝ (hessian F) p d) u))|
        = |((1 - τ * a) / (1 - s * a))| *
            |inner ℝ w ((fderiv ℝ (hessian F) p d) u)| := by
              rw [abs_mul]
    _ ≤ ((1 - τ * a) / (1 - s * a)) *
          (((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[F; z] * ‖u‖[F; x]) := habs
    _ = ((2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖w‖[F; z] * ‖u‖[F; x] := by
      field_simp [hτfactor_pos.ne', hsfactor_pos.ne']

/-- Helper for Lemma 5.2.2: the direct short-interval weighted tail-gap integrand rewrites as a
single negative pairing against the combined live operator. -/
private theorem weightedTailGapPrimitiveIntegrand_eq_negCombinedPairing
    {F : E → ℝ} {x y u wz : E} {τ t : ℝ} :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian F (x + q • d) u)
    let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian F) (x + q • d) d) u)
    let K : E →L[ℝ] E :=
      a • (hessian F (x + t • d) - hessian F z) +
        (1 - t * a) • fderiv ℝ (hessian F) (x + t • d) d
    ((((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ t)) -
        (((1 - τ * a) / (1 - t * a)) * θ t) =
      -(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u)) := by
  -- Expand the direct short-interval integrand once so the unresolved content becomes a single
  -- pairing against the combined live operator `K`.
  dsimp
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, inner_add_right,
    inner_sub_right, inner_smul_right]
  ring

/-- Helper for Lemma 5.2.2: the sharp fixed-`z` blocker is the scaled same-metric pairing bound
for the combined live operator on the short interval. -/
private theorem weightedTailGapPrimitiveScaledCombinedPairingBoundAtZ
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ))) {τ t : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let p := x + t • d
    let K : E →L[ℝ] E :=
      a • (hessian F p - hessian F z) + (1 - t * a) • fderiv ℝ (hessian F) p d
    |(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤
      ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[F; z]) *
        ‖u‖[F; x] := by
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let p : E := x + t • d
  let K : E →L[ℝ] E :=
    a • (hessian F p - hessian F z) + (1 - t * a) • fderiv ℝ (hessian F) p d
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x d)
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hta_le_a : t * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right ht.2 ha_nonneg
  have hτa_le_a : τ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have htfactor_pos : 0 < 1 - t * a := by
    linarith
  have hτfactor_nonneg : 0 ≤ 1 - τ * a := by
    linarith
  by_cases htτ : t = τ
  · subst htτ
    -- At the fixed endpoint `p = z`, the Hessian-gap term vanishes and only the weighted live
    -- third-derivative estimate remains.
    have hsame :
        |inner ℝ wz ((fderiv ℝ (hessian F) z d) u)| ≤
          ((2 * a) / ((1 - τ * a) * (1 - τ * a))) * ‖wz‖[F; z] * ‖u‖[F; x] := by
      simpa [r, a, z, d] using
        pointwiseSegmentHessianDerivPairingBoundAtSegmentPoint
          (F := F) (x := x) (y := y) (u := u) (w := wz) hx hy hxy (τ := τ) hτ (s := τ)
            ⟨hτ.1, le_rfl⟩
    have hscaled := mul_le_mul_of_nonneg_left hsame hτfactor_nonneg
    simpa [K, z, p, htfactor_pos.ne', abs_of_nonneg hτfactor_nonneg, mul_assoc, mul_left_comm,
      mul_comm, div_eq_mul_inv, ContinuousLinearMap.sub_self] using hscaled
  · -- TODO: the remaining interior case `t < τ` needs the fixed-`z` short-subsegment Loewner or
    -- right-difference-quotient estimate for the combined operator `K`, now that the endpoint
    -- branch and the `p → z` comparison helpers are available.
    sorry

/-- Helper for Lemma 5.2.2: once the direct short-interval integrand is rewritten as one pairing,
the sharp reciprocal-square majorant reduces to the combined fixed-`z` pairing estimate. -/
private theorem weightedTailGapPrimitiveIntegrandBoundAtZ
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ))) {τ s t : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) (ht : t ∈ Set.Icc s τ) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian F (x + q • d) u)
    let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian F) (x + q • d) d) u)
    |((((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ t)) -
        (((1 - τ * a) / (1 - t * a)) * θ t)| ≤
      ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[F; z]) *
        ‖u‖[F; x] := by
  -- Route correction: rewrite the shell as one combined pairing, then isolate the remaining
  -- blocker as the fixed-`z` same-metric operator bound.
  dsimp
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian F (x + q • d) u)
  let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian F) (x + q • d) d) u)
  let K : E →L[ℝ] E :=
    a • (hessian F (x + t • d) - hessian F z) +
      (1 - t * a) • fderiv ℝ (hessian F) (x + t • d) d
  have ht0τ : t ∈ Set.Icc (0 : ℝ) τ := ⟨le_trans hs.1 ht.1, ht.2⟩
  have hrewrite :
      ((((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ t)) -
          (((1 - τ * a) / (1 - t * a)) * θ t) =
        -(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u)) := by
    simpa [r, a, d, z, ψ, θ, K] using
      weightedTailGapPrimitiveIntegrand_eq_negCombinedPairing
        (Mf := Mf) (F := F) (x := x) (y := y) (u := u) (wz := wz) (τ := τ) (t := t)
  have hpair :
      |(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤
        ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[F; z]) *
          ‖u‖[F; x] := by
    -- The open frontier is now exactly the combined fixed-`z` pairing estimate.
    simpa [r, a, d, z, K] using
      weightedTailGapPrimitiveScaledCombinedPairingBoundAtZ
        (F := F) (x := x) (y := y) (u := u) (wz := wz) hx hy hxy (τ := τ) (t := t) hτ ht0τ
  calc
    |((((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ t)) -
          (((1 - τ * a) / (1 - t * a)) * θ t)|
        = | -(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u)) | := by
            rw [hrewrite]
    _ = |(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| := by
          rw [abs_neg]
    _ ≤
        ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[F; z]) *
          ‖u‖[F; x] := hpair

/-- Helper for Lemma 5.2.2: the reciprocal-square majorant factors the fixed endpoint norms
completely out of the short-interval integral. -/
private theorem weightedTailGapMajorantIntegralFactor
    {a τ s C B : ℝ} :
    ∫ t in s..τ, ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * C) * B
      =
        (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) * C) * B := by
  -- Pull the constant endpoint norms out of the majorant before evaluating the reciprocal-square
  -- kernel.
  calc
    ∫ t in s..τ, ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * C) * B
        =
          (∫ t in s..τ,
            (((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * C) * B := by
              rw [intervalIntegral.integral_mul_const]
    _ =
        ((∫ t in s..τ,
          ((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * C) * B := by
            rw [intervalIntegral.integral_mul_const]
    _ =
        (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) * C) * B := by
          congr 2
          simpa [mul_assoc] using
            (intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
              (a := (1 - τ * a))
              (f := fun t : ℝ ↦ (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)
              (a := s) (b := τ))

/-- Helper for Lemma 5.2.2: once the short-interval shell is rewritten directly and bounded
pointwise, the primitive drop at the fixed endpoint `z` is controlled by the reciprocal-square
kernel without reopening the older by-parts shell. -/
private theorem weightedTailGapPrimitiveIntegralMajorantAtZ
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ))) {τ s : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian F (x + q • d) u)
    let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian F) (x + q • d) d) u)
    let Φ : ℝ → ℝ := fun q ↦
      inner ℝ wz ((((1 - τ * a) / (1 - q * a)) • (hessian F (x + q • d) - hessian F z)) u)
    |Φ s - Φ τ| ≤
      (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) * ‖wz‖[F; z]) *
        ‖u‖[F; x] := by
  -- Route correction: keep the direct short-interval shell in its stabilized spelling and consume
  -- the new pointwise integrand bound instead of reopening the old by-parts normalization.
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian F (x + q • d) u)
  let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian F) (x + q • d) d) u)
  let Φ : ℝ → ℝ := fun q ↦
    inner ℝ wz ((((1 - τ * a) / (1 - q * a)) • (hessian F (x + q • d) - hessian F z)) u)
  let ω : ℝ → ℝ := fun q ↦ ((1 - τ * a) / (1 - q * a)) * θ q
  let K : ℝ → ℝ := fun q ↦
    ((((1 - τ * a) * a) * ((1 - q * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ q))
  let integrand : ℝ → ℝ := fun q ↦ K q - ω q
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hden_pos : ∀ t ∈ Set.Icc s τ, 0 < 1 - t * a := by
    intro t ht
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
    have hta_le_τa : t * a ≤ τ * a := by
      simpa using mul_le_mul_of_nonneg_right ht.2 ha_nonneg
    have hτa_le_a : τ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    have hta_lt_one : t * a < 1 := by
      linarith [ha_lt_one, hta_le_τa, hτa_le_a]
    linarith
  have hψ_cont : ContinuousOn ψ (Set.Icc s τ) := by
    -- The scalarized Hessian line stays continuous on the short interval.
    simpa [ψ, d] using
      scalarizedHessianLineContinuousOn
        (F := F) hself (x := x) (y := y) (u := u) (w := wz) hx hy hτ hs
  have hθ_cont : ContinuousOn θ (Set.Icc s τ) := by
    -- The scalarized third-derivative line is continuous on the same interval.
    simpa [θ, d] using
      scalarizedHessianLineDerivContinuousOn
        (F := F) hself (x := x) (y := y) (u := u) (w := wz) hx hy hτ hs
  have hψ_deriv :
      ∀ t ∈ Set.Ioo s τ, HasDerivAt ψ (θ t) t := by
    intro t ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans hs.1 (le_of_lt ht.1), le_trans (le_of_lt ht.2) hτ.2⟩
    have hxt : x + t • d ∈ dom := by
      exact hsegment_dom (segmentPoint_mem_segment ht01)
    -- Differentiate the scalarized Hessian line at the live short-segment point.
    simpa [ψ, θ, d] using
      scalarizedHessianLineHasDerivAt
        (F := F) hself (x := x) (d := d) (u := u) (w := wz) (t := t) hxt
  have hω_cont : ContinuousOn ω (Set.Icc s τ) := by
    have hweight_cont :
        ContinuousOn (fun t : ℝ ↦ ((1 - τ * a) / (1 - t * a))) (Set.Icc s τ) := by
      -- The fixed-endpoint rational weight is continuous because its denominator stays positive.
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 - t * a) by continuity).continuousOn
      · intro t ht
        exact (hden_pos t ht).ne'
    exact hweight_cont.mul hθ_cont
  have hω_int : IntervalIntegrable ω MeasureTheory.volume s τ :=
    hω_cont.intervalIntegrable_of_Icc hs.2
  have hK_cont : ContinuousOn K (Set.Icc s τ) := by
    have hpow_inv :
        ContinuousOn (fun t : ℝ ↦ ((1 - t * a) ^ (2 : ℕ))⁻¹) (Set.Icc s τ) := by
      have hbase :
          ContinuousOn
            (fun t : ℝ ↦ (1 : ℝ) / (1 - t * a) ^ (2 : ℕ)) (Set.Icc s τ) := by
        refine continuousOn_const.div ?_ ?_
        · exact
            (show Continuous (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) by continuity).continuousOn
        · intro t ht
          exact pow_ne_zero 2 ((hden_pos t ht).ne')
      simpa [one_div] using hbase
    have hkernel_weight :
        ContinuousOn
          (fun t : ℝ ↦ (((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹))
          (Set.Icc s τ) := by
      simpa [mul_assoc] using ((continuous_const.mul continuous_const).continuousOn.mul hpow_inv)
    have hgap_cont : ContinuousOn (fun t : ℝ ↦ ψ τ - ψ t) (Set.Icc s τ) := by
      exact continuous_const.continuousOn.sub hψ_cont
    exact hkernel_weight.mul hgap_cont
  have hintegrand_cont : ContinuousOn integrand (Set.Icc s τ) := hK_cont.sub hω_cont
  have hintegrand_int : IntervalIntegrable integrand MeasureTheory.volume s τ :=
    hintegrand_cont.intervalIntegrable_of_Icc hs.2
  have habs_integrand_int :
      IntervalIntegrable (fun t : ℝ ↦ |integrand t|) MeasureTheory.volume s τ := by
    simpa [Real.norm_eq_abs] using hintegrand_int.norm
  have hΦτ : Φ τ = 0 := by
    -- At the fixed endpoint `τ`, the primitive vanishes because the Hessian gap is zero.
    simp [Φ, z]
  have htail_identity :
      Φ s - Φ τ = ∫ t in s..τ, K t - ω t := by
    -- Evaluate the weighted tail-gap identity on `[s, τ]` in the primitive spelling.
    calc
      Φ s - Φ τ = Φ s := by
        rw [hΦτ]
        ring
      _ = ((1 - τ * a) / (1 - s * a)) * (ψ s - ψ τ) := by
        simp [Φ, ψ, z, ContinuousLinearMap.sub_apply, inner_sub_right, inner_smul_right]
      _ = ∫ t in s..τ, K t - ω t := by
        simpa [K, ω] using
          weightedTailGapEndpointIdentityOnIcc
            (a := a) (τ := τ) (s0 := s) (ψ := ψ) (θ := θ)
            hs.2 hψ_cont hθ_cont hψ_deriv hden_pos
  have htail_integrand :
      Φ s - Φ τ = ∫ t in s..τ, integrand t := by
    -- Keep the shell in its original `K - ω` spelling before applying the pointwise bound.
    simpa [integrand] using htail_identity
  have hmajorant_cont :
      ContinuousOn
        (fun t : ℝ ↦
          ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[F; z]) *
            ‖u‖[F; x])
        (Set.Icc s τ) := by
    have hpow_inv :
        ContinuousOn (fun t : ℝ ↦ ((1 - t * a) ^ (2 : ℕ))⁻¹) (Set.Icc s τ) := by
      have hbase :
          ContinuousOn
            (fun t : ℝ ↦ (1 : ℝ) / (1 - t * a) ^ (2 : ℕ)) (Set.Icc s τ) := by
        refine continuousOn_const.div ?_ ?_
        · exact
            (show Continuous (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) by continuity).continuousOn
        · intro t ht
          exact pow_ne_zero 2 ((hden_pos t ht).ne')
      simpa [one_div] using hbase
    have hkernel_cont :
        ContinuousOn
          (fun t : ℝ ↦ (((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹))
          (Set.Icc s τ) := by
      simpa [mul_assoc] using ((continuous_const.mul continuous_const).continuousOn.mul hpow_inv)
    exact (hkernel_cont.mul continuous_const.continuousOn).mul continuous_const.continuousOn
  have hmajorant_int :
      IntervalIntegrable
        (fun t : ℝ ↦
          ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[F; z]) *
            ‖u‖[F; x])
        MeasureTheory.volume s τ := by
    exact hmajorant_cont.intervalIntegrable_of_Icc hs.2
  have hintegrand_pointwise :
      ∀ t ∈ Set.Icc s τ,
        |integrand t| ≤
          ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[F; z]) *
            ‖u‖[F; x] := by
    intro t ht
    -- Consume the direct pointwise short-interval shell estimate in the stabilized local spelling.
    simpa [integrand, K, ω, r, a, d, z, ψ, θ] using
      weightedTailGapPrimitiveIntegrandBoundAtZ
        (F := F) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (s := s) (t := t) hτ hs ht
  calc
    |Φ s - Φ τ| = |∫ t in s..τ, integrand t| := by
      rw [htail_integrand]
    _ ≤ ∫ t in s..τ, |integrand t| := by
          simpa [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm
              (f := integrand) (μ := MeasureTheory.volume) (a := s) (b := τ) hs.2)
    _ ≤
        ∫ t in s..τ,
          ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[F; z]) *
            ‖u‖[F; x] := by
          exact intervalIntegral.integral_mono_on
            (μ := MeasureTheory.volume) (a := s) (b := τ)
            (f := fun t : ℝ ↦ |integrand t|)
            (g := fun t : ℝ ↦
              ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[F; z]) *
                ‖u‖[F; x])
            hs.2 habs_integrand_int hmajorant_int hintegrand_pointwise
    _ = (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) *
          ‖wz‖[F; z]) * ‖u‖[F; x] := by
          simpa [z] using
            weightedTailGapMajorantIntegralFactor
              (a := a) (τ := τ) (s := s) (C := ‖wz‖[F; z]) (B := ‖u‖[F; x])

/-- Helper for Lemma 5.2.2: before reading off a dual norm at the fixed endpoint `z`, the
inverse-Hessian witness there should already satisfy the sharp short-interval pairing bound
against the weighted primitive covector. -/
private theorem weightedTailGapPrimitiveSegmentEndpointWitnessBoundAtZ
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ)
    (hz : x + τ • (y - x) ∈ dom) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    let Hz := hessian F z
    let v := (((1 - τ * a) / (1 - s * a)) • (hessian F p - Hz)) u
    let wz := Hz.inverse v
    |inner ℝ wz v| ≤
      (((2 * (τ - s) * a) / (1 - s * a)) * ‖wz‖[F; z]) * ‖u‖[F; x] := by
  -- Route correction: first rewrite the weighted primitive as the drop `Φ s - Φ τ`, then isolate
  -- the remaining blocker as the sharp short-interval integral majorant.
  dsimp
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let Hz : E →L[ℝ] E := hessian F z
  let v : E := (((1 - τ * a) / (1 - s * a)) • (hessian F p - Hz)) u
  let wz : E := Hz.inverse v
  let Φ : ℝ → ℝ := fun t ↦
    inner ℝ wz ((((1 - τ * a) / (1 - t * a)) • (hessian F (x + t • d) - Hz)) u)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x d)
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsa_le_ta : s * a ≤ τ * a := by
    simpa using mul_le_mul_of_nonneg_right hs.2 ha_nonneg
  have hτa_le_a : τ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hsfactor_pos : 0 < 1 - s * a := by
    linarith
  have hτfactor_pos : 0 < 1 - τ * a := by
    linarith
  have hΦτ : Φ τ = 0 := by
    -- At the fixed endpoint `τ`, the weighted primitive vanishes because the Hessian gap is zero.
    simp [Φ, z, Hz]
  have hΦs : Φ s = inner ℝ wz v := by
    -- At the left endpoint `s`, the weighted primitive is exactly the target witness pairing.
    simp [Φ, p, z, Hz, v]
  have hprimitive_rewrite : |inner ℝ wz v| = |Φ s - Φ τ| := by
    -- Rewrite the target pairing as the primitive drop on `[s, τ]`.
    rw [hΦs, hΦτ]
    simp
  have hprimitive_bound :
      |Φ s - Φ τ| ≤
        (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) * ‖wz‖[F; z]) *
          ‖u‖[F; x] := by
    -- The primitive drop is now delegated to the direct short-interval integrand majorant in the
    -- fixed metric at `z`, so the remaining blocker has been isolated upstream.
    simpa [r, a, d, p, z, Hz] using
      weightedTailGapPrimitiveIntegralMajorantAtZ
        (F := F) (x := x) (y := y) (u := u) (wz := wz) hx hy hxy (τ := τ) (s := s) hτ hs
  have hkernel :
      (1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) =
        (2 * (τ - s) * a) / (1 - s * a) := by
    -- Evaluate the short-interval reciprocal-square kernel before the final witness estimate.
    calc
      (1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)
          = (1 - τ * a) * (2 * ∫ t in s..τ, a * ((1 - t * a) ^ (2 : ℕ))⁻¹) := by
              congr 1
              calc
                ∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹
                    = ∫ t in s..τ, 2 * (a * ((1 - t * a) ^ (2 : ℕ))⁻¹) := by
                        refine intervalIntegral.integral_congr ?_
                        intro t ht
                        ring
                _ = 2 * ∫ t in s..τ, a * ((1 - t * a) ^ (2 : ℕ))⁻¹ := by
                        rw [intervalIntegral.integral_const_mul]
      _ = (1 - τ * a) *
            (2 * (((τ - s) * a) / ((1 - τ * a) * (1 - s * a)))) := by
              rw [segmentReciprocalSquareIntegralBetween (τ := τ) (s := s) hτ hs ha_lt_one]
      _ = (2 * (τ - s) * a) / (1 - s * a) := by
              field_simp [hτfactor_pos.ne', hsfactor_pos.ne']
  calc
    |inner ℝ wz v| = |Φ s - Φ τ| := hprimitive_rewrite
    _ ≤
        (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) * ‖wz‖[F; z]) *
          ‖u‖[F; x] := hprimitive_bound
    _ = (((2 * (τ - s) * a) / (1 - s * a)) * ‖wz‖[F; z]) * ‖u‖[F; x] := by
          rw [hkernel]

/-- Helper for Lemma 5.2.2: the fixed-`τ` endpoint-witness residual estimate is the remaining
pointwise frontier for the endpoint-metric route. -/
private theorem segmentPointDualLocalNorm_le_endpointFactor_ofPosDefMem
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (v : E) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E v) ≤
      ((1 - τ * a) / (1 - a)) *
        HessianDualLocalNorm.ofPosDefMem F
          (show z ∈ dom from
            (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) F).convex_domain.segment_subset
              hx hy (segmentPoint_mem_segment hτ))
          (toDual ℝ E v) := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  let ρ : ℝ := ‖y - z‖[F; z]
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hz : z ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy (segmentPoint_mem_segment hτ)
  have htail :
      ρ ≤ ((1 - τ) * r) / (1 - τ * a) := by
    -- Control the short tail radius in the fixed metric at `z`.
    simpa [r, a, z, ρ] using
      segmentTailLocalNormLe (F := F) (x := x) (y := y) hx hy hxy (τ := τ) hτ
  have hρ_lt : ρ < 1 / (Mf : ℝ) := by
    have hτa_le_a : τ * a ≤ a := by
      have ha_nonneg : 0 ≤ a := by
        dsimp [a]
        exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    have hfactor_posτ : 0 < 1 - τ * a := by
      linarith
    have htail_lt : ((1 - τ) * r) / (1 - τ * a) < 1 / (Mf : ℝ) := by
      have hmul :
          (Mf : ℝ) * (((1 - τ) * r) / (1 - τ * a)) < 1 := by
        have hrew :
            (Mf : ℝ) * (((1 - τ) * r) / (1 - τ * a)) =
              ((1 - τ) * a) / (1 - τ * a) := by
          dsimp [a]
          field_simp [hfactor_posτ.ne']
        rw [hrew]
        have hnum_lt_den : (1 - τ) * a < 1 - τ * a := by
          linarith
        exact (div_lt_iff₀ hfactor_posτ).2 (by simpa using hnum_lt_den)
      exact (lt_div_iff₀ hMf_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    exact lt_of_le_of_lt htail htail_lt
  have hzy : y ∈ W⁰[F; z](1 / (Mf : ℝ)) := by
    -- Repackage the tail-radius estimate as the required Dikin-membership witness at `z`.
    exact (mem_openDikinEllipsoid_iff F z y (1 / (Mf : ℝ))).2 hρ_lt
  have hρ_factor :
      1 / (1 - (Mf : ℝ) * ρ) ≤ (1 - τ * a) / (1 - a) := by
    have hden_posρ : 0 < 1 - (Mf : ℝ) * ρ := by
      have hmul_lt_one : (Mf : ℝ) * ρ < 1 := by
        simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
      linarith
    have hτa_factor_pos : 0 < 1 - τ * a := by
      have hτa_le_a : τ * a ≤ a := by
        have ha_nonneg : 0 ≤ a := by
          dsimp [a]
          exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
        simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
      linarith
    have hρ_upper : (Mf : ℝ) * ρ ≤ ((1 - τ) * a) / (1 - τ * a) := by
      have hMf_nonneg : 0 ≤ (Mf : ℝ) := le_of_lt hMf_pos
      have hρ_upper_raw := mul_le_mul_of_nonneg_left htail hMf_nonneg
      dsimp [ρ, a] at hρ_upper_raw ⊢
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hρ_upper_raw
    have hfactor_lower :
        (1 - a) / (1 - τ * a) ≤ 1 - (Mf : ℝ) * ρ := by
      have hrewrite :
          1 - ((1 - τ) * a) / (1 - τ * a) = (1 - a) / (1 - τ * a) := by
        field_simp [hτa_factor_pos.ne']
        ring
      rw [← hrewrite]
      linarith
    have hleft_pos : 0 < (1 - a) / (1 - τ * a) := by
      have hnum_pos : 0 < 1 - a := by
        linarith
      exact div_pos hnum_pos hτa_factor_pos
    have hrecip :
        1 / (1 - (Mf : ℝ) * ρ) ≤ 1 / ((1 - a) / (1 - τ * a)) := by
      exact (one_div_le_one_div hden_posρ hleft_pos).2 hfactor_lower
    simpa [div_eq_mul_inv] using hrecip
  have hδz_nonneg :
      0 ≤ HessianDualLocalNorm.ofPosDefMem F hz (toDual ℝ E v) := by
    simp [HessianDualLocalNorm.ofPosDefMem_def]
  have htransport :
      HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E v) ≤
        (1 / (1 - (Mf : ℝ) * ρ)) * HessianDualLocalNorm.ofPosDefMem F hz (toDual ℝ E v) := by
    -- Transport the same covector once from `z` to `y` through the short tail segment.
    simpa [ρ] using
      hessianDualLocalNorm_ofPosDefMem_le_mul_of_mem_openDikinEllipsoid
        (F := F) (x := z) (y := y) hz hy hzy
  calc
    HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E v) ≤
        (1 / (1 - (Mf : ℝ) * ρ)) * HessianDualLocalNorm.ofPosDefMem F hz (toDual ℝ E v) :=
      htransport
    _ ≤ ((1 - τ * a) / (1 - a)) * HessianDualLocalNorm.ofPosDefMem F hz (toDual ℝ E v) := by
      exact mul_le_mul_of_nonneg_right hρ_factor hδz_nonneg

/-- Helper for Lemma 5.2.2: the remaining sharp primitive estimate is the fixed-endpoint dual
bound for the weighted Hessian gap on a short interval `[s, τ]`. -/
private theorem weightedTailGapPrimitiveSegmentDualBoundAtZ
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ)
    (hz : x + τ • (y - x) ∈ dom) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    HessianDualLocalNorm.ofPosDefMem F hz
      (toDual ℝ E ((((1 - τ * a) / (1 - s * a)) • (hessian F p - hessian F z)) u)) ≤
      ((2 * (τ - s) * a) / (1 - s * a)) * ‖u‖[F; x] := by
  -- Route correction: realize the fixed-endpoint dual norm by its inverse-Hessian witness at `z`,
  -- then delegate the remaining work to the witness-specific primitive pairing estimate.
  dsimp
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let v : E := (((1 - τ * a) / (1 - s * a)) • (hessian F p - hessian F z)) u
  let wz : E := (hessian F z).inverse v
  let δ : ℝ := HessianDualLocalNorm.ofPosDefMem F hz (toDual ℝ E v)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x d)
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsa_le_ta : s * a ≤ τ * a := by
    simpa using mul_le_mul_of_nonneg_right hs.2 ha_nonneg
  have hsfactor_pos : 0 < 1 - s * a := by
    have hτa_le_a : τ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    linarith
  have hcoeff_nonneg : 0 ≤ ((2 * (τ - s) * a) / (1 - s * a)) := by
    have hnum_nonneg : 0 ≤ 2 * (τ - s) * a := by
      exact mul_nonneg (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) (sub_nonneg.mpr hs.2)) ha_nonneg
    exact div_nonneg hnum_nonneg (le_of_lt hsfactor_pos)
  have hw_realize : ‖wz‖[F; z] = δ ∧ inner ℝ v wz = δ ^ (2 : ℕ) := by
    -- The inverse-Hessian witness at `z` realizes both the fixed-endpoint dual norm and its
    -- squared pairing.
    simpa [z, v, wz, δ] using
      (inverseHessianWitness_localNorm_eq_dual_and_pairing_ofPosDefMem (F := F) hz v)
  have hw_norm : ‖wz‖[F; z] = δ := hw_realize.1
  have hpair_sq : inner ℝ v wz = δ ^ (2 : ℕ) := hw_realize.2
  have hδ_nonneg : 0 ≤ δ := by
    change 0 ≤ HessianDualLocalNorm.ofPosDefMem F hz (toDual ℝ E v)
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    exact Real.sqrt_nonneg _
  have hvw_nonneg : 0 ≤ inner ℝ v wz := by
    rw [hpair_sq]
    positivity
  have hpair :
      |inner ℝ wz v| ≤
        (((2 * (τ - s) * a) / (1 - s * a)) * ‖wz‖[F; z]) * ‖u‖[F; x] := by
    -- This is the remaining same-metric primitive witness estimate at the fixed endpoint `z`.
    simpa [r, a, d, p, z, v, wz] using
      weightedTailGapPrimitiveSegmentEndpointWitnessBoundAtZ
        (F := F) (x := x) (y := y) (u := u) hx hy hxy (τ := τ) (s := s) hτ hs hz
  by_cases hδ_zero : δ = 0
  · -- If the realized dual norm vanishes, the target bound is immediate.
    have hrhs_nonneg :
        0 ≤ ((2 * (τ - s) * a) / (1 - s * a)) * ‖u‖[F; x] := by
      exact mul_nonneg hcoeff_nonneg (hessianLocalNorm_nonneg F x u)
    change δ ≤ ((2 * (τ - s) * a) / (1 - s * a)) * ‖u‖[F; x]
    simpa [hδ_zero] using hrhs_nonneg
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (by simpa [eq_comm] using hδ_zero)
    have hsq_bound :
        δ ^ (2 : ℕ) ≤
          ((2 * (τ - s) * a) / (1 - s * a)) * (δ * ‖u‖[F; x]) := by
      calc
        δ ^ (2 : ℕ) = inner ℝ v wz := by
          symm
          exact hpair_sq
        _ = |inner ℝ v wz| := by
          rw [abs_of_nonneg hvw_nonneg]
        _ = |inner ℝ wz v| := by
          rw [real_inner_comm]
        _ ≤ (((2 * (τ - s) * a) / (1 - s * a)) * ‖wz‖[F; z]) * ‖u‖[F; x] := hpair
        _ = ((2 * (τ - s) * a) / (1 - s * a)) * (δ * ‖u‖[F; x]) := by
          rw [hw_norm]
          ring
    -- Cancel the positive realized witness norm from the squared dual-norm bound.
    change δ ≤ ((2 * (τ - s) * a) / (1 - s * a)) * ‖u‖[F; x]
    nlinarith

/-- Helper for Lemma 5.2.2: once the primitive covector is controlled in the fixed endpoint
metric `z`, its inverse endpoint image at `y` inherits the sharp endpoint-metric norm bound. -/
private theorem weightedTailGapPrimitiveEndpointImageLocalNormBound
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    let He := hessian F y
    let q := He.inverse ((((1 - τ * a) / (1 - s * a)) • (hessian F p - hessian F z)) u)
    ‖q‖[F; y] ≤
      (((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) * ‖u‖[F; x] := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let He : E →L[ℝ] E := hessian F y
  let v : E := (((1 - τ * a) / (1 - s * a)) • (hessian F p - hessian F z)) u
  let q : E := He.inverse v
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hz : z ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy (segmentPoint_mem_segment hτ)
  have hfactor_nonneg : 0 ≤ (1 - τ * a) / (1 - a) := by
    have hτa_le_a : τ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    have hden_pos : 0 < 1 - a := by
      linarith
    have hnum_nonneg : 0 ≤ 1 - τ * a := by
      linarith
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hq_norm :
      ‖q‖[F; y] = HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E v) := by
    -- The endpoint inverse-Hessian image realizes the endpoint dual norm of the primitive
    -- covector.
    simpa [He, q, v] using
      (inverseHessianWitness_localNorm_eq_dual_and_pairing_ofPosDefMem (F := F) hy v).1
  have hδy_le :
      HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E v) ≤
        ((1 - τ * a) / (1 - a)) * HessianDualLocalNorm.ofPosDefMem F hz (toDual ℝ E v) := by
    -- Transport the primitive covector from the fixed metric at `z` to the true endpoint metric
    -- at `y` exactly once.
    simpa [r, a, d, p, z, v] using
      segmentPointDualLocalNorm_le_endpointFactor_ofPosDefMem
        (F := F) (x := x) (y := y) hx hy hxy (τ := τ) hτ v
  have hδz_le :
      HessianDualLocalNorm.ofPosDefMem F hz (toDual ℝ E v) ≤
        ((2 * (τ - s) * a) / (1 - s * a)) * ‖u‖[F; x] := by
    -- This is the single same-metric primitive frontier still left open.
    simpa [r, a, d, p, z, v] using
      weightedTailGapPrimitiveSegmentDualBoundAtZ
        (F := F) (x := x) (y := y) (u := u) hx hy hxy (τ := τ) (s := s) hτ hs hz
  calc
    ‖q‖[F; y] = HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E v) := hq_norm
    _ ≤ ((1 - τ * a) / (1 - a)) * HessianDualLocalNorm.ofPosDefMem F hz (toDual ℝ E v) :=
      hδy_le
    _ ≤ ((1 - τ * a) / (1 - a)) * (((2 * (τ - s) * a) / (1 - s * a)) * ‖u‖[F; x]) := by
      exact mul_le_mul_of_nonneg_left hδz_le hfactor_nonneg
    _ = (((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) * ‖u‖[F; x] := by
      ring

/-- Helper for Lemma 5.2.2: pairing the endpoint witness with the weighted primitive covector is
the same as pairing the endpoint primitive image with the averaged-Hessian residual. -/
private theorem weightedTailGapPrimitive_pairing_eq_averageResidualImage
    {F : E → ℝ} [HasPositiveDefiniteHessianOn dom F]
    {x y u : E} (hy : y ∈ dom) {τ s : ℝ} :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    let H := hessian F x
    let G := ∫ σ in (0 : ℝ)..1, hessian F (x + σ • d)
    let k := (H - G) u
    let He := hessian F y
    let w := He.inverse k
    let v := (((1 - τ * a) / (1 - s * a)) • (hessian F p - hessian F z)) u
    let q := He.inverse v
    inner ℝ w v = inner ℝ q k := by
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let H : E →L[ℝ] E := hessian F x
  let G : E →L[ℝ] E := ∫ σ in (0 : ℝ)..1, hessian F (x + σ • d)
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian F y
  let w : E := He.inverse k
  let v : E := (((1 - τ * a) / (1 - s * a)) • (hessian F p - hessian F z)) u
  let q : E := He.inverse v
  let hHeInv : He.IsInvertible := hessian_isInvertible_of_det_ne_zero
    (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy)
  have hw_apply : He w = k := by
    -- Unfold the endpoint witness once.
    simpa [He, w, k] using hHeInv.self_apply_inverse k
  have hq_apply : He q = v := by
    -- Unfold the auxiliary endpoint image once.
    simpa [He, q, v] using hHeInv.self_apply_inverse v
  have hHe_symm : He.IsSymmetric := by
    simpa [He] using (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hy).isSymmetric
  calc
    inner ℝ w v = inner ℝ w (He q) := by rw [hq_apply]
    _ = inner ℝ (He w) q := by
          simpa [real_inner_comm] using hHe_symm q w
    _ = inner ℝ k q := by rw [hw_apply]
    _ = inner ℝ q k := by rw [real_inner_comm]

/-- Helper for Lemma 5.2.2: once the primitive image `q` is controlled at the endpoint `y`, the
endpoint witness pairing follows from the endpoint Cauchy estimate. -/
private theorem weightedTailGapPrimitiveBoundAtEndpointViaWitnessImage
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    let H := hessian F x
    let G := ∫ σ in (0 : ℝ)..1, hessian F (x + σ • d)
    let k := (H - G) u
    let He := hessian F y
    let w := He.inverse k
    let v := (((1 - τ * a) / (1 - s * a)) • (hessian F p - hessian F z)) u
    |inner ℝ w v| ≤
      ((((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) *
        ‖w‖[F; y]) * ‖u‖[F; x] := by
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let H : E →L[ℝ] E := hessian F x
  let G : E →L[ℝ] E := ∫ σ in (0 : ℝ)..1, hessian F (x + σ • d)
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian F y
  let w : E := He.inverse k
  let v : E := (((1 - τ * a) / (1 - s * a)) • (hessian F p - hessian F z)) u
  let q : E := He.inverse v
  let δres : ℝ := HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E k)
  have hw_norm : ‖w‖[F; y] = δres := by
    -- The endpoint inverse-Hessian witness realizes the dual norm of the averaged residual `k`.
    simpa [He, w, δres, k] using
      (inverseHessianWitness_localNorm_eq_dual_and_pairing_ofPosDefMem (F := F) hy k).1
  have hδres_nonneg : 0 ≤ δres := by
    simp [δres, HessianDualLocalNorm.ofPosDefMem_def]
  have hdual_apply :
      |inner ℝ q k| ≤ δres * ‖q‖[F; y] := by
    -- Test the averaged residual against the endpoint primitive image in the endpoint metric.
    simpa [δres, real_inner_comm] using
      abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm_ofPosDefMem
        (F := F) hy k q
  have hq_bound :
      ‖q‖[F; y] ≤
        (((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) * ‖u‖[F; x] := by
    -- This is the isolated endpoint-image estimate for the primitive vector.
    simpa [r, a, d, p, z, He, v, q] using
      weightedTailGapPrimitiveEndpointImageLocalNormBound
        (F := F) (x := x) (y := y) (u := u) hx hy hxy (τ := τ) (s := s) hτ hs
  calc
    |inner ℝ w v| = |inner ℝ q k| := by
      rw [weightedTailGapPrimitive_pairing_eq_averageResidualImage
        (F := F) (x := x) (y := y) (u := u) hy (τ := τ) (s := s)]
    _ ≤ δres * ‖q‖[F; y] := hdual_apply
    _ ≤ δres *
          ((((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) * ‖u‖[F; x]) := by
            exact mul_le_mul_of_nonneg_left hq_bound hδres_nonneg
    _ = ((((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) *
          ‖w‖[F; y]) * ‖u‖[F; x] := by
          rw [← hw_norm]
          ring

/-- Helper for Lemma 5.2.2: the fixed-`τ` endpoint-witness residual estimate now reduces to the
primitive endpoint-image theorem specialized at `s = 0`. -/
private theorem pointwiseSegmentResidualEndpointWitnessBoundAtSegmentPoint
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let H := hessian F x
    let z := x + τ • (y - x)
    let G := ∫ σ in (0 : ℝ)..1, hessian F (x + σ • (y - x))
    let k := (H - G) u
    let He := hessian F y
    let w := He.inverse k
    |inner ℝ w ((H - hessian F z) u)| ≤
      ((2 * τ * a) / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x] := by
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian F x
  let z : E := x + τ • (y - x)
  let G : E →L[ℝ] E := ∫ σ in (0 : ℝ)..1, hessian F (x + σ • (y - x))
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian F y
  let w : E := He.inverse k
  let d : E := y - x
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hτfactor_pos : 0 < 1 - τ * a := by
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
    have hτa_le_a : τ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    linarith
  have hs0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) τ := ⟨le_rfl, hτ.1⟩
  have hscaled_pointwise :
      |inner ℝ w ((1 - τ * a) • ((H - hessian F z) u))| ≤
        ((((1 - τ * a) / (1 - a)) * (2 * τ * a)) * ‖w‖[F; y]) * ‖u‖[F; x] := by
    -- Route correction: specialize the primitive endpoint-image theorem at `s = 0`.
    simpa [r, a, d, H, G, k, He, w, z] using
      weightedTailGapPrimitiveBoundAtEndpointViaWitnessImage
        (F := F) (x := x) (y := y) (u := u) hx hy hxy (τ := τ) (s := (0 : ℝ)) hτ hs0
  have hscaled :
      (1 - τ * a) * |inner ℝ w ((H - hessian F z) u)| ≤
        ((((1 - τ * a) / (1 - a)) * (2 * τ * a)) * ‖w‖[F; y]) * ‖u‖[F; x] := by
    -- Pull the positive scalar `1 - τ * a` into the pairing before canceling it at the end.
    calc
      (1 - τ * a) * |inner ℝ w ((H - hessian F z) u)| =
          |inner ℝ w ((1 - τ * a) • ((H - hessian F z) u))| := by
            rw [inner_smul_right, abs_mul, abs_of_nonneg (le_of_lt hτfactor_pos)]
      _ ≤ ((((1 - τ * a) / (1 - a)) * (2 * τ * a)) * ‖w‖[F; y]) * ‖u‖[F; x] :=
        hscaled_pointwise
  have htarget_scaled :
      (1 - τ * a) * |inner ℝ w ((H - hessian F z) u)| ≤
        (1 - τ * a) * (((2 * τ * a) / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x]) := by
    calc
      (1 - τ * a) * |inner ℝ w ((H - hessian F z) u)| ≤
          ((((1 - τ * a) / (1 - a)) * (2 * τ * a)) * ‖w‖[F; y]) * ‖u‖[F; x] := hscaled
      _ = (1 - τ * a) * (((2 * τ * a) / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x]) := by
          ring_nf
  exact le_of_mul_le_mul_left htarget_scaled hτfactor_pos

/-- Helper for Lemma 5.2.2: integrating the sharp fixed-`τ` endpoint-witness residual estimate
gives the full endpoint witness pairing bound for the averaged-Hessian residual. -/
private theorem averageHessianResidual_endpointWitnessBound
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let H := hessian F x
    let G := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (y - x))
    let k := (H - G) u
    let He := hessian F y
    let w := He.inverse k
    |inner ℝ w k| ≤
      (a / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x] := by
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian F x
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (y - x))
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian F y
  let w : E := He.inverse k
  let θ : ℝ → ℝ := fun τ ↦ inner ℝ w ((H - hessian F (x + τ • (y - x))) u)
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) F := inferInstance
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hHessCont : ContinuousOn (hessian F) dom := hessianContinuousOn hself
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hθ_cont : ContinuousOn θ (Set.Icc (0 : ℝ) 1) := by
    let Hτ : ℝ → E →L[ℝ] E := fun τ ↦ hessian F (x + τ • (y - x))
    have hHτ_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • (y - x)) (Set.Icc (0 : ℝ) 1) dom := by
      intro τ hτ
      exact hsegment_dom (segmentPoint_mem_segment hτ)
    have hHτ_cont : ContinuousOn Hτ (Set.Icc (0 : ℝ) 1) := by
      -- Restrict the continuous Hessian field to the affine segment used in the residual integral.
      simpa [Hτ] using
        hHessCont.comp
          (show Continuous (fun τ : ℝ ↦ x + τ • (y - x)) by continuity).continuousOn
          hHτ_maps
    let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E u
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
    have hscalar_cont :
        ContinuousOn (fun τ : ℝ ↦ inner ℝ w (Hτ τ u)) (Set.Icc (0 : ℝ) 1) := by
      simpa [Hτ, ev, φ, InnerProductSpace.toDual_apply_apply] using
        φ.continuous.comp_continuousOn (ev.continuous.comp_continuousOn hHτ_cont)
    -- Pairing against the fixed endpoint witness and subtracting the frozen base Hessian
    -- preserves continuity on the segment.
    have hdiff_cont :
        ContinuousOn (fun τ : ℝ ↦ inner ℝ w (H u) - inner ℝ w (Hτ τ u)) (Set.Icc (0 : ℝ) 1) :=
      continuous_const.continuousOn.sub hscalar_cont
    simpa [θ, Hτ, H, ContinuousLinearMap.sub_apply, inner_sub_right] using hdiff_cont
  have hθ_int : IntervalIntegrable θ MeasureTheory.volume 0 1 :=
    hθ_cont.intervalIntegrable_of_Icc (by norm_num)
  have hrewrite : inner ℝ w k = ∫ τ in (0 : ℝ)..1, θ τ := by
    -- Rewrite the endpoint witness pairing as the scalar segment integral of the pointwise
    -- residual integrand before taking absolute values.
    simpa [r, a, H, G, k, He, w, θ] using
      averageHessianResidual_endpointWitnessIntegralRewrite hself hx hy
  have hsharp_pointwise :
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        |θ τ| ≤ (((2 * a) / (1 - a)) * τ) * ‖w‖[F; y] * ‖u‖[F; x] := by
    intro τ hτ
    have hpoint :
        |inner ℝ w ((H - hessian F (x + τ • (y - x))) u)| ≤
          ((2 * τ * a) / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x] := by
      -- Consume the fixed-`τ` endpoint residual estimate in the current spelling.
      simpa [r, a, H, G, k, He, w] using
        pointwiseSegmentResidualEndpointWitnessBoundAtSegmentPoint hx hy hxy hτ
    calc
      |θ τ| = |inner ℝ w ((H - hessian F (x + τ • (y - x))) u)| := by
        simp [θ]
      _ ≤ ((2 * τ * a) / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x] := hpoint
      _ = (((2 * a) / (1 - a)) * τ) * ‖w‖[F; y] * ‖u‖[F; x] := by
        field_simp [hfactor_pos.ne']
  have habs_int : IntervalIntegrable (fun τ : ℝ ↦ |θ τ|) MeasureTheory.volume 0 1 :=
    hθ_int.abs
  have hmajorant_int :
      IntervalIntegrable
        (fun τ : ℝ ↦ (((2 * a) / (1 - a)) * τ) * ‖w‖[F; y] * ‖u‖[F; x])
        MeasureTheory.volume 0 1 := by
    -- The linear scalar majorant is interval-integrable on `[0, 1]`.
    exact
      (show Continuous
          (fun τ : ℝ ↦ (((2 * a) / (1 - a)) * τ) * ‖w‖[F; y] * ‖u‖[F; x]) by
          continuity).continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hnorm_int :
      ‖∫ τ in (0 : ℝ)..1, θ τ‖ ≤ ∫ τ in (0 : ℝ)..1, ‖θ τ‖ := by
    simpa using
      (show ‖∫ τ in (0 : ℝ)..1, θ τ‖ ≤ ∫ τ in (0 : ℝ)..1, ‖θ τ‖ from
        intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1))
  -- Integrate the sharp pointwise estimate and simplify the outer linear coefficient.
  calc
    |inner ℝ w k| = |∫ τ in (0 : ℝ)..1, θ τ| := by
      rw [hrewrite]
    _ ≤ ∫ τ in (0 : ℝ)..1, |θ τ| := by
      simpa [Real.norm_eq_abs] using hnorm_int
    _ ≤ ∫ τ in (0 : ℝ)..1, (((2 * a) / (1 - a)) * τ) * ‖w‖[F; y] * ‖u‖[F; x] := by
      exact intervalIntegral.integral_mono_on
        (by norm_num) habs_int hmajorant_int hsharp_pointwise
    _ = ∫ τ in (0 : ℝ)..1,
          ((((2 * a) / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x]) * τ) := by
        refine intervalIntegral.integral_congr ?_
        intro τ hτ
        ring
    _ = (((2 * a) / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x]) *
          ∫ τ in (0 : ℝ)..1, τ := by
        rw [intervalIntegral.integral_const_mul]
    _ = (((2 * a) / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x]) *
          (((1 : ℝ) ^ (2 : ℕ) - (0 : ℝ) ^ (2 : ℕ)) / 2) := by
        rw [integral_id]
    _ = (a / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x] := by
      field_simp [hfactor_pos.ne']
      ring

/-- Helper for Lemma 5.2.2: the missing sharp step is the endpoint-metric bound for the
averaged-Hessian residual. -/
private theorem averageHessianResidual_endpointDualBound
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[F; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[F; x]
    let a := (Mf : ℝ) * r
    let H := hessian F x
    let G := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (y - x))
    HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E ((H - G) u)) ≤
      (a / (1 - a)) * ‖u‖[F; x] := by
  let r : ℝ := ‖y - x‖[F; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian F x
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (y - x))
  let k : E := (H - G) u
  let δ : ℝ := HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E k)
  let He : E →L[ℝ] E := hessian F y
  let w : E := He.inverse k
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff F x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg F x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hw_realize : ‖w‖[F; y] = δ ∧ inner ℝ k w = δ ^ (2 : ℕ) := by
    -- The endpoint inverse-Hessian witness realizes both the endpoint dual norm and its square.
    have hw_realize_raw :
        ‖He.inverse k‖[F; y] = HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E k) ∧
          inner ℝ k (He.inverse k) =
            (HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E k)) ^ (2 : ℕ) :=
      inverseHessianWitness_localNorm_eq_dual_and_pairing_ofPosDefMem hy k
    simpa [He, w, δ] using hw_realize_raw
  have hw_norm : ‖w‖[F; y] = δ := hw_realize.1
  have hpair_sq : inner ℝ k w = δ ^ (2 : ℕ) := hw_realize.2
  have hδ_nonneg : 0 ≤ δ := by
    rw [show δ = HessianDualLocalNorm.ofPosDefMem F hy (toDual ℝ E k) by rfl]
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    exact Real.sqrt_nonneg _
  have hpair_nonneg : 0 ≤ inner ℝ k w := by
    rw [hpair_sq]
    positivity
  have hpair_bound :
      |inner ℝ w k| ≤ (a / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x] := by
    -- Test the endpoint witness bound against the inverse-Hessian witness at `y`.
    simpa [r, a, H, G, k, He, w, real_inner_comm, mul_assoc, mul_left_comm, mul_comm] using
      averageHessianResidual_endpointWitnessBound hx hy hxy
  change δ ≤ (a / (1 - a)) * ‖u‖[F; x]
  by_cases hzero : δ = 0
  · have hfactor_nonneg : 0 ≤ (a / (1 - a)) * ‖u‖[F; x] := by
      have hden_pos : 0 < 1 - a := by
        linarith
      exact mul_nonneg (div_nonneg ha_nonneg (le_of_lt hden_pos)) (hessianLocalNorm_nonneg F x u)
    simpa [hzero] using hfactor_nonneg
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (by simpa [eq_comm] using hzero)
    have hsq_bound : δ ^ (2 : ℕ) ≤ (a / (1 - a)) * (δ * ‖u‖[F; x]) := by
      calc
        δ ^ (2 : ℕ) = inner ℝ k w := by
          symm
          exact hpair_sq
        _ = |inner ℝ k w| := by
          rw [abs_of_nonneg hpair_nonneg]
        _ = |inner ℝ w k| := by
          rw [real_inner_comm]
        _ ≤ (a / (1 - a)) * ‖w‖[F; y] * ‖u‖[F; x] := hpair_bound
        _ = (a / (1 - a)) * (δ * ‖u‖[F; x]) := by
          rw [hw_norm]
          ring
    -- Cancel the positive endpoint witness norm from the squared dual-norm bound.
    nlinarith

/-- Helper for Lemma 5.2.2: under the cubic smallness condition, the variant `C` intermediate
Newton step satisfies the explicit decrement bound from `(5.2.8)`. This is the single missing
bridge needed to close the path-following centering estimate without importing the later
`Theorem_5_2_2` module. -/
private theorem intermediateNewtonDecrement_explicitBound
    {F : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) F]
    [HasPositiveDefiniteHessianOn dom F]
    {x : E} (hx : x ∈ dom) (hH : (hessian F x).det ≠ 0)
    (hsmall :
      let δ := ndec(F, x, (Mf : NNReal), hx, hH)
      (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤ 1)
    (hHPlus :
      let xPlus := selfConcordantNewtonNextPoint F (Mf : NNReal) .intermediate x hx hH
      (hessian F xPlus).det ≠ 0) :
    let δ := ndec(F, x, (Mf : NNReal), hx, hH)
    let xPlus := selfConcordantNewtonNextPoint F (Mf : NNReal) .intermediate x hx hH
    let hxPlus := intermediateNewtonNextPoint_mem_of_smallness hx hH hsmall
    ndec(F, xPlus, (Mf : NNReal), hxPlus, hHPlus) ≤
      ((Mf : ℝ) * δ ^ (2 : ℕ)) *
        (1 + (Mf : ℝ) * δ +
          ((Mf : ℝ) * δ) / (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) := by
  let δ := ndec(F, x, (Mf : NNReal), hx, hH)
  let xPlus := selfConcordantNewtonNextPoint F (Mf : NNReal) .intermediate x hx hH
  let hxPlus : xPlus ∈ dom := intermediateNewtonNextPoint_mem_of_smallness hx hH hsmall
  let H : E →L[ℝ] E := hessian F x
  let u : E := H.inverse (∇ F x)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian F (x + τ • (xPlus - x))
  let α : ℝ := selfConcordantNewtonStepSize F (Mf : NNReal) .intermediate x hx hH
  let a : ℝ := (Mf : ℝ) * ‖xPlus - x‖[F; x]
  let s : ℝ := (Mf : ℝ) * δ
  have hHPlus' : (hessian F xPlus).det ≠ 0 := by
    simpa [xPlus] using hHPlus
  let hPosPlus : (hessian F xPlus).IsPositive :=
    HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hxPlus
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg (Mf : NNReal) F hx hH
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) hδ_nonneg
  have hden_pos : 0 < 1 + s + s ^ (2 : ℕ) := by
    positivity
  have hα_eq : α = (1 + s) / (1 + s + s ^ (2 : ℕ)) := by
    dsimp [α, s]
    rw [intermediateStepSize_eq hx hH]
    ring
  have hα_nonneg : 0 ≤ α := by
    rw [hα_eq]
    positivity
  have h1mα_nonneg : 0 ≤ 1 - α := by
    rw [hα_eq]
    have hrew :
        1 - (1 + s) / (1 + s + s ^ (2 : ℕ)) =
          s ^ (2 : ℕ) / (1 + s + s ^ (2 : ℕ)) := by
      field_simp [hden_pos.ne']
      ring_nf
    rw [hrew]
    exact div_nonneg (sq_nonneg s) (le_of_lt hden_pos)
  have hstep_norm :
      ‖xPlus - x‖[F; x] =
        δ * (1 + (Mf : ℝ) * δ) /
          (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) := by
    have hstep :=
      nextPointSubLocalNormEqStepSizeMulNdec
        (Mf := (Mf : NNReal)) (F := F) .intermediate hx hH
    rw [intermediateStepSize_eq (Mf := Mf) (F := F) hx hH] at hstep
    simpa [δ, xPlus, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hstep
  have hstep_mem : xPlus ∈ W⁰[F; x](1 / ((Mf : NNReal) : ℝ)) := by
    refine (mem_openDikinEllipsoid_iff F x xPlus (1 / ((Mf : NNReal) : ℝ))).2 ?_
    rw [hstep_norm]
    exact intermediateStepLocalNorm_lt_inv (Mf := Mf) hδ_nonneg
  have ha_eq : a = s * (1 + s) / (1 + s + s ^ (2 : ℕ)) := by
    dsimp [a, s]
    rw [hstep_norm]
    ring
  have ha_lt_one : a < 1 := by
    have hMf_pos : 0 < (Mf : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
    have hnorm_lt : ‖xPlus - x‖[F; x] < 1 / (Mf : ℝ) := by
      simpa [xPlus] using (mem_openDikinEllipsoid_iff F x xPlus (1 / (Mf : ℝ))).1 hstep_mem
    dsimp [a]
    simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hnorm_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hu_norm : ‖u‖[F; x] = δ := by
    -- The inverse-Hessian gradient direction realizes the old Newton decrement at `x`.
    have hu_norm' :
        ‖u‖[F; x] =
          HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E (∇ F x)) := by
      simpa [H, u] using
        (inverseHessianWitness_localNorm_eq_dual_and_pairing_ofPosDefMem (F := F) hx (∇ F x)).1
    simpa [δ, NewtonDecrement.ofDetNeZero_def] using hu_norm'
  have hgrad :
      ∇ F xPlus = (1 - α) • ∇ F x + α • ((H - G) u) := by
    -- Rewrite the new gradient as the transported old gradient plus the averaged residual.
    simpa [α, H, u, G] using
      nextGradient_eq_oldGradient_plus_averageResidual
        (F := F) (variant := .intermediate) hx hH
        (hxPlus := by exact hxPlus)
  have htransport_g :
      HessianDualLocalNorm.ofPosDefMem F hxPlus (toDual ℝ E (∇ F x)) ≤
        (1 / (1 - a)) * δ := by
    calc
      HessianDualLocalNorm.ofPosDefMem F hxPlus (toDual ℝ E (∇ F x)) ≤
          (1 / (1 - (Mf : ℝ) * ‖xPlus - x‖[F; x])) *
            HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E (∇ F x)) := by
              simpa [xPlus] using
                hessianDualLocalNorm_ofPosDefMem_le_mul_of_mem_openDikinEllipsoid
                  (F := F) hx hxPlus hstep_mem
      _ = (1 / (1 - a)) * δ := by
            simp [a, δ, NewtonDecrement.ofDetNeZero_def]
  have hresidual :
      HessianDualLocalNorm.ofPosDefMem F hxPlus (toDual ℝ E ((H - G) u)) ≤
        (a / (1 - a)) * δ := by
    have hraw :
        HessianDualLocalNorm.ofPosDefMem F hxPlus (toDual ℝ E ((H - G) u)) ≤
          (a / (1 - a)) * ‖u‖[F; x] := by
      -- Route correction: keep the averaged residual in the endpoint metric from the start.
      simpa [xPlus, H, G, u, a] using
        averageHessianResidual_endpointDualBound
          (F := F) hx hxPlus hstep_mem
    simpa [hu_norm] using hraw
  have hfirst :
      HessianDualLocalNorm.ofPosDefMem F hxPlus
        ((1 - α) • toDual ℝ E (∇ F x)) ≤
          ((1 - α) / (1 - a)) * δ := by
    have hsmul_abs :
        HessianDualLocalNorm.ofPosDefMem F hxPlus
          ((1 - α) • toDual ℝ E (∇ F x)) =
          |1 - α| * HessianDualLocalNorm.ofPosDefMem F hxPlus (toDual ℝ E (∇ F x)) := by
      simpa using
        hessianDualLocalNorm_ofPosDefMem_smul
          (F := F) hxPlus (∇ F x) (1 - α)
    have hsmul :
        HessianDualLocalNorm.ofPosDefMem F hxPlus
          ((1 - α) • toDual ℝ E (∇ F x)) =
          (1 - α) * HessianDualLocalNorm.ofPosDefMem F hxPlus (toDual ℝ E (∇ F x)) := by
      rw [hsmul_abs, abs_of_nonneg h1mα_nonneg]
    rw [hsmul]
    calc
      (1 - α) * HessianDualLocalNorm.ofPosDefMem F hxPlus
          (toDual ℝ E (∇ F x)) ≤
          (1 - α) * ((1 / (1 - a)) * δ) := by
            exact mul_le_mul_of_nonneg_left htransport_g h1mα_nonneg
      _ = ((1 - α) / (1 - a)) * δ := by
            field_simp [hfactor_pos.ne']
  have hsecond :
      HessianDualLocalNorm.ofPosDefMem F hxPlus
        (α • toDual ℝ E ((H - G) u)) ≤
          α * ((a / (1 - a)) * δ) := by
    have hsmul_abs :
        HessianDualLocalNorm.ofPosDefMem F hxPlus
          (α • toDual ℝ E ((H - G) u)) =
          |α| * HessianDualLocalNorm.ofPosDefMem F hxPlus (toDual ℝ E ((H - G) u)) := by
      simpa using
        hessianDualLocalNorm_ofPosDefMem_smul
          (F := F) hxPlus ((H - G) u) α
    have hsmul :
        HessianDualLocalNorm.ofPosDefMem F hxPlus
          (α • toDual ℝ E ((H - G) u)) =
          α * HessianDualLocalNorm.ofPosDefMem F hxPlus (toDual ℝ E ((H - G) u)) := by
      rw [hsmul_abs, abs_of_nonneg hα_nonneg]
    rw [hsmul]
    exact mul_le_mul_of_nonneg_left hresidual hα_nonneg
  have hcoeff :
      ((1 - α) / (1 - a) + α * (a / (1 - a))) =
        s * (1 + s + s / (1 + s + s ^ (2 : ℕ))) := by
    rw [hα_eq, ha_eq]
    field_simp [hden_pos.ne', hfactor_pos.ne']
    ring
  have hsq : (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) = s ^ (2 : ℕ) := by
    dsimp [s]
    ring
  have hndec :
      ndec(F, xPlus, (Mf : NNReal), hxPlus, hHPlus') =
        HessianDualLocalNorm.ofPosDefMem F hxPlus (toDual ℝ E (∇ F xPlus)) := by
    rw [NewtonDecrement.ofDetNeZero_def, HessianDualLocalNorm.ofPosDefMem_def]
    simp [InnerProductSpace.toDual_apply_apply]
  -- Assemble the endpoint gradient decomposition and simplify the explicit intermediate
  -- coefficient.
  calc
    ndec(F, xPlus, (Mf : NNReal), hxPlus, hHPlus') =
        HessianDualLocalNorm.ofPosDefMem F hxPlus
          (((1 - α) • toDual ℝ E (∇ F x)) + (α • toDual ℝ E ((H - G) u))) := by
            rw [hndec, hgrad, map_add, map_smul, map_smul]
    _ ≤ HessianDualLocalNorm.ofPosDefMem F hxPlus
          ((1 - α) • toDual ℝ E (∇ F x)) +
        HessianDualLocalNorm.ofPosDefMem F hxPlus
          (α • toDual ℝ E ((H - G) u)) := by
            exact hessianDualLocalNorm_ofPosDefMem_add_le hxPlus _ _
    _ ≤ ((1 - α) / (1 - a)) * δ + α * ((a / (1 - a)) * δ) := by
          exact add_le_add hfirst hsecond
    _ = (((1 - α) / (1 - a)) + α * (a / (1 - a))) * δ := by
          ring
    _ = (s * (1 + s + s / (1 + s + s ^ (2 : ℕ)))) * δ := by
          rw [hcoeff]
    _ = ((Mf : ℝ) * δ ^ (2 : ℕ)) *
          (1 + (Mf : ℝ) * δ + ((Mf : ℝ) * δ) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) := by
          rw [hsq]
          dsimp [s]
          ring

-- Proof sketch: let `λ = ‖∇f(y) - t ∇f(y₀)‖*_y`, `λ₁ = ‖∇f(y) - t₊ ∇f(y₀)‖*_y`, and
-- `λ₊ = ‖∇f(y₊) - t₊ ∇f(y₀)‖*_{y₊}`. The assumption `hcenter` gives
-- `λ ≤ pathFollowingCenteringBeta τ / M_f`, while the path-parameter update and the bound on
-- `|γ|` imply `λ₁ ≤ τ / M_f`. Applying the intermediate-step decrement estimate `(5.2.8)` to the
-- tilted objective then yields
-- `λ₊ ≤ pathFollowingCenteringBeta τ / M_f`, which is exactly the same approximate-centering
-- condition at `(t₊, y₊)`.
/-- Lemma 5.2.2: if `(t, y)` satisfies the approximate centering condition `(5.2.13)` with
`β = τ² (1 + τ + τ / (1 + τ + τ²))` and `τ ≤ 1 / 2`, then the path-following update
`𝒫_γ(t, y)` also satisfies the same centering condition whenever its computed first coordinate
lies in `[0, 1]` and `|γ| ≤ τ - τ² (1 + τ + τ / (1 + τ + τ²))`. The updated point is read
through the canonical intermediate Newton owner for the tilted objective `ψ(t₊; ·)`, so its
domain membership is derived rather than assumed separately. -/
theorem pathFollowingUpdate_preserves_approximate_centering_condition
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) {y : E} (hy : y ∈ dom) {τ gamma : ℝ}
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (htau : τ ≤ 1 / 2)
    (hcenter : satisfies_approximate_centering_condition f y0 t y hy Mf
      (pathFollowingCenteringBeta τ))
    (hgamma : |gamma| ≤ pathFollowingGammaRadius τ) :
    satisfies_approximate_centering_condition f y0
      (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1
      (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).2
      (pathFollowingUpdate_snd_mem y0 t hy hObjectiveNorm htau hcenter hgamma) Mf
      (pathFollowingCenteringBeta τ) := by
  let tPlus := (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1
  let ψ := auxiliaryCentralPathObjective f y0 tPlus
  let δ := λ[ψ; y | hy]
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hH : (hessian ψ y).det ≠ 0 := by
    simpa [ψ] using auxiliaryCentralPathObjective_hessian_det_ne_zero f y0 tPlus hy
  have hδ_nonneg : 0 ≤ δ := by
    have hδ_eq :
        δ = ndec(ψ, y, (Mf : NNReal), hy, hH) := by
      symm
      simpa [δ, ψ] using auxiliaryCentralPathObjective_ndec_eq_centeringDecrement y0 tPlus hy hH
    rw [hδ_eq]
    exact NewtonDecrement.ofDetNeZero_nonneg (Mf : NNReal) ψ hy hH
  have hcenter_old :
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤
        pathFollowingCenteringBeta τ / (Mf : ℝ) := by
    exact (satisfies_approximate_centering_condition_iff f y0 t y hy Mf
      (pathFollowingCenteringBeta τ)).1 hcenter
  have hδ_le_shifted :
      δ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
        |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
    calc
      δ ≤ λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
            have hshift_raw :
                λ[auxiliaryCentralPathObjective f y0 tPlus; y | hy] ≤
                  λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
                    |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy :=
              auxiliaryCentralPathObjective_decrement_le_add_objectiveNorm_mul_abs_sub
                y0 hy (t : ℝ) tPlus
            simpa [δ, ψ, tPlus] using hshift_raw
      _ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
            gcongr
  have hstep_eq :
      |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy =
        |gamma| / (Mf : ℝ) := by
    dsimp [tPlus]
    rw [pathFollowingUpdate_fst]
    have hObjectiveNorm_nonneg : 0 ≤ pathFollowingObjectiveNorm f y0 y hy := le_of_lt hObjectiveNorm
    calc
      |(t : ℝ) - gamma / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy) - (t : ℝ)| *
          pathFollowingObjectiveNorm f y0 y hy =
          |(-gamma) / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy)| *
            pathFollowingObjectiveNorm f y0 y hy := by
              congr 1
              ring
      _ = (|gamma| / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy)) *
            pathFollowingObjectiveNorm f y0 y hy := by
              rw [abs_div, abs_neg, abs_mul, abs_of_pos hMf_pos,
                abs_of_nonneg hObjectiveNorm_nonneg]
      _ = |gamma| / (Mf : ℝ) := by
              field_simp [hMf_pos.ne', hObjectiveNorm.ne']
  have hδ_le_tau_div :
      δ ≤ τ / (Mf : ℝ) := by
    calc
      δ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := hδ_le_shifted
      _ = pathFollowingCenteringBeta τ / (Mf : ℝ) + |gamma| / (Mf : ℝ) := by
            rw [hstep_eq]
      _ ≤ τ / (Mf : ℝ) := by
            have hsum :
                pathFollowingCenteringBeta τ + |gamma| ≤ τ := by
              calc
                pathFollowingCenteringBeta τ + |gamma| ≤
                    pathFollowingCenteringBeta τ + pathFollowingGammaRadius τ := by
                      gcongr
                _ = τ := by
                      simp [pathFollowingGammaRadius]
            simpa [add_div] using
              (div_le_div_of_nonneg_right hsum (le_of_lt hMf_pos))
  have hscaled : (Mf : ℝ) * δ ≤ τ := by
    simpa [mul_comm] using (le_div_iff₀ hMf_pos).mp hδ_le_tau_div
  have hsmall :
      (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤ 1 :=
    pathFollowingIntermediateSmallness_of_scaled_le_half hδ_nonneg hscaled htau
  let yPlus := selfConcordantNewtonNextPoint ψ (Mf : NNReal) .intermediate y hy hH
  let hyPlus : yPlus ∈ dom :=
    intermediateNewtonNextPoint_mem_of_smallness hy hH hsmall
  have hHPlus :
      (hessian ψ yPlus).det ≠ 0 := by
    simpa [ψ, yPlus] using
      auxiliaryCentralPathObjective_hessian_det_ne_zero f y0 tPlus hyPlus
  rw [satisfies_approximate_centering_condition_iff]
  have hHPlus_input :
      let xPlus := selfConcordantNewtonNextPoint ψ (Mf : NNReal) .intermediate y hy hH
      (hessian ψ xPlus).det ≠ 0 := by
    simpa [yPlus] using hHPlus
  have hendpoint :
      λ[ψ; yPlus | hyPlus] ≤
        ((Mf : ℝ) * δ ^ (2 : ℕ)) *
          (1 + (Mf : ℝ) * δ +
            ((Mf : ℝ) * δ) /
              (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) := by
    -- Rewrite the endpoint decrement into `ndec` so the intermediate-step estimate applies.
    have hndec_eq :
        ndec(ψ, yPlus, (Mf : NNReal), hyPlus, hHPlus) = λ[ψ; yPlus | hyPlus] := by
      simpa [ψ, yPlus] using auxiliaryCentralPathObjective_ndec_eq_centeringDecrement y0 tPlus hyPlus hHPlus
    rw [← hndec_eq]
    have hendpoint_raw :
        ndec(ψ, yPlus, (Mf : NNReal), hyPlus, hHPlus) ≤
          ((Mf : ℝ) * δ ^ (2 : ℕ)) *
            (1 + (Mf : ℝ) * δ +
              ((Mf : ℝ) * δ) /
                (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) :=
      by
        let _ : IsSelfConcordantOnWith dom (Mf : NNReal) ψ := inferInstance
        let _ : HasPositiveDefiniteHessianOn dom ψ := inferInstance
        exact intermediateNewtonDecrement_explicitBound hy hH hsmall hHPlus_input
    simpa [δ, yPlus, hyPlus] using hendpoint_raw
  simpa [tPlus, ψ, yPlus, pathFollowingUpdate_snd] using
    (le_trans hendpoint <|
      pathFollowingExplicitIntermediateBound_le_centeringBeta_div hδ_nonneg hscaled htau)

end
