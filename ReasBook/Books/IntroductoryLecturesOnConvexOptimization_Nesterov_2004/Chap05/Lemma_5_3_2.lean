/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Lemma 5.3.2: the Chapter 2 dual norm of a separated seminorm is bounded above on
the closed primal unit ball image, so `le_csSup` can be used pointwise. -/
private theorem seminorm_dualNorm_bddAbove_innerImage_closedBall
    (p : Seminorm ℝ E) [p.IsNorm] (g : E) :
    BddAbove ((fun y : E ↦ inner ℝ g y) '' p.closedBall 0 1) := by
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
  -- The ambient Cauchy inequality turns the unit-ball membership into a uniform upper bound.
  calc
    inner ℝ g y ≤ ‖g‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖g‖ * C := by
      gcongr

/-- Helper for Lemma 5.3.2: the Chapter 2 dual norm is subadditive on covectors after passing
through the Riesz identification. -/
private theorem seminorm_dualNorm_add_le
    (p : Seminorm ℝ E) [p.IsNorm] (g h : E) :
    Seminorm.dualNorm p (g + h) ≤ Seminorm.dualNorm p g + Seminorm.dualNorm p h := by
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⟨0, by simpa [Seminorm.mem_closedBall_zero], by simp⟩⟩
  · rintro z ⟨u, hu, rfl⟩
    have hu_ball : u ∈ p.closedBall 0 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hu
    have hg_le : inner ℝ g u ≤ Seminorm.dualNorm p g := by
      have hmem : inner ℝ g u ∈ ((fun y : E ↦ inner ℝ g y) '' p.closedBall 0 1) :=
        ⟨u, hu_ball, rfl⟩
      exact le_csSup (seminorm_dualNorm_bddAbove_innerImage_closedBall p g) hmem
    have hh_le : inner ℝ h u ≤ Seminorm.dualNorm p h := by
      have hmem : inner ℝ h u ∈ ((fun y : E ↦ inner ℝ h y) '' p.closedBall 0 1) :=
        ⟨u, hu_ball, rfl⟩
      exact le_csSup (seminorm_dualNorm_bddAbove_innerImage_closedBall p h) hmem
    -- Evaluate the sum at the same unit-ball witness and bound each summand separately.
    calc
      inner ℝ (g + h) u = inner ℝ g u + inner ℝ h u := by
        rw [inner_add_left]
      _ ≤ Seminorm.dualNorm p g + Seminorm.dualNorm p h := add_le_add hg_le hh_le

/-- Helper for Lemma 5.3.2: the Hessian operator induces the positive-definite bilinear form used
by the Chapter 5 dual local norm. -/
private theorem hessian_bilin_posDef_of_isPositive_of_isInvertible
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    ((((innerSL ℝ).comp (hessian F x)).toBilinForm).toQuadraticMap).PosDef := by
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
    apply hInv.injective
    simpa using hHu

/-- Helper for Lemma 5.3.2: the Hessian dual local norm satisfies the triangle inequality at a
fixed point `x`. -/
lemma hessianDualLocalNorm_ofDetNeZero_add_le
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hH : (fderiv ℝ (∇ F) x).det ≠ 0) (g₁ g₂ : StrongDual ℝ E) :
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (g₁ + g₂) ≤
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g₁ +
        HessianDualLocalNorm.ofDetNeZero F x hPos hH g₂ := by
  let hInv : (hessian F x).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  let B : LinearMap.BilinForm ℝ E := ((innerSL ℝ).comp (hessian F x)).toBilinForm
  let hBPos : B.toQuadraticMap.PosDef :=
    hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv
  let p : Seminorm ℝ E := B.primalSeminorm hBPos
  let v₁ : E := (InnerProductSpace.toDual ℝ E).symm g₁
  let v₂ : E := (InnerProductSpace.toDual ℝ E).symm g₂
  have hsum :
      Seminorm.dualNorm p (v₁ + v₂) ≤ Seminorm.dualNorm p v₁ + Seminorm.dualNorm p v₂ :=
    seminorm_dualNorm_add_le p v₁ v₂
  have hleft :
      HessianDualLocalNorm.ofDetNeZero F x hPos hH (g₁ + g₂) =
        Seminorm.dualNorm p (v₁ + v₂) := by
    trans B.dualNorm hBPos ((g₁ + g₂).toLinearMap)
    · simp [HessianDualLocalNorm.ofDetNeZero, dualLocalNorm, B]
      change
        B.dualNorm (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv)
            ((g₁ + g₂).toLinearMap) =
          B.dualNorm hBPos ((g₁ + g₂).toLinearMap)
      rw [Subsingleton.elim
        (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv) hBPos]
    · symm
      simpa [p, v₁, v₂] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos (v₁ + v₂))
  have hg₁ :
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g₁ =
        Seminorm.dualNorm p v₁ := by
    trans B.dualNorm hBPos g₁.toLinearMap
    · simp [HessianDualLocalNorm.ofDetNeZero, dualLocalNorm, B]
      change
        B.dualNorm (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv)
            g₁.toLinearMap =
          B.dualNorm hBPos g₁.toLinearMap
      rw [Subsingleton.elim
        (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv) hBPos]
    · symm
      simpa [p, v₁] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos v₁)
  have hg₂ :
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g₂ =
        Seminorm.dualNorm p v₂ := by
    trans B.dualNorm hBPos g₂.toLinearMap
    · simp [HessianDualLocalNorm.ofDetNeZero, dualLocalNorm, B]
      change
        B.dualNorm (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv)
            g₂.toLinearMap =
          B.dualNorm hBPos g₂.toLinearMap
      rw [Subsingleton.elim
        (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv) hBPos]
    · symm
      simpa [p, v₂] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos v₂)
  -- Move the fixed Hessian dual norm onto the Chapter 2 dual norm surface, apply subadditivity,
  -- and then move back.
  calc
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (g₁ + g₂) =
        Seminorm.dualNorm p (v₁ + v₂) := hleft
    _ ≤ Seminorm.dualNorm p v₁ + Seminorm.dualNorm p v₂ := hsum
    _ = HessianDualLocalNorm.ofDetNeZero F x hPos hH g₁ +
          HessianDualLocalNorm.ofDetNeZero F x hPos hH g₂ := by
      rw [← hg₁, ← hg₂]

/-- Helper for Lemma 5.3.2: the Hessian dual local norm is even on covectors. -/
lemma hessianDualLocalNorm_ofDetNeZero_neg
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hH : (fderiv ℝ (∇ F) x).det ≠ 0) (g : StrongDual ℝ E) :
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (-g) =
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g := by
  -- Both sides square to the same inverse-Hessian pairing after the two minus signs cancel.
  rw [HessianDualLocalNorm.ofDetNeZero_def, HessianDualLocalNorm.ofDetNeZero_def]
  simp

/-- Helper for Lemma 5.3.2: at a domain point of a `ν`-self-concordant barrier, the gradient
covector has Hessian dual local norm at most `√ν`. -/
lemma barrier_gradient_hessianDualLocalNorm_ofDetNeZero_le_sqrt
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F] {x : dom}
    (hH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0) :
    HessianDualLocalNorm.ofDetNeZero F (x : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hH
      ((InnerProductSpace.toDual ℝ E) (∇ F (x : E))) ≤
      Real.sqrt (ν : ℝ) := by
  let hPos : (hessian F (x : E)).IsPositive :=
    IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2
  let hInv : (hessian F (x : E)).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hpair :
      inner ℝ (∇ F (x : E)) ((hessian F (x : E)).inverse (∇ F (x : E))) ≤ (ν : ℝ) := by
    refine
      (barrier_parameter_bound_iff_gradient_inverse_hessian_gradient_le
        (F := F) (ν := ν) (x := (x : E)) hPos hInv).1 ?_
    intro u
    exact IsSelfConcordantBarrierOnWith.barrier_parameter_bound_of_mem ν x.2 u
  -- Rewrite the norm as the square root of the inverse-Hessian pairing and invoke Proposition 5.3.2.
  rw [HessianDualLocalNorm.ofDetNeZero_def]
  simpa [InnerProductSpace.toDual_apply_apply] using
    (Real.sqrt_le_sqrt_iff ν.2).2 hpair

-- Proof sketch: rewrite the approximate-centering hypothesis as
-- `t ‖c‖*_x ≤ ‖t c + ∇ F(x)‖*_x + ‖∇ F(x)‖*_x` by the triangle inequality for the dual local norm.
-- Then use the barrier gradient estimate `‖∇ F(x)‖*_x ≤ √ν`, which is the inverse-Hessian form of
-- the barrier-parameter bound, and divide by the positive scalar `t`.
/-- Lemma 5.3.2: if `x` in the domain of a `ν`-self-concordant barrier `F` satisfies the
approximate-centering condition `‖t c + ∇ F(x)‖*ₓ ≤ β` for some `t > 0`, then the dual local norm
of the objective vector is bounded by `‖c‖*ₓ ≤ (β + √ν) / t`. -/
theorem dualLocalNorm_objectiveVector_le_add_sqrt_barrierParameter_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) {t β : ℝ} (ht : 0 < t)
    {x : dom}
    (hH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hH
        ((InnerProductSpace.toDual ℝ E) (t • c + ∇ F (x : E))) ≤ β) :
    HessianDualLocalNorm.ofDetNeZero F (x : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hH
      ((InnerProductSpace.toDual ℝ E) c) ≤
      (β + Real.sqrt (ν : ℝ)) / t := by
  let hPos : (hessian F (x : E)).IsPositive :=
    IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2
  have hsplit :
      (InnerProductSpace.toDual ℝ E) (t • c) =
        (InnerProductSpace.toDual ℝ E) (t • c + ∇ F (x : E)) +
          (InnerProductSpace.toDual ℝ E) (-∇ F (x : E)) := by
    rw [← map_add]
    simp
  have hgrad :
      HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
        ((InnerProductSpace.toDual ℝ E) (∇ F (x : E))) ≤
        Real.sqrt (ν : ℝ) :=
    barrier_gradient_hessianDualLocalNorm_ofDetNeZero_le_sqrt (ν := ν) (F := F) hH
  have hscaled_bound :
      HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
        ((InnerProductSpace.toDual ℝ E) (t • c)) ≤
        β + Real.sqrt (ν : ℝ) := by
    -- Rewrite `t • c` as the residual plus the negated gradient and apply the triangle inequality.
    calc
      HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
          ((InnerProductSpace.toDual ℝ E) (t • c)) =
          HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
            (((InnerProductSpace.toDual ℝ E) (t • c + ∇ F (x : E))) +
              ((InnerProductSpace.toDual ℝ E) (-∇ F (x : E)))) := by
        rw [hsplit]
      _ ≤ HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
            ((InnerProductSpace.toDual ℝ E) (t • c + ∇ F (x : E))) +
          HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
            ((InnerProductSpace.toDual ℝ E) (-∇ F (x : E))) := by
        exact hessianDualLocalNorm_ofDetNeZero_add_le hPos hH _ _
      _ = HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
            ((InnerProductSpace.toDual ℝ E) (t • c + ∇ F (x : E))) +
          HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
            ((InnerProductSpace.toDual ℝ E) (∇ F (x : E))) := by
        rw [map_neg, hessianDualLocalNorm_ofDetNeZero_neg hPos hH]
      _ ≤ β + Real.sqrt (ν : ℝ) := add_le_add happrox hgrad
  have hsmul :
      HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
        ((InnerProductSpace.toDual ℝ E) (t • c)) =
        t *
          HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
            ((InnerProductSpace.toDual ℝ E) c) := by
    -- Positive homogeneity pulls the scalar `t` out of the fixed local dual norm.
    simpa [HessianDualLocalNorm.ofDetNeZero, smul_eq_mul] using
      dualLocalNorm_smul_nonneg F (x : E) hPos
        (hessian_isInvertible_of_det_ne_zero hH)
        ((InnerProductSpace.toDual ℝ E) c) ht.le
  have hobjective :
      t *
          HessianDualLocalNorm.ofDetNeZero F (x : E) hPos hH
            ((InnerProductSpace.toDual ℝ E) c) ≤
        β + Real.sqrt (ν : ℝ) := by
    rw [hsmul] at hscaled_bound
    exact hscaled_bound
  -- Divide the controlled quantity by the positive scalar `t`.
  exact (le_div_iff₀ ht).2 (by simpa [mul_comm] using hobjective)

end
