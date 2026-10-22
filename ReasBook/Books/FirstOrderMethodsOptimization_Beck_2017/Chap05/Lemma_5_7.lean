/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: parametrize the chord from `x` to `y` by `AffineMap.lineMap x y`, compare the
-- restriction of `f` with the quadratic barrier determined by `fderiv ℝ f x`, and use the
-- derivative-Lipschitz clause of `is_l_smooth_on` along the segment inside the convex set `D`.
/-- Companion bridge for Lemma 5.7: on a convex set, `L`-smoothness gives the Banach-space
quadratic upper model with the Fréchet derivative as linear term. -/
theorem is_l_smooth_on_fderiv_descent {L : NNReal} {D : Set E} {f : E → ℝ}
    (hD : Convex ℝ D) (hf : is_l_smooth_on f D L)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    f y ≤
      f x + fderiv ℝ f x (y - x) + ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  rcases is_l_smooth_on_iff.mp hf with ⟨hdiff, hLip⟩
  let φ : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  let a0 : ℝ := fderiv ℝ f x (y - x)
  let s : ℝ := ‖y - x‖ ^ (2 : ℕ)
  let B : ℝ → ℝ := fun t ↦ f x + t * a0 + ((L : ℝ) / 2) * t ^ (2 : ℕ) * s
  have hline_mem : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) 1 → AffineMap.lineMap x y t ∈ D := by
    intro t ht
    exact hD.lineMap_mem hx hy ht
  have hφ_deriv :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivAt φ (fderiv ℝ f (AffineMap.lineMap x y t) (y - x)) t := by
    intro t ht
    simpa [φ] using
      HasFDerivAt.comp_hasDerivAt t
        ((hdiff _ (hline_mem ht)).hasFDerivAt)
        (show HasDerivAt (AffineMap.lineMap x y) (y - x) t from
          AffineMap.hasDerivAt_lineMap)
  have hφ_cont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hφ_deriv ht).continuousAt.continuousWithinAt
  have hB_deriv : ∀ t : ℝ, HasDerivAt B (a0 + (L : ℝ) * t * s) t := by
    intro t
    have hlin : HasDerivAt (fun u : ℝ ↦ u * a0) a0 t := by
      simpa [one_mul] using (hasDerivAt_id t).mul_const a0
    have hquad :
        HasDerivAt
          (fun u : ℝ ↦ ((L : ℝ) / 2) * u ^ (2 : ℕ) * s)
          ((L : ℝ) * t * s) t := by
      simpa [pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (((hasDerivAt_pow 2 t).const_mul ((L : ℝ) / 2)).mul_const s)
    convert ((hasDerivAt_const t (f x)).add hlin).add hquad using 1
    · simp [a0, s, add_comm]
  have hB_cont : ContinuousOn B (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hB_deriv t).continuousAt.continuousWithinAt
  have hbound :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        fderiv ℝ f (AffineMap.lineMap x y t) (y - x) ≤ a0 + (L : ℝ) * t * s := by
    intro t ht
    have hline_mem_t : AffineMap.lineMap x y t ∈ D := hline_mem ⟨ht.1, ht.2.le⟩
    have hline_norm :
        ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
      calc
        ‖AffineMap.lineMap x y t - x‖ = ‖t • (y - x)‖ := by
          simp [AffineMap.lineMap_apply_module']
        _ = ‖t‖ * ‖y - x‖ := norm_smul _ _
        _ = t * ‖y - x‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hnorm :
        ‖(fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x) (y - x)‖ ≤
          (L : ℝ) * t * s := by
      calc
        ‖(fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x) (y - x)‖
            ≤ ‖fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x‖ * ‖y - x‖ := by
              exact (fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x).le_opNorm (y - x)
        _ ≤ ((L : ℝ) * ‖AffineMap.lineMap x y t - x‖) * ‖y - x‖ := by
              exact mul_le_mul_of_nonneg_right
                (hLip _ hline_mem_t _ hx) (norm_nonneg _)
        _ = ((L : ℝ) * (t * ‖y - x‖)) * ‖y - x‖ := by
              rw [hline_norm]
        _ = (L : ℝ) * t * s := by
              dsimp [s]
              rw [pow_two]
              ring
    have hlinear :
        (fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x) (y - x) ≤
          (L : ℝ) * t * s := by
      exact (le_abs_self _).trans hnorm
    have hrewrite :
        (fderiv ℝ f (AffineMap.lineMap x y t) - fderiv ℝ f x) (y - x) =
          fderiv ℝ f (AffineMap.lineMap x y t) (y - x) - a0 := by
      simp [a0]
    rw [hrewrite] at hlinear
    linarith
  have hcompare :=
    image_le_of_deriv_right_le_deriv_boundary
      hφ_cont
      (fun t ht ↦ (hφ_deriv (Set.mem_Icc_of_Ico ht)).hasDerivWithinAt)
      (by simp [φ, B])
      hB_cont
      (fun t ht ↦ (hB_deriv t).hasDerivWithinAt)
      hbound
  have hendpoint : φ 1 ≤ B 1 := hcompare (by simp)
  simpa [φ, B, a0, s, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    pow_two, mul_assoc, mul_left_comm, mul_comm] using hendpoint

/-- Global companion to `is_l_smooth_on_fderiv_descent`: on `Set.univ`, the convex-set descent
estimate specializes to an unrestricted Fréchet-derivative quadratic upper model. -/
theorem is_l_smooth_on_univ_fderiv_descent {L : NNReal} {f : E → ℝ}
    (hf : is_l_smooth_on f Set.univ L) (x y : E) :
    f y ≤
      f x + fderiv ℝ f x (y - x) + ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) :=
  is_l_smooth_on_fderiv_descent convex_univ hf (by simp) (by simp)

section

open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 5.7 is `source-facing`: its content is the quadratic upper model on a convex set. The
Chapter 5 owner abstraction for smoothness on a set is `is_l_smooth_on` from Definition 5.2, so
the convexity of `D` is kept as its own hypothesis instead of being rebundled into a local
wrapper. The source-facing linear term is the ambient gradient `∇ f x`; this matches the chapter
owner API, which controls ambient differentiability on `D`, without introducing the stronger
within-set uniqueness hypotheses that would be needed to justify `gradientWithin`. -/

-- Proof sketch: parametrize the segment from `x` to `y`, use convexity of `D` to keep the segment
-- inside the domain, differentiate `t ↦ f (x + t • (y - x))`, integrate the resulting derivative,
-- and bound the error term with Cauchy--Schwarz together with the `L`-Lipschitz control of the
-- ambient gradient field encoded by `is_l_smooth_on f D L`.
/-- Lemma 5.7: if `D` is convex and `f` is `L`-smooth on `D`, then
`f y ≤ f x + ⟪∇ f x, y - x⟫ + (L / 2) * ‖x - y‖²` for all `x, y ∈ D`. -/
theorem is_l_smooth_on_descent_lemma {L : NNReal} {D : Set E} {f : E → ℝ}
    (hD : Convex ℝ D) (hf : is_l_smooth_on f D L)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    f y ≤
      f x + inner ℝ (∇ f x) (y - x) + ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  have hx_diff : DifferentiableAt ℝ f x := hf.1 x hx
  simpa [HasGradientAt.fderiv_apply hx_diff.hasGradientAt, norm_sub_rev] using
    (is_l_smooth_on_fderiv_descent hD hf hx hy)

/-- Global companion to Lemma 5.7: on `Set.univ`, `L`-smoothness gives the quadratic upper model
with the ambient gradient field. -/
theorem is_l_smooth_on_univ_descent_lemma {L : NNReal} {f : E → ℝ}
    (hf : is_l_smooth_on f Set.univ L) (x y : E) :
    f y ≤
      f x + inner ℝ (∇ f x) (y - x) + ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  simpa using is_l_smooth_on_descent_lemma convex_univ hf (by simp) (by simp)

end
