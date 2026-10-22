/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u v

/- This item lies in the Chapter 6 smoothed-primal / Danskin-gradient domain.

Sampled owner-style declarations:
- `smoothedPrimalObjective`, `smoothedPrimalObjectiveMaximand`, and
  `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the chapter owners for the
  regularized primal smoothing formula and the canonical argmax set of the textbook maximizer
  `u_{μ₂}(x)`;
- `smoothed_maximizer_unique` in `Chap06/Proposition_6_6`, the chapter uniqueness theorem for the
  penalized dual maximizer under convexity of `\hat φ` and strong convexity of `d₂`;
- `nesterovSmoothedObjective_hasFDerivAt` and `smoothedObjective_gradient_lipschitz` in
  `Chap06/Theorem_6_1`, the zero-`\hat f` whole-space smoothing surfaces;
- `explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn` in
  `Chap06/Proposition_6_10`, the additive within-set gradient/Lipschitz owner for an explicit
  model `\hat f + f_μ`.

Best owner abstraction:
- source-facing: the uniqueness, gradient formula, and Lipschitz estimate for the smoothed primal
  objective `f_{μ₂}`;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`,
  `HasGradientWithinAt` and `LipschitzOnWith`;
- bridge/view: a chosen argmax selector `uμ₂` and the Riesz-vector form
  `(InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x))` of the textbook term `A^* u_{μ₂}(x)`.

Primitive data:
- the primal and dual feasible sets `Q₁`, `Q₂`;
- the smooth primal term `hatf`, the convex dual term `hatφ`, the prox term `d₂`, and the
  smoothing parameter `μ₂`;
- a chosen gradient field `gradHatf` for `hatf` on `Q₁`;
- a chosen selection `uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x`;
- pointwise within-gradient hypotheses for `hatf` on `Q₁`, convexity of `hatφ` on `Q₂`, and
  `1`-strong convexity of `d₂` on `Q₂`.

Derived API:
- uniqueness of the feasible maximizer defining `u_{μ₂}(x)`;
- the within-set gradient formula for `smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂` on the
  displayed gradient field on `Q₁`;
- the corresponding Lipschitz bound on that displayed gradient field.

Semantic recall:
- LeanSearch hit: `HasGradientWithinAt`, `gradientWithin`.
- `gradientWithin` and `HasGradientWithinAt.fderivWithin_apply` confirmed the
  `UniqueDiffWithinAt` side condition for identifying a canonical within-gradient value, so the
  source-facing statements below use an explicit gradient field `gradHatf` for `\hat f` and state
  the displayed gradient field for `f_{μ₂}` directly over `Q₁`.

This file keeps the statement directly on the existing Chapter 6 owners instead of introducing a
parallel `u_{μ₂}` wrapper or a second smoothing owner.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Helper for Proposition 6.24: an element of
`smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x` minimizes the positive slice
`v ↦ hatφ v + μ₂ * d₂ v - A x v` on `Q₂`. -/
lemma smoothedPrimalObjectiveArgmax_isMinOnSlice
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₂ : Set E₂}
    {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {x : E₁} {u : E₂}
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x) :
    u ∈ Q₂ ∧ IsMinOn (fun v ↦ hatφ v + μ₂ * d₂ v - A x v) Q₂ u := by
  -- Unpack the canonical argmax witness into feasibility and maximality.
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ μ₂ x u).mp hu with
    ⟨hu_mem, hu_max⟩
  refine ⟨hu_mem, ?_⟩
  -- Negating the maximand converts the max witness into the corresponding min witness.
  refine isMinOn_iff.mpr ?_
  intro v hv
  have hmax :
      smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x v ≤
        smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x u :=
    (isMaxOn_iff.mp hu_max) v hv
  have hu_neg :
      hatφ u + μ₂ * d₂ u - A x u =
        -smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x u := by
    simp [smoothedPrimalObjectiveMaximand, sub_eq_add_neg]
    ring
  have hv_neg :
      hatφ v + μ₂ * d₂ v - A x v =
        -smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x v := by
    simp [smoothedPrimalObjectiveMaximand, sub_eq_add_neg]
    ring
  rw [hu_neg, hv_neg]
  exact neg_le_neg hmax

/-- Helper for Proposition 6.24: the selected maximizer varies Lipschitzly on `Q₁`
with constant `(1 / μ₂) * ‖A‖`. -/
lemma smoothedPrimalObjectiveArgmaxSelection_norm_sub_le
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {uμ₂ : E₁ → E₂}
    (hhatφ : ConvexOn ℝ Q₂ hatφ)
    (hd₂ : StrongConvexOn Q₂ 1 d₂)
    (hμ₂ : 0 < μ₂)
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    {x y : E₁} (hx : x ∈ Q₁) (hy : y ∈ Q₁) :
    ‖uμ₂ x - uμ₂ y‖ ≤ ((1 / μ₂) * ‖A‖) * ‖x - y‖ := by
  -- Convert the two selected argmax points into minimizers of strongly convex slices.
  rcases smoothedPrimalObjectiveArgmax_isMinOnSlice
      A (huμ₂ hx) with ⟨hux_mem, hux_min⟩
  rcases smoothedPrimalObjectiveArgmax_isMinOnSlice
      A (huμ₂ hy) with ⟨huy_mem, huy_min⟩
  have hstrong_x :
      StrongConvexOn Q₂ μ₂ (fun u ↦ hatφ u + μ₂ * d₂ u - A x u) :=
    smoothedObjective_slice_strongConvexOn A Q₂ hatφ d₂ hhatφ hd₂ hμ₂ x
  have hstrong_y :
      StrongConvexOn Q₂ μ₂ (fun u ↦ hatφ u + μ₂ * d₂ u - A y u) :=
    smoothedObjective_slice_strongConvexOn A Q₂ hatφ d₂ hhatφ hd₂ hμ₂ y
  -- Compare the two slices at the two selected minimizers and add the inequalities.
  have hquad_x :
      (hatφ (uμ₂ y) + μ₂ * d₂ (uμ₂ y) - A x (uμ₂ y)) ≥
        (hatφ (uμ₂ x) + μ₂ * d₂ (uμ₂ x) - A x (uμ₂ x)) +
          (μ₂ / 2) * ‖uμ₂ y - uμ₂ x‖ ^ (2 : ℕ) :=
    hstrong_x.quadratic_growth_of_isMinOn_of_mem hux_mem hux_min (uμ₂ y) huy_mem
  have hquad_y :
      (hatφ (uμ₂ x) + μ₂ * d₂ (uμ₂ x) - A y (uμ₂ x)) ≥
        (hatφ (uμ₂ y) + μ₂ * d₂ (uμ₂ y) - A y (uμ₂ y)) +
          (μ₂ / 2) * ‖uμ₂ x - uμ₂ y‖ ^ (2 : ℕ) :=
    hstrong_y.quadratic_growth_of_isMinOn_of_mem huy_mem huy_min (uμ₂ x) hux_mem
  have hpair :
      μ₂ * ‖uμ₂ x - uμ₂ y‖ ^ (2 : ℕ) ≤
        A (x - y) (uμ₂ x - uμ₂ y) := by
    have hadd := add_le_add hquad_x hquad_y
    have hnorm_sq :
        ‖uμ₂ y - uμ₂ x‖ ^ (2 : ℕ) = ‖uμ₂ x - uμ₂ y‖ ^ (2 : ℕ) := by
      rw [norm_sub_rev]
    have hrew :
        ((hatφ (uμ₂ x) + μ₂ * d₂ (uμ₂ x) - A x (uμ₂ x)) +
            (μ₂ / 2) * ‖uμ₂ y - uμ₂ x‖ ^ (2 : ℕ)) +
          ((hatφ (uμ₂ y) + μ₂ * d₂ (uμ₂ y) - A y (uμ₂ y)) +
            (μ₂ / 2) * ‖uμ₂ x - uμ₂ y‖ ^ (2 : ℕ)) =
        (hatφ (uμ₂ x) + μ₂ * d₂ (uμ₂ x) - A x (uμ₂ x)) +
          (hatφ (uμ₂ y) + μ₂ * d₂ (uμ₂ y) - A y (uμ₂ y)) +
            μ₂ * ‖uμ₂ x - uμ₂ y‖ ^ (2 : ℕ) := by
      rw [hnorm_sq]
      ring
    rw [hrew] at hadd
    have hcancel :
        ((hatφ (uμ₂ y) + μ₂ * d₂ (uμ₂ y) - A x (uμ₂ y)) +
            (hatφ (uμ₂ x) + μ₂ * d₂ (uμ₂ x) - A y (uμ₂ x))) -
          ((hatφ (uμ₂ x) + μ₂ * d₂ (uμ₂ x) - A x (uμ₂ x)) +
            (hatφ (uμ₂ y) + μ₂ * d₂ (uμ₂ y) - A y (uμ₂ y))) =
        A (x - y) (uμ₂ x - uμ₂ y) := by
      simp [sub_eq_add_neg]
      ring
    linarith [hadd, hcancel]
  have hpair_le :
      A (x - y) (uμ₂ x - uμ₂ y) ≤ ‖A‖ * ‖x - y‖ * ‖uμ₂ x - uμ₂ y‖ := by
    -- Bound the bilinear perturbation by the operator norm of `A`.
    have hfunctional :
        ‖A (x - y) (uμ₂ x - uμ₂ y)‖ ≤
          ‖A (x - y)‖ * ‖uμ₂ x - uμ₂ y‖ := by
      simpa using (A (x - y)).le_opNorm (uμ₂ x - uμ₂ y)
    have hfunctional' :
        A (x - y) (uμ₂ x - uμ₂ y) ≤ ‖A (x - y)‖ * ‖uμ₂ x - uμ₂ y‖ :=
      le_trans (le_abs_self _) hfunctional
    exact hfunctional'.trans <| by
      gcongr
      exact A.le_opNorm (x - y)
  have hpair' :
      μ₂ * ‖uμ₂ x - uμ₂ y‖ ^ (2 : ℕ) ≤
        ‖A‖ * ‖x - y‖ * ‖uμ₂ x - uμ₂ y‖ := by
    exact hpair.trans <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hpair_le
  by_cases hxy : uμ₂ x = uμ₂ y
  · simp [hxy]
    positivity
  · have hnorm_pos : 0 < ‖uμ₂ x - uμ₂ y‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr hxy
    have hlinear :
        μ₂ * ‖uμ₂ x - uμ₂ y‖ ≤ ‖A‖ * ‖x - y‖ := by
      nlinarith [hμ₂, hnorm_pos, norm_nonneg (x - y), norm_nonneg A, hpair']
    have hdiv :
        ‖uμ₂ x - uμ₂ y‖ ≤ (‖A‖ * ‖x - y‖) / μ₂ := by
      refine (le_div_iff₀ hμ₂).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlinear
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- Helper for Proposition 6.24: the zero-`\hat f` smoothed part has a quadratic remainder
bound along `Q₁`. -/
lemma smoothedPrimalObjectiveZeroPart_remainder_norm_le
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {uμ₂ : E₁ → E₂}
    (hhatφ : ConvexOn ℝ Q₂ hatφ)
    (hd₂ : StrongConvexOn Q₂ 1 d₂)
    (hμ₂ : 0 < μ₂)
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    {x y : E₁} (hx : x ∈ Q₁) (hy : y ∈ Q₁) :
    ‖smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂ y -
        smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂ x -
        (A.flip (uμ₂ x)) (y - x)‖ ≤
      ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)) * ‖y - x‖ ^ (2 : ℕ) := by
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ μ₂ x (uμ₂ x)).mp (huμ₂ hx) with
    ⟨hux_mem, hux_max⟩
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ μ₂ y (uμ₂ y)).mp (huμ₂ hy) with
    ⟨huy_mem, huy_max⟩
  let remainder : ℝ :=
    smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂ y -
      smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂ x -
      (A.flip (uμ₂ x)) (y - x)
  have hy_eq : y = x + (y - x) := by
    abel_nf
  have hshift_x :
      smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ y (uμ₂ x) =
        smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x (uμ₂ x) +
          A (y - x) (uμ₂ x) := by
    rw [hy_eq]
    simp [smoothedPrimalObjectiveMaximand, map_add, sub_eq_add_neg]
    ring
  have hshift_y :
      smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ y (uμ₂ y) =
        smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x (uμ₂ y) +
          A (y - x) (uμ₂ y) := by
    rw [hy_eq]
    simp [smoothedPrimalObjectiveMaximand, map_add, sub_eq_add_neg]
    ring
  have hsup_x :
      sSup (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x '' Q₂) =
        smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x (uμ₂ x) := by
    simpa [smoothedPrimalObjective_apply] using
      smoothedPrimalObjectiveArgmax.value_eq (A := A) (Q := Q₂) (phiHat := hatφ)
        (d2 := d₂) (μ := μ₂) (huμ₂ hx)
  have hsup_y :
      sSup (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ y '' Q₂) =
        smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ y (uμ₂ y) := by
    simpa [smoothedPrimalObjective_apply] using
      smoothedPrimalObjectiveArgmax.value_eq (A := A) (Q := Q₂) (phiHat := hatφ)
        (d2 := d₂) (μ := μ₂) (huμ₂ hy)
  have hnonneg : 0 ≤ remainder := by
    have hcompare :
        smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ y (uμ₂ x) ≤
          smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ y (uμ₂ y) :=
      (isMaxOn_iff.mp huy_max) (uμ₂ x) hux_mem
    -- Rewrite the remainder as the selected value gap at `y`.
    have hremainder_eq :
        remainder =
          smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ y (uμ₂ y) -
            smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ y (uμ₂ x) := by
      dsimp [remainder]
      rw [hsup_y, hsup_x, hshift_x]
      simp
      ring
    rw [hremainder_eq]
    exact sub_nonneg.mpr hcompare
  have hupper :
      remainder ≤ A (y - x) (uμ₂ y - uμ₂ x) := by
    have hcompare :
        smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x (uμ₂ y) ≤
          smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x (uμ₂ x) :=
      (isMaxOn_iff.mp hux_max) (uμ₂ y) huy_mem
    -- Compare the `y`-optimizer against the `x`-slice and isolate the affine discrepancy.
    have hremainder_eq :
        remainder =
          smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x (uμ₂ y) +
              A (y - x) (uμ₂ y) -
            smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x (uμ₂ x) -
              A (y - x) (uμ₂ x) := by
      dsimp [remainder]
      rw [hsup_y, hsup_x, hshift_y]
      simp
    rw [hremainder_eq]
    have hmap_sub :
        A (y - x) (uμ₂ y - uμ₂ x) = A (y - x) (uμ₂ y) - A (y - x) (uμ₂ x) := by
      rw [map_sub]
    rw [hmap_sub]
    linarith
  -- Control the scalar remainder by the operator norm of `A` and the selector Lipschitz bound.
  calc
    ‖smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂ y -
        smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂ x -
        (A.flip (uμ₂ x)) (y - x)‖ = ‖remainder‖ := by
          dsimp [remainder]
    _ = remainder := Real.norm_of_nonneg hnonneg
    _ ≤ ‖A (y - x) (uμ₂ y - uμ₂ x)‖ := le_trans hupper (le_abs_self _)
    _ ≤ ‖A (y - x)‖ * ‖uμ₂ y - uμ₂ x‖ := by
          simpa using (A (y - x)).le_opNorm (uμ₂ y - uμ₂ x)
    _ ≤ (‖A‖ * ‖y - x‖) * ((((1 / μ₂) * ‖A‖) * ‖y - x‖)) := by
          gcongr
          · exact A.le_opNorm (y - x)
          · exact
              smoothedPrimalObjectiveArgmaxSelection_norm_sub_le
                A hhatφ hd₂ hμ₂ huμ₂ hy hx
    _ = ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)) * ‖y - x‖ ^ (2 : ℕ) := by
          ring_nf

/-- Helper for Proposition 6.24: the zero-`\hat f` smoothed part has the displayed within-set
Fréchet derivative on `Q₁`. -/
lemma smoothedPrimalObjectiveZeroPart_hasFDerivWithinAt
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {uμ₂ : E₁ → E₂}
    (hhatφ : ConvexOn ℝ Q₂ hatφ)
    (hd₂ : StrongConvexOn Q₂ 1 d₂)
    (hμ₂ : 0 < μ₂)
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    {x : E₁} (hx : x ∈ Q₁) :
    HasFDerivWithinAt (smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂)
      (A.flip (uμ₂ x)) Q₁ x := by
  -- Route correction: the selector is only certified on `Q₁`, so the derivative is proved
  -- directly within `Q₁` instead of first on all of `E₁`.
  rw [hasFDerivWithinAt_iff_isLittleO]
  have hbigO :
      (fun y : E₁ ↦
        smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂ y -
          smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂ x -
          (A.flip (uμ₂ x)) (y - x)) =O[nhdsWithin x Q₁]
        (fun y : E₁ ↦ (‖y - x‖ ^ (2 : ℕ) : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)) ?_
    filter_upwards [eventually_mem_nhdsWithin] with y hy
    have hpow_nonneg : 0 ≤ (‖y - x‖ ^ (2 : ℕ) : ℝ) := by
      positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg] using
      smoothedPrimalObjectiveZeroPart_remainder_norm_le
        A hhatφ hd₂ hμ₂ huμ₂ hx hy
  exact hbigO.trans_isLittleO
    ((Asymptotics.isLittleO_pow_sub_sub x one_lt_two).mono nhdsWithin_le_nhds)

/-- Helper for Proposition 6.24: the explicit vector field
`x ↦ (InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x))` is Lipschitz on `Q₁`
with constant `(1 / μ₂) * ‖A‖²`. -/
lemma smoothedPrimalObjectiveSelectedDualVector_norm_sub_le
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {uμ₂ : E₁ → E₂}
    (hhatφ : ConvexOn ℝ Q₂ hatφ)
    (hd₂ : StrongConvexOn Q₂ 1 d₂)
    (hμ₂ : 0 < μ₂)
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    {x y : E₁} (hx : x ∈ Q₁) (hy : y ∈ Q₁) :
    ‖(InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x)) -
        (InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ y))‖ ≤
      ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)) * ‖x - y‖ := by
  calc
    ‖(InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x)) -
        (InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ y))‖ =
      ‖A.flip (uμ₂ x) - A.flip (uμ₂ y)‖ := by
        rw [← LinearIsometryEquiv.map_sub]
        simpa using
          (InnerProductSpace.toDual ℝ E₁).symm.norm_map
            (A.flip (uμ₂ x) - A.flip (uμ₂ y))
    _ = ‖A.flip (uμ₂ x - uμ₂ y)‖ := by
      rw [← A.flip.map_sub]
    _ ≤ ‖A.flip‖ * ‖uμ₂ x - uμ₂ y‖ := A.flip.le_opNorm (uμ₂ x - uμ₂ y)
    _ = ‖A‖ * ‖uμ₂ x - uμ₂ y‖ := by
      rw [ContinuousLinearMap.opNorm_flip]
    _ ≤ ‖A‖ * ((((1 / μ₂) * ‖A‖) * ‖x - y‖)) := by
      gcongr
      exact
        smoothedPrimalObjectiveArgmaxSelection_norm_sub_le
          A hhatφ hd₂ hμ₂ huμ₂ hx hy
    _ = ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)) * ‖x - y‖ := by
      ring_nf

-- Proof sketch: apply the Chapter 6 uniqueness mechanism for the penalized dual maximand to each
-- fiber `x`, then use the chosen within-gradient field of `hatf` on `Q₁` together with the
-- gradient formula for the smoothed supremum term, identifying the dual contribution with the
-- Riesz vector of `A.flip (uμ₂ x)`.
/-- Proposition 6.24 (1) [Chapter6_2.json:64]: if `\hat f` has within-gradient field
`gradHatf` on `Q₁`,
`\hat φ` is convex on `Q₂`, `d₂` is `1`-strongly convex on `Q₂`, and `u_{μ₂}` selects a feasible
maximizer of the canonical Chapter 6 argmax owner, then that maximizer is unique for every
`x ∈ Q₁`, and the smoothed primal objective has within-gradient
`gradHatf x + A^* u_{μ₂}(x)` on `Q₁`. -/
theorem smoothedPrimalObjective_argmax_unique_and_hasGradientWithinAt
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {gradHatf : E₁ → E₁} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    (hμ₂ : 0 < μ₂)
    (hhatφ : ConvexOn ℝ Q₂ hatφ)
    (hd₂ : StrongConvexOn Q₂ 1 d₂)
    (hhatf_grad : ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      HasGradientWithinAt hatf (gradHatf x) Q₁ x)
    {uμ₂ : E₁ → E₂}
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x) :
    (∀ ⦃x : E₁⦄, x ∈ Q₁ → ∀ ⦃u : E₂⦄,
      u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x → u = uμ₂ x) ∧
    (∀ ⦃x : E₁⦄, x ∈ Q₁ →
      HasGradientWithinAt
        (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂)
        (gradHatf x +
          (InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x)))
        Q₁ x) := by
  refine ⟨?_, ?_⟩
  · intro x hx u hu
    -- Unpack both feasible maximizers and apply the Chapter 6 uniqueness theorem.
    rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ μ₂ x u).mp hu with
      ⟨hu_mem, hu_max⟩
    rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ μ₂ x (uμ₂ x)).mp (huμ₂ hx) with
      ⟨huμ₂_mem, huμ₂_max⟩
    exact smoothed_maximizer_unique (ℓ := A x) hhatφ hd₂ hμ₂ hu_mem huμ₂_mem
      (by simpa [smoothedPrimalObjectiveMaximand] using hu_max)
      (by simpa [smoothedPrimalObjectiveMaximand] using huμ₂_max)
  · intro x hx
    -- Combine the given within-gradient of `hatf` with the zero-part derivative on `Q₁`.
    have hzero :
        HasFDerivWithinAt (smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂)
          (A.flip (uμ₂ x)) Q₁ x :=
      smoothedPrimalObjectiveZeroPart_hasFDerivWithinAt
        A hhatφ hd₂ hμ₂ huμ₂ hx
    have hsum :
        HasFDerivWithinAt
          (fun y ↦ hatf y + smoothedPrimalObjective A Q₂ (fun _ : E₁ ↦ 0) hatφ d₂ μ₂ y)
          ((InnerProductSpace.toDual ℝ E₁) (gradHatf x) + A.flip (uμ₂ x)) Q₁ x :=
      (hhatf_grad hx).hasFDerivWithinAt.add hzero
    have hfield :
        (InnerProductSpace.toDual ℝ E₁).symm
            ((InnerProductSpace.toDual ℝ E₁) (gradHatf x) + A.flip (uμ₂ x)) =
          gradHatf x + (InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x)) := by
      rw [LinearIsometryEquiv.map_add]
      simp
    -- Rewrite the summed derivative back to the stated smoothed objective and vector field.
    rw [← hfield]
    simpa [smoothedPrimalObjective, add_assoc, add_left_comm, add_comm] using
      hsum.hasGradientWithinAt

-- Proof sketch: combine the gradient identity from
-- `smoothedPrimalObjective_argmax_unique_and_hasGradientWithinAt` with the Chapter 6 Lipschitz
-- estimate for the smoothed supremum term, then add the given Lipschitz field for `gradHatf`.
/-- Proposition 6.24 (2) [Chapter6_2.json:64]: if, in addition,
`gradHatf` is Lipschitz on `Q₁` with constant `L₁(\hat f)`, then the displayed gradient field of
`f_{μ₂}` is Lipschitz on `Q₁` with constant
`L₁(\hat f) + μ₂⁻¹ ‖A‖²`. -/
theorem smoothedPrimalObjective_gradientWithin_lipschitzOn
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {gradHatf : E₁ → E₁} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {Lhatf : NNReal}
    (hμ₂ : 0 < μ₂)
    (hhatφ : ConvexOn ℝ Q₂ hatφ)
    (hd₂ : StrongConvexOn Q₂ 1 d₂)
    (hhatf_grad : ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      HasGradientWithinAt hatf (gradHatf x) Q₁ x)
    {uμ₂ : E₁ → E₂}
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    (hhatf_lipschitz : LipschitzOnWith Lhatf gradHatf Q₁) :
    LipschitzOnWith
      (Lhatf + Real.toNNReal ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)))
      (fun x ↦ gradHatf x +
        (InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x))) Q₁ := by
  intro x hx y hy
  have hconst_nonneg : 0 ≤ (1 / μ₂) * ‖A‖ ^ (2 : ℕ) := by
    positivity
  have hdual :
      edist ((InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x)))
          ((InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ y))) ≤
        Real.toNNReal ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)) * edist x y := by
    have hcoeff :
        ((Real.toNNReal ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)) : NNReal) : ℝ) =
          (1 / μ₂) * ‖A‖ ^ (2 : ℕ) := by
      rw [Real.toNNReal_of_nonneg hconst_nonneg]
      rfl
    have hdist :
        dist ((InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x)))
            ((InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ y))) ≤
          (Real.toNNReal ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)) : ℝ) * dist x y := by
      rw [hcoeff]
      simpa [dist_eq_norm] using
        smoothedPrimalObjectiveSelectedDualVector_norm_sub_le
          A hhatφ hd₂ hμ₂ huμ₂ hx hy
    have hedist :
        edist ((InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x)))
            ((InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ y))) ≤
          ENNReal.ofReal
            ((Real.toNNReal ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)) : ℝ) * dist x y) :=
      (edist_le_ofReal (hr := by positivity)).2 hdist
    simpa [edist_dist, ENNReal.ofReal_mul, Real.toNNReal_of_nonneg hconst_nonneg] using hedist
  -- Add the given Lipschitz field of `hatf` to the selected dual vector estimate.
  calc
    edist (gradHatf x + (InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x)))
        (gradHatf y + (InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ y))) ≤
      edist (gradHatf x) (gradHatf y) +
        edist ((InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x)))
          ((InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ y))) :=
      edist_add_add_le _ _ _ _
    _ ≤
        (Lhatf + Real.toNNReal ((1 / μ₂) * ‖A‖ ^ (2 : ℕ))) * edist x y := by
      simpa [add_mul] using add_le_add (hhatf_lipschitz hx hy) hdual
