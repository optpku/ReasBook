/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_8_5

open scoped Gradient

noncomputable section

universe u

section General

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {xStar : E}

/- Theorem 1.4.21 lies in second-order local optimality.

Sampled owner declarations before refinement:
* `hessian` and `∇²` from `Definition_1_4_16`, the intrinsic Hessian owner and its Euclidean
  matrix view;
* `isLocalMin_gradient_eq_zero_and_hessian_isPositive` from `Theorem_1_4_20`, the nearby
  necessary second-order condition;
* `posDef_exists_quadraticForm_bounds` from `Lemma_1_8_5`, the Euclidean bridge turning matrix
  positive definiteness into a uniform quadratic lower bound;
* `HasGradientAt` from the chapter's first-order differential API.

Best owner abstraction:
* source-facing: the Euclidean sufficient condition `(∇² f xStar).PosDef` together with the
  strict local minimum conclusion in metric-radius form;
* core/canonical: `HasGradientAt f 0 xStar`, `hessian f xStar`, and the intrinsic quadratic lower
  bound `μ ‖h‖² ≤ ⟪hessian f xStar h, h⟫` on a complete real inner product space;
* bridge/view: `posDef_exists_quadraticForm_bounds`, which converts the matrix hypothesis to that
  intrinsic lower bound.

Primitive data:
* source-facing layer: `f : ℝⁿ → ℝ`, `xStar`, stationarity at `xStar`, differentiability of `∇ f`
  at `xStar`, and `(∇² f xStar).PosDef`;
* core companion layer: a positive constant `μ` and the intrinsic Hessian quadratic lower bound
  by `μ`.

Derived API:
* the second-order Taylor-model remainder estimate at `xStar`,
* domination of the remainder by a quarter of the quadratic term,
* the intrinsic lower-bound companion theorem,
* the Euclidean positive-definite Hessian specialization matching the textbook statement. -/

/-- Helper for Theorem 1.4.21: translating the Hessian differentiability hypothesis to the
basepoint gives the first-order little-`o` remainder for the gradient map. -/
private lemma translated_gradient_linearization_isLittleO
    (_hgradDiff : HasFDerivAt (∇ f) (hessian f xStar) xStar) :
    (fun h : E ↦ ∇ f (xStar + h) - ∇ f xStar - hessian f xStar h) =o[nhds (0 : E)]
      fun h ↦ h := by
  -- Rewrite the Fréchet derivative statement exactly in the translated `h ↦ xStar + h` form.
  simpa [hessian] using (hasFDerivAt_iff_isLittleO_nhds_zero.mp _hgradDiff)

/-- Helper for Theorem 1.4.21: pairing the gradient linearization remainder with the displacement
turns the vector little-`o` term into a scalar `o(‖h‖²)` remainder. -/
private lemma paired_gradient_remainder_isLittleO_quadratic
    (_hgradDiff : HasFDerivAt (∇ f) (hessian f xStar) xStar) :
    (fun h : E ↦ inner ℝ (∇ f (xStar + h) - ∇ f xStar - hessian f xStar h) h) =o[nhds (0 : E)]
      fun h ↦ ‖h‖ ^ (2 : ℕ) := by
  let r : E → E := fun h ↦ ∇ f (xStar + h) - ∇ f xStar - hessian f xStar h
  have hr : r =o[nhds (0 : E)] fun h ↦ h :=
    translated_gradient_linearization_isLittleO _hgradDiff
  -- Control the scalar pairing by Cauchy-Schwarz and reuse the vector little-`o` estimate.
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  have hr_bound : ∀ᶠ h : E in nhds (0 : E), ‖r h‖ ≤ c * ‖h‖ := by
    rw [Asymptotics.isLittleO_iff] at hr
    simpa using hr hc
  filter_upwards [hr_bound] with h hh
  calc
    ‖inner ℝ (r h) h‖ ≤ ‖r h‖ * ‖h‖ := by
      simpa [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) (r h) h)
    _ ≤ (c * ‖h‖) * ‖h‖ := by gcongr
    _ = c * ‖h‖ ^ (2 : ℕ) := by ring
    _ = c * ‖‖h‖ ^ (2 : ℕ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      positivity

/-- Helper for the intrinsic companion to Theorem 1.4.21: a quadratic little-o remainder is
eventually bounded by one quarter of a positive quadratic coefficient. -/
private lemma remainder_abs_le_quarter_quadratic_eventually
    {E : Type u} [NormedAddCommGroup E] {R : E → ℝ} {μ : ℝ}
    (hR : R =o[nhds (0 : E)] fun h : E ↦ ‖h‖ ^ (2 : ℕ))
    (hμ : 0 < μ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ h : E, ‖h‖ < δ → |R h| ≤ (μ / 4) * ‖h‖ ^ (2 : ℕ) := by
  have hquarter : 0 < μ / 4 := by positivity
  rw [Asymptotics.isLittleO_iff] at hR
  rcases Metric.mem_nhds_iff.mp (hR hquarter) with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro h hh
  have hmem : h ∈ Metric.ball (0 : E) δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hh
  have hbound := hball hmem
  simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg h) _)] using hbound

/-- Helper for Theorem 1.4.21: scaling a displacement by a parameter in `[0,1]` keeps it inside
the same radius bound. -/
private lemma norm_smul_lt_of_mem_Icc
    {δ : ℝ} {h : E} (hh : ‖h‖ < δ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖t • h‖ < δ := by
  -- Along a segment, the displacement norm contracts by at most the scalar parameter.
  have hle : ‖t • h‖ ≤ ‖h‖ := by
    calc
      ‖t • h‖ = |t| * ‖h‖ := norm_smul _ _
      _ = t * ‖h‖ := by rw [abs_of_nonneg ht0]
      _ ≤ 1 * ‖h‖ := by gcongr
      _ = ‖h‖ := by ring
  exact lt_of_le_of_lt hle hh

/-- Helper for Theorem 1.4.21: near `xStar`, the displacement pairing with the gradient is
strictly positive once the Hessian quadratic form has a positive lower bound. -/
private lemma inner_gradient_displacement_pos_eventually
    (hstationary : HasGradientAt f 0 xStar)
    (hgradDiff : HasFDerivAt (∇ f) (hessian f xStar) xStar)
    {μ : ℝ} (hμ : 0 < μ)
    (hH : ∀ h : E, μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar h) h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : E, h ≠ 0 → ‖h‖ < δ → 0 < inner ℝ (∇ f (xStar + h)) h := by
  have hpair := paired_gradient_remainder_isLittleO_quadratic (f := f) (xStar := xStar) hgradDiff
  obtain ⟨δ, hδ, hδbound⟩ :=
    remainder_abs_le_quarter_quadratic_eventually hpair (show 0 < 2 * μ by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro h hh_ne hh_norm
  have hrem_abs :
      |inner ℝ (∇ f (xStar + h) - ∇ f xStar - hessian f xStar h) h| ≤
        ((2 * μ) / 4) * ‖h‖ ^ (2 : ℕ) :=
    hδbound h hh_norm
  have hquad : μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar h) h := hH h
  have hrem_lower :
      -(((2 * μ) / 4) * ‖h‖ ^ (2 : ℕ)) ≤
        inner ℝ (∇ f (xStar + h) - ∇ f xStar - hessian f xStar h) h := by
    exact (abs_le.mp hrem_abs).1
  -- The positive Hessian term dominates the quadratic error term.
  have hmain : (μ / 2) * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f (xStar + h)) h := by
    calc
      (μ / 2) * ‖h‖ ^ (2 : ℕ) ≤
          inner ℝ (hessian f xStar h) h +
            inner ℝ (∇ f (xStar + h) - ∇ f xStar - hessian f xStar h) h := by
        nlinarith
      _ = inner ℝ ((hessian f xStar h) + (∇ f (xStar + h) - ∇ f xStar - hessian f xStar h)) h := by
        rw [inner_add_left]
      _ = inner ℝ (∇ f (xStar + h) - ∇ f xStar) h := by
        abel_nf
      _ = inner ℝ (∇ f (xStar + h)) h := by
        simp [hstationary.gradient]
  have hsq_pos : 0 < ‖h‖ ^ (2 : ℕ) := by
    have hnorm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh_ne
    positivity
  have hpos : 0 < (μ / 2) * ‖h‖ ^ (2 : ℕ) := by
    positivity
  exact lt_of_lt_of_le hpos hmain

private theorem strict_local_minimizer_of_gradient_zero_of_hessian_lower_bound_aux
    {μ : ℝ}
    (hstationary : HasGradientAt f 0 xStar)
    (hgradDiff : DifferentiableAt ℝ (∇ f) xStar)
    (hμ : 0 < μ)
    (hH : ∀ h : E, μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar h) h) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : E, y ≠ xStar → dist y xStar < δ → f xStar < f y := by
-- Route correction: the current owner hypotheses directly control the gradient linearization, so
-- we prove strict local minimality by showing that every short segment from `xStar` has positive
-- directional derivative away from the basepoint.
  have hgradDiffAt : HasFDerivAt (∇ f) (hessian f xStar) xStar := by
    simpa [hessian] using hgradDiff.hasFDerivAt
  obtain ⟨δ, hδ, hpos⟩ :=
    inner_gradient_displacement_pos_eventually hstationary hgradDiffAt hμ hH
  refine ⟨δ, hδ, ?_⟩
  intro y hy_ne hy_dist
  let h : E := y - xStar
  have hy_eq : xStar + h = y := by
    simp [h]
  have hh_ne : h ≠ 0 := by
    dsimp [h]
    intro hzero
    apply hy_ne
    simpa using sub_eq_zero.mp hzero
  have hh_norm : ‖h‖ < δ := by
    dsimp [h] at *
    simpa [dist_eq_norm] using hy_dist
  let φ : ℝ → ℝ := fun t ↦ f (xStar + t • h)
  -- The displacement pairing is positive along the whole short segment, hence the ray map is
  -- strictly increasing on `[0,1]`.
  have hφ_mono : StrictMonoOn φ (Set.Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
    · intro t ht
      by_cases ht0 : t = 0
      · have hline : DifferentiableAt ℝ (fun s : ℝ ↦ xStar + s • h) (0 : ℝ) := by
          exact (((hasDerivAt_id 0).smul_const h).const_add xStar).differentiableAt
        have hbase : DifferentiableAt ℝ f (xStar + (0 : ℝ) • h) := by
          simpa [zero_smul] using hstationary.differentiableAt
        simpa [Function.comp, φ, ht0] using
          (hbase.comp (0 : ℝ) hline).continuousAt.continuousWithinAt
      · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
        have hsmall : ‖t • h‖ < δ := norm_smul_lt_of_mem_Icc hh_norm ht.1 ht.2
        have hth_ne : t • h ≠ 0 := smul_ne_zero ht_pos.ne' hh_ne
        have hdisp_pos : 0 < inner ℝ (∇ f (xStar + t • h)) (t • h) :=
          hpos (t • h) hth_ne hsmall
        have hdiff : DifferentiableAt ℝ f (xStar + t • h) := by
          by_contra hnot
          have hzero : ∇ f (xStar + t • h) = 0 := gradient_eq_zero_of_not_differentiableAt hnot
          have : ¬ 0 < inner ℝ (∇ f (xStar + t • h)) (t • h) := by
            simp [hzero]
          exact this hdisp_pos
        have hline : DifferentiableAt ℝ (fun s : ℝ ↦ xStar + s • h) t := by
          exact (((hasDerivAt_id t).smul_const h).const_add xStar).differentiableAt
        simpa [Function.comp, φ] using
          (hdiff.comp t hline).continuousAt.continuousWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := htIoo.1
      have hsmall : ‖t • h‖ < δ :=
        norm_smul_lt_of_mem_Icc hh_norm (le_of_lt htIoo.1) (le_of_lt htIoo.2)
      have hth_ne : t • h ≠ 0 := smul_ne_zero ht_pos.ne' hh_ne
      have hdisp_pos : 0 < inner ℝ (∇ f (xStar + t • h)) (t • h) :=
        hpos (t • h) hth_ne hsmall
      have hdiff : DifferentiableAt ℝ f (xStar + t • h) := by
        by_contra hnot
        have hzero : ∇ f (xStar + t • h) = 0 := gradient_eq_zero_of_not_differentiableAt hnot
        have : ¬ 0 < inner ℝ (∇ f (xStar + t • h)) (t • h) := by
          simp [hzero]
        exact this hdisp_pos
      have hline : HasDerivAt (fun s : ℝ ↦ xStar + s • h) h t := by
        simpa [one_smul] using (((hasDerivAt_id t).smul_const h).const_add xStar)
      have hderiv : HasDerivAt φ (inner ℝ (∇ f (xStar + t • h)) h) t := by
        have hcomp : HasDerivAt φ (fderiv ℝ f (xStar + t • h) h) t :=
          hdiff.hasFDerivAt.comp_hasDerivAt t hline
        simpa [φ, hdiff.hasGradientAt.fderiv_apply] using hcomp
      rw [hderiv.deriv]
      have hderiv_pos : 0 < inner ℝ (∇ f (xStar + t • h)) h := by
        rw [inner_smul_right] at hdisp_pos
        exact (mul_pos_iff_of_pos_left ht_pos).mp hdisp_pos
      simpa using hderiv_pos
  have hlt : φ 0 < φ 1 := hφ_mono (by simp) (by simp) zero_lt_one
  simpa [φ, h, hy_eq] using hlt

end General

section Euclidean

variable {n : ℕ}

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {xStar : EuclideanSpace ℝ (Fin n)}

/-- Helper for Theorem 1.4.21: the Euclidean Hessian matrix and the intrinsic Hessian operator
have the same quadratic form. -/
private lemma matrix_quadratic_form_rewrite
    (h : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (((∇² f xStar).toEuclideanLin) h) h = inner ℝ (hessian f xStar h) h := by
  -- Rewrite the matrix-side action through the canonical Euclidean Hessian operator.
  have hlin :
      ((∇² f xStar).toEuclideanLin) h = hessian f xStar h := by
    simpa using DFunLike.congr_fun (hessianMatrix_toEuclideanLin f xStar) h
  simpa using congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ inner ℝ v h) hlin

/-- Euclidean bridge: a positive-definite Hessian matrix gives the intrinsic quadratic lower bound
required by the intrinsic companion theorem. -/
private lemma hessian_posDef_quadratic_lower_bound
    (hH : (∇² f xStar).PosDef) :
    ∃ μ : ℝ, 0 < μ ∧
      ∀ h : EuclideanSpace ℝ (Fin n), μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar h) h := by
  obtain ⟨μ, hμ, _M, _hM, hbounds⟩ :=
    posDef_exists_quadraticForm_bounds (∇² f xStar) hH
  refine ⟨μ, hμ, ?_⟩
  intro h
  -- Keep only the lower matrix-side coercivity bound and rewrite it intrinsically.
  calc
    μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (((∇² f xStar).toEuclideanLin) h) h := by
      simpa using (hbounds h).1
    _ = inner ℝ (hessian f xStar h) h := by
      simpa using matrix_quadratic_form_rewrite (f := f) (xStar := xStar) h

/-- Theorem 1.4.21: if `f : ℝⁿ → ℝ` is stationary at `xStar`, the gradient map `∇ f` is
differentiable at `xStar`, and the Hessian matrix `∇² f xStar` is positive definite, then
`xStar` is a strict local minimizer of `f`. -/
theorem strict_local_minimizer_of_gradient_zero_of_hessian_posDef
    (hstationary : HasGradientAt f 0 xStar)
    (hgradDiff : DifferentiableAt ℝ (∇ f) xStar)
    (hH : (∇² f xStar).PosDef) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : EuclideanSpace ℝ (Fin n), y ≠ xStar → dist y xStar < δ → f xStar < f y := by
  -- Route correction: close the Euclidean theorem by extracting the intrinsic quadratic bound
  -- and feeding it into the already-verified intrinsic companion theorem.
  obtain ⟨μ, hμ, hμbound⟩ := hessian_posDef_quadratic_lower_bound (f := f) (xStar := xStar) hH
  exact strict_local_minimizer_of_gradient_zero_of_hessian_lower_bound_aux
    hstationary hgradDiff hμ hμbound

end Euclidean

section General

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {xStar : E}

/-- Companion intrinsic form of Theorem 1.4.21: on a real complete inner product space, if `f` is
stationary at `xStar`, the gradient map `∇ f` is differentiable at `xStar`, and the Hessian
quadratic form at `xStar` is bounded below by `μ ‖h‖²` for some `μ > 0`, then `xStar` is a strict
local minimizer of `f`. -/
theorem strict_local_minimizer_of_gradient_zero_of_hessian_lower_bound
    {μ : ℝ}
    (hstationary : HasGradientAt f 0 xStar)
    (hgradDiff : DifferentiableAt ℝ (∇ f) xStar)
    (hμ : 0 < μ)
    (hH : ∀ h : E, μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar h) h) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : E, y ≠ xStar → dist y xStar < δ → f xStar < f y :=
  strict_local_minimizer_of_gradient_zero_of_hessian_lower_bound_aux
    hstationary hgradDiff hμ hH

end General
