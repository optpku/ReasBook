/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 1.4.20 is a source-facing item in second-order smooth optimization.

Relevant owner declarations sampled before refinement:
* `hessian` from `Definition_1_4_16`
* `isLocalMin_hasGradientAt_zero_of_differentiableAt` from `Theorem_1_4_13`
* `gradient_eq_zero_of_not_differentiableAt`
* `fderiv_gradient_isSymmetric_of_contDiffAt` from `Theorem_1_4_19`
* `ContinuousLinearMap.isPositive_iff`

Best owner abstractions:
* source-facing: the Hessian quadratic-form condition
  `∀ s, 0 ≤ inner ℝ (hessian f xStar s) s`
* bridge/view: the positive-operator conclusion
  `ContinuousLinearMap.IsPositive (hessian f xStar)` under `ContDiffAt ℝ 2 f xStar`

Primitive data:
* `f`
* `xStar`
* local minimality of `f` at `xStar`
* differentiability of `f` at `xStar`
* differentiability of `∇ f` at `xStar`

Derived API:
* vanishing gradient at `xStar`
* nonnegativity of the Hessian quadratic form at `xStar`
* positivity of the Hessian operator at `xStar` once Hessian symmetry is supplied canonically by
  `ContDiffAt.isSymmSndFDerivAt`

Source/core/bridge triage:
* source-facing: the combined first- and second-order necessary conditions
* core/canonical: `∇ f xStar = 0` together with the directional inequality
  `∀ s, 0 ≤ inner ℝ (hessian f xStar s) s`
* bridge/view: the `C²` upgrade to `ContinuousLinearMap.IsPositive`; Euclidean matrix
  restatements belong in separate Hessian-matrix view files

The public API therefore keeps the source-facing quadratic-form theorem as the main entry. The
positive-operator statement is retained only as the thin `C²` bridge that reuses the canonical
second-derivative symmetry owner instead of routing through a separate Euclidean coordinate view. -/

-- Helper for Theorem 1.4.20: restricting `f` to an affine line through `xStar`
-- preserves local minimality at the origin.
omit [CompleteSpace E] in
private lemma line_restriction_isLocalMin
    {f : E → ℝ} {xStar : E} (hmin : IsLocalMin f xStar) (s : E) :
    IsLocalMin (fun t : ℝ ↦ f (xStar + t • s)) 0 := by
  let g : ℝ → E := fun t ↦ xStar + t • s
  have hmin' : IsLocalMin f (g 0) := by
    dsimp [g]
    simpa using hmin
  have hcont : ContinuousAt g 0 := by
    simpa [g] using
      ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt :
        ContinuousAt (fun t : ℝ ↦ xStar + t • s) 0)
  -- Compose the local minimum with the continuous affine line parameterization.
  simpa [g] using hmin'.comp_continuous hcont

-- Helper for Theorem 1.4.20: the derivative of the line restriction at `t` is the line
-- derivative of `f` at the translated base point.
omit [CompleteSpace E] in
private lemma line_restriction_deriv_eq_lineDeriv
    {f : E → ℝ} {xStar s : E} (t : ℝ) :
    deriv (fun u : ℝ ↦ f (xStar + u • s)) t = lineDeriv ℝ f (xStar + t • s) s := by
  -- Shift the affine parameter so the derivative at `t` becomes a line derivative at the origin.
  rw [lineDeriv]
  nth_rewrite 1 [← zero_add t]
  rw [← deriv_comp_add_const (fun u : ℝ ↦ f (xStar + u • s)) t 0]
  congr with u
  simp [add_smul, add_assoc, add_comm (u • s)]

/-- Helper for Theorem 1.4.20: differentiating the directional gradient along a line recovers the
Hessian quadratic form in that direction. -/
private lemma directional_gradient_deriv_eq_hessian_quadratic
    {f : E → ℝ} {xStar : E} (hgradDiff : DifferentiableAt ℝ (∇ f) xStar) (s : E) :
    HasDerivAt (fun t : ℝ ↦ inner ℝ (∇ f (xStar + t • s)) s)
      (inner ℝ ((fderiv ℝ (∇ f) xStar) s) s) 0 := by
  have hLine : HasDerivAt (fun t : ℝ ↦ ∇ f (xStar + t • s))
      ((fderiv ℝ (∇ f) xStar) s) 0 := by
    -- Differentiate the gradient field along the affine line.
    simpa using (hgradDiff.hasFDerivAt.hasLineDerivAt s)
  have hs : HasDerivAt (fun _ : ℝ ↦ s) 0 0 := hasDerivAt_const 0 s
  -- Pair the differentiated gradient with the fixed direction `s`.
  simpa using hLine.inner ℝ hs

/-- Helper for Theorem 1.4.20: at points where `f` is differentiable, the derivative of the line
restriction agrees with the directional pairing of the gradient. -/
private lemma line_restriction_deriv_eq_directional_gradient
    {f : E → ℝ} {xStar s : E} {t : ℝ}
    (hdiff : DifferentiableAt ℝ f (xStar + t • s)) :
    deriv (fun u : ℝ ↦ f (xStar + u • s)) t = inner ℝ (∇ f (xStar + t • s)) s := by
  -- Rewrite the line derivative at time `t` using differentiability of `f` at the translated
  -- base point.
  rw [line_restriction_deriv_eq_lineDeriv t]
  rw [hdiff.lineDeriv_eq_fderiv]
  symm
  simpa using (inner_gradient_left hdiff)

/-- Helper for Theorem 1.4.20: if a scalar function is constant on a neighborhood of the origin,
then every interior derivative in that neighborhood vanishes. -/
private lemma deriv_zero_of_locally_constant_near_zero
    {φ : ℝ → ℝ} {ε t : ℝ} (ht : |t| < ε)
    (hconst : ∀ u, |u| < ε → φ u = φ 0) : HasDerivAt φ 0 t := by
  have hδ : 0 < ε - |t| := sub_pos.mpr ht
  have heq : φ =ᶠ[nhds t] fun _ ↦ φ 0 := by
    -- Shrink the original neighborhood of constancy so it becomes a neighborhood of `t`.
    refine Metric.mem_nhds_iff.mpr ?_
    refine ⟨ε - |t|, hδ, ?_⟩
    intro u hu
    have hu' : |u| < ε := by
      have hut' : |u - t| < ε - |t| := by
        simpa [Real.dist_eq] using hu
      have habs : |u| ≤ |u - t| + |t| := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (abs_sub_le u t 0)
      linarith
    exact hconst u hu'
  -- Replace `φ` by the locally equal constant function.
  exact ((heq.hasDerivAt_iff).2 (hasDerivAt_const t (φ 0)))

/-- Helper for Theorem 1.4.20: every directional Hessian quadratic form is nonnegative at a local
minimizer. -/
private lemma directional_quadratic_nonneg_of_isLocalMin
    {f : E → ℝ} {xStar : E} (hf : DifferentiableAt ℝ f xStar)
    (hgradDiff : DifferentiableAt ℝ (∇ f) xStar) (hmin : IsLocalMin f xStar) (s : E) :
    0 ≤ inner ℝ ((fderiv ℝ (∇ f) xStar) s) s := by
  let φ : ℝ → ℝ := fun t ↦ f (xStar + t • s)
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (xStar + t • s)) s
  have hφmin : IsLocalMin φ 0 := by
    -- Restrict the multivariate local minimum to the affine line through `xStar` in direction `s`.
    simpa [φ] using line_restriction_isLocalMin hmin s
  have hgrad0 : ∇ f xStar = 0 :=
    isLocalMin_gradient_eq_zero hmin
  have hψderiv : HasDerivAt ψ (inner ℝ ((fderiv ℝ (∇ f) xStar) s) s) 0 := by
    -- The derivative of the directional gradient at the origin is the Hessian quadratic form.
    simpa [ψ] using directional_gradient_deriv_eq_hessian_quadratic hgradDiff s
  have hψ0 : ψ 0 = 0 := by
    simp [ψ, hgrad0]
  by_contra hneg
  have hψright : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ψ t < 0 := by
    have hsign : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        SignType.sign (ψ t) = SignType.sign (0 - t) :=
      (eventually_nhdsWithin_sign_eq_of_deriv_neg
        (by simpa [hψderiv.deriv] using hneg) hψ0).filter_mono inf_le_left
    -- A negative derivative at `0` forces the directional gradient to be negative on the right.
    filter_upwards [hsign, self_mem_nhdsWithin] with t ht hpos
    have hsignneg : SignType.sign (ψ t) = -1 := by
      calc
        SignType.sign (ψ t) = SignType.sign (0 - t) := ht
        _ = -1 := by
          apply sign_eq_neg_one_iff.mpr
          have htpos : 0 < t := hpos
          linarith
    exact sign_eq_neg_one_iff.mp hsignneg
  have hψleft : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0), 0 < ψ t := by
    have hsign : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0),
        SignType.sign (ψ t) = SignType.sign (0 - t) :=
      (eventually_nhdsWithin_sign_eq_of_deriv_neg
        (by simpa [hψderiv.deriv] using hneg) hψ0).filter_mono inf_le_left
    -- The same derivative information makes the directional gradient positive on the left.
    filter_upwards [hsign, self_mem_nhdsWithin] with t ht hneg_t
    have hsignpos : SignType.sign (ψ t) = 1 := by
      calc
        SignType.sign (ψ t) = SignType.sign (0 - t) := ht
        _ = 1 := by
          apply sign_eq_one_iff.mpr
          have htneg : t < 0 := hneg_t
          linarith
    exact sign_eq_one_iff.mp hsignpos
  have hφcont : ContinuousAt φ 0 := by
    let g : ℝ → E := fun t ↦ xStar + t • s
    have hline : ContinuousAt g 0 := by
      simpa [g] using
        ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt :
          ContinuousAt (fun t : ℝ ↦ xStar + t • s) 0)
    have hcont_f : ContinuousAt f (g 0) := by
      dsimp [g]
      simpa using hf.continuousAt
    -- Continuity of `f` at `xStar` gives continuity of the restricted scalar function at `0`.
    simpa [φ, g] using hcont_f.comp hline
  have hfdiff_right : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      DifferentiableAt ℝ f (xStar + t • s) := by
    -- On the right, a nonzero directional gradient forces `∇ f` to be nonzero, hence `f` is
    -- genuinely differentiable there because the totalized gradient vanishes at non-differentiable
    -- points.
    filter_upwards [hψright] with t ht
    have hgrad_ne : ∇ f (xStar + t • s) ≠ 0 := by
      intro hzero
      have : ψ t = 0 := by
        simp [ψ, hzero]
      exact ht.ne this
    by_contra hdiff
    exact hgrad_ne (by simpa using gradient_eq_zero_of_not_differentiableAt hdiff)
  have hfdiff_left : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0),
      DifferentiableAt ℝ f (xStar + t • s) := by
    -- The same argument works on the left.
    filter_upwards [hψleft] with t ht
    have hgrad_ne : ∇ f (xStar + t • s) ≠ 0 := by
      intro hzero
      have : ψ t = 0 := by
        simp [ψ, hzero]
      exact ht.ne' this
    by_contra hdiff
    exact hgrad_ne (by simpa using gradient_eq_zero_of_not_differentiableAt hdiff)
  have hφdiff_right : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), DifferentiableAt ℝ φ t := by
    filter_upwards [hfdiff_right] with t hdiff_f
    have hline : DifferentiableAt ℝ (fun u : ℝ ↦ xStar + u • s) t :=
      (differentiableAt_id.smul_const s).const_add xStar
    -- Compose the affine line with the differentiability of `f`.
    simpa [φ] using hdiff_f.comp t hline
  have hφdiff_left : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0), DifferentiableAt ℝ φ t := by
    filter_upwards [hfdiff_left] with t hdiff_f
    have hline : DifferentiableAt ℝ (fun u : ℝ ↦ xStar + u • s) t :=
      (differentiableAt_id.smul_const s).const_add xStar
    -- Compose the affine line with the differentiability of `f`.
    simpa [φ] using hdiff_f.comp t hline
  have hderiv_right : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), deriv φ t < 0 := by
    -- On the right, the derivative of the restricted function is exactly the negative directional
    -- gradient.
    filter_upwards [hψright, hfdiff_right] with t ht hdiff
    rw [line_restriction_deriv_eq_directional_gradient hdiff]
    simpa [φ, ψ] using ht
  have hderiv_left : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Iio 0), 0 < deriv φ t := by
    -- On the left, the derivative of the restricted function is positive.
    filter_upwards [hψleft, hfdiff_left] with t ht hdiff
    rw [line_restriction_deriv_eq_directional_gradient hdiff]
    simpa [φ, ψ] using ht
  have hφmax : IsLocalMax φ 0 := by
    -- These one-sided derivative signs force a local maximum of the restricted function at `0`.
    refine isLocalMax_of_deriv' hφcont hφdiff_left hφdiff_right ?_ ?_
    · exact hderiv_left.mono fun _ ht ↦ le_of_lt ht
    · exact hderiv_right.mono fun _ ht ↦ le_of_lt ht
  have hconst_event : ∀ᶠ t in nhds (0 : ℝ), φ t = φ 0 := by
    -- Having both a local minimum and a local maximum makes the line restriction locally constant.
    filter_upwards [hφmin, hφmax] with t htmin htmax
    exact le_antisymm htmax htmin
  obtain ⟨ε, hε, hconst⟩ : ∃ ε > 0, ∀ t, |t| < ε → φ t = φ 0 := by
    rcases Metric.mem_nhds_iff.mp hconst_event with ⟨ε, hε, hεmem⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht
    exact hεmem (by simpa [Metric.ball, Real.dist_eq] using ht)
  obtain ⟨δ, hδ, hδprop⟩ : ∃ δ > 0, ∀ t, t ∈ Set.Ioo (0 : ℝ) δ → deriv φ t < 0 := by
    rcases (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hderiv_right with ⟨δ, hδ, hδprop⟩
    exact ⟨δ, hδ, fun t ht ↦ hδprop ht⟩
  let t0 : ℝ := min ε δ / 2
  have ht0_pos : 0 < t0 := by
    positivity
  have ht0_lt_ε : |t0| < ε := by
    have ht0_lt : t0 < ε := by
      have hmin_pos : 0 < min ε δ := lt_min hε hδ
      have : min ε δ / 2 < min ε δ := by
        nlinarith
      exact this.trans_le (min_le_left _ _)
    simpa [t0, abs_of_pos ht0_pos] using ht0_lt
  have ht0_mem : t0 ∈ Set.Ioo (0 : ℝ) δ := by
    refine ⟨ht0_pos, ?_⟩
    have hmin_pos : 0 < min ε δ := lt_min hε hδ
    have : min ε δ / 2 < min ε δ := by
      nlinarith
    exact this.trans_le (min_le_right _ _)
  have hderiv_zero : deriv φ t0 = 0 := by
    -- A function constant near `0` is constant near `t0`, so its derivative at `t0` vanishes.
    exact (deriv_zero_of_locally_constant_near_zero ht0_lt_ε hconst).deriv
  have hderiv_neg : deriv φ t0 < 0 := hδprop t0 ht0_mem
  exact hderiv_neg.ne' hderiv_zero.symm

/-- Theorem 1.4.20: if a real-valued function on a real complete inner product space is
differentiable at `xStar` and the gradient map `∇ f` is differentiable at `xStar`, then every
local minimizer `xStar` has vanishing gradient and nonnegative Hessian quadratic form in every
direction at `xStar`. -/
-- Proof sketch: combine Fermat's theorem for the gradient with the line-restriction argument
-- proving nonnegativity of every directional Hessian quadratic form.
theorem isLocalMin_gradient_eq_zero_and_hessian_quadratic_nonneg
    {f : E → ℝ} {xStar : E} (hf : DifferentiableAt ℝ f xStar)
    (hgradDiff : DifferentiableAt ℝ (∇ f) xStar) (hmin : IsLocalMin f xStar) :
    ∇ f xStar = 0 ∧ ∀ s : E, 0 ≤ inner ℝ (hessian f xStar s) s := by
  refine ⟨isLocalMin_gradient_eq_zero hmin, ?_⟩
  intro s
  simpa [hessian] using directional_quadratic_nonneg_of_isLocalMin hf hgradDiff hmin s

/-- Companion bridge: under the chapter's canonical `C²` owner assumption, the source-facing
quadratic-form condition from Theorem 1.4.20 upgrades to positivity of the Hessian operator. -/
theorem isLocalMin_gradient_eq_zero_and_hessian_isPositive
    {f : E → ℝ} {xStar : E} (hf : ContDiffAt ℝ 2 f xStar) (hmin : IsLocalMin f xStar) :
    ∇ f xStar = 0 ∧ ContinuousLinearMap.IsPositive (hessian f xStar) := by
  have hdiff : DifferentiableAt ℝ f xStar :=
    hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hgradDiff : DifferentiableAt ℝ (∇ f) xStar := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) xStar :=
      hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) xStar :=
      hfderiv.differentiableAt one_ne_zero
    simpa [gradient] using
      (((InnerProductSpace.toDual ℝ E).symm).comp_differentiableAt_iff).2 hfdiff
  have hsymm : (hessian f xStar).IsSymmetric :=
    fderiv_gradient_isSymmetric_of_contDiffAt hf
  rcases isLocalMin_gradient_eq_zero_and_hessian_quadratic_nonneg hdiff hgradDiff hmin with
    ⟨hgrad, hquad⟩
  exact ⟨hgrad, (ContinuousLinearMap.isPositive_iff _).2 ⟨hsymm, hquad⟩⟩

end
