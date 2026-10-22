/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_27
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_29
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Text_6_1_1_Conjugate_Closedness_and_Domain_Nonemptiness

open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

-- Semantic recall: LeanSearch exposed no direct owner theorem for the full source-level
-- Legendre statement, so this file keeps the source clauses explicit on the existing Fenchel-dual
-- API.

omit [FiniteDimensional ℝ E] in
/-- A Fenchel-support maximizer yields the corresponding subgradient on the effective domain. -/
theorem subgradient_mem_subdifferential_of_fenchelSupport_isMaxOn
    {f : E → WithTop ℝ} {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    s ∈ ∂ f(x) := by
  -- Repackage the support maximizer inequality as the owner-level subgradient inequality.
  refine mem_subdifferential_iff.mpr ?_
  constructor
  · exact hx
  · intro y hy
    have hsupport :
        inner ℝ s y - withTopRealPart f y ≤ inner ℝ s x - withTopRealPart f x :=
      hmax hy
    have hreal :
        withTopRealPart f y ≥ withTopRealPart f x + inner ℝ s (y - x) := by
      rw [inner_sub_right]
      linarith
    rw [← coe_withTopRealPart hy, ← coe_withTopRealPart hx]
    exact_mod_cast hreal

omit [FiniteDimensional ℝ E] in
/-- A subgradient at `x` makes `x` a Fenchel-support maximizer on `dom f`. -/
theorem fenchelSupport_isMaxOn_of_subgradient
    {f : E → WithTop ℝ} {s x : E}
    (hsub : s ∈ ∂ f(x)) :
    IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x := by
  rcases mem_subdifferential_iff.mp hsub with ⟨hx, hminorant⟩
  intro y hy
  -- The owner-level affine lower support bound is exactly the maximizer inequality after
  -- rearranging the inner-product term.
  have hminorant_real :
      withTopRealPart f x + inner ℝ s (y - x) ≤ withTopRealPart f y := by
    have hminorant_withTop :
        f y ≥ f x + (inner ℝ s (y - x) : WithTop ℝ) :=
      hminorant hy
    rw [← coe_withTopRealPart hy, ← coe_withTopRealPart hx] at hminorant_withTop
    exact_mod_cast hminorant_withTop
  calc
    inner ℝ s y - withTopRealPart f y
        ≤ inner ℝ s y - (withTopRealPart f x + inner ℝ s (y - x)) := by
          exact sub_le_sub_left hminorant_real (inner ℝ s y)
    _ = inner ℝ s x - withTopRealPart f x := by
          rw [inner_sub_right]
          ring

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 5.1.6: Fenchel-support maximizers are exactly minimizers of the affine tilt
`withTopRealPart f - ⟪s, ·⟫` on `dom f`. -/
lemma fenchelSupport_isMaxOn_iff_tiltedIsMinOn
    {f : E → WithTop ℝ} {s x : E} :
    IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x ↔
      IsMinOn
        (quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E) + withTopRealPart f)
        (dom f) x := by
  constructor
  · intro hmax z hz
    -- Negating the support-maximizer inequality converts it into the affine-tilt minimizer form.
    have hsupport : inner ℝ s z - withTopRealPart f z ≤ inner ℝ s x - withTopRealPart f x :=
      hmax hz
    simpa [quadraticAffineObjective_zero_operator, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using (neg_le_neg hsupport)
  · intro hmin z hz
    let G : E → ℝ := quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E) + withTopRealPart f
    -- Reading the tilted objective as `withTopRealPart f - ⟪s, ·⟫` restores the support inequality.
    have htilt0 : G x ≤ G z := by
      simpa [Set.mem_setOf_eq, G] using hmin hz
    have htilt :
        withTopRealPart f x - inner ℝ s x ≤ withTopRealPart f z - inner ℝ s z := by
      simpa [G, quadraticAffineObjective_zero_operator, sub_eq_add_neg, add_left_comm, add_comm]
        using htilt0
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (neg_le_neg htilt)

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 5.1.6: a finite Fenchel-dual point forces the primal effective domain to be
nonempty. -/
lemma dom_nonempty_of_mem_dom_fenchelDual
    {f : E → WithTop ℝ} {s : E} (hs : s ∈ dom (f⋆)) :
    (dom f).Nonempty := by
  by_contra hdom
  -- If `dom f` were empty, the Fenchel dual would be identically `⊥`, contradicting `hs`.
  have hdual_bot : (f⋆) s = ⊥ :=
    fenchelDual_eq_bot_of_not_dom_nonempty (f := f) hdom s
  exact (mem_extendedRealEffectiveDomain_iff.mp hs).2 hdual_bot

section SelfConcordantPrimal

variable {f : E → WithTop ℝ}
variable (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))

/-- For a self-concordant primal function, the subdifferential at a finite point is the singleton
consisting of the primal gradient. -/
theorem subdifferential_eq_singleton_gradient_of_selfConcordant
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    {x : E} (hx : x ∈ dom f) :
    ∂ f(x) = {∇ (withTopRealPart f) x} := by
  rcases hself with ⟨Mf, hMf⟩
  have hxInterior : x ∈ interior (dom f) := by
    simpa [hMf.isOpen_domain.interior_eq] using hx
  have hdiff :
      DifferentiableAt ℝ (withTopRealPart f) x := by
    -- Self-concordance supplies `C²` regularity, hence differentiability, on the open domain.
    have hcontDiffAt :
        ContDiffAt ℝ 2 (withTopRealPart f) x := by
      exact (hMf.contDiffOn.of_le (by norm_num)).contDiffAt (hMf.isOpen_domain.mem_nhds hx)
    exact hcontDiffAt.differentiableAt (by norm_num)
  -- Once `x` is interior to the open domain, the chapter singleton-subdifferential theorem
  -- identifies `∂ f(x)` with the gradient.
  exact subdifferential_eq_singleton_gradient hMf.convexOn hxInterior hdiff

/-- At a Fenchel-support maximizer of a self-concordant function, the primal gradient recovers
the dual slope. -/
theorem gradient_eq_of_fenchelSupport_isMaxOn
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    ∇ (withTopRealPart f) x = s := by
  have hsub :
      s ∈ ∂ f(x) :=
    subgradient_mem_subdifferential_of_fenchelSupport_isMaxOn hx hmax
  have hs_eq :
      s = ∇ (withTopRealPart f) x := by
    simpa [subdifferential_eq_singleton_gradient_of_selfConcordant (f := f) hself hx] using hsub
  exact hs_eq.symm

/-- Every primal gradient lies in the effective domain of the Fenchel dual. -/
theorem image_gradient_subset_dom_fenchelDual_of_selfConcordant
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f)) :
    ∇ (withTopRealPart f) '' dom f ⊆ dom (f⋆) := by
  intro s hs
  rcases hs with ⟨x, hx, rfl⟩
  rcases hself with ⟨Mf, hMf⟩
  have hxInterior : x ∈ interior (dom f) := by
    simpa [hMf.isOpen_domain.interior_eq] using hx
  have hdiff :
      DifferentiableAt ℝ (withTopRealPart f) x := by
    -- The self-concordant regularity makes the primal gradient available at every domain point.
    have hcontDiffAt :
        ContDiffAt ℝ 2 (withTopRealPart f) x := by
      exact (hMf.contDiffOn.of_le (by norm_num)).contDiffAt (hMf.isOpen_domain.mem_nhds hx)
    exact hcontDiffAt.differentiableAt (by norm_num)
  have hsub :
      ∇ (withTopRealPart f) x ∈ ∂ f(x) := by
    -- The gradient is a subgradient at interior points of a convex differentiable function.
    simpa using
      gradient_mem_subdifferential_of_hasGradientAt hMf.convexOn hxInterior hdiff.hasGradientAt
  exact subdifferential_subset_dom_fenchelDual (f := f) (x := x) hsub

end SelfConcordantPrimal

section SourceFacing

variable {f : E → WithTop ℝ}

/-- Source-facing Legendre-type condition for Lemma 5.1.6: besides differentiability on the open
effective domain, the gradient is injective there, becomes unbounded when approaching the
boundary of `dom f` from within the domain, and also becomes unbounded along every nontrivial
forward ray that stays inside `dom f`. The extra ray clause restores the source meaning when
`dom f = Set.univ`, where the frontier condition is vacuous. -/
class IsLegendreType (f : E → WithTop ℝ) : Prop where
  gradient_inj :
    Set.InjOn (∇ (withTopRealPart f)) (dom f)
  gradient_norm_tendsto_atTop :
    ∀ ⦃x : E⦄, x ∈ frontier (dom f) →
      Filter.Tendsto (fun y : E ↦ ‖∇ (withTopRealPart f) y‖) (nhdsWithin x (dom f))
        Filter.atTop
  gradient_norm_tendsto_atTop_along_ray :
    ∀ ⦃x d : E⦄, x ∈ dom f → d ≠ 0 →
      (∀ τ : ℝ, 0 ≤ τ → x + τ • d ∈ dom f) →
        Filter.Tendsto
          (fun τ : ℝ ↦ ‖∇ (withTopRealPart f) (x + τ • d)‖)
          Filter.atTop
          Filter.atTop

/-- The Legendre-type hypothesis implies injectivity of the gradient map on `dom f`. -/
theorem IsLegendreType.gradient_injOn
    (hleg : IsLegendreType f) :
    Set.InjOn (∇ (withTopRealPart f)) (dom f) :=
  hleg.gradient_inj

/-- Along every nontrivial forward ray contained in `dom f`, the Legendre-type gradient norm
tends to `+∞`. -/
theorem IsLegendreType.gradient_norm_tendsto_atTop_of_ray
    (hleg : IsLegendreType f) {x d : E}
    (hx : x ∈ dom f) (hd : d ≠ 0)
    (hray : ∀ τ : ℝ, 0 ≤ τ → x + τ • d ∈ dom f) :
    Filter.Tendsto
      (fun τ : ℝ ↦ ‖∇ (withTopRealPart f) (x + τ • d)‖)
      Filter.atTop
      Filter.atTop :=
  hleg.gradient_norm_tendsto_atTop_along_ray hx hd hray

/-- Lemma 5.1.6 (1): if `f : E → ℝ ∪ {+∞}` is a closed proper convex function on a
finite-dimensional real inner-product space, differentiable on its open effective domain, and of
Legendre type, then the Fenchel dual has a closed convex effective epigraph. -/
theorem fenchelDual_effectiveEpigraph_closed_convex_of_legendre
    (hf : ClosedConvexFunction f)
    (hdom : (dom f).Nonempty)
    (hdom_open : IsOpen (dom f))
    (hdiff : DifferentiableOn ℝ (withTopRealPart f) (dom f))
    (hleg : IsLegendreType f) :
    IsClosed (effectiveEpigraph (f⋆)) ∧
      Convex ℝ (effectiveEpigraph (f⋆)) := by
  -- The Chapter 6 Fenchel-dual epigraph theorem already packages the closed-convex conclusion.
  simpa using fenchelDual_effectiveEpigraph_closed_convex (f := f)

/-- Core source-facing package for Lemma 5.1.6. -/
theorem dom_fenchelDual_eq_image_gradient_and_isOpen_of_legendre_core
    (hf : ClosedConvexFunction f)
    (hdom : (dom f).Nonempty)
    (hdom_open : IsOpen (dom f))
    (hdiff : DifferentiableOn ℝ (withTopRealPart f) (dom f))
    (hleg : IsLegendreType f) :
    dom (f⋆) = ∇ (withTopRealPart f) '' dom f ∧ IsOpen (dom (f⋆)) := by
  -- TODO Lemma 5.1.6: this source-facing Legendre branch still needs the global gradient-image
  -- argument proving both surjectivity onto `dom (f⋆)` and openness of that image from the local
  -- `IsLegendreType` hypotheses.
  sorry

/-- Lemma 5.1.6 (2): under the same hypotheses, the effective domain of the Fenchel dual is
nonempty and open. -/
theorem dom_fenchelDual_nonempty_and_isOpen_of_legendre
    (hf : ClosedConvexFunction f)
    (hdom : (dom f).Nonempty)
    (hdom_open : IsOpen (dom f))
    (hdiff : DifferentiableOn ℝ (withTopRealPart f) (dom f))
    (hleg : IsLegendreType f) :
    (dom (f⋆)).Nonempty ∧ IsOpen (dom (f⋆)) := by
  obtain ⟨heq, hopen⟩ :=
    dom_fenchelDual_eq_image_gradient_and_isOpen_of_legendre_core
      (f := f) hf hdom hdom_open hdiff hleg
  rcases hdom with ⟨x, hx⟩
  constructor
  · -- A primal domain point contributes its gradient to the dual domain through the image formula.
    rw [heq]
    exact ⟨∇ (withTopRealPart f) x, ⟨x, hx, rfl⟩⟩
  · exact hopen

/-- Lemma 5.1.6 (3): under the same hypotheses, the effective domain of the Fenchel dual is
exactly the gradient image of the primal effective domain. -/
theorem dom_fenchelDual_eq_image_gradient_of_legendre
    (hf : ClosedConvexFunction f)
    (hdom : (dom f).Nonempty)
    (hdom_open : IsOpen (dom f))
    (hdiff : DifferentiableOn ℝ (withTopRealPart f) (dom f))
    (hleg : IsLegendreType f) :
    dom (f⋆) = ∇ (withTopRealPart f) '' dom f := by
  -- The equality component is the first projection of the Legendre core package.
  exact
    (dom_fenchelDual_eq_image_gradient_and_isOpen_of_legendre_core
      (f := f) hf hdom hdom_open hdiff hleg).1

end SourceFacing

section SelfConcordantCompatibility

variable {f : E → WithTop ℝ}

/-- Helper for Lemma 5.1.6: the normalized affine tilt by a fixed slope preserves
self-concordance on the primal effective domain. -/
lemma affineTilt_isSelfConcordantOnWith
    {Mf : NNReal} (hself : IsSelfConcordantOnWith (dom f) Mf (withTopRealPart f))
    (s : E) :
    IsSelfConcordantOnWith (dom f) Mf
      (quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E) + withTopRealPart f) := by
  -- Apply the Chapter 5 quadratic-affine perturbation corollary with the zero Hessian operator.
  simpa [quadraticAffineObjective_zero_operator, add_comm, add_left_comm, add_assoc] using
    hself.add_quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E)
      ContinuousLinearMap.isPositive_zero

/-- Helper for Lemma 5.1.6: every self-concordant witness can be enlarged to a strictly positive
constant without losing self-concordance. -/
private theorem existsPositiveSelfConcordantConstant
    {Q : Set E} {g : E → ℝ} {Mf0 : NNReal}
    (h0 : IsSelfConcordantOnWith Q Mf0 g) :
    ∃ Mf : NNReal, 0 < (Mf : ℝ) ∧ IsSelfConcordantOnWith Q Mf g := by
  -- Increase the witness by `1` so the inverse Dikin radius is strictly positive.
  refine ⟨Mf0 + 1, ?_, ?_⟩
  · exact_mod_cast show (0 : NNReal) < Mf0 + 1 by simp
  · exact h0.of_le (by simp)

/-- Helper for Lemma 5.1.6: a qualitative self-concordance witness can be repackaged with a
strictly positive unit constant. -/
private theorem existsPositiveUnitSelfConcordantConstant
    {Q : Set E} {g : E → ℝ} {Mf0 : NNReal}
    (h0 : IsSelfConcordantOnWith Q Mf0 g) :
    ∃ Mf : NNRealˣ, IsSelfConcordantOnWith Q (Mf : NNReal) g := by
  -- First enlarge the witness to a positive `NNReal`, then package it as a unit.
  obtain ⟨Mf, hMf_pos, hMf⟩ := existsPositiveSelfConcordantConstant h0
  refine ⟨Units.mk0 Mf (ne_of_gt hMf_pos), ?_⟩
  simpa using hMf

/-- Helper for Lemma 5.1.6: vanishing Hessian quadratic form along `h` forces every point on the
affine line `x + τ • h` into the open Dikin ellipsoid centered at `x`. -/
private theorem linePoint_mem_openDikinEllipsoid_of_zeroQuadraticForm
    {g : E → ℝ} {Mf : NNReal} {x h : E}
    (hq : inner ℝ h (hessian g x h) = 0) (hMf_pos : 0 < (Mf : ℝ)) :
    ∀ τ : ℝ, x + τ • h ∈ openDikinEllipsoid g x (1 / (Mf : ℝ)) := by
  intro τ
  -- Rewriting the displacement as `τ • h` collapses the quadratic form to `0`.
  have hquad :
      inner ℝ ((x + τ • h) - x) (hessian g x ((x + τ • h) - x)) = 0 := by
    simp [inner_smul_left, inner_smul_right, hq]
  have hquad_nonneg :
      0 ≤ inner ℝ ((x + τ • h) - x) (hessian g x ((x + τ • h) - x)) := by
    rw [hquad]
  refine
    (mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq g x (x + τ • h) hquad_nonneg
      (le_of_lt (one_div_pos.mpr hMf_pos))).2 ?_
  rw [hquad]
  positivity

/-- Helper for Lemma 5.1.6: a vanishing Hessian quadratic form along `h` should force the whole
affine line `x + τ • h` to stay inside `dom f`. -/
-- TODO Lemma 5.1.6: the available admissible-step theorem
-- `openDikinEllipsoid_inv_constant_subset` still requires
-- `[HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f)]`, so closing this bridge without
-- circularity needs an earlier theorem that derives domain membership from self-concordance alone
-- along zero-curvature directions.
lemma affineLine_mem_dom_of_zeroQuadraticForm
    {Mf : NNReal}
    (hself : IsSelfConcordantOnWith (dom f) Mf (withTopRealPart f))
    (hMf_pos : 0 < (Mf : ℝ)) {x h : E} (hx : x ∈ dom f)
    (hq : inner ℝ h (hessian (withTopRealPart f) x h) = 0) :
    ∀ τ : ℝ, x + τ • h ∈ dom f := sorry

/-- Helper for Lemma 5.1.6: once `HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f)` is
available, a zero Hessian quadratic form along `h` forces the whole affine line through `x` to
stay inside `dom f`. -/
private theorem affineLine_mem_dom_of_zeroQuadraticForm_of_posdef
    {Mf : NNRealˣ}
    [HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f)]
    (hself : IsSelfConcordantOnWith (dom f) (Mf : NNReal) (withTopRealPart f))
    {x h : E} (hx : x ∈ dom f)
    (hq : inner ℝ h (hessian (withTopRealPart f) x h) = 0) :
    ∀ τ : ℝ, x + τ • h ∈ dom f := by
  intro τ
  have hMf_pos : 0 < ((Mf : NNReal) : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  -- First place the affine-line point in the inverse-radius Dikin ellipsoid around `x`.
  have hτ_mem :
      x + τ • h ∈ openDikinEllipsoid (withTopRealPart f) x (1 / ((Mf : NNReal) : ℝ)) :=
    linePoint_mem_openDikinEllipsoid_of_zeroQuadraticForm
      (g := withTopRealPart f) hq hMf_pos τ
  -- The Chapter 5 admissible-step theorem then returns that ellipsoid point to `dom f`.
  exact hself.openDikinEllipsoid_inv_constant_subset hx hτ_mem

/-- Helper for Lemma 5.1.6: the self-concordant Chapter 5 standing assumptions should upgrade the
primal Hessian to a positive-definite owner on `dom f`. -/
lemma selfConcordantHasPositiveDefiniteHessianOn_of_noAffineLine
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f) :
    HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f) := by
  let _ := hclosed
  rcases hself with ⟨Mf0, hMf0⟩
  obtain ⟨Mf, hMf_pos, hMf⟩ := existsPositiveSelfConcordantConstant hMf0
  refine ⟨?_, ?_⟩
  · intro x hx
    -- The quantitative self-concordance witness already carries pointwise Hessian positivity.
    exact hMf.hessian_isPositive hx
  · intro x hx h hh
    -- Route correction: use the Dikin inclusion theorem directly to turn a vanishing Hessian
    -- quadratic form into an affine line inside `dom f`.
    by_contra hnotlt
    have hnonneg :
        0 ≤ inner ℝ h (hessian (withTopRealPart f) x h) :=
      hMf.hessian_posSemidef hx h
    have hq :
        inner ℝ h (hessian (withTopRealPart f) x h) = 0 :=
      le_antisymm (not_lt.mp hnotlt) hnonneg
    have hline : ∀ τ : ℝ, x + τ • h ∈ dom f :=
      affineLine_mem_dom_of_zeroQuadraticForm (f := f) hMf hMf_pos hx hq
    exact (hnoAffineLine hh) hline

/-- Helper for Lemma 5.1.6: once the primal Hessian is known to be positive definite on `dom f`,
the inverse-function theorem makes the primal gradient image a neighborhood of each gradient
value. -/
theorem gradientImage_mem_nhds_of_selfConcordant_of_posdef
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    [HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f)]
    {x : E} (hx : x ∈ dom f) :
    ∇ (withTopRealPart f) '' dom f ∈ nhds (∇ (withTopRealPart f) x) := by
  rcases hself with ⟨Mf, hMf⟩
  let G : E → E := ∇ (withTopRealPart f)
  let s : E := G x
  let H : E →L[ℝ] E := hessian (withTopRealPart f) x
  have hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (dom f) := by
    -- The inverse-function theorem only needs the `C²` regularity already included in
    -- self-concordance.
    exact hMf.contDiffOn.of_le (by norm_num)
  have hHinjt : Function.Injective ⇑H := by
    intro u v huv
    by_contra huv_ne
    have hdiff_ne : u - v ≠ 0 := sub_ne_zero.mpr huv_ne
    have hpos : 0 < inner ℝ (u - v) (H (u - v)) :=
      HasPositiveDefiniteHessianOn.posdef hx hdiff_ne
    have hzero : H (u - v) = 0 := by
      simp [H, map_sub, huv]
    simpa [hzero] using hpos
  have hker : H.ker = ⊥ := by
    exact LinearMap.ker_eq_bot.mpr (by simpa using hHinjt)
  have hrange : H.range = ⊤ := by
    exact LinearMap.range_eq_top.2 <|
      LinearMap.surjective_of_injective (f := H.toLinearMap) (by simpa using hHinjt)
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective H hker hrange
  have hgrad_C1 : ContDiffAt ℝ 1 G x := by
    let D : StrongDual ℝ E →L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hfderiv_C1 : ContDiffAt ℝ 1 (fderiv ℝ (withTopRealPart f)) x := by
      -- Restrict the primal `C²` owner to the base point before differentiating once.
      exact
        (hf_contDiff.contDiffAt (hMf.isOpen_domain.mem_nhds hx)).fderiv_right
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    -- Rewrite the gradient through the Riesz map so the remaining regularity becomes `C¹`.
    simpa [G, gradient, D] using D.contDiff.contDiffAt.comp x hfderiv_C1
  have hgrad_fderiv : HasFDerivAt G H x := by
    let D : StrongDual ℝ E →L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hfderiv :
        DifferentiableAt ℝ (fderiv ℝ (withTopRealPart f)) x := by
      have hcont : ContDiffAt ℝ 1 (fderiv ℝ (withTopRealPart f)) x := by
        -- The same `C²` restriction makes the Fréchet derivative differentiable at `x`.
        exact
          (hf_contDiff.contDiffAt (hMf.isOpen_domain.mem_nhds hx)).fderiv_right
            (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
      exact hcont.differentiableAt one_ne_zero
    have hgrad : DifferentiableAt ℝ G x := by
      -- Differentiate the gradient by composing the derivative field with the Riesz map.
      simpa [G, gradient, D] using D.differentiableAt.comp x hfderiv
    simpa [G, H, hessian] using hgrad.hasFDerivAt
  have hgrad_fderiv_e : HasFDerivAt G (e : E →L[ℝ] E) x := by
    -- The chosen linear equivalence is exactly the Hessian map at the base point.
    simpa [e, H] using hgrad_fderiv
  have hstrict : HasStrictFDerivAt G (e : E →L[ℝ] E) x := by
    -- Upgrade the `C¹` gradient derivative to the strict derivative used by the inverse API.
    exact hgrad_C1.hasStrictFDerivAt' hgrad_fderiv_e one_ne_zero
  let ψ : E → E := hstrict.localInverse G e x
  have hψ_tendsto : Filter.Tendsto ψ (nhds s) (nhds x) := by
    -- The local inverse returns to the primal point at the base dual slope.
    simpa [ψ, G, s] using hstrict.localInverse_tendsto (f := G) (f' := e) (a := x)
  have hψ_mem : ∀ᶠ t in nhds s, ψ t ∈ dom f :=
    hψ_tendsto (hMf.isOpen_domain.mem_nhds hx)
  have hψ_right_inverse : ∀ᶠ t in nhds s, G (ψ t) = t := by
    -- Near `s`, the local inverse is a genuine right inverse of the primal gradient map.
    simpa [ψ, G, s] using hstrict.eventually_right_inverse (f := G) (f' := e) (a := x)
  -- A neighborhood on which the local inverse lands back in `dom f` is already contained in the
  -- primal gradient image.
  filter_upwards [hψ_mem, hψ_right_inverse] with t htDom htEq
  exact ⟨ψ t, htDom, by simpa [G] using htEq⟩

/-- Under the Chapter 5 self-concordant standing assumptions, every finite dual point admits a
Fenchel-support maximizer on the primal effective domain. -/
theorem exists_fenchelSupport_isMaxOn_of_mem_dom_fenchelDual
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f)
    {s : E} (hs : s ∈ dom (f⋆)) :
    ∃ x, x ∈ dom f ∧
      IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x := by
  have hdom : (dom f).Nonempty :=
    dom_nonempty_of_mem_dom_fenchelDual (f := f) hs
  have hboundedBelow :
      BddBelow ((fun y : E ↦ withTopRealPart f y - inner ℝ s y) '' dom f) :=
    (mem_dom_fenchelDual_iff (f := f) hdom (s := s)).mp hs
  -- Route correction: the dual-domain input has now been reduced to the bounded-below affine tilt
  -- on a nonempty primal domain. The remaining gap is to upgrade this to bounded sublevels and
  -- then apply the Chapter 3 minimizer-existence theorem.
  -- TODO: show every constrained sublevel of the affine tilt is bounded using `hself` and
  -- `hnoAffineLine`, obtain a minimizer on `dom f`, and convert it back with
  -- `fenchelSupport_isMaxOn_iff_tiltedIsMinOn`.
  sorry

/-- Under the same self-concordant standing assumptions, every finite dual point belongs to the
primal gradient image. -/
theorem dom_fenchelDual_subset_image_gradient_of_selfConcordant
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f) :
    dom (f⋆) ⊆ ∇ (withTopRealPart f) '' dom f := by
  intro s hs
  rcases exists_fenchelSupport_isMaxOn_of_mem_dom_fenchelDual
      (f := f) hclosed hself hnoAffineLine hs with ⟨x, hx, hmax⟩
  -- Once a support maximizer exists, the self-concordant singleton-subdifferential bridge
  -- identifies its gradient with the dual slope.
  exact ⟨x, hx, gradient_eq_of_fenchelSupport_isMaxOn (f := f) hself hx hmax⟩

/-- Core compatibility package for the self-concordant Chapter 5 branch. -/
theorem dom_fenchelDual_eq_image_gradient_and_isOpen_of_selfConcordant_core
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f) :
    dom (f⋆) = ∇ (withTopRealPart f) '' dom f ∧ IsOpen (dom (f⋆)) := by
  -- Route correction: the core assembly only needs the positive-definite Hessian bridge once;
  -- after that, equality and openness follow from the existing inclusion and neighborhood lemmas.
  letI : HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f) :=
    selfConcordantHasPositiveDefiniteHessianOn_of_noAffineLine
      (f := f) hclosed hself hnoAffineLine
  have hsubset_left :
      dom (f⋆) ⊆ ∇ (withTopRealPart f) '' dom f :=
    dom_fenchelDual_subset_image_gradient_of_selfConcordant
      (f := f) hclosed hself hnoAffineLine
  have hsubset_right :
      ∇ (withTopRealPart f) '' dom f ⊆ dom (f⋆) :=
    image_gradient_subset_dom_fenchelDual_of_selfConcordant (f := f) hself
  have heq :
      dom (f⋆) = ∇ (withTopRealPart f) '' dom f :=
    Set.Subset.antisymm hsubset_left hsubset_right
  have himage_open :
      IsOpen (∇ (withTopRealPart f) '' dom f) := by
    -- Each gradient value has an image-neighborhood inside the gradient image.
    rw [isOpen_iff_mem_nhds]
    intro s hs
    rcases hs with ⟨x, hx, rfl⟩
    exact gradientImage_mem_nhds_of_selfConcordant_of_posdef (f := f) hself hx
  constructor
  · exact heq
  · -- Rewrite the target openness statement through the established image description.
    simpa [heq] using himage_open

/-- In the finite-dimensional self-concordant Chapter 5 setting, the Fenchel dual has a closed
convex effective epigraph. -/
theorem fenchelDual_effectiveEpigraph_closed_convex_of_selfConcordant
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f)
    (hdom : (dom f).Nonempty) :
    IsClosed (effectiveEpigraph (f⋆)) ∧
      Convex ℝ (effectiveEpigraph (f⋆)) := by
  -- The effective epigraph conclusion is already available from the chapter Fenchel-dual API.
  simpa using fenchelDual_effectiveEpigraph_closed_convex (f := f)

/-- In the same self-concordant setting, a nonempty primal effective domain yields a nonempty open
dual effective domain. -/
theorem dom_fenchelDual_nonempty_and_isOpen_of_selfConcordant
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f)
    (hdom : (dom f).Nonempty) :
    (dom (f⋆)).Nonempty ∧ IsOpen (dom (f⋆)) := by
  obtain ⟨heq, hopen⟩ :=
    dom_fenchelDual_eq_image_gradient_and_isOpen_of_selfConcordant_core
      (f := f) hclosed hself hnoAffineLine
  rcases hdom with ⟨x, hx⟩
  constructor
  · -- A primal domain point contributes its gradient to the dual domain through the image formula.
    rw [heq]
    exact ⟨∇ (withTopRealPart f) x, ⟨x, hx, rfl⟩⟩
  · exact hopen

/-- Compatibility corollary: under the self-concordant standing assumptions of Section 5.1.5,
the effective domain of the Fenchel dual is exactly the gradient image of the primal effective
domain. -/
theorem dom_fenchelDual_eq_image_gradient_of_selfConcordant
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f) :
    dom (f⋆) = ∇ (withTopRealPart f) '' dom f := by
  -- The equality component is the first projection of the self-concordant core package.
  exact
    (dom_fenchelDual_eq_image_gradient_and_isOpen_of_selfConcordant_core
      (f := f) hclosed hself hnoAffineLine).1

/-- Compatibility corollary: under the self-concordant standing assumptions of Section 5.1.5,
the effective domain of the Fenchel dual is open. -/
theorem isOpen_dom_fenchelDual_of_selfConcordant
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f) :
    IsOpen (dom (f⋆)) := by
  -- Openness is the second projection of the self-concordant core package.
  exact
    (dom_fenchelDual_eq_image_gradient_and_isOpen_of_selfConcordant_core
      (f := f) hclosed hself hnoAffineLine).2

/-- Compatibility corollary: under the self-concordant standing assumptions of Section 5.1.5,
a nonempty primal effective domain forces the effective domain of the Fenchel dual to be
nonempty. -/
theorem dom_fenchelDual_nonempty_of_selfConcordant
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f)
    (hdom : (dom f).Nonempty) :
    (dom (f⋆)).Nonempty := by
  -- Nonemptiness is the first projection of the already-packaged dual-domain corollary.
  exact
    (dom_fenchelDual_nonempty_and_isOpen_of_selfConcordant
      (f := f) hclosed hself hnoAffineLine hdom).1

/-- Compatibility corollary: under the self-concordant standing assumptions of Section 5.1.5,
the effective epigraph of the Fenchel dual is closed. -/
theorem isClosed_effectiveEpigraph_fenchelDual_of_selfConcordant
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f) :
    IsClosed (effectiveEpigraph (f⋆)) := by
  -- Closedness is already packaged by the chapter Fenchel-dual epigraph theorem.
  exact (fenchelDual_effectiveEpigraph_closed_convex (f := f)).1

/-- Compatibility corollary: under the self-concordant standing assumptions of Section 5.1.5,
the effective epigraph of the Fenchel dual is convex. -/
theorem convex_effectiveEpigraph_fenchelDual_of_selfConcordant
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f) :
    Convex ℝ (effectiveEpigraph (f⋆)) := by
  -- Convexity is already packaged by the chapter Fenchel-dual epigraph theorem.
  exact (fenchelDual_effectiveEpigraph_closed_convex (f := f)).2

/-- Compatibility corollary: in the finite-dimensional self-concordant Chapter 5 setting, a
nonempty primal effective domain yields the gradient-image description of the dual effective
domain. -/
theorem dom_fenchelDual_eq_image_gradient_of_selfConcordant_of_nonempty
    (hclosed :
      IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
    (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f)
    (hdom : (dom f).Nonempty) :
    dom (f⋆) = ∇ (withTopRealPart f) '' dom f := by
  -- The nonempty-domain variant is a direct wrapper around the same equality theorem.
  exact dom_fenchelDual_eq_image_gradient_of_selfConcordant (f := f) hclosed hself hnoAffineLine

end SelfConcordantCompatibility

end
