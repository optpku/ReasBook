/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open Topology
open scoped Gradient DikinEllipsoidNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- This file needs a compatibility owner bundling the Chapter 5 self-concordant barrier structure
on `interior Q` with the Chapter 1 barrier owner for the canonical restriction map and an explicit
nonvacuous-boundary witness. Semantic search found no existing combined owner in mathlib/local
API, so this file uses a thin local owner for the textbook notion of a genuine barrier on `Q`. -/

/-- The frontier-growth condition needed to interpret `F` as a genuine barrier on `Q`: along any
sequence in `interior Q` converging to a boundary point of `Q`, the function values tend to
`+∞`. This is stated explicitly because `IsSelfConcordantBarrierOnWith` currently records only
self-concordance together with the barrier-parameter inequality, not divergence at frontier
points. -/
def HasBarrierBoundaryGrowthOn (dom : Set E) (F : E → ℝ) : Prop :=
  ∀ (x : ℕ → interior dom) {xBar : E},
    Tendsto (fun n : ℕ ↦ (x n : E)) atTop (𝓝 xBar) →
    xBar ∈ frontier dom →
    Tendsto (fun n : ℕ ↦ F (x n)) atTop atTop

/-- The intrinsic continuous-map restriction of an ambient self-concordant barrier candidate to
`interior Q`. -/
def selfConcordantBarrierRestriction
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F) :
    C(interior Q, ℝ) where
  toFun x := F x
  continuous_toFun := by
    let hstd : IsStandardSelfConcordantOn (interior Q) F := hF.toIsStandardSelfConcordantOn
    exact ContinuousOn.comp_continuous hstd.contDiffOn.continuousOn continuous_subtype_val
      (fun x ↦ x.property)

/-- A compatibility owner for a genuine `ν`-self-concordant barrier on `Q`: it bundles the
Chapter 5 owner on `interior Q` with the Chapter 1 barrier owner for the canonical restriction to
`Q`, together with an explicit frontier witness so the boundary-growth clause is nonvacuous. This
is the local source-facing predicate used for Theorem 5.4.1.1. -/
class IsSelfConcordantBarrierForWith (Q : Set E) (ν : NNReal) (F : E → ℝ) : Prop
    extends IsSelfConcordantBarrierOnWith (interior Q) ν F where
  toIsBarrierFunctionOn :
      IsBarrierFunctionOn Q
        (selfConcordantBarrierRestriction toIsSelfConcordantBarrierOnWith)
  frontier_nonempty : (frontier Q).Nonempty

/-- The strengthened compatibility owner canonically supplies the Chapter 5 owner on
`interior Q`. -/
instance instIsSelfConcordantBarrierOnWithOfIsSelfConcordantBarrierForWith
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    [hF : IsSelfConcordantBarrierForWith Q ν F] :
    IsSelfConcordantBarrierOnWith (interior Q) ν F :=
  hF.toIsSelfConcordantBarrierOnWith

namespace IsSelfConcordantBarrierForWith

/-- The strengthened bundled barrier hypothesis on `Q` has nonempty interior through its Chapter 1
barrier-function companion. -/
theorem interior_nonempty
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierForWith Q ν F) :
    (interior Q).Nonempty :=
  hF.toIsBarrierFunctionOn.interior_nonempty

/-- The strengthened bundled barrier hypothesis on `Q` has the explicit boundary-growth property
needed by the scalar reduction arguments in Chapter 5. -/
theorem hasBarrierBoundaryGrowthOn
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierForWith Q ν F) :
    HasBarrierBoundaryGrowthOn Q F := by
  intro x xBar hx hxBar
  simpa [selfConcordantBarrierRestriction] using
    hF.toIsBarrierFunctionOn.tendsTo_atTop_of_tendsto_frontier x hx hxBar

/-- The strengthened bundled barrier hypothesis on `Q` has a nonempty frontier, so its Chapter 1
boundary-growth condition is not vacuous. -/
theorem frontier_nonempty_of_barrier
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierForWith Q ν F) :
    (frontier Q).Nonempty :=
  hF.frontier_nonempty

end IsSelfConcordantBarrierForWith

section

variable {α : WithBot ℝ} {β : ℝ}

/-- Helper for Theorem 5.4.1.1: the scalar open interval `(\alpha, \beta)` used in the scalar
reduction. The lower endpoint is allowed to be `-∞`, matching the source half-line variants. -/
abbrev scalarBarrierInterval (α : WithBot ℝ) (β : ℝ) : Set ℝ :=
  {t : ℝ | α < (t : WithBot ℝ) ∧ t < β}

/-- Helper for Theorem 5.4.1.1: at a scalar point, the Hessian quadratic form in direction `1`
recovers the usual second derivative. -/
private theorem scalar_hessian_quadratic_form_one_eq_secondDeriv
    {f : ℝ → ℝ} {t : ℝ} :
    inner ℝ (1 : ℝ) (hessian f t 1) = iteratedDeriv 2 f t := by
  have hgrad_eq : (∇ f) = deriv f := by
    funext x
    simp [gradient_eq_deriv']
  calc
    inner ℝ (1 : ℝ) (hessian f t 1) = inner ℝ (1 : ℝ) (deriv (∇ f) t) := by
      rw [hessian, fderiv_apply_one_eq_deriv]
    _ = deriv (∇ f) t := by
      calc
        inner ℝ (1 : ℝ) (deriv (∇ f) t) = inner ℝ (deriv (∇ f) t) 1 := by
          rw [real_inner_comm]
        _ = deriv (∇ f) t := by
          convert (RCLike.inner_apply (deriv (∇ f) t) (1 : ℝ)) using 1
          simp
    _ = iteratedDeriv 2 f t := by
      rw [hgrad_eq]
      simp [iteratedDeriv_succ]

/-- Helper for Theorem 5.4.1.1: on the scalar line, the Hessian quadratic form in direction `u`
is `u²` times the usual second derivative. -/
private theorem scalar_hessian_quadratic_form_eq_sq_mul_secondDeriv
    {f : ℝ → ℝ} {t u : ℝ} :
    inner ℝ u (hessian f t u) = u ^ (2 : ℕ) * iteratedDeriv 2 f t := by
  have hgrad_eq : (∇ f) = deriv f := by
    funext x
    simp [gradient_eq_deriv']
  calc
    inner ℝ u (hessian f t u) = inner ℝ u (deriv (∇ f) t * u) := by
      rw [hessian, fderiv_eq_deriv_mul]
    _ = u * (deriv (∇ f) t * u) := by
      simpa using (RCLike.inner_apply' u (deriv (∇ f) t * u))
    _ = deriv (∇ f) t * u ^ (2 : ℕ) := by
      ring
    _ = u ^ (2 : ℕ) * iteratedDeriv 2 f t := by
      rw [hgrad_eq]
      rw [show iteratedDeriv 2 f t = deriv (deriv f) t by simp [iteratedDeriv_succ]]
      ring

/-- Helper for Theorem 5.4.1.1: the unit-direction Chapter 5 third directional derivative is the
ordinary third derivative on `ℝ`. -/
private theorem scalar_thirdDirectionalDerivative_one_eq_iteratedDeriv_three
    {f : ℝ → ℝ} {t : ℝ} :
    thirdDirectionalDerivative f t 1 = iteratedDeriv 3 f t := by
  calc
    thirdDirectionalDerivative f t 1 = iteratedDeriv 3 (directionalSlice f t 1) 0 := by
      rfl
    _ = iteratedDeriv 3 (fun s : ℝ ↦ f (t + s)) 0 := by
      congr 1
      funext s
      simp [directionalSlice]
    _ = iteratedDeriv 3 f t := by
      simpa using congrArg (fun g : ℝ → ℝ ↦ g 0) (iteratedDeriv_comp_const_add 3 f t)

/-- Helper for Theorem 5.4.1.1: a scalar quadratic family bounded above by `ν` forces the
discriminant estimate `a² ≤ ν b`. -/
private theorem sq_le_mul_of_barrier_line_family
    {a b ν : ℝ} (hb : 0 ≤ b)
    (hline : ∀ s : ℝ, 2 * s * a - s ^ (2 : ℕ) * b ≤ ν) :
    a ^ (2 : ℕ) ≤ ν * b := by
  by_cases hb0 : b = 0
  · by_cases ha0 : a = 0
    · simp [ha0, hb0]
    · have htest := hline ((|ν| + 1) / a)
      have hineq : 2 * (|ν| + 1) ≤ ν := by
        have hcalc : 2 * ((|ν| + 1) / a) * a = 2 * (|ν| + 1) := by
          field_simp [ha0]
        calc
          2 * (|ν| + 1) = 2 * ((|ν| + 1) / a) * a := by simpa using hcalc.symm
          _ = 2 * ((|ν| + 1) / a) * a - (((|ν| + 1) / a) ^ (2 : ℕ) * b) := by simp [hb0]
          _ ≤ ν := htest
      exfalso
      have habs : ν ≤ |ν| := le_abs_self ν
      have hcontr : |ν| + 2 ≤ 0 := by
        linarith
      nlinarith [abs_nonneg ν, hcontr]
  · have hb_pos : 0 < b := by
      exact lt_of_le_of_ne hb (Ne.symm hb0)
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    have htest := hline (a / b)
    have hquot : a ^ (2 : ℕ) / b ≤ ν := by
      have hrewrite :
          2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
        field_simp [hb_ne]
        ring
      simpa [hrewrite] using htest
    exact (_root_.div_le_iff₀ hb_pos).1 hquot

-- Proof sketch: specialize the owner barrier inequality to scalar directions `s : ℝ`, rewrite
-- the gradient and Hessian terms using the scalar derivative bridges above, and optimize the
-- resulting quadratic family in `s`.
/-- Helper for Theorem 5.4.1.1: the canonical scalar specialization of the barrier-parameter
owner inequality gives `(f'(t))^2 ≤ ν f''(t)` on `(\alpha, \beta)`. -/
theorem selfConcordantBarrier_deriv_sq_le_parameter_mul_secondDeriv
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    deriv f t ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 f t := by
  have hstd := hself.toIsStandardSelfConcordantOn
  have hnonneg :
      0 ≤ iteratedDeriv 2 f t := by
    have hquad :
        0 ≤ inner ℝ (1 : ℝ) (hessian f t 1) :=
      hstd.hessian_posSemidef t.property 1
    rw [scalar_hessian_quadratic_form_one_eq_secondDeriv] at hquad
    exact hquad
  have hline :
      ∀ s : ℝ, 2 * s * deriv f t - s ^ (2 : ℕ) * iteratedDeriv 2 f t ≤ (ν : ℝ) := by
    intro s
    have hbound := hself.barrier_parameter_bound t.property s
    have hsgrad : inner ℝ (deriv f t) s = s * deriv f t := by
      rw [real_inner_comm]
      simpa using (RCLike.inner_apply' s (deriv f t))
    rw [gradient_eq_deriv', hsgrad, scalar_hessian_quadratic_form_eq_sq_mul_secondDeriv] at hbound
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, two_mul] using hbound
  simpa [mul_comm] using sq_le_mul_of_barrier_line_family hnonneg hline

-- Proof sketch: the barrier owner supplies the Chapter 1 frontier-blow-up theorem on `closure I`,
-- and `I` contains no affine line because of the finite upper endpoint `β`. Applying the chapter
-- no-affine-line positivity bridge to the scalar direction `1` yields `0 < f''(t)` at every
-- interior point.
/-- Helper for Theorem 5.4.1.1: on the scalar barrier interval `(\alpha, \beta)`, the second
derivative is strictly positive. -/
theorem selfConcordantBarrier_secondDeriv_pos
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    0 < iteratedDeriv 2 f t := by
  have hstd := hself.toIsStandardSelfConcordantOn
  have hnonneg :
      0 ≤ iteratedDeriv 2 f t := by
    have hquad :
        0 ≤ inner ℝ (1 : ℝ) (hessian f t 1) :=
      hstd.hessian_posSemidef t.property 1
    rw [scalar_hessian_quadratic_form_one_eq_secondDeriv] at hquad
    exact hquad
  by_contra hnotlt
  have hzero : iteratedDeriv 2 f t = 0 :=
    le_antisymm (not_lt.mp hnotlt) hnonneg
  let y : ℝ := β + 1
  have hquad_zero :
      inner ℝ (y - (t : ℝ)) (hessian f t (y - (t : ℝ))) = 0 := by
    rw [scalar_hessian_quadratic_form_eq_sq_mul_secondDeriv, hzero]
    ring
  have hy_mem : y ∈ openDikinEllipsoid f (t : ℝ) (1 / (1 : ℝ)) := by
    have hquad_nonneg :
        0 ≤ inner ℝ (y - (t : ℝ)) (hessian f t (y - (t : ℝ))) := by
      rw [hquad_zero]
    refine
      (mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq f (t : ℝ) y hquad_nonneg
        (by positivity : 0 ≤ (1 / (1 : ℝ)))).2 ?_
    rw [hquad_zero]
    norm_num
  have hy_dom : y ∈ scalarBarrierInterval α β :=
    IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset
      (domain := scalarBarrierInterval α β) (f := f) (Mf := 1) hstd t.property hy_mem
  have : ¬ y < β := by
    dsimp [y]
    linarith
  exact this hy_dom.2

/-- Helper for Theorem 5.4.1.1: the source-facing scalar barrier ratio at `t`, expressed through
the canonical positive second-derivative theorem supplied by the barrier owner. -/
def selfConcordantBarrierRatio
    (α : WithBot ℝ) (β : ℝ) (f : ℝ → ℝ) (t : scalarBarrierInterval α β) : ℝ :=
  deriv f t ^ (2 : ℕ) / iteratedDeriv 2 f t

/-- Helper for Theorem 5.4.1.1: expanding the scalar barrier ratio recovers the textbook formula
`(f'(t))^2 / f''(t)`. -/
@[simp] theorem selfConcordantBarrierRatio_def
    (f : ℝ → ℝ) (t : scalarBarrierInterval α β) :
    selfConcordantBarrierRatio α β f t =
      deriv f t ^ (2 : ℕ) / iteratedDeriv 2 f t :=
  rfl

/-- Helper for Theorem 5.4.1.1: the scalar barrier ratio supremum
`κ = sup_{t ∈ (\alpha, \beta)} (f'(t))^2 / f''(t)`. -/
def selfConcordantBarrierKappa
    (α : WithBot ℝ) (β : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup (Set.range (selfConcordantBarrierRatio α β f))

/-- Helper for Theorem 5.4.1.1: the scalar frontier-growth condition needed to interpret `f` as a
genuine barrier on `(\alpha, \beta)`. -/
def HasBarrierBoundaryGrowthOnScalarInterval
    (α : WithBot ℝ) (β : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (x : ℕ → scalarBarrierInterval α β) {xBar : ℝ},
    Tendsto (fun n : ℕ ↦ (x n : ℝ)) atTop (𝓝 xBar) →
    xBar ∈ frontier (scalarBarrierInterval α β) →
    Tendsto (fun n : ℕ ↦ f (x n)) atTop atTop

/-- Helper for Theorem 5.4.1.1: unfolding the scalar frontier-growth predicate gives the
boundary-divergence criterion used in the scalar reduction. -/
@[simp] theorem hasBarrierBoundaryGrowthOnScalarInterval_iff
    (f : ℝ → ℝ) :
    HasBarrierBoundaryGrowthOnScalarInterval α β f ↔
      ∀ (x : ℕ → scalarBarrierInterval α β) {xBar : ℝ},
        Tendsto (fun n : ℕ ↦ (x n : ℝ)) atTop (𝓝 xBar) →
        xBar ∈ frontier (scalarBarrierInterval α β) →
        Tendsto (fun n : ℕ ↦ f (x n)) atTop atTop :=
  Iff.rfl

/-- Helper for Theorem 5.4.1.1: the source-facing scalar `ν`-self-concordant barrier owner on
`(\alpha, \beta)` is the Chapter 5 owner together with the missing boundary-divergence field. -/
class IsSelfConcordantBarrierOnScalarIntervalWith
    (α : WithBot ℝ) (β : ℝ) (ν : NNReal) (f : ℝ → ℝ) : Prop
    extends IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f where
  boundary_growth : HasBarrierBoundaryGrowthOnScalarInterval α β f

/-- Helper for Theorem 5.4.1.1: a scalar source-facing barrier canonically supplies the Chapter 5
barrier owner on the same interval. -/
instance instIsSelfConcordantBarrierOnWithOfScalarIntervalBarrier
    {ν : NNReal} {f : ℝ → ℝ}
    [hbarrier : IsSelfConcordantBarrierOnScalarIntervalWith α β ν f] :
    IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f :=
  hbarrier.toIsSelfConcordantBarrierOnWith

namespace IsSelfConcordantBarrierOnScalarIntervalWith

/-- Helper for Theorem 5.4.1.1: project the frontier-divergence part of the source-facing scalar
barrier owner. -/
theorem hasBarrierBoundaryGrowthOnScalarInterval
    {ν : NNReal} {f : ℝ → ℝ}
    (hbarrier : IsSelfConcordantBarrierOnScalarIntervalWith α β ν f) :
    HasBarrierBoundaryGrowthOnScalarInterval α β f :=
  hbarrier.boundary_growth

end IsSelfConcordantBarrierOnScalarIntervalWith

/-- Helper for Theorem 5.4.1.1: every scalar barrier ratio value is bounded above by the barrier
parameter. -/
theorem selfConcordantBarrierRatio_le_parameter
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    selfConcordantBarrierRatio α β f t ≤ (ν : ℝ) := by
  have hpos : 0 < iteratedDeriv 2 f t :=
    selfConcordantBarrier_secondDeriv_pos hself t
  have hbound :
      deriv f t ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 f t :=
    selfConcordantBarrier_deriv_sq_le_parameter_mul_secondDeriv hself t
  exact (_root_.div_le_iff₀ hpos).2 (by simpa [selfConcordantBarrierRatio])

/-- Helper for Theorem 5.4.1.1: for a scalar `ν`-self-concordant barrier on `(\alpha, \beta)`,
the source-facing ratio supremum `κ` is bounded above by the barrier parameter. -/
theorem selfConcordantBarrierKappa_le_parameter
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f) :
    selfConcordantBarrierKappa α β f ≤ (ν : ℝ) := by
  by_cases hI : Set.Nonempty (scalarBarrierInterval α β)
  · have hrange_nonempty :
        (Set.range (selfConcordantBarrierRatio α β f)).Nonempty := by
      rcases hI with ⟨t, ht⟩
      refine ⟨selfConcordantBarrierRatio α β f ⟨t, ht⟩, ?_⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    refine csSup_le hrange_nonempty ?_
    rintro y ⟨t, rfl⟩
    exact selfConcordantBarrierRatio_le_parameter hself t
  · have hrange_empty : Set.range (selfConcordantBarrierRatio α β f) = ∅ := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact hI ⟨t.1, t.2⟩
      · intro hy
        cases hy
    rw [selfConcordantBarrierKappa, hrange_empty]
    have hν_nonneg : (0 : ℝ) ≤ (ν : ℝ) := by positivity
    simp [hν_nonneg]

/-- Helper for Theorem 5.4.1.1: the reciprocal local norm in the unit direction is bounded by the
distance to the finite right endpoint. -/
theorem scalar_reciprocal_localNorm_le_right_gap
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    1 / Real.sqrt (iteratedDeriv 2 f t) ≤ β - t := by
  have hstd := hself.toIsStandardSelfConcordantOn
  have hsecond_pos : 0 < iteratedDeriv 2 f t :=
    selfConcordantBarrier_secondDeriv_pos hself t
  have hgap_pos : 0 < β - (t : ℝ) := sub_pos.mpr t.property.2
  have hsqrt_pos : 0 < Real.sqrt (iteratedDeriv 2 f t) :=
    Real.sqrt_pos.mpr hsecond_pos
  have hr_pos : 0 < 1 / Real.sqrt (iteratedDeriv 2 f t) :=
    one_div_pos.mpr hsqrt_pos
  by_contra hgap
  let δ : ℝ := ((β - (t : ℝ)) + 1 / Real.sqrt (iteratedDeriv 2 f t)) / 2
  have hgap_lt_r : β - (t : ℝ) < 1 / Real.sqrt (iteratedDeriv 2 f t) :=
    lt_of_not_ge hgap
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hδ_lt_r : δ < 1 / Real.sqrt (iteratedDeriv 2 f t) := by
    dsimp [δ]
    linarith
  have hβ_lt : β < (t : ℝ) + δ := by
    dsimp [δ]
    linarith
  let y : ℝ := (t : ℝ) + δ
  have hquad_nonneg :
      0 ≤ inner ℝ (y - (t : ℝ)) (hessian f t (y - (t : ℝ))) := by
    rw [show y - (t : ℝ) = δ by simp [y]]
    rw [scalar_hessian_quadratic_form_eq_sq_mul_secondDeriv]
    positivity
  have hy_mem : y ∈ openDikinEllipsoid f (t : ℝ) (1 / (1 : ℝ)) := by
    refine
      (mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq f (t : ℝ) y hquad_nonneg
        (by positivity : 0 ≤ (1 / (1 : ℝ)))).2 ?_
    rw [show y - (t : ℝ) = δ by simp [y]]
    rw [scalar_hessian_quadratic_form_eq_sq_mul_secondDeriv]
    have hpow :
        δ ^ (2 : ℕ) < (1 / Real.sqrt (iteratedDeriv 2 f t)) ^ (2 : ℕ) := by
      nlinarith
    have hpow' :
        δ ^ (2 : ℕ) < 1 / iteratedDeriv 2 f t := by
      simpa [one_div, Real.sq_sqrt hsecond_pos.le] using hpow
    have hlt_one : δ ^ (2 : ℕ) * iteratedDeriv 2 f t < 1 :=
      (_root_.lt_div_iff₀ hsecond_pos).1 hpow'
    simpa using hlt_one
  have hy_dom : y ∈ scalarBarrierInterval α β :=
    IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset
      (domain := scalarBarrierInterval α β) (f := f) (Mf := 1) hstd t.property hy_mem
  have : ¬ y < β := by
    linarith
  exact this hy_dom.2

/-- Helper for Theorem 5.4.1.1: the finite right endpoint `β` lies on the frontier of the scalar
barrier interval whenever the interval is nonempty. -/
private theorem scalarBarrierInterval_right_endpoint_mem_frontier
    (hI : Set.Nonempty (scalarBarrierInterval α β)) :
    β ∈ frontier (scalarBarrierInterval α β) := by
  rcases hI with ⟨x0, hx0⟩
  have hx0_lt : x0 < β := hx0.2
  have hclosure : β ∈ closure (scalarBarrierInterval α β) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨β - min (ε / 2) ((β - x0) / 2), ?_, ?_⟩
    · constructor
      · have hmin_le : min (ε / 2) ((β - x0) / 2) ≤ (β - x0) / 2 := min_le_right _ _
        have hsub_lt : (β - x0) / 2 < β - x0 := by linarith
        have hlt : min (ε / 2) ((β - x0) / 2) < β - x0 := lt_of_le_of_lt hmin_le hsub_lt
        have hx0_lt_y : x0 < β - min (ε / 2) ((β - x0) / 2) := by
          linarith
        exact lt_trans hx0.1 (by exact_mod_cast hx0_lt_y)
      · have hmin_pos : 0 < min (ε / 2) ((β - x0) / 2) := by
          refine lt_min ?_ ?_
          · positivity
          · linarith
        linarith
    · rw [Real.dist_eq]
      have hmin_nonneg : 0 ≤ min (ε / 2) ((β - x0) / 2) := by
        refine le_min ?_ ?_
        · positivity
        · linarith
      have habs :
          |β - (β - min (ε / 2) ((β - x0) / 2))| = min (ε / 2) ((β - x0) / 2) := by
        have hsub :
            β - (β - min (ε / 2) ((β - x0) / 2)) = min (ε / 2) ((β - x0) / 2) := by
          ring
        rw [hsub, abs_of_nonneg hmin_nonneg]
      rw [habs]
      calc
        min (ε / 2) ((β - x0) / 2) ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
  have hnot_mem : β ∉ scalarBarrierInterval α β := by
    simp [scalarBarrierInterval]
  have hnot_int : β ∉ interior (scalarBarrierInterval α β) := by
    intro hβ
    exact hnot_mem (interior_subset hβ)
  exact ⟨hclosure, hnot_int⟩

/-- Helper for Theorem 5.4.1.1: the explicit sequence approaching the finite right endpoint from
an interior base point stays in the scalar barrier interval. -/
private theorem rightEndpointApproachFrom_mem_scalarBarrierInterval
    (x0 : scalarBarrierInterval α β)
    (n : ℕ) :
    β - (β - (x0 : ℝ)) / (n + 2 : ℝ) ∈ scalarBarrierInterval α β := by
  have hgap_pos : 0 < β - (x0 : ℝ) := sub_pos.mpr x0.property.2
  constructor
  · have hdiv_lt : (β - (x0 : ℝ)) / (n + 2 : ℝ) < β - (x0 : ℝ) := by
      have hden_pos : 0 < (n + 2 : ℝ) := by positivity
      refine (_root_.div_lt_iff₀ hden_pos).2 ?_
      nlinarith
    have hlt :
        (x0 : ℝ) < β - (β - (x0 : ℝ)) / (n + 2 : ℝ) := by
      linarith
    exact lt_trans x0.property.1 (by exact_mod_cast hlt)
  · have hdiv_pos : 0 < (β - (x0 : ℝ)) / (n + 2 : ℝ) := by positivity
    linarith

/-- Helper for Theorem 5.4.1.1: the explicit right-endpoint sequence issued from an interior base
point converges to `β`. -/
private theorem tendsto_rightEndpointApproachFrom
    (x0 : scalarBarrierInterval α β) :
    Tendsto (fun n : ℕ ↦ β - (β - (x0 : ℝ)) / (n + 2 : ℝ)) atTop (𝓝 β) := by
  have hdiv :
      Tendsto (fun n : ℕ ↦ (β - (x0 : ℝ)) / (n + 2 : ℝ)) atTop (𝓝 0) := by
    have hden :
        Tendsto (fun n : ℕ ↦ (((n + 2 : ℕ) : ℝ))) atTop atTop := by
      exact (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    have hdiv' :
        Tendsto (fun n : ℕ ↦ (β - (x0 : ℝ)) / (((n + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
      exact Filter.Tendsto.const_div_atTop hden (β - (x0 : ℝ))
    simpa [Nat.cast_add] using hdiv'
  simpa using tendsto_const_nhds.sub hdiv

/-- Helper for Theorem 5.4.1.1: under the explicit scalar boundary-growth hypothesis, the barrier
values blow up along the explicit sequence converging to the finite right endpoint `β`. -/
private theorem tendsto_selfConcordantBarrier_atTop_rightEndpointFrom
    {f : ℝ → ℝ}
    (hblow : HasBarrierBoundaryGrowthOnScalarInterval α β f)
    (x0 : scalarBarrierInterval α β) :
    Tendsto
      (fun n : ℕ ↦ f (β - (β - (x0 : ℝ)) / (n + 2 : ℝ)))
      atTop
      atTop := by
  let x : ℕ → scalarBarrierInterval α β := fun n ↦
    ⟨β - (β - (x0 : ℝ)) / (n + 2 : ℝ), rightEndpointApproachFrom_mem_scalarBarrierInterval x0 n⟩
  have hx :
      Tendsto (fun n : ℕ ↦ ((x n : scalarBarrierInterval α β) : ℝ)) atTop (𝓝 β) := by
    simpa [x] using tendsto_rightEndpointApproachFrom x0
  have hfront : β ∈ frontier (scalarBarrierInterval α β) :=
    scalarBarrierInterval_right_endpoint_mem_frontier ⟨(x0 : ℝ), x0.property⟩
  simpa [x] using hblow x hx hfront

/-- Helper for Theorem 5.4.1.1: barrier blow-up at the finite right endpoint forces the
derivative to be nonnegative at some interior point. -/
private theorem exists_nonneg_deriv_of_tendsto_right_endpoint
    {ν : NNReal} {f : ℝ → ℝ}
    (hI : Set.Nonempty (scalarBarrierInterval α β))
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (hblow : HasBarrierBoundaryGrowthOnScalarInterval α β f) :
    ∃ t : scalarBarrierInterval α β, 0 ≤ deriv f t := by
  by_contra hnonneg
  have hneg : ∀ t : scalarBarrierInterval α β, deriv f t < 0 := by
    intro t
    exact lt_of_not_ge (fun ht ↦ hnonneg ⟨t, ht⟩)
  rcases hI with ⟨x0, hx0⟩
  let x0' : scalarBarrierInterval α β := ⟨x0, hx0⟩
  let y : ℕ → scalarBarrierInterval α β := fun n ↦
    ⟨β - (β - (x0' : ℝ)) / (n + 2 : ℝ), rightEndpointApproachFrom_mem_scalarBarrierInterval x0' n⟩
  have hstd := hself.toIsStandardSelfConcordantOn
  have hanti : StrictAntiOn f (scalarBarrierInterval α β) := by
    refine strictAntiOn_of_deriv_neg hstd.convex_domain hstd.contDiffOn.continuousOn ?_
    intro x hx
    exact hneg ⟨x, interior_subset hx⟩
  have hy_gt : ∀ n : ℕ, (x0' : ℝ) < (y n : ℝ) := by
    intro n
    have hdiv_lt : (β - (x0' : ℝ)) / (n + 2 : ℝ) < β - (x0' : ℝ) := by
      have hden_pos : 0 < (n + 2 : ℝ) := by positivity
      refine (_root_.div_lt_iff₀ hden_pos).2 ?_
      nlinarith [sub_pos.mpr x0'.property.2]
    linarith
  have hupper : ∀ n : ℕ, f (y n) < f x0' := by
    intro n
    exact hanti x0'.property (y n).property (hy_gt n)
  have htendsto : Tendsto (fun n : ℕ ↦ f (y n)) atTop atTop := by
    simpa [y] using tendsto_selfConcordantBarrier_atTop_rightEndpointFrom hblow x0'
  have hevent : ∀ᶠ n : ℕ in atTop, f x0' < f (y n) := by
    exact htendsto.eventually (Ioi_mem_atTop (f x0'))
  rcases Filter.Eventually.exists hevent with ⟨n, hn⟩
  linarith [hupper n, hn]

/-- Helper for Theorem 5.4.1.1: if scalar ratio roots converge to `1` along a sequence in the
interval, then the supremum `κ` of the squared ratios is at least `1`. -/
private theorem one_le_kappa_of_ratio_root_tendsto_one
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (y : ℕ → scalarBarrierInterval α β)
    (hroot :
      Tendsto
        (fun n : ℕ ↦ deriv f (y n) / Real.sqrt (iteratedDeriv 2 f (y n)))
        atTop
        (𝓝 1)) :
    1 ≤ selfConcordantBarrierKappa α β f := by
  let κ := selfConcordantBarrierKappa α β f
  have hbdd :
      BddAbove (Set.range (selfConcordantBarrierRatio α β f)) := by
    refine ⟨(ν : ℝ), ?_⟩
    rintro z ⟨t, rfl⟩
    exact selfConcordantBarrierRatio_le_parameter hself t
  have hratio :
      Tendsto (fun n : ℕ ↦ selfConcordantBarrierRatio α β f (y n)) atTop (𝓝 1) := by
    have hpow := hroot.pow 2
    have hrewrite :
        (fun n : ℕ ↦
          (deriv f (y n) / Real.sqrt (iteratedDeriv 2 f (y n))) ^ (2 : ℕ)) =
          fun n : ℕ ↦ selfConcordantBarrierRatio α β f (y n) := by
      funext n
      have hpos : 0 < iteratedDeriv 2 f (y n) :=
        selfConcordantBarrier_secondDeriv_pos hself (y n)
      rw [selfConcordantBarrierRatio, div_pow, pow_two]
      rw [Real.sq_sqrt hpos.le]
    simpa [hrewrite] using hpow
  have hupper :
      ∀ n : ℕ, selfConcordantBarrierRatio α β f (y n) ≤ κ := by
    intro n
    exact le_csSup hbdd ⟨y n, rfl⟩
  by_contra hk
  have hk_lt : κ < 1 := not_le.mp hk
  have hmid_lt_one : (1 + κ) / 2 < 1 := by
    nlinarith
  have hevent :
      ∀ᶠ n : ℕ in atTop, (1 + κ) / 2 < selfConcordantBarrierRatio α β f (y n) := by
    exact hratio.eventually (Ioi_mem_nhds hmid_lt_one)
  rcases Filter.Eventually.exists hevent with ⟨n, hn⟩
  have hbound := hupper n
  nlinarith

/-- Helper for Theorem 5.4.1.1: when the Chapter 5 associated univariate function is specialized
to `x = 0` and `h = 1`, its positivity domain is exactly the scalar barrier interval. -/
private theorem scalarAssociatedUnivariateFunctionDomain_eq
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f) :
    associatedUnivariateFunctionDomain (scalarBarrierInterval α β) f (0 : ℝ) (1 : ℝ) =
      scalarBarrierInterval α β := by
  ext t
  constructor
  · intro ht
    simpa [zero_add, one_smul] using
      (mem_associatedUnivariateFunctionDomain_iff (scalarBarrierInterval α β) f 0 1 t).1 ht |>.1
  · intro ht
    refine (mem_associatedUnivariateFunctionDomain_iff (scalarBarrierInterval α β) f 0 1 t).2 ?_
    refine ⟨by simpa using ht, ?_⟩
    have hpos : 0 < iteratedDeriv 2 f t :=
      selfConcordantBarrier_secondDeriv_pos hself ⟨t, ht⟩
    have hsqrt_pos : 0 < Real.sqrt (iteratedDeriv 2 f t) :=
      Real.sqrt_pos.mpr hpos
    have hlocalNorm :
        0 < Real.sqrt (inner ℝ (1 : ℝ) (hessian f t 1)) := by
      rw [scalar_hessian_quadratic_form_one_eq_secondDeriv]
      exact hsqrt_pos
    simpa [zero_add, one_smul, hessianLocalNorm_def] using hlocalNorm

/-- Helper for Theorem 5.4.1.1: the reciprocal square root of `f''` has the expected scalar
derivative formula on the whole barrier interval. -/
private theorem scalarReciprocalSecondDeriv_hasDerivAt
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    HasDerivAt
      (fun s : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f s))
      (-(iteratedDeriv 3 f t / (2 * (Real.sqrt (iteratedDeriv 2 f t)) ^ (3 : ℕ))))
      t := by
  let I := scalarBarrierInterval α β
  let hstd := hself.toIsStandardSelfConcordantOn
  have hsecond_pos : 0 < iteratedDeriv 2 f t :=
    selfConcordantBarrier_secondDeriv_pos hself t
  have hsqrt_ne : Real.sqrt (iteratedDeriv 2 f t) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hsecond_pos)
  have hcontDeriv : ContDiffOn ℝ 2 (deriv f) I := by
    simpa [I] using hstd.contDiffOn.deriv_of_isOpen hstd.isOpen_domain (m := 2) (by norm_num)
  have hcontSecond : ContDiffOn ℝ 1 (iteratedDeriv 2 f) I := by
    simpa [I, iteratedDeriv_succ] using
      hcontDeriv.deriv_of_isOpen hstd.isOpen_domain (m := 1) (by norm_num)
  have hcontSecondAt : ContDiffAt ℝ 1 (iteratedDeriv 2 f) t :=
    hcontSecond.contDiffAt (hstd.isOpen_domain.mem_nhds t.property)
  have hsecond_hasDerivAt :
      HasDerivAt (fun s : ℝ ↦ iteratedDeriv 2 f s) (iteratedDeriv 3 f t) t := by
    simpa [iteratedDeriv_succ] using
      (hcontSecondAt.hasStrictDerivAt (by norm_num)).hasDerivAt
  have hsqrt_hasDerivAt :
      HasDerivAt
        (fun s : ℝ ↦ Real.sqrt (iteratedDeriv 2 f s))
        (iteratedDeriv 3 f t / (2 * Real.sqrt (iteratedDeriv 2 f t)))
        t :=
    hsecond_hasDerivAt.sqrt hsecond_pos.ne'
  have hinv_hasDerivAt :
      HasDerivAt
        (fun s : ℝ ↦ (Real.sqrt (iteratedDeriv 2 f s))⁻¹)
        (-(iteratedDeriv 3 f t / (2 * Real.sqrt (iteratedDeriv 2 f t))) /
          (Real.sqrt (iteratedDeriv 2 f t)) ^ (2 : ℕ))
        t :=
    hsqrt_hasDerivAt.inv hsqrt_ne
  have hcoeff :
      (-(iteratedDeriv 3 f t / (2 * Real.sqrt (iteratedDeriv 2 f t))) /
          (Real.sqrt (iteratedDeriv 2 f t)) ^ (2 : ℕ)) =
        (-(iteratedDeriv 3 f t / (2 * (Real.sqrt (iteratedDeriv 2 f t)) ^ (3 : ℕ)))) := by
    field_simp [hsqrt_ne]
  have hrewritten :
      HasDerivAt
        (fun s : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f s))
        (-(iteratedDeriv 3 f t / (2 * Real.sqrt (iteratedDeriv 2 f t))) /
          (Real.sqrt (iteratedDeriv 2 f t)) ^ (2 : ℕ))
        t := by
    simpa [one_div] using hinv_hasDerivAt
  exact hrewritten.congr_deriv hcoeff

/-- Helper for Theorem 5.4.1.1: on the scalar barrier interval, the derivative of `deriv f` is
the ordinary second iterated derivative `iteratedDeriv 2 f`. -/
private theorem scalarDeriv_hasDerivAt
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    HasDerivAt (deriv f) (iteratedDeriv 2 f t) t := by
  let I := scalarBarrierInterval α β
  let hstd := hself.toIsStandardSelfConcordantOn
  have hcontDeriv : ContDiffOn ℝ 1 (deriv f) I := by
    simpa [I] using hstd.contDiffOn.deriv_of_isOpen hstd.isOpen_domain (m := 1) (by norm_num)
  have hcontDerivAt : ContDiffAt ℝ 1 (deriv f) t :=
    hcontDeriv.contDiffAt (hstd.isOpen_domain.mem_nhds t.property)
  simpa [iteratedDeriv_succ] using
    (hcontDerivAt.hasStrictDerivAt (by norm_num)).hasDerivAt

/-- Helper for Theorem 5.4.1.1: the derivative of `t ↦ 1 / sqrt (f''(t))` has absolute value at
most `1` on the scalar barrier interval. -/
private theorem abs_deriv_scalarReciprocalSecondDeriv_le_one
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    |deriv (fun s : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f s)) t| ≤ 1 := by
  let hstd := hself.toIsStandardSelfConcordantOn
  have hsecond_pos : 0 < iteratedDeriv 2 f t :=
    selfConcordantBarrier_secondDeriv_pos hself t
  have hderiv_eq :
      deriv (fun s : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f s)) t =
        (-(iteratedDeriv 3 f t / (2 * (Real.sqrt (iteratedDeriv 2 f t)) ^ (3 : ℕ)))) :=
    (scalarReciprocalSecondDeriv_hasDerivAt hself t).deriv
  have hthird_bound :
      |iteratedDeriv 3 f t| ≤ 2 * (Real.sqrt (iteratedDeriv 2 f t)) ^ (3 : ℕ) := by
    have hraw := hstd.third_deriv_bound t.property (1 : ℝ)
    rw [scalar_thirdDirectionalDerivative_one_eq_iteratedDeriv_three,
      hessianLocalNorm_def, scalar_hessian_quadratic_form_one_eq_secondDeriv] at hraw
    simpa [one_mul] using hraw
  rw [hderiv_eq, abs_neg, abs_div]
  have hden_pos : 0 < 2 * (Real.sqrt (iteratedDeriv 2 f t)) ^ (3 : ℕ) := by
    positivity
  rw [abs_of_nonneg hden_pos.le]
  have hthird_bound' :
      |iteratedDeriv 3 f t| ≤ 1 * (2 * (Real.sqrt (iteratedDeriv 2 f t)) ^ (3 : ℕ)) := by
    simpa using hthird_bound
  simpa [one_mul] using (_root_.div_le_iff₀ hden_pos).2 hthird_bound'

/-- Helper for Theorem 5.4.1.1: on the hard branch, the normalized ratio root
`q(s) = deriv f s / sqrt (iteratedDeriv 2 f s)` satisfies the scalar lower differential
inequality needed for the tail invariant. -/
private theorem ratioRoot_deriv_lower_bound
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t0 : scalarBarrierInterval α β)
    (ht0_nonneg : 0 ≤ deriv f t0)
    (hbranch :
      ∀ t : scalarBarrierInterval α β,
        deriv f t / Real.sqrt (iteratedDeriv 2 f t) < 1)
    {s : ℝ} (hs : s ∈ Set.Ioo (t0 : ℝ) β) :
    ((1 - deriv f s / Real.sqrt (iteratedDeriv 2 f s)) / (β - s)) ≤
      deriv (fun x : ℝ ↦ deriv f x / Real.sqrt (iteratedDeriv 2 f x)) s := by
  let ts : scalarBarrierInterval α β := by
    refine ⟨s, ?_⟩
    constructor
    · exact lt_trans t0.property.1 (by exact_mod_cast hs.1)
    · exact hs.2
  let hstd := hself.toIsStandardSelfConcordantOn
  have hsecond_pos : 0 < iteratedDeriv 2 f s :=
    selfConcordantBarrier_secondDeriv_pos hself ts
  have hsqrt_pos : 0 < Real.sqrt (iteratedDeriv 2 f s) :=
    Real.sqrt_pos.mpr hsecond_pos
  have hsqrt_ne : Real.sqrt (iteratedDeriv 2 f s) ≠ 0 := hsqrt_pos.ne'
  have hgap_pos : 0 < β - s := sub_pos.mpr hs.2
  have hderiv_diff :
      ∀ x ∈ scalarBarrierInterval α β, DifferentiableAt ℝ f x := by
    intro x hx
    exact
      (hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds hx)).differentiableAt
        (by norm_num)
  have hderiv_mono : MonotoneOn (deriv f) (scalarBarrierInterval α β) :=
    hstd.convexOn.monotoneOn_deriv hderiv_diff
  have hs_nonneg : 0 ≤ deriv f s := by
    exact hderiv_mono t0.property ts.property hs.1.le |> le_trans ht0_nonneg
  have hbranch_s :
      deriv f s / Real.sqrt (iteratedDeriv 2 f s) < 1 :=
    hbranch ts
  have hone_sub_nonneg :
      0 ≤ 1 - deriv f s / Real.sqrt (iteratedDeriv 2 f s) := by
    linarith
  have hp_deriv_lower :
      -1 ≤ deriv (fun x : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f x)) s := by
    have habs := abs_deriv_scalarReciprocalSecondDeriv_le_one hself ts
    have hpair :
        -1 ≤ deriv (fun x : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f x)) s ∧
          deriv (fun x : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f x)) s ≤ 1 := by
      simpa [abs_le] using habs
    exact hpair.1
  have hp_deriv_eq :
      deriv (fun x : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f x)) s =
        (-(iteratedDeriv 3 f s / (2 * (Real.sqrt (iteratedDeriv 2 f s)) ^ (3 : ℕ)))) :=
    (scalarReciprocalSecondDeriv_hasDerivAt hself ts).deriv
  have hq_prod :
      HasDerivAt
        (deriv f * fun x : ℝ => (Real.sqrt (iteratedDeriv 2 f x))⁻¹)
        (iteratedDeriv 2 f s * (1 / Real.sqrt (iteratedDeriv 2 f s)) +
          deriv f s *
            (-(iteratedDeriv 3 f s / (2 * (Real.sqrt (iteratedDeriv 2 f s)) ^ (3 : ℕ)))))
        s := by
    convert
      (scalarDeriv_hasDerivAt hself ts).mul
        (scalarReciprocalSecondDeriv_hasDerivAt hself ts) using 1
    · ring
  have hq_raw :
      HasDerivAt
        (fun x : ℝ ↦ deriv f x / Real.sqrt (iteratedDeriv 2 f x))
        (iteratedDeriv 2 f s * (1 / Real.sqrt (iteratedDeriv 2 f s)) +
          deriv f s *
            (-(iteratedDeriv 3 f s / (2 * (Real.sqrt (iteratedDeriv 2 f s)) ^ (3 : ℕ)))))
        s := by
    simpa [div_eq_mul_inv] using hq_prod
  have hq_hasDeriv :
      HasDerivAt
        (fun x : ℝ ↦ deriv f x / Real.sqrt (iteratedDeriv 2 f x))
        (iteratedDeriv 2 f s * (1 / Real.sqrt (iteratedDeriv 2 f s)) +
          deriv f s *
            deriv (fun x : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f x)) s)
        s :=
    hq_raw.congr_deriv (by rw [hp_deriv_eq])
  have hq_deriv :
      deriv (fun x : ℝ ↦ deriv f x / Real.sqrt (iteratedDeriv 2 f x)) s =
        iteratedDeriv 2 f s * (1 / Real.sqrt (iteratedDeriv 2 f s)) +
          deriv f s * deriv (fun x : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f x)) s :=
    hq_hasDeriv.deriv
  have hsqrt_term :
      iteratedDeriv 2 f s * (1 / Real.sqrt (iteratedDeriv 2 f s)) =
        Real.sqrt (iteratedDeriv 2 f s) := by
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt hsecond_pos.le]
  have hq_lower_aux :
      Real.sqrt (iteratedDeriv 2 f s) - deriv f s ≤
        deriv (fun x : ℝ ↦ deriv f x / Real.sqrt (iteratedDeriv 2 f x)) s := by
    have hmul :
        deriv f s * (-1 : ℝ) ≤
          deriv f s * deriv (fun x : ℝ ↦ 1 / Real.sqrt (iteratedDeriv 2 f x)) s :=
      mul_le_mul_of_nonneg_left hp_deriv_lower hs_nonneg
    have hadd := add_le_add_left hmul (Real.sqrt (iteratedDeriv 2 f s))
    rw [hq_deriv, hsqrt_term]
    simpa [sub_eq_add_neg] using hadd
  have hp_le_gap :
      1 / Real.sqrt (iteratedDeriv 2 f s) ≤ β - s :=
    scalar_reciprocal_localNorm_le_right_gap hself ts
  have hgapinv_le_sqrt :
      (β - s)⁻¹ ≤ Real.sqrt (iteratedDeriv 2 f s) := by
    have hp_pos : 0 < 1 / Real.sqrt (iteratedDeriv 2 f s) :=
      one_div_pos.mpr hsqrt_pos
    have htmp :
        (β - s)⁻¹ ≤ (1 / Real.sqrt (iteratedDeriv 2 f s))⁻¹ :=
      (inv_le_inv₀ hgap_pos hp_pos).2 hp_le_gap
    simpa [one_div, inv_inv, hsqrt_ne] using htmp
  have hleft_le :
      ((1 - deriv f s / Real.sqrt (iteratedDeriv 2 f s)) / (β - s)) ≤
        Real.sqrt (iteratedDeriv 2 f s) - deriv f s := by
    have hmul :=
      mul_le_mul_of_nonneg_left hgapinv_le_sqrt hone_sub_nonneg
    have hright_eq :
        (1 - deriv f s / Real.sqrt (iteratedDeriv 2 f s)) *
            Real.sqrt (iteratedDeriv 2 f s) =
          Real.sqrt (iteratedDeriv 2 f s) - deriv f s := by
      field_simp [hsqrt_ne]
    have hmul' :
        ((1 - deriv f s / Real.sqrt (iteratedDeriv 2 f s)) / (β - s)) ≤
          (1 - deriv f s / Real.sqrt (iteratedDeriv 2 f s)) *
            Real.sqrt (iteratedDeriv 2 f s) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    exact hmul'.trans_eq hright_eq
  exact hleft_le.trans hq_lower_aux

/-- Helper for Theorem 5.4.1.1: on the right tail, the normalized gap quotient
`(1 - q(s)) / (β - s)` has the expected ambient scalar derivative. -/
private theorem oneMinusRatioRootOverRightGap_hasDerivAt
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t0 : scalarBarrierInterval α β)
    {s : ℝ} (hs : s ∈ Set.Ioo (t0 : ℝ) β) :
    HasDerivAt
      (fun x : ℝ ↦ (1 - deriv f x / Real.sqrt (iteratedDeriv 2 f x)) / (β - x))
      (((1 - deriv f s / Real.sqrt (iteratedDeriv 2 f s)) -
          (β - s) * deriv (fun x : ℝ ↦ deriv f x / Real.sqrt (iteratedDeriv 2 f x)) s) /
        (β - s) ^ (2 : ℕ))
      s := by
  let ts : scalarBarrierInterval α β := by
    refine ⟨s, ?_⟩
    constructor
    · exact lt_trans t0.property.1 (by exact_mod_cast hs.1)
    · exact hs.2
  let q : ℝ → ℝ := fun x ↦ deriv f x / Real.sqrt (iteratedDeriv 2 f x)
  have hgap_pos : 0 < β - s := sub_pos.mpr hs.2
  have hgap_ne : β - s ≠ 0 := hgap_pos.ne'
  have hq_prod :
      HasDerivAt
        (deriv f * fun x : ℝ ↦ (Real.sqrt (iteratedDeriv 2 f x))⁻¹)
        (iteratedDeriv 2 f s * (1 / Real.sqrt (iteratedDeriv 2 f s)) +
          deriv f s *
            (-(iteratedDeriv 3 f s / (2 * (Real.sqrt (iteratedDeriv 2 f s)) ^ (3 : ℕ)))))
        s := by
    convert
      (scalarDeriv_hasDerivAt hself ts).mul
        (scalarReciprocalSecondDeriv_hasDerivAt hself ts) using 1
    ring
  have hq_raw :
      HasDerivAt
        q
        (iteratedDeriv 2 f s * (1 / Real.sqrt (iteratedDeriv 2 f s)) +
          deriv f s *
            (-(iteratedDeriv 3 f s / (2 * (Real.sqrt (iteratedDeriv 2 f s)) ^ (3 : ℕ)))))
        s := by
    simpa [q, div_eq_mul_inv] using hq_prod
  have hq_hasDeriv : HasDerivAt q (deriv q s) s :=
    hq_raw.congr_deriv hq_raw.deriv.symm
  have hnum : HasDerivAt (fun x : ℝ ↦ 1 - q x) (-deriv q s) s := by
    simpa using hq_hasDeriv.const_sub (1 : ℝ)
  have hden : HasDerivAt (fun x : ℝ ↦ β - x) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub β
  have hquot :
      HasDerivAt
        (fun x : ℝ ↦ (1 - q x) / (β - x))
        (((-deriv q s) * (β - s) - (1 - q s) * (-1)) / (β - s) ^ (2 : ℕ))
        s :=
    hnum.div hden hgap_ne
  have hquot' :
      HasDerivAt
        (fun x : ℝ ↦ (1 - deriv f x / Real.sqrt (iteratedDeriv 2 f x)) / (β - x))
        (((-deriv q s) * (β - s) - (1 - q s) * (-1)) / (β - s) ^ (2 : ℕ))
        s := by
    simpa [q] using hquot
  have hcoeff :
      (((-deriv q s) * (β - s) - (1 - q s) * (-1)) / (β - s) ^ (2 : ℕ)) =
        (((1 - deriv f s / Real.sqrt (iteratedDeriv 2 f s)) -
            (β - s) * deriv (fun x : ℝ ↦ deriv f x / Real.sqrt (iteratedDeriv 2 f x)) s) /
          (β - s) ^ (2 : ℕ)) := by
    simp [q]
    ring
  exact hquot'.congr_deriv hcoeff

/-- Helper for Theorem 5.4.1.1: on the branch where
`deriv f t / sqrt (iteratedDeriv 2 f t) < 1` everywhere, the normalized gap
`(1 - deriv f t / sqrt (iteratedDeriv 2 f t)) / (β - t)` is antitone on the right tail. -/
private theorem oneSubRatioRootDivRightGap_antitoneOn
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t0 : scalarBarrierInterval α β)
    (ht0_nonneg : 0 ≤ deriv f t0)
    (hbranch :
      ∀ t : scalarBarrierInterval α β,
        deriv f t / Real.sqrt (iteratedDeriv 2 f t) < 1) :
    AntitoneOn
      (fun s : ℝ ↦ (1 - deriv f s / Real.sqrt (iteratedDeriv 2 f s)) / (β - s))
      (Set.Ioo (t0 : ℝ) β) := by
  let q : ℝ → ℝ := fun s ↦ deriv f s / Real.sqrt (iteratedDeriv 2 f s)
  let g : ℝ → ℝ := fun s ↦ (1 - q s) / (β - s)
  let g' : ℝ → ℝ := fun s ↦ ((1 - q s) - (β - s) * deriv q s) / (β - s) ^ (2 : ℕ)
  refine
    antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Ioo (t0 : ℝ) β) (f := g) (f' := g')
      (convex_Ioo _ _) ?_ ?_ ?_
  · intro s hs
    exact
      (oneMinusRatioRootOverRightGap_hasDerivAt hself t0 hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Set.Ioo (t0 : ℝ) β := by
      simpa [interior_Ioo] using hs
    simpa [g, g', q, interior_Ioo] using
      (oneMinusRatioRootOverRightGap_hasDerivAt hself t0 hs').hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Set.Ioo (t0 : ℝ) β := by
      simpa [interior_Ioo] using hs
    have hratio_lower :
        ((1 - q s) / (β - s)) ≤ deriv q s := by
      simpa [q] using ratioRoot_deriv_lower_bound hself t0 ht0_nonneg hbranch hs'
    have hbase :
        1 - q s ≤ (β - s) * deriv q s := by
      simpa [mul_comm] using (_root_.div_le_iff₀ (sub_pos.mpr hs'.2)).1 hratio_lower
    have hnum_nonpos : (1 - q s) - (β - s) * deriv q s ≤ 0 := by
      linarith
    have hden_nonneg : 0 ≤ (β - s) ^ (2 : ℕ) := by positivity
    simpa [g', q] using div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_nonneg

/-- Helper for Theorem 5.4.1.1: on the hard branch
`deriv f t / sqrt (iteratedDeriv 2 f t) < 1`, the explicit approach-to-`β` sequence forces the
ratio root to converge to `1`. -/
private theorem tendsto_ratioRoot_rightEndpointApproachFrom
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t0 : scalarBarrierInterval α β)
    (ht0_nonneg : 0 ≤ deriv f t0)
    (hbranch :
      ∀ t : scalarBarrierInterval α β,
        deriv f t / Real.sqrt (iteratedDeriv 2 f t) < 1) :
    Tendsto
      (fun n : ℕ ↦
        deriv f (β - (β - (t0 : ℝ)) / (n + 2 : ℝ)) /
          Real.sqrt (iteratedDeriv 2 f (β - (β - (t0 : ℝ)) / (n + 2 : ℝ))))
      atTop
      (𝓝 1) := by
  let q : ℝ → ℝ := fun s ↦ deriv f s / Real.sqrt (iteratedDeriv 2 f s)
  let g : ℝ → ℝ := fun s ↦ (1 - q s) / (β - s)
  let y : ℕ → ℝ := fun n ↦ β - (β - (t0 : ℝ)) / (n + 2 : ℝ)
  have hanti := oneSubRatioRootDivRightGap_antitoneOn hself t0 ht0_nonneg hbranch
  have hy_mem : ∀ n : ℕ, y n ∈ Set.Ioo (t0 : ℝ) β := by
    intro n
    constructor
    · have hdiv_lt : (β - (t0 : ℝ)) / (n + 2 : ℝ) < β - (t0 : ℝ) := by
        have hden_pos : 0 < (n + 2 : ℝ) := by positivity
        refine (_root_.div_lt_iff₀ hden_pos).2 ?_
        nlinarith [sub_pos.mpr t0.property.2]
      linarith
    · simpa [y] using (rightEndpointApproachFrom_mem_scalarBarrierInterval t0 n).2
  have hy0_le : ∀ n : ℕ, y 0 ≤ y n := by
    intro n
    have hgap_nonneg : 0 ≤ β - (t0 : ℝ) := by linarith [t0.property.2]
    have htwo_le : (2 : ℝ) ≤ (n + 2 : ℝ) := by
      have hn_nonneg : (0 : ℝ) ≤ n := by positivity
      nlinarith
    have hrecip :
        (1 : ℝ) / (n + 2 : ℝ) ≤ (1 : ℝ) / 2 := by
      exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2) htwo_le
    have hscaled :
        (β - (t0 : ℝ)) * ((1 : ℝ) / (n + 2 : ℝ)) ≤
          (β - (t0 : ℝ)) * ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hrecip hgap_nonneg
    have hdiv_le :
        (β - (t0 : ℝ)) / (n + 2 : ℝ) ≤ (β - (t0 : ℝ)) / 2 := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    dsimp [y]
    linarith
  have hone_sub_nonneg : ∀ n : ℕ, 0 ≤ 1 - q (y n) := by
    intro n
    have hbranch_n : q (y n) < 1 := by
      simpa [q, y] using hbranch
        ⟨y n, rightEndpointApproachFrom_mem_scalarBarrierInterval t0 n⟩
    linarith
  have hone_sub_le : ∀ n : ℕ, 1 - q (y n) ≤ g (y 0) * (β - y n) := by
    intro n
    have hy0 : y 0 ∈ Set.Ioo (t0 : ℝ) β := hy_mem 0
    have hyn : y n ∈ Set.Ioo (t0 : ℝ) β := hy_mem n
    have hmono : g (y n) ≤ g (y 0) := hanti hy0 hyn (hy0_le n)
    have hgap_nonneg : 0 ≤ β - y n := by linarith [hyn.2]
    have hmul : g (y n) * (β - y n) ≤ g (y 0) * (β - y n) :=
      mul_le_mul_of_nonneg_right hmono hgap_nonneg
    have hgap_ne : β - y n ≠ 0 := ne_of_gt (sub_pos.mpr hyn.2)
    have hrewrite : g (y n) * (β - y n) = 1 - q (y n) := by
      dsimp [g]
      field_simp [hgap_ne]
    calc
      1 - q (y n) = g (y n) * (β - y n) := hrewrite.symm
      _ ≤ g (y 0) * (β - y n) := hmul
  have hgap_tendsto : Tendsto (fun n : ℕ ↦ β - y n) atTop (𝓝 0) := by
    have hgap_eq :
        (fun n : ℕ ↦ β - y n) = fun n : ℕ ↦ (β - (t0 : ℝ)) / (n + 2 : ℝ) := by
      funext n
      dsimp [y]
      ring
    rw [hgap_eq]
    have hden : Tendsto (fun n : ℕ ↦ (((n + 2 : ℕ) : ℝ))) atTop atTop := by
      exact (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    have hdiv' :
        Tendsto (fun n : ℕ ↦ (β - (t0 : ℝ)) / (((n + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
      exact Filter.Tendsto.const_div_atTop hden (β - (t0 : ℝ))
    simpa [Nat.cast_add] using hdiv'
  have hupper_tendsto : Tendsto (fun n : ℕ ↦ g (y 0) * (β - y n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hgap_tendsto)
  have hone_sub_tendsto_zero : Tendsto (fun n : ℕ ↦ 1 - q (y n)) atTop (𝓝 0) :=
    squeeze_zero hone_sub_nonneg hone_sub_le hupper_tendsto
  have hq_tendsto :
      Tendsto (fun n : ℕ ↦ q (y n)) atTop (𝓝 1) := by
    have hshift :
        Tendsto (fun n : ℕ ↦ 1 - (1 - q (y n))) atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hone_sub_tendsto_zero
    have hrewrite :
        (fun n : ℕ ↦ 1 - (1 - q (y n))) = fun n : ℕ ↦ q (y n) := by
      funext n
      ring
    rw [hrewrite] at hshift
    simpa using hshift
  simpa [q, y] using hq_tendsto

/-- Helper for Theorem 5.4.1.1: if `(\alpha, \beta)` is nonempty and `f` is a scalar
`ν`-self-concordant barrier on it, then the source-facing ratio supremum satisfies `1 ≤ κ`. -/
theorem one_le_selfConcordantBarrierKappa
    {ν : NNReal} {f : ℝ → ℝ}
    (hI : Set.Nonempty (scalarBarrierInterval α β))
    (hbarrier : IsSelfConcordantBarrierOnScalarIntervalWith α β ν f) :
    1 ≤ selfConcordantBarrierKappa α β f := by
  let hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f :=
    hbarrier.toIsSelfConcordantBarrierOnWith
  by_cases hge :
      ∃ t : scalarBarrierInterval α β,
        1 ≤ deriv f t / Real.sqrt (iteratedDeriv 2 f t)
  · rcases hge with ⟨t, ht⟩
    have hbdd :
        BddAbove (Set.range (selfConcordantBarrierRatio α β f)) := by
      refine ⟨(ν : ℝ), ?_⟩
      rintro z ⟨u, rfl⟩
      exact selfConcordantBarrierRatio_le_parameter hself u
    have hsecond_pos : 0 < iteratedDeriv 2 f t :=
      selfConcordantBarrier_secondDeriv_pos hself t
    have hratio_one :
        1 ≤ selfConcordantBarrierRatio α β f t := by
      have hpow : 1 ≤ (deriv f t / Real.sqrt (iteratedDeriv 2 f t)) ^ (2 : ℕ) := by
        nlinarith
      rw [div_pow, pow_two, Real.sq_sqrt hsecond_pos.le] at hpow
      simpa [selfConcordantBarrierRatio, pow_two] using hpow
    exact le_trans hratio_one (le_csSup hbdd ⟨t, rfl⟩)
  · have hbranch :
        ∀ t : scalarBarrierInterval α β,
          deriv f t / Real.sqrt (iteratedDeriv 2 f t) < 1 := by
      intro t
      exact lt_of_not_ge (fun ht ↦ hge ⟨t, ht⟩)
    obtain ⟨t0, ht0_nonneg⟩ :=
      exists_nonneg_deriv_of_tendsto_right_endpoint
        hI hself hbarrier.hasBarrierBoundaryGrowthOnScalarInterval
    let y : ℕ → scalarBarrierInterval α β := fun n ↦
      ⟨β - (β - (t0 : ℝ)) / (n + 2 : ℝ),
        rightEndpointApproachFrom_mem_scalarBarrierInterval t0 n⟩
    have hroot :
        Tendsto
          (fun n : ℕ ↦ deriv f (y n) / Real.sqrt (iteratedDeriv 2 f (y n)))
          atTop
          (𝓝 1) := by
      simpa [y] using tendsto_ratioRoot_rightEndpointApproachFrom hself t0 ht0_nonneg hbranch
    exact one_le_kappa_of_ratio_root_tendsto_one hself y hroot

/-- Helper for Theorem 5.4.1.1: the split self-concordance and boundary-growth assumptions
assemble the source-facing scalar barrier owner used in the scalar reduction. -/
theorem isSelfConcordantBarrierOnScalarIntervalWith_of_self_and_boundaryGrowth
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (hblow : HasBarrierBoundaryGrowthOnScalarInterval α β f) :
    IsSelfConcordantBarrierOnScalarIntervalWith α β ν f := by
  refine
    { toIsSelfConcordantBarrierOnWith := hself
      boundary_growth := hblow }

/-- Helper for Theorem 5.4.1.1: compatibility form of the scalar `κ` bounds using the split
Chapter 5 barrier owner together with the explicit frontier-divergence hypothesis. -/
theorem selfConcordantBarrier_one_le_kappa_and_kappa_le_parameter_of_self_and_boundaryGrowth
    {ν : NNReal} {f : ℝ → ℝ}
    (hI : Set.Nonempty (scalarBarrierInterval α β))
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (hblow : HasBarrierBoundaryGrowthOnScalarInterval α β f) :
    1 ≤ selfConcordantBarrierKappa α β f ∧
      selfConcordantBarrierKappa α β f ≤ (ν : ℝ) := by
  refine ⟨?_, ?_⟩
  · exact
      one_le_selfConcordantBarrierKappa hI
        (isSelfConcordantBarrierOnScalarIntervalWith_of_self_and_boundaryGrowth hself hblow)
  · exact selfConcordantBarrierKappa_le_parameter hself

/-- Helper for Theorem 5.4.1.1: source-facing bundled `κ` bounds for a scalar
`ν`-self-concordant barrier on `(\alpha, \beta)`. -/
theorem selfConcordantBarrier_one_le_kappa_and_kappa_le_parameter
    {ν : NNReal} {f : ℝ → ℝ}
    (hI : Set.Nonempty (scalarBarrierInterval α β))
    (hbarrier : IsSelfConcordantBarrierOnScalarIntervalWith α β ν f) :
    1 ≤ selfConcordantBarrierKappa α β f ∧
      selfConcordantBarrierKappa α β f ≤ (ν : ℝ) := by
  refine ⟨?_, ?_⟩
  · exact one_le_selfConcordantBarrierKappa hI hbarrier
  · exact selfConcordantBarrierKappa_le_parameter hbarrier.toIsSelfConcordantBarrierOnWith

end

/-- Helper for Theorem 5.4.1.1: if `1` lies in the closure of a scalar set `S`, then every
strictly smaller point has some point of `S` to its right. -/
private theorem exists_mem_gt_of_one_mem_closure
    {S : Set ℝ}
    (hclosure : (1 : ℝ) ∈ closure S)
    {t : ℝ} (ht : t < 1) :
    ∃ y ∈ S, t < y := by
  rw [Metric.mem_closure_iff] at hclosure
  rcases hclosure (1 - t) (sub_pos.mpr ht) with ⟨y, hyS, hyDist⟩
  rw [Real.dist_eq] at hyDist
  have hyAbs : |y - 1| < 1 - t := by
    simpa [abs_sub_comm] using hyDist
  have hyLower : -(1 - t) < y - 1 := (abs_lt.mp hyAbs).1
  refine ⟨y, hyS, ?_⟩
  linarith

/-- Helper for Theorem 5.4.1.1: an open convex scalar slice containing `0` and having `1` as a
missing closure point is exactly `scalarBarrierInterval α 1` for some lower endpoint `α`. -/
private theorem exists_scalarBarrierInterval_eq_of_zero_mem_of_one_frontier
    {S : Set ℝ}
    (hopen : IsOpen S)
    (hconvex : Convex ℝ S)
    (hzero : (0 : ℝ) ∈ S)
    (hclosure : (1 : ℝ) ∈ closure S)
    (hone : (1 : ℝ) ∉ S) :
    ∃ α : WithBot ℝ, S = scalarBarrierInterval α 1 := by
  let hord : Set.OrdConnected S := hconvex.ordConnected
  have hnonempty : S.Nonempty := ⟨0, hzero⟩
  have hlt_one : ∀ ⦃t : ℝ⦄, t ∈ S → t < 1 := by
    intro t ht
    by_contra hnot
    have hle : 1 ≤ t := le_of_not_gt hnot
    have hsubset : Set.Icc (0 : ℝ) t ⊆ S := hord.out hzero ht
    exact hone (hsubset ⟨by norm_num, hle⟩)
  by_cases hbdd : BddBelow S
  · refine ⟨(sInf S : ℝ), ?_⟩
    ext t
    constructor
    · intro ht
      constructor
      · have hne_sInf : sInf S ≠ t := by
          intro hsInf
          have hsInf_mem : sInf S ∈ S := by
            simpa [hsInf] using ht
          have hsInf_nhds := hopen.mem_nhds hsInf_mem
          rw [Metric.mem_nhds_iff] at hsInf_nhds
          rcases hsInf_nhds with ⟨ε, hε, hball⟩
          have hsmaller_mem : sInf S - ε / 2 ∈ S := by
            apply hball
            rw [Metric.mem_ball, Real.dist_eq]
            have hdist : |sInf S - ε / 2 - sInf S| = ε / 2 := by
              ring_nf
              rw [abs_mul, abs_of_pos hε]
              norm_num
            rw [hdist]
            linarith
          have hsInf_le : sInf S ≤ sInf S - ε / 2 := csInf_le hbdd hsmaller_mem
          linarith
        have hsInf_lt : sInf S < t := lt_of_le_of_ne (csInf_le hbdd ht) hne_sInf
        exact_mod_cast hsInf_lt
      · exact hlt_one ht
    · intro ht
      rcases ht with ⟨ht_lower, ht_upper⟩
      have ht_lower_real : sInf S < t := by
        exact_mod_cast ht_lower
      obtain ⟨x, hxS, hxt⟩ := exists_lt_of_csInf_lt hnonempty ht_lower_real
      obtain ⟨y, hyS, hty⟩ := exists_mem_gt_of_one_mem_closure hclosure ht_upper
      exact (hord.out hxS hyS) ⟨le_of_lt hxt, le_of_lt hty⟩
  · refine ⟨⊥, ?_⟩
    ext t
    constructor
    · intro ht
      simpa [scalarBarrierInterval] using hlt_one ht
    · intro ht
      have ht_upper : t < 1 := by
        simpa [scalarBarrierInterval] using ht
      have hlower : ∃ x ∈ S, x < t := by
        by_contra hnot
        apply hbdd
        refine ⟨t, ?_⟩
        intro x hxS
        by_contra hxt
        exact hnot ⟨x, hxS, lt_of_not_ge hxt⟩
      obtain ⟨x, hxS, hxt⟩ := hlower
      obtain ⟨y, hyS, hty⟩ := exists_mem_gt_of_one_mem_closure hclosure ht_upper
      exact (hord.out hxS hyS) ⟨le_of_lt hxt, le_of_lt hty⟩

-- Proof sketch: choose an affine line through an interior point whose line slice meets the
-- frontier, identify the preimage with a nonempty scalar interval, and pull back both the Chapter
-- 5 owner and the ambient frontier-growth hypothesis to the scalar bundled barrier owner above.
private theorem exists_scalarBarrierInterval_affinePullback
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hdom : dom.Nonempty)
    (hfront : (frontier dom).Nonempty)
    (hself : IsSelfConcordantBarrierOnWith dom ν F)
    (hblow : HasBarrierBoundaryGrowthOn dom F) :
    ∃ (α : WithBot ℝ) (β : ℝ) (g : ℝ →ᴬ[ℝ] E),
      Set.Nonempty (scalarBarrierInterval α β) ∧
        IsSelfConcordantBarrierOnScalarIntervalWith α β ν (F ∘ g) :=
  by
  -- Route correction: reuse the canonical scalar interval API from `Lemma_5_4_1_1` and only
  -- build the affine slice and boundary-growth transport locally in this file.
  rcases hdom with ⟨x, hx⟩
  rcases hfront with ⟨xBar, hxBar_frontier⟩
  let gAffine : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x xBar
  let g : ℝ →ᴬ[ℝ] E := ⟨gAffine, gAffine.continuous_of_finiteDimensional⟩
  let J : Set ℝ := g ⁻¹' dom
  let hstd : IsStandardSelfConcordantOn dom F := hself.toIsStandardSelfConcordantOn
  have hdom_open : IsOpen dom := hstd.isOpen_domain
  have hdom_convex : Convex ℝ dom := hstd.convex_domain
  have hJ_open : IsOpen J := hdom_open.preimage g.continuous
  have hJ_convex : Convex ℝ J := by
    simpa [J] using hdom_convex.affine_preimage g.toAffineMap
  have hzero_mem : (0 : ℝ) ∈ J := by
    simpa [J, g, gAffine, AffineMap.lineMap_apply_zero] using hx
  have hxBar_not_dom : xBar ∉ dom := by
    simpa [hdom_open.interior_eq] using hxBar_frontier.2
  have hone_not_mem : (1 : ℝ) ∉ J := by
    simpa [J, g, gAffine, AffineMap.lineMap_apply_one] using hxBar_not_dom
  have hone_mem_closure : (1 : ℝ) ∈ closure J := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let t : ℝ := 1 - min (ε / 2) (1 / 2)
    have hmin_pos : 0 < min (ε / 2) (1 / 2) := by
      positivity
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      have hmin_le : min (ε / 2) (1 / 2) ≤ (1 / 2 : ℝ) := min_le_right _ _
      linarith
    have ht_mem_dom : g t ∈ dom := by
      have hx_interior : x ∈ interior dom := by
        simpa [hdom_open.interior_eq] using hx
      have := hdom_convex.combo_interior_closure_mem_interior
          hx_interior hxBar_frontier.1 hmin_pos ht_nonneg (by
            dsimp [t]
            ring)
      simpa [g, gAffine, t, hdom_open.interior_eq, AffineMap.lineMap_apply_module] using this
    refine ⟨t, ?_, ?_⟩
    · simpa [J] using ht_mem_dom
    rw [Real.dist_eq]
    have hmin_nonneg : 0 ≤ min (ε / 2) (1 / 2) := by positivity
    have hmin_lt : min (ε / 2) (1 / 2) < ε := by
      calc
        min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
    dsimp [t]
    have hdist : |1 - (1 - min (ε / 2) (1 / 2))| = min (ε / 2) (1 / 2) := by
      have htmp : 1 - (1 - min (ε / 2) (1 / 2)) = min (ε / 2) (1 / 2) := by ring
      rw [htmp, abs_of_nonneg hmin_nonneg]
    rw [hdist]
    exact hmin_lt
  obtain ⟨α, hJ_eq⟩ :=
    exists_scalarBarrierInterval_eq_of_zero_mem_of_one_frontier
      hJ_open hJ_convex hzero_mem hone_mem_closure hone_not_mem
  have hI : Set.Nonempty (scalarBarrierInterval α 1) := by
    refine ⟨0, ?_⟩
    simpa [hJ_eq] using hzero_mem
  have hself_pull : IsSelfConcordantBarrierOnWith J ν (F ∘ g) :=
    hself.comp_continuousAffineMap g
  have hself_scalar : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α 1) ν (F ∘ g) := by
    simpa [hJ_eq] using hself_pull
  have hblow_scalar : HasBarrierBoundaryGrowthOnScalarInterval α 1 (F ∘ g) := by
    intro x tBar hxTendsto htBar_frontier
    let y : ℕ → interior dom := fun n ↦
      ⟨g (x n), by
        have hx_mem_interval : (x n : ℝ) ∈ scalarBarrierInterval α 1 := (x n).property
        have hx_mem_J : (x n : ℝ) ∈ J := by
          rw [hJ_eq]
          exact hx_mem_interval
        have hg_mem_dom : g (x n) ∈ dom := by
          simpa [J] using hx_mem_J
        simpa [hdom_open.interior_eq] using hg_mem_dom⟩
    have hy_tendsto : Tendsto (fun n : ℕ ↦ (y n : E)) atTop (𝓝 (g tBar)) := by
      simpa [y] using (g.continuous.continuousAt.tendsto.comp hxTendsto)
    have hg_frontier : g tBar ∈ frontier dom := by
      have htBar_mem_closure : tBar ∈ closure (scalarBarrierInterval α 1) := htBar_frontier.1
      have hg_mem_closure_image : g tBar ∈ closure (g '' scalarBarrierInterval α 1) :=
        (image_closure_subset_closure_image g.continuous) (Set.mem_image_of_mem g htBar_mem_closure)
      have hg_mem_closure : g tBar ∈ closure dom := by
        refine closure_mono ?_ hg_mem_closure_image
        rintro _ ⟨s, hs, rfl⟩
        have hsJ : s ∈ J := by
          simpa [hJ_eq] using hs
        exact hsJ
      have hg_not_dom : g tBar ∉ dom := by
        intro hg_mem
        have htBar_mem_interiorJ : tBar ∈ interior J := by
          simpa [J, hJ_open.interior_eq] using hg_mem
        have htBar_mem_interior :
            tBar ∈ interior (scalarBarrierInterval α 1) := by
          simpa [hJ_eq] using htBar_mem_interiorJ
        exact htBar_frontier.2 htBar_mem_interior
      exact ⟨hg_mem_closure, by simpa [hdom_open.interior_eq] using hg_not_dom⟩
    -- Proof comment: the frontier-approaching scalar sequence maps to a frontier-approaching
    -- sequence in `dom`, so the ambient boundary-growth hypothesis applies verbatim.
    simpa [Function.comp, y] using hblow y hy_tendsto hg_frontier
  refine ⟨α, 1, g, hI, ?_⟩
  exact
    isSelfConcordantBarrierOnScalarIntervalWith_of_self_and_boundaryGrowth
      hself_scalar hblow_scalar

namespace IsSelfConcordantBarrierOnWith

/-- Compatibility form of the lower barrier-parameter bound using the split Chapter 5 barrier
owner together with the explicit frontier-growth hypothesis. -/
theorem one_le_parameter_of_nonempty_boundaryGrowth
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hdom : dom.Nonempty)
    (hfront : (frontier dom).Nonempty)
    (hself : IsSelfConcordantBarrierOnWith dom ν F)
    (hblow : HasBarrierBoundaryGrowthOn dom F) :
    1 ≤ ν :=
  by
  -- Proof comment: the affine pullback helper reduces the ambient barrier to a scalar barrier, and
  -- the imported scalar theorem supplies the lower and upper `κ` bounds needed to compare with `ν`.
  rcases exists_scalarBarrierInterval_affinePullback hdom hfront hself hblow with
    ⟨α, β, g, hI, hbarrier⟩
  have hkappa :
      1 ≤ selfConcordantBarrierKappa α β (F ∘ g) ∧
        selfConcordantBarrierKappa α β (F ∘ g) ≤ (ν : ℝ) :=
    selfConcordantBarrier_one_le_kappa_and_kappa_le_parameter hI hbarrier
  have hν_real : (1 : ℝ) ≤ (ν : ℝ) := le_trans hkappa.1 hkappa.2
  simpa using hν_real

end IsSelfConcordantBarrierOnWith

/-- Helper form of Theorem 5.4.1.1 retaining the split open-domain, barrier, and nonempty-frontier
hypotheses explicitly. -/
theorem one_le_selfConcordantBarrierParameter_of_nonempty_frontier
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hbar : IsBarrierFunctionOn Q (selfConcordantBarrierRestriction hself))
    (hfront : (frontier Q).Nonempty) :
    1 ≤ ν := by
  -- Proof comment: the Chapter 1 barrier owner upgrades frontier growth on `Q` to the split
  -- boundary-growth hypothesis on `interior Q`, so the ambient reduction theorem applies.
  have hfrontInterior : (frontier (interior Q)).Nonempty := by
    have hproper : interior Q ≠ (Set.univ : Set E) := by
      intro hInt
      have hQ : Q = (Set.univ : Set E) := by
        apply Set.eq_univ_of_univ_subset
        simpa [hInt] using (interior_subset : interior Q ⊆ Q)
      have hfront_univ : (frontier (Set.univ : Set E)).Nonempty := by
        exact hQ ▸ hfront
      simp at hfront_univ
    exact (nonempty_frontier_iff).2 ⟨hbar.interior_nonempty, hproper⟩
  have hblowInterior : HasBarrierBoundaryGrowthOn (interior Q) F := by
    intro x xBar hx hxBar
    let xQ : ℕ → interior Q := fun n ↦
      ⟨x n, by simpa [interior_interior] using (x n).property⟩
    have hxQ : Tendsto (fun n : ℕ ↦ (xQ n : E)) atTop (𝓝 xBar) := by
      simpa [xQ] using hx
    have hxBarQ : xBar ∈ frontier Q := by
      rw [frontier, interior_interior] at hxBar
      rw [frontier]
      exact ⟨closure_mono interior_subset hxBar.1, hxBar.2⟩
    simpa [selfConcordantBarrierRestriction] using
      hbar.tendsTo_atTop_of_tendsto_frontier xQ hxQ hxBarQ
  exact
    IsSelfConcordantBarrierOnWith.one_le_parameter_of_nonempty_boundaryGrowth
      hbar.interior_nonempty hfrontInterior hself hblowInterior

/-- The lower bound on the parameter for the strengthened bundled barrier owner. -/
theorem IsSelfConcordantBarrierForWith.one_le_parameter
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierForWith Q ν F) :
    1 ≤ ν := by
  -- Proof comment: unpack the bundled barrier data and apply the split-frontier wrapper.
  exact
    one_le_selfConcordantBarrierParameter_of_nonempty_frontier
      hF.toIsSelfConcordantBarrierOnWith hF.toIsBarrierFunctionOn hF.frontier_nonempty

/-- Theorem 5.4.1.1: if `F` is a `ν`-self-concordant barrier for `Q`, then the barrier parameter
satisfies `ν ≥ 1`. In this file the genuine-barrier hypothesis is expressed by
`IsSelfConcordantBarrierForWith Q ν F`, which packages the Chapter 5 owner on `interior Q`, the
Chapter 1 barrier owner for the canonical restriction to `Q`, and the nonvacuous-boundary
condition. -/
theorem one_le_selfConcordantBarrierParameter_of_nonempty_interior
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierForWith Q ν F) :
    1 ≤ ν := by
  -- Proof comment: the final theorem is exactly the bundled-owner wrapper.
  exact IsSelfConcordantBarrierForWith.one_le_parameter hF

end
