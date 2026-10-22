/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_1
import Mathlib.Analysis.Convex.Deriv

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin ConvexAnalysis Gradient
open ContinuousLinearMap

noncomputable section

universe u₁ u₂

variable {E₁ : Type u₁} {E₂ : Type u₂}

variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
variable [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
variable [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

local notation "Z" => WithLp 2 (E₁ × E₂)

/- Theorem 5.1.11 lies in the chapter's partial-minimization / self-concordance calculus.

Sampled owner-style declarations in this domain:
- `IsSelfConcordantOnWith` from `Definition_5_1_1`, the Chapter 5 owner for quantitative
  self-concordance on an ambient Hilbert space;
- `partialInfProjection` from Chapter 3 and `extendedRealRealPart` from `Definition_5_0_18`, the
  canonical owners for the partial-minimization objective;
- `argmin[Q] f` and `mem_constrainedArgmin_iff` from `Chap01/Definition_1_3_3`, the project
  owner for chosen constrained minimizers;
- mathlib `WithLp 2 (E₁ × E₂)` together with the canonical bridge `z ↦ z.ofLp`, the intrinsic
  `L²` product owner determined by `E₁` and `E₂`;
- mathlib/project `hessian`, applied to the frozen `y`-slice `Φ ∘ Prod.mk x`, the canonical
  Chapter 5 owner for the `yy` second-derivative data.

Best owner abstraction:
- source-facing: the self-concordance of `Φ : E₁ × E₂ → ℝ` on `interior Q`;
- core/canonical:
  `IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
    (Φ ∘ WithLp.ofLp)`,
  `partialInfProjection Q (Real.toEReal ∘ Φ)`, its real surface, and the frozen-slice Hessian
  `hessian (Φ ∘ Prod.mk x) (y x)`;
- bridge/view: the chosen minimizer branch `y`, used to evaluate the slice Hessian at the
  minimizing point.

Primitive data:
- the feasible set `Q : Set (E₁ × E₂)`;
- the objective `Φ : E₁ × E₂ → ℝ`;
- the selected minimizing branch `y : E₁ → E₂`, recorded by membership in the canonical fiberwise
  owner `argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)`.

Derived API:
- the partial-minimization objective
  `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))`;
- the frozen-slice Hessian `hessian (Φ ∘ Prod.mk x) (y x)`.

This refinement keeps the main theorem on the intrinsic product-space owner
`IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
  (Φ ∘ WithLp.ofLp)` over finite-dimensional real inner-product spaces `E₁` and `E₂`; the
`WithLp` realization is now the canonical ambient owner rather than extra raw-product instance
data, while the fiberwise data is expressed through the canonical map `Prod.mk x : E₂ → E₁ × E₂`
instead of coordinate-level set comprehensions and lambdas. -/

-- Proof sketch: combine the global lower Taylor inequality for the self-concordant function `Φ`
-- on `interior Q` with the envelope identities at the canonical fiber minimizer
-- `y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)`. The minimizing property removes the
-- `y`-gradient term, and the positive-definite frozen-slice `yy` Hessian identifies the Hessian
-- of the value
-- function with the Schur complement of the ambient Hessian, yielding the same self-concordance
-- constant for the partial minimization objective.
-- Semantic recall check: no direct mathlib semantic search hit was useful here; the local Chapter
-- 5 bridge `Proposition_5_0_19` confirms that source-faithful partial-minimization statements
-- should be phrased around a chosen attained interior minimizer branch, while the source-side
-- domain identification can be recorded separately from the canonical owner theorem.
/-- Helper for Theorem 5.1.11: the book's displayed source domain for the partial-minimization
objective. -/
abbrev partialMinimizationSourceDom (Q : Set (E₁ × E₂)) : Set E₁ :=
  {x | ((Prod.mk x) ⁻¹' Q).Nonempty ∧
    ∃ yy : E₂, yy ∈ (Prod.mk x) ⁻¹' Q ∧ (x, yy) ∈ interior Q}

/-- Helper for Theorem 5.1.11: the textbook source domain is exactly the first projection of
`interior Q`. -/
private lemma mem_partialMinimizationSourceDom_iff_exists_mem_interior
    (Q : Set (E₁ × E₂)) {x : E₁} :
    x ∈ partialMinimizationSourceDom Q ↔ ∃ yy : E₂, (x, yy) ∈ interior Q := by
  constructor
  · intro hx
    rcases hx.2 with ⟨yy, _, hxy_int⟩
    exact ⟨yy, hxy_int⟩
  · rintro ⟨yy, hxy_int⟩
    -- Any interior witness is automatically feasible and keeps the fiber nonempty.
    exact ⟨⟨yy, by simpa using interior_subset hxy_int⟩, yy,
      by simpa using interior_subset hxy_int, hxy_int⟩

/-- Helper for Theorem 5.1.11: the textbook source domain is open because it is the image of
`interior Q` under the open first projection. -/
private lemma partialMinimizationSourceDom_isOpen
    (Q : Set (E₁ × E₂)) :
    IsOpen (partialMinimizationSourceDom Q) := by
  have himage :
      partialMinimizationSourceDom Q = Prod.fst '' interior Q := by
    ext x
    constructor
    · intro hx
      rcases (mem_partialMinimizationSourceDom_iff_exists_mem_interior Q).1 hx with ⟨yy, hxy_int⟩
      exact ⟨(x, yy), hxy_int, rfl⟩
    · rintro ⟨⟨x', yy⟩, hxy_int, rfl⟩
      exact (mem_partialMinimizationSourceDom_iff_exists_mem_interior Q).2 ⟨yy, hxy_int⟩
  -- The open map theorem for `Prod.fst` transports openness of `interior Q`.
  rw [himage]
  exact isOpenMap_fst _ isOpen_interior

/-- Helper for Theorem 5.1.11: the source domain is convex because convex combinations of
interior feasible pairs stay in `interior Q`. -/
private lemma partialMinimizationSourceDom_convex
    {Q : Set (E₁ × E₂)} (hQ_convex : Convex ℝ Q) :
    Convex ℝ (partialMinimizationSourceDom Q) := by
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  rcases (mem_partialMinimizationSourceDom_iff_exists_mem_interior Q).1 hx₁ with ⟨y₁, hx₁_int⟩
  rcases (mem_partialMinimizationSourceDom_iff_exists_mem_interior Q).1 hx₂ with ⟨y₂, hx₂_int⟩
  refine (mem_partialMinimizationSourceDom_iff_exists_mem_interior Q).2 ?_
  refine ⟨a • y₁ + b • y₂, ?_⟩
  -- Work on the ambient pair and then project back to the first coordinate.
  simpa [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] using
    (hQ_convex.interior hx₁_int hx₂_int ha hb hab)

/-- Helper for Theorem 5.1.11: if the fiber infimum is attained at `yy`, then the canonical
partial infimal projection evaluates to the attained fiber value. -/
private lemma partialInfProjection_eq_argmin_eReal
    (Q : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) {x : E₁} {yy : E₂}
    (hy : yy ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    partialInfProjection Q (Real.toEReal ∘ Φ) x = (Φ (x, yy) : EReal) := by
  rcases mem_constrainedArgmin_iff.mp hy with ⟨hyy_mem, hyy_min⟩
  have himage_mem :
      ((Φ (x, yy) : ℝ) : EReal) ∈
        (Real.toEReal ∘ Φ) '' {z : E₁ × E₂ | z ∈ Q ∧ z.1 = x} := by
    refine ⟨(x, yy), ⟨hyy_mem, rfl⟩, by simp⟩
  have himage_nonempty :
      ((Real.toEReal ∘ Φ) '' {z : E₁ × E₂ | z ∈ Q ∧ z.1 = x}).Nonempty := ⟨_, himage_mem⟩
  -- The attained minimizer supplies both a witness in the image and the lower bound for every
  -- other feasible fiber value.
  rw [partialInfProjection_eq_sInf]
  refine le_antisymm ?_ ?_
  · exact sInf_le himage_mem
  · refine le_csInf himage_nonempty ?_
    rintro r ⟨⟨x', y'⟩, hz, rfl⟩
    rcases hz with ⟨hy'_mem, hx'⟩
    change x' = x at hx'
    subst x'
    have hmin : Φ (x, yy) ≤ Φ (x, y') := by
      simpa using hyy_min hy'_mem
    change (Φ (x, yy) : EReal) ≤ (Φ (x, y') : EReal)
    exact_mod_cast hmin

/-- Helper for Theorem 5.1.11: on any attained fiber minimum, the real surface of the partial
infimal projection recovers that minimizing value. -/
private lemma partialMinimizationObjective_eq_of_mem_argmin
    (Q : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) {x : E₁} {yy : E₂}
    (hy : yy ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)) x = Φ (x, yy) := by
  have hx_dom : x ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) := by
    -- The attained fiber value is finite, so `x` lies in the effective domain.
    rw [mem_extendedRealEffectiveDomain_iff, partialInfProjection_eq_argmin_eReal Q Φ hy]
    simp
  -- Once the partial infimum is known to be finite, the real-part bridge gives the value.
  apply EReal.coe_injective
  rw [coe_extendedRealRealPart hx_dom, partialInfProjection_eq_argmin_eReal Q Φ hy]

/-- Helper for Theorem 5.1.11: the ambient self-concordance hypothesis already gives convexity of
`Φ` on `interior Q` after transporting through the canonical `WithLp` product model. -/
private lemma ambientConvexOn_interior_of_selfConcordantLift
    {Q : Set (E₁ × E₂)} {Mf : NNReal} {Φ : E₁ × E₂ → ℝ}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
        (Φ ∘ WithLp.ofLp)) :
    ConvexOn ℝ (interior Q) Φ := by
  constructor
  · intro p hp q hq a b ha hb hab
    have hp' : WithLp.toLp 2 p ∈ ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) := by
      simpa using hp
    have hq' : WithLp.toLp 2 q ∈ ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) := by
      simpa using hq
    simpa [Function.comp, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] using
      hself.convexOn.1 hp' hq' ha hb hab
  · intro p hp q hq a b ha hb hab
    have hp' : WithLp.toLp 2 p ∈ ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) := by
      simpa using hp
    have hq' : WithLp.toLp 2 q ∈ ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) := by
      simpa using hq
    simpa [Function.comp, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] using
      hself.convexOn.2 hp' hq' ha hb hab

/-- Helper for Theorem 5.1.11: the reduced objective is convex on the textbook source domain by
evaluating it at the chosen minimizers and testing the midpoint against the convex combination of
those endpoint fiber values. -/
private lemma partialMinimizationObjective_convexOn_sourceDom
    {Q : Set (E₁ × E₂)} {Mf : NNReal} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hQ_convex : Convex ℝ Q)
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    ConvexOn ℝ (partialMinimizationSourceDom Q)
      (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) := by
  let f : E₁ → ℝ := extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))
  let hQint_conv : Convex ℝ (interior Q) := hQ_convex.interior
  let hΦ_conv : ConvexOn ℝ (interior Q) Φ := ambientConvexOn_interior_of_selfConcordantLift hself
  refine ⟨partialMinimizationSourceDom_convex hQ_convex, ?_⟩
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  let z : E₁ := a • x₁ + b • x₂
  let yz : E₂ := a • y x₁ + b • y x₂
  have hz : z ∈ partialMinimizationSourceDom Q :=
    (partialMinimizationSourceDom_convex hQ_convex) hx₁ hx₂ ha hb hab
  have hx₁_argmin : y x₁ ∈ argmin[(Prod.mk x₁) ⁻¹' Q] (Φ ∘ Prod.mk x₁) := hy_argmin hx₁
  have hx₂_argmin : y x₂ ∈ argmin[(Prod.mk x₂) ⁻¹' Q] (Φ ∘ Prod.mk x₂) := hy_argmin hx₂
  have hz_argmin : y z ∈ argmin[(Prod.mk z) ⁻¹' Q] (Φ ∘ Prod.mk z) := hy_argmin hz
  have hx₁_val : f x₁ = Φ (x₁, y x₁) :=
    partialMinimizationObjective_eq_of_mem_argmin Q Φ hx₁_argmin
  have hx₂_val : f x₂ = Φ (x₂, y x₂) :=
    partialMinimizationObjective_eq_of_mem_argmin Q Φ hx₂_argmin
  have hz_val : f z = Φ (z, y z) :=
    partialMinimizationObjective_eq_of_mem_argmin Q Φ hz_argmin
  have hz_pair_mem : (z, yz) ∈ interior Q := by
    -- The convex combination of the endpoint interior minimizers stays in `interior Q`.
    exact hQint_conv (hy_mem_interior hx₁) (hy_mem_interior hx₂) ha hb hab
  have hz_compare : Φ (z, y z) ≤ Φ (z, yz) := by
    rcases mem_constrainedArgmin_iff.mp hz_argmin with ⟨_, hz_min⟩
    simpa [z, yz] using hz_min (by simpa using interior_subset hz_pair_mem)
  have hconv_value :
      Φ (z, yz) ≤ a * Φ (x₁, y x₁) + b * Φ (x₂, y x₂) := by
    -- Apply Jensen to the ambient convex objective at the two interior minimizing pairs.
    simpa [z, yz, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] using
      hΦ_conv.2 (hy_mem_interior hx₁) (hy_mem_interior hx₂) ha hb hab
  calc
    f z = Φ (z, y z) := hz_val
    _ ≤ Φ (z, yz) := hz_compare
    _ ≤ a * Φ (x₁, y x₁) + b * Φ (x₂, y x₂) := hconv_value
    _ = a * f x₁ + b * f x₂ := by rw [hx₁_val, hx₂_val]

/-- Helper for Theorem 5.1.11: the ambient lifted product objective used to compare the canonical
`WithLp` gradients with the frozen coordinate slices. -/
private abbrev partialMinimizationLift
    (Φ : E₁ × E₂ → ℝ) : Z → ℝ :=
  Φ ∘ (WithLp.ofLp : Z → E₁ × E₂)

/-- Helper for Theorem 5.1.11: at a `C¹` point, the `y`-component of the ambient `WithLp`
gradient agrees with the gradient of the frozen `y`-slice. -/
private lemma partialMinimizationYGradient_eq_frozenYGradient
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 1 Φ (x, yy)) :
    WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy))) =
      ∇ (Φ ∘ Prod.mk x) yy := by
  have hLiftDiff :
      DifferentiableAt ℝ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) := by
    -- Only first-order differentiability is needed to compare the two gradient presentations.
    simpa [partialMinimizationLift, Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp (WithLp.toLp 2 (x, yy))
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂ : Z ≃L[ℝ] E₁ × E₂) :
          Z →L[ℝ] E₁ × E₂)).hasFDerivAt.differentiableAt)
  have hAmbient :
      HasGradientAt (Φ ∘ Prod.mk x)
        (WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)))) yy := by
    rw [hasGradientAt_iff_hasFDerivAt]
    -- Rewrite the derivative of the lifted objective along the right-coordinate inclusion.
    convert
      (hLiftDiff.hasGradientAt.hasFDerivAt.comp yy
        (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.hasFDerivAt.comp yy
          (hasFDerivAt_prodMk_right x yy)))) using 1
    ext k
    simp [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      partialMinimizationLift, WithLp.prod_inner_apply]
  have hSliceDiff :
      DifferentiableAt ℝ (Φ ∘ Prod.mk x) yy := by
    -- Freeze the first coordinate and differentiate in the `y`-direction.
    simpa [Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp yy
        (hasFDerivAt_prodMk_right x yy).differentiableAt
  -- Both vectors are gradients of the same frozen slice at the same point.
  exact hAmbient.unique hSliceDiff.hasGradientAt

/-- Helper for Theorem 5.1.11: at a `C¹` point, the `x`-component of the ambient `WithLp`
gradient agrees with the gradient of the frozen `x`-slice. -/
private lemma partialMinimizationXGradient_eq_frozenXGradient
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 1 Φ (x, yy)) :
    WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy))) =
      ∇ (fun u : E₁ ↦ Φ (u, yy)) x := by
  have hLiftDiff :
      DifferentiableAt ℝ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) := by
    -- Only first-order differentiability is needed to compare the two gradient presentations.
    simpa [partialMinimizationLift, Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp (WithLp.toLp 2 (x, yy))
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂ : Z ≃L[ℝ] E₁ × E₂) :
          Z →L[ℝ] E₁ × E₂)).hasFDerivAt.differentiableAt)
  have hAmbient :
      HasGradientAt (fun u : E₁ ↦ Φ (u, yy))
        (WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)))) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    -- Rewrite the derivative of the lifted objective along the left-coordinate inclusion.
    convert
      (hLiftDiff.hasGradientAt.hasFDerivAt.comp x
        (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left x yy)))) using 1
    ext k
    simp [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      partialMinimizationLift, WithLp.prod_inner_apply]
  have hSliceDiff :
      DifferentiableAt ℝ (fun u : E₁ ↦ Φ (u, yy)) x := by
    -- Freeze the second coordinate and differentiate in the `x`-direction.
    simpa [Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp x
        (hasFDerivAt_prodMk_left x yy).differentiableAt
  -- Both vectors are gradients of the same frozen slice at the same point.
  exact hAmbient.unique hSliceDiff.hasGradientAt

/-- Helper for Theorem 5.1.11: the implicit stationary-map equation already gives the vanishing
Fréchet derivative of the frozen `y`-slice. -/
private lemma frozenYSlice_hasFDerivAtZero_of_mem_argmin_interior
    (Q : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) (u : E₁) {yy : E₂}
    (hPhi : ContDiffAt ℝ 1 Φ (u, yy))
    (huy_mem_interior : (u, yy) ∈ interior Q)
    (hyy_argmin :
      yy ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u)) :
    HasFDerivAt (Φ ∘ Prod.mk u) (0 : E₂ →L[ℝ] ℝ) yy := by
  rcases mem_constrainedArgmin_iff.mp hyy_argmin with ⟨_, hyy_min⟩
  have hPhi_diff : DifferentiableAt ℝ Φ (u, yy) := hPhi.differentiableAt (by norm_num)
  have hQ_nhds : Q ∈ nhds (u, yy) := by
    -- Interior feasibility upgrades the constrained fiber minimum to an ambient local minimum.
    exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior huy_mem_interior) interior_subset
  have hfiber_nhds : (Prod.mk u) ⁻¹' Q ∈ nhds yy := by
    exact (Continuous.prodMk continuous_const continuous_id).continuousAt.preimage_mem_nhds hQ_nhds
  have hlocal : IsLocalMin (Φ ∘ Prod.mk u) yy := hyy_min.isLocalMin hfiber_nhds
  have hslice :
      HasFDerivAt (Φ ∘ Prod.mk u) (fderiv ℝ (Φ ∘ Prod.mk u) yy) yy :=
    (hPhi_diff.comp yy (hasFDerivAt_prodMk_right u yy).differentiableAt).hasFDerivAt
  have hzero : fderiv ℝ (Φ ∘ Prod.mk u) yy = 0 := hlocal.hasFDerivAt_eq_zero hslice
  -- Route correction: use Fermat directly on the frozen slice before comparing with the
  -- ambient stationary map.
  simpa [hzero] using hslice

/-- Helper for Theorem 5.1.11: an interior fiber minimizer is a stationary point of the ambient
`y`-gradient map. -/
private lemma frozenYSlice_hasFDerivAtZero_of_stationaryMap_eq_zero
    (Φ : E₁ × E₂ → ℝ) (u : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 1 Φ (u, yy))
    (hStationary :
      WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, yy))) = 0) :
    HasFDerivAt (Φ ∘ Prod.mk u) (0 : E₂ →L[ℝ] ℝ) yy := by
  have hSliceDiff :
      DifferentiableAt ℝ (Φ ∘ Prod.mk u) yy := by
    -- The frozen slice inherits differentiability from the ambient `C¹` objective.
    simpa [Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp yy
        (hasFDerivAt_prodMk_right u yy).differentiableAt
  have hGradZero : ∇ (Φ ∘ Prod.mk u) yy = 0 := by
    -- Route correction: read the stationary map as the actual frozen-slice gradient first.
    calc
      ∇ (Φ ∘ Prod.mk u) yy
          = WithLp.sndL 2 ℝ E₁ E₂
              (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, yy))) := by
                symm
                exact partialMinimizationYGradient_eq_frozenYGradient Φ u yy hPhi
      _ = 0 := hStationary
  have hGradAtZero : HasGradientAt (Φ ∘ Prod.mk u) 0 yy := by
    simpa [hGradZero] using hSliceDiff.hasGradientAt
  simpa using hGradAtZero.hasFDerivAt

/-- Helper for Theorem 5.1.11: an interior stationary point of the frozen `y`-slice has the same
fiber value as the selected minimizer. -/
private lemma stationaryInterior_value_eq_selectedMinimizer
    {Q : Set (E₁ × E₂)} {Mf : NNReal} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    {u : E₁} (hu : u ∈ partialMinimizationSourceDom Q) {yy : E₂}
    (hyy_mem_interior : (u, yy) ∈ interior Q)
    (hyy_stationary : HasFDerivAt (Φ ∘ Prod.mk u) (0 : E₂ →L[ℝ] ℝ) yy) :
    Φ (u, yy) = Φ (u, y u) := by
  let γ : ℝ →ᵃ[ℝ] (E₁ × E₂) := AffineMap.lineMap (u, yy) (u, y u)
  let σ : ℝ →ᵃ[ℝ] E₂ := AffineMap.lineMap yy (y u)
  let φ : ℝ → ℝ := fun t ↦ Φ (γ t)
  let hΦ_conv : ConvexOn ℝ (interior Q) Φ :=
    ambientConvexOn_interior_of_selfConcordantLift hself
  have hγ_maps : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (interior Q) := by
    -- Every point on the segment between the two interior fiber points stays in `interior Q`.
    exact hΦ_conv.1.mapsTo_lineMap hyy_mem_interior (hy_mem_interior hu)
  have hφ_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
    -- Restrict the ambient convex objective to the line segment joining `yy` to the chosen
    -- minimizer in the fixed `u`-fiber.
    refine (hΦ_conv.comp_affineMap γ).subset hγ_maps (convex_Icc (0 : ℝ) 1)
  have hγ_zero : γ 0 = (u, yy) := by
    simp [γ]
  have hγ_one : γ 1 = (u, y u) := by
    simp [γ]
  have hσ_deriv : HasDerivAt (fun t : ℝ ↦ σ t) (y u - yy) 0 := by
    simpa [σ] using AffineMap.hasDerivAt_lineMap (a := yy) (b := y u) (x := (0 : ℝ))
  have hφ_deriv_zero : HasDerivAt φ 0 0 := by
    -- Route correction: differentiate the frozen `y`-slice along the scalar segment instead of
    -- trying to identify an argmin branch first.
    have hσ_zero : σ 0 = yy := by
      simp [σ]
    have hyy_stationary' : HasFDerivAt (Φ ∘ Prod.mk u) (0 : E₂ →L[ℝ] ℝ) (σ 0) := by
      simpa [hσ_zero] using hyy_stationary
    have hcomp :
        HasDerivAt (((Φ ∘ Prod.mk u) ∘ fun t : ℝ ↦ σ t)) 0 0 :=
      by simpa using hyy_stationary'.comp_hasDerivAt (0 : ℝ) hσ_deriv
    convert hcomp using 1
    ext t
    have hfst : (1 - t : ℝ) • u + t • u = u := by
      calc
        (1 - t : ℝ) • u + t • u = ((1 - t : ℝ) + t) • u := by
          rw [← add_smul]
        _ = (1 : ℝ) • u := by
          congr 1
          ring
        _ = u := by simp
    simp [φ, γ, σ, AffineMap.lineMap_apply_module, hfst]
  have hslope_nonneg :
      0 ≤ slope φ 0 1 := by
    simpa [hφ_deriv_zero.deriv] using
      hφ_conv.deriv_le_slope
        (by simp)
        (by simp)
        zero_lt_one
        hφ_deriv_zero.differentiableAt
  have hvalue_le :
      Φ (u, yy) ≤ Φ (u, y u) := by
    -- The secant slope from `0` to `1` is nonnegative because the derivative at `0` vanishes.
    simpa [φ, hγ_zero, hγ_one, slope] using hslope_nonneg
  have hvalue_ge :
      Φ (u, y u) ≤ Φ (u, yy) := by
    -- The chosen branch is already a fiberwise minimizer on the displayed source domain.
    exact (mem_constrainedArgmin_iff.mp (hy_argmin hu)).2 (by simpa using interior_subset hyy_mem_interior)
  exact le_antisymm hvalue_le hvalue_ge

/-- Source-domain bridge for Theorem 5.1.11: if the fiber infimum is attained at the chosen
interior minimizer on every textbook-domain point, then the book's displayed domain agrees with
the canonical effective domain `dom (partialInfProjection Q (Real.toEReal ∘ Φ))`. -/
theorem partialMinimizationSourceDom_eq_dom_of_attainedInteriorArgmin
    {Q : Set (E₁ × E₂)} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) → (x, y x) ∈ interior Q)
    (hy_argmin_dom :
      ∀ ⦃x : E₁⦄, x ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_argmin_source :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    partialMinimizationSourceDom Q = dom (partialInfProjection Q (Real.toEReal ∘ Φ)) := by
  ext x
  constructor
  · intro hx
    have hyx : y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) := hy_argmin_source hx
    -- Read the attained fiber minimum back as a finite extended-real value.
    rw [mem_extendedRealEffectiveDomain_iff, partialInfProjection_eq_argmin_eReal Q Φ hyx]
    simp
  · intro hx
    have hyx : y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) := hy_argmin_dom hx
    rcases mem_constrainedArgmin_iff.mp hyx with ⟨hyx_mem, _⟩
    -- The chosen interior minimizer witnesses both fiber nonemptiness and the textbook domain
    -- condition.
    exact ⟨⟨y x, hyx_mem⟩, y x, hyx_mem, hy_mem_interior hx⟩

/-- Helper for Theorem 5.1.11: strict positivity of the frozen `yy` Hessian quadratic form makes
that Hessian invertible as a continuous linear map. -/
private lemma yyHessian_isInvertible_of_mem_sourceDom
    {Q : Set (E₁ × E₂)} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v))
    {x : E₁} (hx : x ∈ partialMinimizationSourceDom Q) :
    (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible := by
  let H : E₂ →L[ℝ] E₂ := hessian (Φ ∘ Prod.mk x) (y x)
  have hHinj : Function.Injective H := by
    intro v w hvw
    by_contra hvw_ne
    have hdiff_ne : v - w ≠ 0 := sub_ne_zero.mpr hvw_ne
    have hpos : 0 < inner ℝ (v - w) (H (v - w)) := hyy_pos hx (v - w) hdiff_ne
    have hzero : H (v - w) = 0 := by
      simpa [H, map_sub, hvw]
    have hinner_zero : inner ℝ (v - w) (H (v - w)) = 0 := by
      simp [hzero]
    linarith
  have hHsurj : Function.Surjective H := LinearMap.surjective_of_injective hHinj
  -- Finite-dimensional injective endomorphisms are bijective, hence continuous linear
  -- equivalences.
  letI : CompleteSpace E₂ := FiniteDimensional.complete ℝ E₂
  refine ⟨ContinuousLinearEquiv.ofBijective H (LinearMap.ker_eq_bot.mpr hHinj)
    (LinearMap.range_eq_top.mpr hHsurj), ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective H (LinearMap.ker_eq_bot.mpr hHinj)
    (LinearMap.range_eq_top.mpr hHsurj)

/-- Helper for Theorem 5.1.11: the lifted `L²` product objective is `C³` at the canonical product
point whenever the raw objective is `C³` at the corresponding pair. -/
private lemma partialMinimizationLift_contDiffAt
    {n : WithTop ℕ∞} (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ n Φ (x, yy)) :
    ContDiffAt ℝ n (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) := by
  -- The `WithLp` lift is just `Φ` composed with the fixed product equivalence.
  simpa [partialMinimizationLift, Function.comp] using
    hPhi.comp (WithLp.toLp 2 (x, yy))
      ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂ : Z ≃L[ℝ] E₁ × E₂) :
          Z →L[ℝ] E₁ × E₂)).contDiff.contDiffAt)

/-- Helper for Theorem 5.1.11: a `C²` lifted objective has a differentiable ambient gradient at
the base point. -/
private lemma partialMinimizationLift_gradient_differentiableAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, yy)) :
    DifferentiableAt ℝ (∇ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
  let D : StrongDual ℝ Z →L[ℝ] Z :=
    (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hLift : ContDiffAt ℝ 2 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) :=
    partialMinimizationLift_contDiffAt Φ x yy hPhi
  have hfderiv_C1 :
      ContDiffAt ℝ 1 (fderiv ℝ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
    -- Differentiating once leaves a `C¹` field of Fréchet derivatives.
    exact hLift.fderiv_right (by norm_num)
  have hGrad_C1 :
      ContDiffAt ℝ 1 (∇ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
    -- The gradient is the Riesz transport of `fderiv`, so it inherits the same local smoothness.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp (WithLp.toLp 2 (x, yy)) hfderiv_C1
  -- A `C¹` map is differentiable at the base point.
  exact hGrad_C1.differentiableAt (by norm_num)

/-- Helper for Theorem 5.1.11: the ambient Hessian block operator on the `WithLp` product chart.
It packages the mixed second derivatives needed by the implicit-branch argument. -/
private abbrev partialMinimizationAmbientHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂) : E₁ × E₂ →L[ℝ] Z :=
  hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.toContinuousLinearMap

/-- Helper for Theorem 5.1.11: the `xx` block of the ambient Hessian in product coordinates. -/
private abbrev partialMinimizationXXHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂) : E₁ →L[ℝ] E₁ :=
  WithLp.fstL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x yy ∘L inl ℝ E₁ E₂

/-- Helper for Theorem 5.1.11: the `xy` block of the ambient Hessian in product coordinates. -/
private abbrev partialMinimizationXYHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂) : E₂ →L[ℝ] E₁ :=
  WithLp.fstL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x yy ∘L inr ℝ E₁ E₂

/-- Helper for Theorem 5.1.11: the `yx` block of the ambient Hessian in product coordinates. -/
private abbrev partialMinimizationYXHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂) : E₁ →L[ℝ] E₂ :=
  WithLp.sndL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x yy ∘L inl ℝ E₁ E₂

/-- Helper for Theorem 5.1.11: differentiating the ambient `y`-gradient of the lifted objective
produces the `y`-component of the canonical ambient Hessian block operator. -/
private lemma partialMinimizationYGradient_hasFDerivAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, yy)) :
    HasFDerivAt
      (fun z : E₁ × E₂ ↦
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z)))
      ((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x yy))
      (x, yy) := by
  have hGrad :
      HasFDerivAt
        (fun z : Z ↦ ∇ (partialMinimizationLift Φ) z)
        (hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)))
        (WithLp.toLp 2 (x, yy)) := by
    -- The Hessian is, by definition, the derivative of the ambient gradient.
    simpa [hessian] using
      (partialMinimizationLift_gradient_differentiableAt Φ x yy hPhi).hasFDerivAt
  have hToLp :
      HasFDerivAt
        (fun z : E₁ × E₂ ↦ ∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))
        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy))).comp
          ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm : (E₁ × E₂) →L[ℝ] Z))
        (x, yy) := by
    -- Rewrite the derivative through the fixed `WithLp` chart.
    simpa [Function.comp] using
      hGrad.comp (x, yy)
        (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
          (E₁ × E₂) →L[ℝ] Z).hasFDerivAt)
  -- Project to the `y`-component after differentiating the ambient gradient field.
  simpa [partialMinimizationAmbientHessian, Function.comp] using
    (WithLp.sndL 2 ℝ E₁ E₂).hasFDerivAt.comp (x, yy) hToLp

/-- Helper for Theorem 5.1.11: the stationary map
`(u, yy) ↦ ∇ᵧ Φ(u, yy)` is `C²` at a `C³` point. This is the extra regularity needed to obtain a
`C²` implicit minimizer branch. -/
private lemma partialMinimizationYStationaryMap_contDiffAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 3 Φ (x, yy)) :
    ContDiffAt ℝ 2
      (fun z : E₁ × E₂ ↦
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z)))
      (x, yy) := by
  let D : StrongDual ℝ Z →L[ℝ] Z :=
    (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hLift : ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) :=
    partialMinimizationLift_contDiffAt Φ x yy hPhi
  have hfderiv_C2 :
      ContDiffAt ℝ 2 (fderiv ℝ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
    -- Differentiating the lifted objective once leaves a `C²` field of Fréchet derivatives.
    exact hLift.fderiv_right (by norm_num)
  have hGrad_C2 :
      ContDiffAt ℝ 2 (∇ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
    -- The gradient is the Riesz transport of `fderiv`, so it inherits the same local smoothness.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp (WithLp.toLp 2 (x, yy)) hfderiv_C2
  -- Compose the ambient gradient with the `WithLp` chart and project to the `y`-component.
  simpa [Function.comp] using
    (WithLp.sndL 2 ℝ E₁ E₂).contDiff.contDiffAt.comp (x, yy)
      (hGrad_C2.comp (x, yy)
        (((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z) : (E₁ × E₂) →L[ℝ] Z)).contDiff.contDiffAt))

/-- Helper for Theorem 5.1.11: the ambient `x`-gradient map
`(u, yy) ↦ ∇ₓ Φ(u, yy)` is `C²` at a `C³` point. This is the regularity input for the reduced
gradient field along the implicit stationary branch. -/
private lemma partialMinimizationXGradientMap_contDiffAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 3 Φ (x, yy)) :
    ContDiffAt ℝ 2
      (fun z : E₁ × E₂ ↦
        WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z)))
      (x, yy) := by
  let D : StrongDual ℝ Z →L[ℝ] Z :=
    (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hLift : ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) :=
    partialMinimizationLift_contDiffAt Φ x yy hPhi
  have hfderiv_C2 :
      ContDiffAt ℝ 2 (fderiv ℝ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
    -- Differentiating the lifted objective once leaves a `C²` field of Fréchet derivatives.
    exact hLift.fderiv_right (by norm_num)
  have hGrad_C2 :
      ContDiffAt ℝ 2 (∇ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
    -- The gradient is the Riesz transport of `fderiv`, so it inherits the same local smoothness.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp (WithLp.toLp 2 (x, yy)) hfderiv_C2
  -- Compose the ambient gradient with the `WithLp` chart and project to the `x`-component.
  simpa [Function.comp] using
    (WithLp.fstL 2 ℝ E₁ E₂).contDiff.contDiffAt.comp (x, yy)
      (hGrad_C2.comp (x, yy)
        (((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z) : (E₁ × E₂) →L[ℝ] Z)).contDiff.contDiffAt))

/-- Helper for Theorem 5.1.11: the frozen `y`-gradient is differentiable at a `C²` point, and its
derivative is the frozen-slice Hessian. -/
private lemma frozenYGradient_hasFDerivAt_hessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, yy)) :
    HasFDerivAt (fun z : E₂ ↦ ∇ (Φ ∘ Prod.mk x) z) (hessian (Φ ∘ Prod.mk x) yy) yy := by
  let D : StrongDual ℝ E₂ →L[ℝ] E₂ :=
    (InnerProductSpace.toDual ℝ E₂).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hSlice : ContDiffAt ℝ 2 (Φ ∘ Prod.mk x) yy := by
    have hProdMkRight : ContDiffAt ℝ 2 (Prod.mk x : E₂ → E₁ × E₂) yy := by
      fun_prop
    simpa [Function.comp] using hPhi.comp yy hProdMkRight
  have hfderiv_C1 :
      ContDiffAt ℝ 1 (fderiv ℝ (Φ ∘ Prod.mk x)) yy := by
    -- Differentiating the frozen slice once leaves a `C¹` derivative field.
    exact hSlice.fderiv_right (by norm_num)
  have hGrad_C1 : ContDiffAt ℝ 1 (∇ (Φ ∘ Prod.mk x)) yy := by
    -- Transport the `C¹` regularity of `fderiv` through the Riesz isomorphism.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp yy hfderiv_C1
  -- The Hessian is, by definition, the derivative of the frozen-slice gradient.
  simpa [hessian] using (hGrad_C1.differentiableAt (by norm_num)).hasFDerivAt

/-- Helper for Theorem 5.1.11: restricting the ambient stationary-map derivative to the vertical
`y`-direction recovers the frozen-slice `yy` Hessian block. -/
private lemma partialMinimizationYGradient_comp_inr_eq_yyHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, yy)) :
    (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x yy)).comp
      (inr ℝ E₁ E₂)) = hessian (Φ ∘ Prod.mk x) yy := by
  have hAmbientDeriv :
      HasFDerivAt
        (fun z : E₂ ↦
          WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, z))))
        (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x yy)).comp
          (inr ℝ E₁ E₂))
        yy := by
    -- Freeze `x` and differentiate the ambient stationary map only in the `y`-direction.
    simpa [Function.comp] using
      (partialMinimizationYGradient_hasFDerivAt Φ x yy hPhi).comp yy
        (hasFDerivAt_prodMk_right x yy)
  have hFrozenDeriv :
      HasFDerivAt
        (fun z : E₂ ↦ ∇ (Φ ∘ Prod.mk x) z)
        (hessian (Φ ∘ Prod.mk x) yy)
        yy :=
    frozenYGradient_hasFDerivAt_hessian Φ x yy hPhi
  have hEventEq :
      (fun z : E₂ ↦
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, z)))) =ᶠ[nhds yy]
          fun z : E₂ ↦ ∇ (Φ ∘ Prod.mk x) z := by
    -- Near a `C²` point, the ambient and frozen `y`-gradient presentations agree on the vertical
    -- line through `x`.
    exact
      (show (fun z : E₁ × E₂ ↦
          WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))) =ᶠ[
            nhds (x, yy)] fun z : E₁ × E₂ ↦ ∇ (Φ ∘ Prod.mk z.1) z.2 from
          by
            rcases (hPhi.contDiffOn (m := 1) (by norm_num) (by simp)) with ⟨u, hu_nhds, hContU⟩
            rcases mem_nhds_iff.mp hu_nhds with ⟨v, hv_sub, hv_open, hv_mem⟩
            have hContV : ContDiffOn ℝ 1 Φ v := hContU.mono hv_sub
            filter_upwards [hv_open.mem_nhds hv_mem] with z hz
            exact partialMinimizationYGradient_eq_frozenYGradient Φ z.1 z.2
              (hContV.contDiffAt (hv_open.mem_nhds hz))).comp_tendsto
        ((Continuous.prodMk continuous_const continuous_id).continuousAt.tendsto)
  have hFrozenDeriv' :
      HasFDerivAt
        (fun z : E₂ ↦
          WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, z))))
        (hessian (Φ ∘ Prod.mk x) yy)
        yy := by
    -- Transfer the frozen-slice Hessian formula through the local gradient equality above.
    exact hFrozenDeriv.congr_of_eventuallyEq hEventEq
  exact hAmbientDeriv.unique hFrozenDeriv'

/-- Helper for Theorem 5.1.11: differentiating the ambient `x`-gradient along a branch
`u ↦ (u, b u)` yields the canonical `XX + XY ∘ Db` block formula. -/
private lemma partialMinimizationXGradientAlongBranch_hasFDerivAt
    {b : E₁ → E₂} {b' : E₁ →L[ℝ] E₂}
    (Φ : E₁ × E₂ → ℝ) (x : E₁)
    (hPhi : ContDiffAt ℝ 2 Φ (x, b x))
    (hb : HasFDerivAt b b' x) :
    HasFDerivAt
      (fun u ↦
        WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, b u))))
      (partialMinimizationXXHessian Φ x (b x) +
        (partialMinimizationXYHessian Φ x (b x)).comp b')
      x := by
  have hGrad :
      HasFDerivAt
        (fun z : E₁ × E₂ ↦
          WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z)))
        ((WithLp.fstL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (b x)))
        (x, b x) := by
    have hAmbient :
        HasFDerivAt
          (fun z : Z ↦ ∇ (partialMinimizationLift Φ) z)
          (hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, b x)))
          (WithLp.toLp 2 (x, b x)) := by
      -- The Hessian is, by definition, the derivative of the ambient gradient.
      simpa [hessian] using
        (partialMinimizationLift_gradient_differentiableAt Φ x (b x) hPhi).hasFDerivAt
    have hToLp :
        HasFDerivAt
          (fun z : E₁ × E₂ ↦ ∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, b x))).comp
            ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm : (E₁ × E₂) →L[ℝ] Z))
          (x, b x) := by
      -- Rewrite the derivative through the fixed `WithLp` chart before projecting.
      simpa [Function.comp] using
        hAmbient.comp (x, b x)
          (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) →L[ℝ] Z).hasFDerivAt)
    simpa [partialMinimizationAmbientHessian, Function.comp] using
      (WithLp.fstL 2 ℝ E₁ E₂).hasFDerivAt.comp (x, b x) hToLp
  have hGraph :
      HasFDerivAt (fun u : E₁ ↦ (u, b u)) ((1 : E₁ →L[ℝ] E₁).prod b') x := by
    -- Differentiate the graph map of the branch.
    simpa using (hasFDerivAt_id x).prodMk hb
  have hComp := hGrad.comp x hGraph
  -- Split the graph derivative into its horizontal and vertical pieces.
  refine hComp.congr_fderiv ?_
  ext h
  have hsplit :
      ((1 : E₁ →L[ℝ] E₁).prod b') h =
        (inl ℝ E₁ E₂) h + (inr ℝ E₁ E₂) (b' h) := by
    ext <;> simp
  have htoLp_split :
      WithLp.toLp 2 (h, b' h) = WithLp.toLp 2 (h, 0) + WithLp.toLp 2 (0, b' h) := by
    simpa using
      ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.map_add (h, 0) (0, b' h))
  simpa [partialMinimizationXXHessian, partialMinimizationXYHessian, hsplit, htoLp_split, map_add,
    ContinuousLinearMap.comp_apply]

/-- Helper for Theorem 5.1.11: near any source-domain point, the stationary equation admits a
canonical implicit `C²` branch through the selected minimizer. -/
private lemma implicitStationaryBranchPacket_of_mem_sourceDom
    {Q : Set (E₁ × E₂)} {Mf : NNReal} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v))
    {x : E₁} (hx : x ∈ partialMinimizationSourceDom Q) :
    ∃ s : Set E₁, ∃ ψ : E₁ → E₂,
      IsOpen s ∧ x ∈ s ∧ ψ x = y x ∧ ContDiffOn ℝ 2 ψ s ∧
      HasStrictFDerivAt ψ (partialMinimizerImplicitFDeriv Φ x (y x)) x ∧
      ∀ u ∈ s, (u, ψ u) ∈ interior Q ∧
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0 := by
  let F : E₁ × E₂ → E₂ := fun z ↦
    WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))
  have hLift :
      ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)) := by
    -- The ambient self-concordant owner already supplies the local `C³` regularity of `Φ`.
    simpa [partialMinimizationLift] using
      hself.contDiffOn.contDiffAt
        (by simpa using hself.isOpen_domain.mem_nhds (by simpa using hy_mem_interior hx))
  have hPhi :
      ContDiffAt ℝ 3 Φ (x, y x) := by
    -- Pull the lifted regularity back through the fixed `WithLp` product equivalence.
    simpa [partialMinimizationLift, Function.comp] using
      hLift.comp (x, y x)
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
  have hF_cont :
      ContDiffAt ℝ 2 F (x, y x) := by
    simpa [F] using partialMinimizationYStationaryMap_contDiffAt Φ x (y x) hPhi
  have hF_deriv :
      HasFDerivAt F ((WithLp.sndL 2 ℝ E₁ E₂).comp
        (partialMinimizationAmbientHessian Φ x (y x))) (x, y x) := by
    simpa [F] using partialMinimizationYGradient_hasFDerivAt Φ x (y x) (hPhi.of_le (by norm_num))
  have hF_inr :
      fderiv ℝ F (x, y x) ∘L inr ℝ E₁ E₂ = hessian (Φ ∘ Prod.mk x) (y x) := by
    rw [hF_deriv.fderiv]
    exact partialMinimizationYGradient_comp_inr_eq_yyHessian Φ x (y x) (hPhi.of_le (by norm_num))
  have hF_inl :
      fderiv ℝ F (x, y x) ∘L inl ℝ E₁ E₂ = partialMinimizationYXHessian Φ x (y x) := by
    rw [hF_deriv.fderiv]
    rfl
  have hIf2 : (fderiv ℝ F (x, y x) ∘L inr ℝ E₁ E₂).IsInvertible := by
    rw [hF_inr]
    exact yyHessian_isInvertible_of_mem_sourceDom (Q := Q) (Φ := Φ) (y := y) hyy_pos hx
  have hbase_zero :
      F (x, y x) = 0 := by
    have hPhi1 : ContDiffAt ℝ 1 Φ (x, y x) := hPhi.of_le (by norm_num)
    have hzero_deriv :
        HasFDerivAt (Φ ∘ Prod.mk x) (0 : E₂ →L[ℝ] ℝ) (y x) :=
      frozenYSlice_hasFDerivAtZero_of_mem_argmin_interior
        Q Φ x hPhi1 (hy_mem_interior hx) (hy_argmin hx)
    have hslice_diff :
        DifferentiableAt ℝ (Φ ∘ Prod.mk x) (y x) := by
      simpa [Function.comp] using
        (hPhi1.differentiableAt (by norm_num)).comp (y x)
          (hasFDerivAt_prodMk_right x (y x)).differentiableAt
    have hgrad_zero : ∇ (Φ ∘ Prod.mk x) (y x) = 0 := by
      simpa using (hzero_deriv.hasGradientAt.unique hslice_diff.hasGradientAt).symm
    -- Compare the stationary map with the frozen-slice gradient at the base point.
    calc
      F (x, y x) = ∇ (Φ ∘ Prod.mk x) (y x) := by
        simpa [F] using partialMinimizationYGradient_eq_frozenYGradient Φ x (y x) (hPhi.of_le (by norm_num))
      _ = 0 := hgrad_zero
  let ψ : E₁ → E₂ := hF_cont.implicitFunction (pn := by norm_num) hIf2
  have hψ_self : ψ x = y x := by
    -- The canonical implicit branch passes through the selected minimizer at the base point.
    simpa [ψ] using hF_cont.implicitFunction_apply_self (pn := by norm_num) hIf2
  have hψ_deriv :
      HasStrictFDerivAt ψ (partialMinimizerImplicitFDeriv Φ x (y x)) x := by
    simpa [ψ, partialMinimizerImplicitFDeriv, hF_inr, hF_inl] using
      (hF_cont.hasStrictFDerivAt_implicitFunction (pn := by norm_num) hIf2)
  have hψ_cont : ContDiffAt ℝ 2 ψ x := by
    simpa [ψ] using hF_cont.contDiffAt_implicitFunction (pn := by norm_num) hIf2
  have hψ_graph_tendsto :
      Filter.Tendsto (fun u ↦ (u, ψ u)) (nhds x) (nhds (x, y x)) := by
    simpa [hψ_self, nhds_prod_eq] using continuousAt_id.tendsto.prodMk hψ_cont.continuousAt.tendsto
  have hψ_mem_interior :
      ∀ᶠ u in nhds x, (u, ψ u) ∈ interior Q := by
    exact hψ_graph_tendsto.eventually (IsOpen.mem_nhds isOpen_interior (hy_mem_interior hx))
  have hψ_stationary :
      ∀ᶠ u in nhds x,
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0 := by
    filter_upwards [hF_cont.eventually_apply_implicitFunction (pn := by norm_num) hIf2] with u hu
    have hu_zero : F (u, ψ u) = 0 := by
      exact hu.trans hbase_zero
    simpa [F] using hu_zero
  rcases hψ_cont.contDiffOn (m := 2) le_rfl (by simp) with ⟨t, ht_nhds, hψOn_t⟩
  have hcore :
      ∀ᶠ u in nhds x,
        u ∈ t ∧ (u, ψ u) ∈ interior Q ∧
          WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0 := by
    filter_upwards [ht_nhds, hψ_mem_interior, hψ_stationary] with u hu_t hu_int hu_stat
    exact ⟨hu_t, hu_int, hu_stat⟩
  rcases mem_nhds_iff.mp hcore with ⟨s, hs_sub, hs_open, hsx⟩
  refine ⟨s, ψ, hs_open, hsx, hψ_self, ?_, hψ_deriv, ?_⟩
  · -- Restrict the implicit branch regularity to the honest open neighborhood `s`.
    exact hψOn_t.mono fun u hu ↦ (hs_sub hu).1
  · intro u hu
    -- Package the local interior and stationary data that will later be transported to `y`.
    exact ⟨(hs_sub hu).2.1, (hs_sub hu).2.2⟩

/-- Helper for Theorem 5.1.11: on the implicit stationary branch, interior stationarity transports
to the actual selected minimizer branch and to the reduced objective value. -/
private lemma selectedMinimizerTransport_onImplicitBranch
    {Q : Set (E₁ × E₂)} {Mf : NNReal} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    {s : Set E₁} {ψ : E₁ → E₂}
    (hpacket :
      ∀ u ∈ s, (u, ψ u) ∈ interior Q ∧
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0) :
    ∀ u ∈ s,
      u ∈ partialMinimizationSourceDom Q ∧
        ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) ∧
        ψ u = y u ∧
        extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)) u = Φ (u, ψ u) := by
  intro u hu
  rcases hpacket u hu with ⟨hu_int, hu_stat⟩
  have hu_source : u ∈ partialMinimizationSourceDom Q :=
    (mem_partialMinimizationSourceDom_iff_exists_mem_interior Q).2 ⟨ψ u, hu_int⟩
  have hLift_u :
      ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u)) := by
    simpa [partialMinimizationLift] using
      hself.contDiffOn.contDiffAt
        (by simpa using hself.isOpen_domain.mem_nhds (by simpa using hu_int))
  have hPhi_u :
      ContDiffAt ℝ 3 Φ (u, ψ u) := by
    -- Pull the ambient `C³` regularity back to the raw pair on the branch.
    simpa [partialMinimizationLift, Function.comp] using
      hLift_u.comp (u, ψ u)
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
  have hzero_deriv :
      HasFDerivAt (Φ ∘ Prod.mk u) (0 : E₂ →L[ℝ] ℝ) (ψ u) :=
    frozenYSlice_hasFDerivAtZero_of_stationaryMap_eq_zero Φ u (ψ u)
      (hPhi_u.of_le (by norm_num)) hu_stat
  have hvalue_eq :
      Φ (u, ψ u) = Φ (u, y u) :=
    stationaryInterior_value_eq_selectedMinimizer
      (Q := Q) (Mf := Mf) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hu_source hu_int hzero_deriv
  have hψ_argmin : ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) := by
    rcases mem_constrainedArgmin_iff.mp (hy_argmin hu_source) with ⟨hyu_mem, hyu_min⟩
    refine mem_constrainedArgmin_iff.mpr ?_
    refine ⟨by simpa using interior_subset hu_int, ?_⟩
    intro z hz
    calc
      Φ (u, ψ u) = Φ (u, y u) := hvalue_eq
      _ ≤ Φ (u, z) := hyu_min hz
  have hψ_eq : ψ u = y u := hy_unique hu_source hψ_argmin
  refine ⟨hu_source, hψ_argmin, hψ_eq, ?_⟩
  -- Once the stationary branch is proved to be the actual minimizer branch, the reduced
  -- objective evaluates to its branch value.
  exact partialMinimizationObjective_eq_of_mem_argmin Q Φ hψ_argmin

/-- Helper for Theorem 5.1.11: at every source-domain point, the Hessian of the reduced
objective is the Schur complement of the ambient Hessian at the selected minimizer. -/
private lemma partialMinimizationObjective_hessian_eq_schur_of_mem_sourceDom
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v))
    {x : E₁} (hx : x ∈ partialMinimizationSourceDom Q) :
    hessian (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x =
      partialMinimizationSchurHessian Φ x (y x) := by
  rcases implicitStationaryBranchPacket_of_mem_sourceDom
      (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hyy_pos hx with
    ⟨s, ψ, hs_open, hsx, hψ_self, hψ_cont, _, hpacket⟩
  have htransport :=
    selectedMinimizerTransport_onImplicitBranch
      (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hy_unique hpacket
  have hψ_tendsto : Filter.Tendsto ψ (nhds x) (nhds (y x)) := by
    -- The canonical implicit branch is continuous at `x` and passes through `y x`.
    simpa [hψ_self] using hψ_cont.contDiffAt (hs_open.mem_nhds hsx) |>.continuousAt.tendsto
  have hPhi_x :
      ContDiffAt ℝ 2 Φ (x, y x) := by
    have hLift_x :
        ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x)) := by
      -- The ambient self-concordant owner supplies `C³` regularity at the branch point.
      simpa [partialMinimizationLift] using
        hself.contDiffOn.contDiffAt
          (by simpa using hself.isOpen_domain.mem_nhds (by simpa using (hpacket x hsx).1))
    have hPhi_branch :
        ContDiffAt ℝ 3 Φ (x, ψ x) := by
      -- Pull the lifted regularity back through the fixed product equivalence.
      simpa [partialMinimizationLift, Function.comp] using
        hLift_x.comp (x, ψ x)
          ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
              (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
    simpa [hψ_self] using hPhi_branch.of_le (by norm_num)
  have hψ_mem_interior :
      ∀ᶠ u in nhds x, (u, ψ u) ∈ interior Q := by
    -- Restrict the local packet to the open neighborhood `s`.
    filter_upwards [hs_open.mem_nhds hsx] with u hu
    exact (hpacket u hu).1
  have hψ_argmin :
      ∀ᶠ u in nhds x, ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) := by
    -- On the same neighborhood, the stationary branch is the actual minimizing branch.
    filter_upwards [hs_open.mem_nhds hsx] with u hu
    exact (htransport u hu).2.1
  have hψ_unique :
      ∀ᶠ u in nhds x,
        ∀ z : E₂, z ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) → z = ψ u := by
    -- Uniqueness is inherited from the chosen branch `y` after transporting `ψ u = y u`.
    filter_upwards [hs_open.mem_nhds hsx] with u hu z hz
    calc
      z = y u := hy_unique (htransport u hu).1 hz
      _ = ψ u := ((htransport u hu).2.2.1).symm
  have hyy_inv :
      (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible :=
    yyHessian_isInvertible_of_mem_sourceDom (Q := Q) (Φ := Φ) (y := y) hyy_pos hx
  -- Invoke Proposition 5.0.19 on the transported minimizing branch near `x`.
  simpa [hψ_self] using
    (partialMinimizationObjective_hessian_eq_schur_of_isInvertible_yyHessian
      (Q := Q) (Φ := Φ) (x := x) (y := ψ)
      (by simpa [hψ_self] using hPhi_x) (by simpa [hψ_self] using hψ_tendsto)
      hψ_mem_interior hψ_argmin hψ_unique
      (by simpa [hψ_self] using hyy_inv))

/-- Helper for Theorem 5.1.11: at every source-domain point, the reduced objective has the
canonical envelope gradient and Schur-complement Hessian formulas. -/
private lemma reducedObjectiveFormulas_of_mem_sourceDom
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v))
    {x : E₁} (hx : x ∈ partialMinimizationSourceDom Q) :
    ∇ (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x =
        ∇ (fun u' ↦ Φ (u', y x)) x ∧
      hessian (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x =
        partialMinimizationSchurHessian Φ x (y x) := by
  rcases implicitStationaryBranchPacket_of_mem_sourceDom
      (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hyy_pos hx with
    ⟨s, ψ, hs_open, hsx, hψ_self, hψ_cont, _, hpacket⟩
  have htransport :=
    selectedMinimizerTransport_onImplicitBranch
      (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hy_unique hpacket
  have hyy_inv :
      (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible :=
    yyHessian_isInvertible_of_mem_sourceDom (Q := Q) (Φ := Φ) (y := y) hyy_pos hx
  have hψ_tendsto : Filter.Tendsto ψ (nhds x) (nhds (y x)) := by
    -- The canonical implicit branch is continuous at `x` and passes through `y x`.
    simpa [hψ_self] using
      (hψ_cont.contDiffAt (hs_open.mem_nhds hsx)).continuousAt.tendsto
  have hPhi_x :
      ContDiffAt ℝ 2 Φ (x, y x) := by
    have hLift_x :
        ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x)) := by
      -- The ambient self-concordant owner supplies `C³` regularity at the branch point.
      simpa [partialMinimizationLift] using
        hself.contDiffOn.contDiffAt
          (by simpa using hself.isOpen_domain.mem_nhds (by simpa using (hpacket x hsx).1))
    have hPhi_branch :
        ContDiffAt ℝ 3 Φ (x, ψ x) := by
      -- Pull the lifted regularity back through the fixed product equivalence.
      simpa [partialMinimizationLift, Function.comp] using
        hLift_x.comp (x, ψ x)
          ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
              (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
    simpa [hψ_self] using hPhi_branch.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hψ_argmin :
      ∀ᶠ u in nhds x, ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) := by
    -- On the branch neighborhood, stationarity transports to the selected minimizer branch.
    filter_upwards [hs_open.mem_nhds hsx] with u hu
    exact (htransport u hu).2.1
  have hgrad :
      ∇ (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x =
        ∇ (fun u' ↦ Φ (u', ψ x)) x := by
    exact partialMinimizationObjective_gradient_eq_xGradient_of_eventually_argmin
      (Q := Q) (Φ := Φ) (x := x) (y := ψ)
      (by simpa [hψ_self] using hPhi_x.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
      ((hψ_cont.contDiffAt (hs_open.mem_nhds hsx)).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
      (by simpa [hψ_self] using hy_mem_interior hx)
      hψ_argmin
  have hhess :
      hessian (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x =
        partialMinimizationSchurHessian Φ x (ψ x) := by
    have hψ_tendsto_self : Filter.Tendsto ψ (nhds x) (nhds (ψ x)) := by
      simpa [hψ_self] using hψ_tendsto
    exact partialMinimizationObjective_hessian_eq_schur_of_isInvertible_yyHessian
      (Q := Q) (Φ := Φ) (x := x) (y := ψ)
      (by simpa [hψ_self] using hPhi_x) hψ_tendsto_self
      (by
        filter_upwards [hs_open.mem_nhds hsx] with u hu
        exact (hpacket u hu).1)
      hψ_argmin
      (by
        filter_upwards [hs_open.mem_nhds hsx] with u hu z hz
        calc
          z = y u := hy_unique (htransport u hu).1 hz
          _ = ψ u := ((htransport u hu).2.2.1).symm)
      (by simpa [hψ_self] using hyy_inv)
  -- Rewrite the local implicit branch back to the selected branch at the base point.
  exact ⟨by simpa [hψ_self] using hgrad, by simpa [hψ_self] using hhess⟩

/-- Helper for Theorem 5.1.11: the reduced partial-minimization objective is `C³` on the source
domain because near each point it admits a genuine `C²` reduced gradient field coming from the
implicit stationary branch. -/
private lemma partialMinimizationObjective_contDiffOn_sourceDom
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v)) :
    ContDiffOn ℝ 3
      (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)))
      (partialMinimizationSourceDom Q) := by
  intro x hx
  rcases implicitStationaryBranchPacket_of_mem_sourceDom
      (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hyy_pos hx with
    ⟨s, ψ, hs_open, hsx, _hψ_self, hψ_cont, _, hpacket⟩
  have htransport :=
    selectedMinimizerTransport_onImplicitBranch
      (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hy_unique hpacket
  let Gψ : E₁ → E₁ := fun u ↦
    WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u)))
  have hgradOn :
      ∀ u ∈ s,
        HasGradientAt
          (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)))
          (Gψ u) u := by
    intro u hu
    have hu_int : (u, ψ u) ∈ interior Q := (hpacket u hu).1
    have hLift_u :
        ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u)) := by
      -- The ambient self-concordant owner supplies `C³` regularity at each branch point.
      simpa [partialMinimizationLift] using
        hself.contDiffOn.contDiffAt
          (by simpa using hself.isOpen_domain.mem_nhds (by simpa using hu_int))
    have hPhi_u :
        ContDiffAt ℝ 3 Φ (u, ψ u) := by
      -- Pull the lifted regularity back through the fixed product equivalence.
      simpa [partialMinimizationLift, Function.comp] using
        hLift_u.comp (u, ψ u)
          ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
              (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
    have hψu_diff : DifferentiableAt ℝ ψ u :=
      (hψ_cont.contDiffAt (hs_open.mem_nhds hu)).differentiableAt (by norm_num)
    have hψ_argmin_near_u :
        ∀ᶠ v in nhds u, ψ v ∈ argmin[(Prod.mk v) ⁻¹' Q] (Φ ∘ Prod.mk v) := by
      filter_upwards [hs_open.mem_nhds hu] with v hv
      exact (htransport v hv).2.1
    have hgrad_u :
        HasGradientAt
          (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)))
          (∇ (fun u' ↦ Φ (u', ψ u)) u) u :=
      partialMinimizationObjective_hasGradientAt_of_eventually_argmin
        (Q := Q) (Φ := Φ) (x := u) (y := ψ)
        (hPhi_u.of_le (by norm_num)) hψu_diff hu_int hψ_argmin_near_u
    have hgrad_eq :
        Gψ u = ∇ (fun u' ↦ Φ (u', ψ u)) u := by
      simpa [Gψ] using
        partialMinimizationXGradient_eq_frozenXGradient Φ u (ψ u) (hPhi_u.of_le (by norm_num))
    simpa [hgrad_eq] using hgrad_u
  have hψ_contAt : ContDiffAt ℝ 2 ψ x :=
    hψ_cont.contDiffAt (hs_open.mem_nhds hsx)
  have hLift_x :
      ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x)) := by
    -- The base branch point also inherits the ambient `C³` regularity.
    simpa [partialMinimizationLift] using
      hself.contDiffOn.contDiffAt
        (by simpa using hself.isOpen_domain.mem_nhds (by simpa using (hpacket x hsx).1))
  have hPhi_x :
      ContDiffAt ℝ 3 Φ (x, ψ x) := by
    -- Pull the lifted regularity back through the fixed product equivalence.
    simpa [partialMinimizationLift, Function.comp] using
      hLift_x.comp (x, ψ x)
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
  have hG_cont : ContDiffAt ℝ 2 Gψ x := by
    have hAmbient :
        ContDiffAt ℝ 2
          (fun z : E₁ × E₂ ↦
            WithLp.fstL 2 ℝ E₁ E₂
              (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z)))
          (x, ψ x) := by
      simpa using partialMinimizationXGradientMap_contDiffAt Φ x (ψ x) hPhi_x
    have hGraph : ContDiffAt ℝ 2 (fun u ↦ (u, ψ u)) x := contDiffAt_id.prodMk hψ_contAt
    simpa [Gψ] using hAmbient.comp x hGraph
  -- Route correction: prove local `C³` regularity through a `C²` reduced gradient field rather
  -- than by trying to show the value function itself is a direct `C³` composition with `ψ`.
  have hcontAt :
      ContDiffAt ℝ 3
        (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x := by
    refine contDiffAt_succ_iff_hasFDerivAt.2 ?_
    refine ⟨fun u ↦ (InnerProductSpace.toDual ℝ E₁) (Gψ u), ?_⟩
    refine ⟨⟨s, hs_open.mem_nhds hsx, ?_⟩, ?_⟩
    · intro u hu
      exact (hgradOn u hu).hasFDerivAt
    · simpa using (InnerProductSpace.toDual ℝ E₁).contDiff.contDiffAt.comp x hG_cont
  exact hcontAt.contDiffWithinAt

/-- Helper for Theorem 5.1.11: on graph directions of the implicit minimizer derivative, the
ambient Hessian quadratic form of the lifted objective collapses to the reduced Hessian quadratic
form on the source domain. -/
private lemma partialMinimizationObjective_graphQuadraticForm_eq_on_sourceDom
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v))
    {x : E₁} (hx : x ∈ partialMinimizationSourceDom Q) (w : E₁) :
    inner ℝ (WithLp.toLp 2 (w, partialMinimizerImplicitFDeriv Φ x (y x) w))
      ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
        (WithLp.toLp 2 (w, partialMinimizerImplicitFDeriv Φ x (y x) w))) =
      inner ℝ w
        (hessian (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x w) := by
  let v : E₂ := partialMinimizerImplicitFDeriv Φ x (y x) w
  have hyy_inv :
      (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible :=
    yyHessian_isInvertible_of_mem_sourceDom (Q := Q) (Φ := Φ) (y := y) hyy_pos hx
  have hformulas :=
    reducedObjectiveFormulas_of_mem_sourceDom
      (Q := Q) (Mf := Mf) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hy_unique hyy_pos hx
  have hhess :
      hessian (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x =
        partialMinimizationSchurHessian Φ x (y x) := hformulas.2
  have hLift_x :
      ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)) := by
    -- The ambient self-concordant owner supplies `C³` regularity at the selected branch point.
    simpa [partialMinimizationLift] using
      hself.contDiffOn.contDiffAt
        (by simpa using hself.isOpen_domain.mem_nhds (by simpa using hy_mem_interior hx))
  have hPhi_x :
      ContDiffAt ℝ 2 Φ (x, y x) := by
    have hPhi_x3 :
        ContDiffAt ℝ 3 Φ (x, y x) := by
      -- Pull the lifted regularity back through the fixed `WithLp` equivalence.
      simpa [partialMinimizationLift, Function.comp] using
        hLift_x.comp (x, y x)
          ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
              (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
    exact hPhi_x3.of_le (by norm_num)
  have hAmbientHessianY :
      WithLp.sndL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
            (WithLp.toLp 2 (w, v))) = 0 := by
    -- The implicit derivative kills the vertical Hessian block on graph directions.
    have hsplit :
        ((w, v) : E₁ × E₂) =
          (ContinuousLinearMap.inl ℝ E₁ E₂) w + (ContinuousLinearMap.inr ℝ E₁ E₂) v := by
      ext <;> simp
    calc
      WithLp.sndL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
            (WithLp.toLp 2 (w, v)))
          = (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x)))
              (w, v)) := by
                rfl
      _ = (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x)))
            ((ContinuousLinearMap.inl ℝ E₁ E₂) w +
              (ContinuousLinearMap.inr ℝ E₁ E₂) v)) := by rw [hsplit]
      _ = (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x))).comp
            (ContinuousLinearMap.inl ℝ E₁ E₂)) w +
            ((((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x))).comp
              (ContinuousLinearMap.inr ℝ E₁ E₂)) v) := by
                rw [map_add]
                rfl
      _ = partialMinimizationYXHessian Φ x (y x) w +
            (hessian (Φ ∘ Prod.mk x) (y x)) v := by
              rw [partialMinimizationYGradient_comp_inr_eq_yyHessian Φ x (y x) hPhi_x]
              rfl
      _ = partialMinimizationYXHessian Φ x (y x) w -
            partialMinimizationYXHessian Φ x (y x) w := by
              simp [v, partialMinimizerImplicitFDeriv, ContinuousLinearMap.comp_apply,
                hyy_inv.self_apply_inverse]
      _ = 0 := sub_self _
  have hAmbientHessianX :
      WithLp.fstL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
            (WithLp.toLp 2 (w, v))) =
        hessian (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x w := by
    -- The horizontal Hessian block on graph directions is the Schur complement.
    have hsplit :
        ((w, v) : E₁ × E₂) =
          (ContinuousLinearMap.inl ℝ E₁ E₂) w + (ContinuousLinearMap.inr ℝ E₁ E₂) v := by
      ext <;> simp
    calc
      WithLp.fstL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
            (WithLp.toLp 2 (w, v)))
          = (((WithLp.fstL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x)))
              (w, v)) := by
                rfl
      _ = (((WithLp.fstL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x)))
            ((ContinuousLinearMap.inl ℝ E₁ E₂) w +
              (ContinuousLinearMap.inr ℝ E₁ E₂) v)) := by rw [hsplit]
      _ = partialMinimizationXXHessian Φ x (y x) w +
            (partialMinimizationXYHessian Φ x (y x)) v := by
              rw [map_add]
              simp [partialMinimizationXXHessian, partialMinimizationXYHessian,
                ContinuousLinearMap.comp_apply]
      _ = partialMinimizationSchurHessian Φ x (y x) w := by
              simp [partialMinimizationSchurHessian, v, ContinuousLinearMap.comp_apply]
      _ = hessian (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x w := by
              simpa [hhess]
  -- The ambient Hessian vector on a graph direction has horizontal component `∇²f(x) w` and zero
  -- vertical component, so the quadratic form reduces to the one on `E₁`.
  calc
    inner ℝ (WithLp.toLp 2 (w, v))
        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
          (WithLp.toLp 2 (w, v)))
        =
          inner ℝ w
            (WithLp.fstL 2 ℝ E₁ E₂
              ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
                (WithLp.toLp 2 (w, v)))) +
            inner ℝ v
              (WithLp.sndL 2 ℝ E₁ E₂
                ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
                  (WithLp.toLp 2 (w, v)))) := by
            simp [WithLp.prod_inner_apply]
    _ = inner ℝ w
          (hessian (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x w) +
          inner ℝ v 0 := by
            rw [hAmbientHessianX, hAmbientHessianY]
    _ = inner ℝ w
          (hessian (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x w) := by
            simp

/-- Helper for Theorem 5.1.11: neighborhood equality transfers the Hessian, the induced local
norm, and all scalar Hessian-direction pairings at the base point. -/
private lemma hessianLocalData_eq_of_eventuallyEq
    {F G : E₁ → ℝ} {x : E₁}
    (hFcontAt : ContDiffAt ℝ 3 F x)
    (hEqAt : F =ᶠ[nhds x] G) :
    hessian F x = hessian G x ∧
      ∀ u : E₁, hessianLocalNorm F x u = hessianLocalNorm G x u := by
  have hhess : hessian F x = hessian G x := by
    -- Differentiate the neighborhood equality once at the gradient level to identify Hessians.
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  refine ⟨hhess, ?_⟩
  intro u
  -- The local norm depends only on the Hessian quadratic form at the base point.
  simp [hessianLocalNorm_def, hhess]

/-- Helper for Theorem 5.1.11: neighborhood equality also transfers the third directional
derivative at the base point. -/
private lemma thirdDirectionalDerivative_eq_of_eventuallyEq
    {F G : E₁ → ℝ} {x : E₁}
    (hFcontAt : ContDiffAt ℝ 3 F x)
    (hEqAt : F =ᶠ[nhds x] G) (u : E₁) :
    thirdDirectionalDerivative G x u = thirdDirectionalDerivative F x u := by
  have hGcontAt : ContDiffAt ℝ 3 G x := hFcontAt.congr_of_eventuallyEq hEqAt.symm
  have hiter :
      iteratedFDeriv ℝ 3 G x = iteratedFDeriv ℝ 3 F x :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ hEqAt.symm 3).eq_of_nhds
  -- Rewrite both cubic terms through the common third iterated derivative at `x`.
  simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hGcontAt,
    thirdDirectionalDerivative_eq_iteratedFDeriv hFcontAt] using
    congrArg (fun A ↦ A fun _ ↦ u) hiter

/-- Helper for Theorem 5.1.11: a pointwise `C³` hypothesis upgrades the Hessian map to a genuine
Fréchet-derivative field. -/
private lemma hessian_hasFDerivAt_of_contDiffAt
    {f : E₁ → ℝ} {x : E₁} (hcontAt : ContDiffAt ℝ 3 f x) :
    HasFDerivAt (hessian f) (fderiv ℝ (hessian f) x) x := by
  let D : StrongDual ℝ E₁ →L[ℝ] E₁ :=
    (InnerProductSpace.toDual ℝ E₁).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) x := by
    -- First differentiate `f` once and keep the two remaining derivatives.
    exact hcontAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ f) x := by
    -- Rewrite the gradient through the Riesz map before differentiating again.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp x hfderiv_C2
  have hhessian_C1 : ContDiffAt ℝ 1 (hessian f) x := by
    -- One more derivative of the gradient is exactly the Hessian owner.
    simpa [hessian] using
      hgrad_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  -- Convert the `C¹` regularity of the Hessian map into the required Fréchet derivative.
  exact (hhessian_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt

/-- Helper for Theorem 5.1.11: the scalar Hessian-direction pairing is the corresponding
evaluation of the third iterated derivative. -/
private lemma hessian_direction_pairing_eq_iteratedFDeriv
    {f : E₁ → ℝ} {x d w v : E₁}
    (hcontAt : ContDiffAt ℝ 3 f x) :
    inner ℝ v ((fderiv ℝ (hessian f) x d) w) = iteratedFDeriv ℝ 3 f x ![d, w, v] := by
  let line : ℝ → E₁ := fun s ↦ x + s • d
  let φ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (line s) w)
  let ψ : ℝ → ℝ := fun s ↦ iteratedFDeriv ℝ 2 f (line s) ![w, v]
  obtain ⟨u, hu, hcontOn⟩ :=
    hcontAt.contDiffOn (m := 3) (by simp) (by intro h; simp at h)
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp hu
  have hs_contOn : ContDiffOn ℝ 3 f s := hcontOn.mono hs_sub
  have hEqOn : ∀ y ∈ s, inner ℝ v (hessian f y w) = iteratedFDeriv ℝ 2 f y ![w, v] := by
    intro y hy
    -- On a local `C³` neighborhood, the Hessian pairing is exactly the second iterated
    -- derivative evaluated on the ordered pair `(w, v)`.
    let D : StrongDual ℝ E₁ →L[ℝ] E₁ :=
      (InnerProductSpace.toDual ℝ E₁).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hy_cont : ContDiffAt ℝ 3 f y := hs_contOn.contDiffAt (hs_open.mem_nhds hy)
    have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) y := by
      exact hy_cont.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ f) y := by
      exact hfderiv_C2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hgrad_hasFDeriv :
        HasFDerivAt (∇ f) (D.comp (fderiv ℝ (fderiv ℝ f) y)) y := by
      simpa [gradient, D] using D.hasFDerivAt.comp y hfderiv_diff.hasFDerivAt
    rw [hessian, hgrad_hasFDeriv.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [real_inner_comm]
    calc
      inner ℝ
          ((InnerProductSpace.toDual ℝ E₁).symm.toContinuousLinearEquiv
            ((fderiv ℝ (fderiv ℝ f) y) w)) v
          = ((fderiv ℝ (fderiv ℝ f) y) w) v := by
              simpa using
                (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E₁) (x := v)
                  (y := ((fderiv ℝ (fderiv ℝ f) y) w)))
      _ = iteratedFDeriv ℝ 2 f y ![w, v] := by
            simpa [iteratedFDeriv_two_apply]
  have hline_mem : ∀ᶠ t in nhds (0 : ℝ), line t ∈ s := by
    let hline0 : ContinuousAt line 0 :=
      (show HasDerivAt line d (0 : ℝ) by
        simpa [line, one_smul] using
          ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x).continuousAt
    exact hline0.tendsto.eventually (hs_open.mem_nhds (by simpa [line] using hxs))
  have hEq : ψ =ᶠ[nhds (0 : ℝ)] φ := by
    filter_upwards [hline_mem] with t ht
    simp [ψ, φ, line, hEqOn _ ht]
  have hφ :
      HasDerivAt φ (inner ℝ v ((fderiv ℝ (hessian f) x d) w)) 0 := by
    have hxLine : HasDerivAt line d (0 : ℝ) := by
      simpa [line, one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
    have hhessianDeriv :
        HasFDerivAt (hessian f) (fderiv ℝ (hessian f) (line 0)) (line 0) := by
      simpa [line] using hessian_hasFDerivAt_of_contDiffAt (f := f) (x := x) hcontAt
    have happly :
        HasDerivAt (fun t : ℝ ↦ hessian f (line t) w)
          ((fderiv ℝ (hessian f) (line 0) d) w) 0 := by
      -- Differentiate the Hessian map along the affine line and then evaluate it on `w`.
      have happlyF :
          HasFDerivAt (fun y : E₁ ↦ hessian f y w)
            ((ContinuousLinearMap.apply ℝ E₁ w).comp (fderiv ℝ (hessian f) (line 0))) (line 0) := by
        exact (ContinuousLinearMap.apply ℝ E₁ w).hasFDerivAt.comp (line 0) hhessianDeriv
      simpa using happlyF.comp_hasDerivAt 0 hxLine
    have hinnerF :
        HasFDerivAt (fun y : E₁ ↦ inner ℝ v y) ((innerSL ℝ) v) (hessian f (line 0) w) := by
      simpa using ((innerSL ℝ) v).hasFDerivAt
    -- The scalar pairing is the composition of the Hessian line with the fixed inner-product
    -- functional against `v`.
    simpa [φ, line] using hinnerF.comp_hasDerivAt 0 happly
  have hiter2_C1 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 2 f) x := by
    exact hcontAt.iteratedFDeriv_right (m := 1) (i := 2)
      (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3)
  have hiter2_deriv :
      HasFDerivAt (iteratedFDeriv ℝ 2 f) (fderiv ℝ (iteratedFDeriv ℝ 2 f) x) x := by
    exact (hiter2_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hψ :
      HasDerivAt ψ (((fderiv ℝ (iteratedFDeriv ℝ 2 f) x) d) ![w, v]) 0 := by
    have hline0 : HasDerivAt line d (0 : ℝ) := by
      simpa [line, one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
    have hcomp :
        HasDerivAt (fun t : ℝ ↦ iteratedFDeriv ℝ 2 f (line t))
          ((fderiv ℝ (iteratedFDeriv ℝ 2 f) x) d) 0 := by
      simpa [line] using
        hiter2_deriv.comp_hasDerivAt_of_eq 0 hline0 (by simp [line])
    -- Evaluate the derivative of the bilinear iterated derivative on the ordered pair `(w, v)`.
    simpa [ψ] using
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E₁) ℝ ![w, v]).hasFDerivAt.comp_hasDerivAt 0
        hcomp)
  have hψ_from_φ : HasDerivAt ψ (inner ℝ v ((fderiv ℝ (hessian f) x d) w)) 0 :=
    hφ.congr_of_eventuallyEq hEq
  have hsame :
      inner ℝ v ((fderiv ℝ (hessian f) x d) w) =
        ((fderiv ℝ (iteratedFDeriv ℝ 2 f) x) d) ![w, v] :=
    hψ_from_φ.unique hψ
  -- Rewrite the derivative of the second iterated derivative back to the canonical
  -- third-order owner.
  simpa [iteratedFDeriv_succ_apply_left] using hsame

/-- Helper for Theorem 5.1.11: near a source-domain point, the reduced objective agrees with the
honest value of the canonical implicit minimizing branch. -/
private lemma branchValueEventualEq_of_mem_sourceDom
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v))
    {x : E₁} (hx : x ∈ partialMinimizationSourceDom Q) :
    ∃ s : Set E₁, ∃ ψ : E₁ → E₂,
      IsOpen s ∧ x ∈ s ∧ ψ x = y x ∧ ContDiffOn ℝ 2 ψ s ∧
        HasStrictFDerivAt ψ (partialMinimizerImplicitFDeriv Φ x (y x)) x ∧
        extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)) =ᶠ[nhds x]
          fun u ↦ Φ (u, ψ u) := by
  rcases implicitStationaryBranchPacket_of_mem_sourceDom
      (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hyy_pos hx with
    ⟨s, ψ, hs_open, hsx, hψ_self, hψ_cont, hψ_strict, hpacket⟩
  have htransport :=
    selectedMinimizerTransport_onImplicitBranch
      (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hy_unique hpacket
  have hψ_argmin :
      ∀ᶠ u in nhds x, ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) := by
    -- On the implicit-branch neighborhood, the stationary branch is already the selected minimizer.
    filter_upwards [hs_open.mem_nhds hsx] with u hu
    exact (htransport u hu).2.1
  refine ⟨s, ψ, hs_open, hsx, hψ_self, hψ_cont, hψ_strict, ?_⟩
  -- Evaluate the reduced objective through the nearby minimizing branch values.
  exact partialMinimizationObjective_eventuallyEq_of_eventually_argmin Q Φ x ψ hψ_argmin

/-- Helper for Theorem 5.1.11: differentiating the local stationary equation along the implicit
branch graph shows that the ambient Hessian has no vertical component on graph tangents. -/
private lemma branchStationary_verticalHessian_eq_zero_on_branch
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    {s : Set E₁} {ψ : E₁ → E₂}
    (hs_open : IsOpen s)
    (hψ_cont : ContDiffOn ℝ 2 ψ s)
    (hpacket :
      ∀ u ∈ s, (u, ψ u) ∈ interior Q ∧
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0)
    {p : E₁} (hp : p ∈ s) (w : E₁) :
    WithLp.sndL 2 ℝ E₁ E₂
        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
          (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w))) = 0 := by
  let F : E₁ → E₂ := fun u ↦
    WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u)))
  have hF_zero :
      F =ᶠ[nhds p] fun _ : E₁ ↦ 0 := by
    filter_upwards [hs_open.mem_nhds hp] with u hu
    -- The local packet records that the stationary branch solves the vertical gradient equation.
    simpa [F] using (hpacket u hu).2
  have hLift_p :
      ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)) := by
    -- The ambient self-concordant owner supplies `C³` regularity at each branch point.
    simpa [partialMinimizationLift] using
      hself.contDiffOn.contDiffAt
        (by simpa using hself.isOpen_domain.mem_nhds (by simpa using (hpacket p hp).1))
  have hPhi_p :
      ContDiffAt ℝ 3 Φ (p, ψ p) := by
    -- Pull the lifted regularity back through the fixed product equivalence.
    simpa [partialMinimizationLift, Function.comp] using
      hLift_p.comp (p, ψ p)
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
  have hψ_fderiv :
      HasFDerivAt ψ (fderiv ℝ ψ p) p := by
    -- The implicit branch is `C²`, hence differentiable with its canonical Fréchet derivative.
    exact
      ((hψ_cont.contDiffAt (hs_open.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt
  have hF_const :
      HasFDerivAt F (0 : E₁ →L[ℝ] E₂) p := by
    -- The stationary field is locally constant with value `0` on the branch neighborhood.
    exact (hasFDerivAt_const p (c := (0 : E₂))).congr_of_eventuallyEq hF_zero
  have hF_branch :
      HasFDerivAt F
        ((((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ p (ψ p))).comp
            ((1 : E₁ →L[ℝ] E₁).prod (fderiv ℝ ψ p)))) p := by
    -- Differentiate the ambient stationary map after restricting it to the graph of `ψ`.
    simpa [F, Function.comp] using
      (partialMinimizationYGradient_hasFDerivAt Φ p (ψ p) (hPhi_p.of_le (by norm_num))).comp p
        ((hasFDerivAt_id p).prodMk hψ_fderiv)
  have hderiv_eq :
      (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ p (ψ p))).comp
          ((1 : E₁ →L[ℝ] E₁).prod (fderiv ℝ ψ p))) = 0 := by
    -- The derivative of the stationary field agrees with the derivative of the constant zero map.
    exact hF_branch.unique hF_const
  have happly := congrArg (fun L : E₁ →L[ℝ] E₂ => L w) hderiv_eq
  -- Evaluate the vanishing derivative on the test direction `w`.
  simpa [partialMinimizationAmbientHessian, ContinuousLinearMap.comp_apply] using happly

/-- Helper for Theorem 5.1.11: on the implicit minimizing branch, the branch value
`u ↦ Φ (u, ψ u)` has Hessian given by the canonical `XX + XY ∘ Dψ` graph formula. -/
private lemma branchValue_hessian_eq_on_branchNeighborhood
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    {s : Set E₁} {ψ : E₁ → E₂}
    (hs_open : IsOpen s)
    (hψ_cont : ContDiffOn ℝ 2 ψ s)
    (hpacket :
      ∀ u ∈ s, (u, ψ u) ∈ interior Q ∧
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0)
    (htransport :
      ∀ u ∈ s,
        u ∈ partialMinimizationSourceDom Q ∧
          ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) ∧
          ψ u = y u ∧
          extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)) u = Φ (u, ψ u))
    {p : E₁} (hp : p ∈ s) :
    hessian (fun u ↦ Φ (u, ψ u)) p =
      partialMinimizationXXHessian Φ p (ψ p) +
        (partialMinimizationXYHessian Φ p (ψ p)).comp (fderiv ℝ ψ p) := by
  let Gψ : E₁ → E₁ := fun u ↦
    WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u)))
  have hLift_p :
      ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)) := by
    -- The ambient self-concordant owner supplies `C³` regularity at the branch point.
    simpa [partialMinimizationLift] using
      hself.contDiffOn.contDiffAt
        (by simpa using hself.isOpen_domain.mem_nhds (by simpa using (hpacket p hp).1))
  have hPhi_p :
      ContDiffAt ℝ 3 Φ (p, ψ p) := by
    -- Pull the lifted regularity back through the fixed product equivalence.
    simpa [partialMinimizationLift, Function.comp] using
      hLift_p.comp (p, ψ p)
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
  have hψ_diff : DifferentiableAt ℝ ψ p :=
    (hψ_cont.contDiffAt (hs_open.mem_nhds hp)).differentiableAt (by norm_num)
  have hgrad_event :
      ∇ (fun u ↦ Φ (u, ψ u)) =ᶠ[nhds p] Gψ := by
    filter_upwards [hs_open.mem_nhds hp] with u hu
    have hPhi_u :
        ContDiffAt ℝ 3 Φ (u, ψ u) := by
      have hLift_u :
          ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u)) := by
        -- Move the ambient `C³` regularity to the current branch point.
        simpa [partialMinimizationLift] using
          hself.contDiffOn.contDiffAt
            (by simpa using hself.isOpen_domain.mem_nhds (by simpa using (hpacket u hu).1))
      simpa [partialMinimizationLift, Function.comp] using
        hLift_u.comp (u, ψ u)
          ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
              (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
    have hψu_diff : DifferentiableAt ℝ ψ u :=
      (hψ_cont.contDiffAt (hs_open.mem_nhds hu)).differentiableAt (by norm_num)
    have hgrad_u :
        HasGradientAt (fun u' ↦ Φ (u', ψ u')) (Gψ u) u := by
      -- Read the branch value gradient through the frozen `x`-gradient because the branch point
      -- is already the selected fiber minimizer.
      have hbranch :
          HasGradientAt
            (fun u' ↦ Φ (u', ψ u'))
            (∇ (fun u' ↦ Φ (u', ψ u)) u) u :=
        partialMinimizationBranch_hasGradientAt_xGradient_of_mem_argmin
          (hPhi_u.of_le (by norm_num)) hψu_diff (hpacket u hu).1 (htransport u hu).2.1
      have hgrad_eq :
          Gψ u = ∇ (fun u' ↦ Φ (u', ψ u)) u := by
        simpa [Gψ] using
          partialMinimizationXGradient_eq_frozenXGradient Φ u (ψ u) (hPhi_u.of_le (by norm_num))
      simpa [hgrad_eq] using hbranch
    exact hgrad_u.gradient
  have hG_deriv :
      HasFDerivAt Gψ
        (partialMinimizationXXHessian Φ p (ψ p) +
          (partialMinimizationXYHessian Φ p (ψ p)).comp (fderiv ℝ ψ p))
        p := by
    -- Differentiate the ambient `x`-gradient field along the graph of `ψ`.
    simpa [Gψ, partialMinimizationSchurHessian] using
      (partialMinimizationXGradientAlongBranch_hasFDerivAt
        (b := ψ) (b' := fderiv ℝ ψ p) Φ p (hPhi_p.of_le (by norm_num)) hψ_diff.hasFDerivAt)
  have hgrad_deriv :
      HasFDerivAt (∇ (fun u ↦ Φ (u, ψ u)))
        (partialMinimizationXXHessian Φ p (ψ p) +
          (partialMinimizationXYHessian Φ p (ψ p)).comp (fderiv ℝ ψ p))
        p := by
    -- The neighborhood-level gradient identity transfers the derivative of `Gψ` to the true
    -- gradient of the branch value.
    exact hG_deriv.congr_of_eventuallyEq hgrad_event
  -- Read the derivative of the branch gradient back as the Hessian.
  simpa [hessian] using hgrad_deriv.fderiv

/-- Helper for Theorem 5.1.11: on graph directions of the implicit branch derivative, the ambient
Hessian quadratic form equals the quadratic form of the honest branch value `u ↦ Φ (u, ψ u)`. -/
private lemma branchValue_graphQuadraticForm_eq_on_branchNeighborhood
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    {s : Set E₁} {ψ : E₁ → E₂}
    (hs_open : IsOpen s)
    (hψ_cont : ContDiffOn ℝ 2 ψ s)
    (hpacket :
      ∀ u ∈ s, (u, ψ u) ∈ interior Q ∧
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0)
    (htransport :
      ∀ u ∈ s,
        u ∈ partialMinimizationSourceDom Q ∧
          ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) ∧
          ψ u = y u ∧
          extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)) u = Φ (u, ψ u))
    {p : E₁} (hp : p ∈ s) (w : E₁) :
    inner ℝ (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w))
        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
          (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w))) =
      inner ℝ w (hessian (fun u ↦ Φ (u, ψ u)) p w) := by
  have hbranchHess :=
    branchValue_hessian_eq_on_branchNeighborhood
      (Q := Q) (Mf := Mf) (Φ := Φ) (y := y)
      hself hs_open hψ_cont hpacket htransport hp
  have hAmbientHessianY :
      WithLp.sndL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
            (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w))) = 0 :=
    branchStationary_verticalHessian_eq_zero_on_branch
      (Q := Q) (Mf := Mf) (Φ := Φ) hself hs_open hψ_cont hpacket hp w
  have hAmbientHessianX :
      WithLp.fstL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
            (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w))) =
        hessian (fun u ↦ Φ (u, ψ u)) p w := by
    -- Expand the graph tangent into horizontal and vertical pieces, then rewrite the surviving
    -- horizontal block through the branch Hessian formula proved above.
    have hsplit :
        ((w, (fderiv ℝ ψ p) w) : E₁ × E₂) =
          (ContinuousLinearMap.inl ℝ E₁ E₂) w +
            (ContinuousLinearMap.inr ℝ E₁ E₂) ((fderiv ℝ ψ p) w) := by
      ext <;> simp
    calc
      WithLp.fstL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
            (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w)))
          = (((WithLp.fstL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ p (ψ p)))
              (w, (fderiv ℝ ψ p) w)) := by
                rfl
      _ = (((WithLp.fstL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ p (ψ p)))
            ((ContinuousLinearMap.inl ℝ E₁ E₂) w +
              (ContinuousLinearMap.inr ℝ E₁ E₂) ((fderiv ℝ ψ p) w))) := by
              rw [hsplit]
      _ = partialMinimizationXXHessian Φ p (ψ p) w +
            (partialMinimizationXYHessian Φ p (ψ p)) ((fderiv ℝ ψ p) w) := by
              rw [map_add]
              simp [partialMinimizationXXHessian, partialMinimizationXYHessian,
                ContinuousLinearMap.comp_apply]
      _ = (partialMinimizationXXHessian Φ p (ψ p) +
            (partialMinimizationXYHessian Φ p (ψ p)).comp (fderiv ℝ ψ p)) w := by
              simp [ContinuousLinearMap.comp_apply]
      _ = hessian (fun u ↦ Φ (u, ψ u)) p w := by
              simpa [hbranchHess]
  -- The vertical component vanishes, so the ambient graph quadratic form reduces to the branch
  -- Hessian quadratic form on `E₁`.
  calc
    inner ℝ (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w))
        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
          (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w)))
        =
          inner ℝ w
            (WithLp.fstL 2 ℝ E₁ E₂
              ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
                (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w)))) +
            inner ℝ ((fderiv ℝ ψ p) w)
              (WithLp.sndL 2 ℝ E₁ E₂
                ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
                  (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w)))) := by
            simp [WithLp.prod_inner_apply]
    _ = inner ℝ w (hessian (fun u ↦ Φ (u, ψ u)) p w) +
          inner ℝ ((fderiv ℝ ψ p) w) 0 := by
            rw [hAmbientHessianX, hAmbientHessianY]
    _ = inner ℝ w (hessian (fun u ↦ Φ (u, ψ u)) p w) := by
            simp

/-- Helper for Theorem 5.1.11: at a branch point, every vertical Hessian direction is orthogonal
to the graph tangent direction. -/
private lemma branchGraphDirection_verticalPairing_eq_zero_on_branch
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    {s : Set E₁} {ψ : E₁ → E₂}
    (hs_open : IsOpen s)
    (hψ_cont : ContDiffOn ℝ 2 ψ s)
    (hpacket :
      ∀ u ∈ s, (u, ψ u) ∈ interior Q ∧
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0)
    {p : E₁} (hp : p ∈ s) (w : E₁) (v : E₂) :
    inner ℝ (WithLp.toLp 2 (w, (fderiv ℝ ψ p) w))
        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
          (WithLp.toLp 2 (0, v))) = 0 := by
  let d : Z := WithLp.toLp 2 (w, (fderiv ℝ ψ p) w)
  let e : Z := WithLp.toLp 2 (0, v)
  have hp_mem :
      WithLp.toLp 2 (p, ψ p) ∈ ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) := by
    simpa using (hpacket p hp).1
  have hpPos :
      (hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p))).IsPositive :=
    hself.hessian_isPositive hp_mem
  have hvertical :
      WithLp.sndL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p))) d) = 0 :=
    branchStationary_verticalHessian_eq_zero_on_branch
      (Q := Q) (Mf := Mf) (Φ := Φ) hself hs_open hψ_cont hpacket hp w
  -- Move the vertical test vector across the symmetric Hessian, then use the previously proved
  -- vanishing of the vertical Hessian component on graph tangents.
  calc
    inner ℝ d
        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p))) e)
        = inner ℝ ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p))) e) d := by
            rw [real_inner_comm]
    _ = inner ℝ e
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p))) d) := by
            simpa [d, e] using hpPos.isSymmetric e d
    _ = 0 := by
            calc
              inner ℝ e
                  ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p))) d)
                  = inner ℝ (0 : E₁)
                      (WithLp.fstL 2 ℝ E₁ E₂
                        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p))) d)) +
                    inner ℝ v
                      (WithLp.sndL 2 ℝ E₁ E₂
                        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p))) d)) := by
                          simp [e, WithLp.prod_inner_apply]
              _ = 0 := by
                    rw [hvertical]
                    simp

/-- Helper for Theorem 5.1.11: the scalar Hessian pairing of the honest branch value differentiates
along `u` to the branch cubic term. -/
private lemma branchValueQuadratic_lineDeriv_eq_thirdDirectionalDerivative
    {g : E₁ → ℝ} {x u : E₁}
    (hcontAt : ContDiffAt ℝ 3 g x) :
    lineDeriv ℝ (fun p ↦ inner ℝ u (hessian g p u)) x u =
      thirdDirectionalDerivative g x u := by
  have hhess :
      HasFDerivAt (hessian g) (fderiv ℝ (hessian g) x) x :=
    hessian_hasFDerivAt_of_contDiffAt (f := g) (x := x) hcontAt
  have happly :
      HasFDerivAt (fun p ↦ hessian g p u)
        ((ContinuousLinearMap.apply ℝ E₁ u).comp (fderiv ℝ (hessian g) x)) x := by
    exact (ContinuousLinearMap.apply ℝ E₁ u).hasFDerivAt.comp x hhess
  have hinner :
      HasFDerivAt (fun p ↦ inner ℝ u (hessian g p u))
        (((innerSL ℝ) u).comp
          ((ContinuousLinearMap.apply ℝ E₁ u).comp (fderiv ℝ (hessian g) x))) x := by
    exact ((innerSL ℝ) u).hasFDerivAt.comp x happly
  have hline :
      HasLineDerivAt ℝ (fun p ↦ inner ℝ u (hessian g p u))
        (((((innerSL ℝ) u).comp
          ((ContinuousLinearMap.apply ℝ E₁ u).comp (fderiv ℝ (hessian g) x))) u)) x u :=
    hinner.hasLineDerivAt u
  have hpair :
      inner ℝ u ((fderiv ℝ (hessian g) x u) u) =
        iteratedFDeriv ℝ 3 g x ![u, u, u] :=
    hessian_direction_pairing_eq_iteratedFDeriv
      (f := g) (x := x) (d := u) (w := u) (v := u) hcontAt
  have hconst : (fun _ : Fin 3 ↦ u) = ![u, u, u] := by
    ext i
    fin_cases i <;> rfl
  have hthird :
      thirdDirectionalDerivative g x u = iteratedFDeriv ℝ 3 g x ![u, u, u] := by
    simpa [hconst] using thirdDirectionalDerivative_eq_iteratedFDeriv (f := g) (x := x) (u := u) hcontAt
  -- Read the line derivative through the Hessian-derivative pairing, then rewrite it as the
  -- canonical third directional derivative.
  calc
    lineDeriv ℝ (fun p ↦ inner ℝ u (hessian g p u)) x u
        = ((((innerSL ℝ) u).comp
            ((ContinuousLinearMap.apply ℝ E₁ u).comp (fderiv ℝ (hessian g) x))) u) := by
              exact hline.lineDeriv
    _ = inner ℝ u ((fderiv ℝ (hessian g) x u) u) := by
          simp [ContinuousLinearMap.comp_apply]
    _ = iteratedFDeriv ℝ 3 g x ![u, u, u] := hpair
    _ = thirdDirectionalDerivative g x u := hthird.symm

/-- Helper for Theorem 5.1.11: the remaining ambient bridge is the derivative of the graph
quadratic field at the base point. -/
private lemma branchGraphQuadratic_lineDeriv_eq_ambientThirdDirectionalDerivative
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    {s : Set E₁} {ψ : E₁ → E₂}
    (hs_open : IsOpen s)
    (hψ_cont : ContDiffOn ℝ 2 ψ s)
    (hpacket :
      ∀ u ∈ s, (u, ψ u) ∈ interior Q ∧
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0)
    {x : E₁} (hx : x ∈ s) (u : E₁) :
    lineDeriv ℝ
        (fun p ↦
          inner ℝ (WithLp.toLp 2 (u, (fderiv ℝ ψ p) u))
            ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
              (WithLp.toLp 2 (u, (fderiv ℝ ψ p) u)))) x u =
      thirdDirectionalDerivative (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x))
        (WithLp.toLp 2 (u, (fderiv ℝ ψ x) u)) := by
  let G : Z → ℝ := partialMinimizationLift Φ
  let z : E₁ → Z := fun p ↦ WithLp.toLp 2 (p, ψ p)
  let d : E₁ → Z := fun p ↦ WithLp.toLp 2 (u, (fderiv ℝ ψ p) u)
  let z0 : Z := z x
  let d0 : Z := d x
  let eZ : (E₁ × E₂) →L[ℝ] Z :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm : (E₁ × E₂) →L[ℝ] Z)
  let Lz : E₁ →L[ℝ] Z :=
    eZ.comp ((1 : E₁ →L[ℝ] E₁).prod (fderiv ℝ ψ x))
  let LdY : E₁ →L[ℝ] E₂ := (fderiv ℝ (fderiv ℝ ψ) x).flip u
  let Ld : E₁ →L[ℝ] Z :=
    eZ.comp ((0 : E₁ →L[ℝ] E₁).prod LdY)
  have hz0_mem :
      z0 ∈ ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) := by
    simpa [z0, z] using (hpacket x hx).1
  have hG_contAt : ContDiffAt ℝ 3 G z0 := by
    -- The ambient self-concordant owner supplies the `C³` regularity needed to differentiate the
    -- Hessian field at the branch point.
    simpa [G] using
      hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hz0_mem)
  have hψ_deriv : HasFDerivAt ψ (fderiv ℝ ψ x) x := by
    -- The implicit branch is `C²`, so its graph point has the expected Fréchet derivative.
    exact
      ((hψ_cont.contDiffAt (hs_open.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  have hz :
      HasFDerivAt z Lz x := by
    -- Differentiate the branch graph and then transport it through the fixed `WithLp` chart.
    simpa [z, Lz, Function.comp] using
      (eZ.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hψ_deriv))
  have hψ_fderiv_cont :
      ContDiffAt ℝ 1 (fderiv ℝ ψ) x := by
    -- One more derivative of the `C²` branch controls the moving graph direction field.
    exact (hψ_cont.contDiffAt (hs_open.mem_nhds hx)).fderiv_right (by norm_num)
  have hdu :
      HasFDerivAt (fun p ↦ fderiv ℝ ψ p u) LdY x := by
    have hψ_fderiv :
        HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) x) x :=
      (hψ_fderiv_cont.differentiableAt one_ne_zero).hasFDerivAt
    -- Freeze the outer direction `u` with the canonical `clm_apply` derivative rule.
    simpa [LdY] using hψ_fderiv.clm_apply (hasFDerivAt_const x (c := u))
  have hd :
      HasFDerivAt d Ld x := by
    -- The derivative of the moving graph direction is purely vertical after applying it to `u`.
    simpa [d, Ld, Function.comp] using
      (eZ.hasFDerivAt.comp x ((hasFDerivAt_const x (c := u)).prodMk hdu))
  have hhess :
      HasFDerivAt (hessian G) (fderiv ℝ (hessian G) z0) z0 :=
    hessian_hasFDerivAt_of_contDiffAt (f := G) (x := z0) hG_contAt
  have hH :
      HasFDerivAt (fun p ↦ hessian G (z p))
        ((fderiv ℝ (hessian G) z0).comp Lz) x := by
    -- Differentiate the ambient Hessian field after restricting it to the branch graph.
    simpa [z, z0] using hhess.comp x hz
  have happly :
      HasFDerivAt (fun p ↦ (hessian G (z p)) (d p))
        ((hessian G z0).comp Ld + ((fderiv ℝ (hessian G) z0).comp Lz).flip d0) x := by
    -- Apply the differentiating Hessian field to the moving graph direction.
    simpa [z0, d0] using hH.clm_apply hd
  have hinner :
      HasFDerivAt
        (fun p ↦ inner ℝ (d p) ((hessian G (z p)) (d p)))
        ((fderivInnerCLM ℝ (d0, (hessian G z0) d0)).comp
          (Ld.prod (((hessian G z0).comp Ld) + (((fderiv ℝ (hessian G) z0).comp Lz).flip d0))))
        x := by
    -- The scalar quadratic field is now a plain inner-product pairing of two differentiable
    -- vector-valued factors.
    simpa [z0, d0] using hd.inner ℝ happly
  have hline :
      HasLineDerivAt ℝ
        (fun p ↦ inner ℝ (d p) ((hessian G (z p)) (d p)))
        (((fderivInnerCLM ℝ (d0, (hessian G z0) d0)).comp
          (Ld.prod (((hessian G z0).comp Ld) + (((fderiv ℝ (hessian G) z0).comp Lz).flip d0))))
          u) x u :=
    hinner.hasLineDerivAt u
  have hz_u : Lz u = d0 := by
    simp [Lz, d0, d, eZ, ContinuousLinearMap.comp_apply]
  obtain ⟨v, hLd_u⟩ : ∃ v : E₂, Ld u = WithLp.toLp 2 (0, v) := by
    refine ⟨LdY u, ?_⟩
    simp [Ld, LdY, eZ, ContinuousLinearMap.comp_apply]
  have hcross_right :
      inner ℝ d0 ((hessian G z0) (Ld u)) = 0 := by
    -- The vertical derivative of the moving graph direction pairs trivially with the graph tangent
    -- through the branch orthogonality lemma proved above.
    rw [hLd_u]
    simpa [G, z0, d0, z, d] using
      branchGraphDirection_verticalPairing_eq_zero_on_branch
        (Q := Q) (Mf := Mf) (Φ := Φ) hself hs_open hψ_cont hpacket hx u v
  have hPos : (hessian G z0).IsPositive := hself.hessian_isPositive hz0_mem
  have hcross_left :
      inner ℝ (Ld u) ((hessian G z0) d0) = 0 := by
    -- Symmetry moves the vertical test vector to the right, where the previous orthogonality
    -- lemma applies unchanged.
    calc
      inner ℝ (Ld u) ((hessian G z0) d0)
          = inner ℝ ((hessian G z0) d0) (Ld u) := by
              rw [real_inner_comm]
      _ = inner ℝ d0 ((hessian G z0) (Ld u)) := by
            simpa using hPos.isSymmetric d0 (Ld u)
      _ = 0 := hcross_right
  have hpair :
      inner ℝ d0 ((fderiv ℝ (hessian G) z0 d0) d0) =
        iteratedFDeriv ℝ 3 G z0 ![d0, d0, d0] :=
    hessian_direction_pairing_eq_iteratedFDeriv
      (f := G) (x := z0) (d := d0) (w := d0) (v := d0) hG_contAt
  have hconst : (fun _ : Fin 3 ↦ d0) = ![d0, d0, d0] := by
    ext i
    fin_cases i <;> rfl
  have hthird :
      thirdDirectionalDerivative G z0 d0 = iteratedFDeriv ℝ 3 G z0 ![d0, d0, d0] := by
    simpa [hconst] using
      thirdDirectionalDerivative_eq_iteratedFDeriv (f := G) (x := z0) (u := d0) hG_contAt
  -- Route correction: differentiate the graph quadratic field in ambient coordinates, split the
  -- derivative into the canonical main term plus two vertical cross terms, then cancel those
  -- cross terms with the branch orthogonality interface.
  calc
    lineDeriv ℝ
        (fun p ↦ inner ℝ (WithLp.toLp 2 (u, (fderiv ℝ ψ p) u))
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
            (WithLp.toLp 2 (u, (fderiv ℝ ψ p) u)))) x u
        = (((fderivInnerCLM ℝ (d0, (hessian G z0) d0)).comp
            (Ld.prod (((hessian G z0).comp Ld) + (((fderiv ℝ (hessian G) z0).comp Lz).flip d0))))
            u) := by
              exact hline.lineDeriv
    _ = inner ℝ (Ld u) ((hessian G z0) d0) +
          (inner ℝ d0 ((fderiv ℝ (hessian G) z0 (Lz u)) d0) +
            inner ℝ d0 ((hessian G z0) (Ld u))) := by
          have hflip :
              (((fderiv ℝ (hessian G) z0).comp Lz).flip d0) u =
                ((fderiv ℝ (hessian G) z0) (Lz u)) d0 := by
            rfl
          rw [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
            ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
            ContinuousLinearMap.comp_apply, inner_add_right, hflip]
          rw [ContinuousLinearMap.comp_apply]
          rw [show Ld u = eZ ((ContinuousLinearMap.prod 0 LdY) u) by rfl]
          ring_nf
    _ = inner ℝ d0 ((fderiv ℝ (hessian G) z0 d0) d0) := by
          have hmain_u :
              inner ℝ d0 ((fderiv ℝ (hessian G) z0 (Lz u)) d0) =
                inner ℝ d0 ((fderiv ℝ (hessian G) z0 d0) d0) := by
            rw [hz_u]
          rw [hcross_left, hcross_right]
          ring_nf
          exact hmain_u
    _ = iteratedFDeriv ℝ 3 G z0 ![d0, d0, d0] := hpair
    _ = thirdDirectionalDerivative G z0 d0 := hthird.symm
    _ =
        thirdDirectionalDerivative (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x))
          (WithLp.toLp 2 (u, (fderiv ℝ ψ x) u)) := by
            rw [show G = partialMinimizationLift Φ by rfl]

/-- Helper for Theorem 5.1.11: after transferring the reduced objective to the honest implicit
branch value near `x`, the only remaining gap is the cubic self-concordance bound for that branch
model at the base point. -/
private lemma partialMinimizationObjective_thirdDerivBound_on_sourceDom
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v))
    {x : E₁} (hx : x ∈ partialMinimizationSourceDom Q) (u : E₁) :
    |thirdDirectionalDerivative
        (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x u| ≤
      2 * (Mf : ℝ) *
        hessianLocalNorm (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x u ^
          (3 : ℕ) := by
  rcases implicitStationaryBranchPacket_of_mem_sourceDom
      (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hyy_pos hx with
    ⟨s, ψ, hs_open, hsx, hψ_self, hψ_cont, hψ_strict, hpacket⟩
  have hEqAt :
      extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)) =ᶠ[nhds x]
        fun u' ↦ Φ (u', ψ u') := by
    -- Evaluate the reduced objective through the nearby branch values selected by the implicit
    -- minimizer packet.
    filter_upwards [hs_open.mem_nhds hsx] with u hu
    exact
      (selectedMinimizerTransport_onImplicitBranch
        (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
        hself hy_mem_interior hy_argmin hy_unique hpacket u hu).2.2.2
  have hcontAt :
      ContDiffAt ℝ 3
        (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x :=
    (partialMinimizationObjective_contDiffOn_sourceDom
      (Q := Q) (Mf := Mf) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hy_unique hyy_pos).contDiffAt
        ((partialMinimizationSourceDom_isOpen Q).mem_nhds hx)
  have htransfer :=
    hessianLocalData_eq_of_eventuallyEq
      (F := extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)))
      (G := fun u' ↦ Φ (u', ψ u')) (x := x) hcontAt hEqAt
  rcases htransfer with ⟨hhess, hnorm⟩
  have hthird_eq :
      thirdDirectionalDerivative (fun u' ↦ Φ (u', ψ u')) x u =
        thirdDirectionalDerivative
          (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x u := by
    -- The cubic term is another germ-level invariant of the reduced objective near `x`.
    exact
      thirdDirectionalDerivative_eq_of_eventuallyEq
        (F := extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)))
        (G := fun u' ↦ Φ (u', ψ u')) (x := x) hcontAt hEqAt u
  suffices
      hbranch :
        |thirdDirectionalDerivative (fun u' ↦ Φ (u', ψ u')) x u| ≤
          2 * (Mf : ℝ) * hessianLocalNorm (fun u' ↦ Φ (u', ψ u')) x u ^ (3 : ℕ) by
    -- Transfer the branch-model cubic estimate back to the reduced objective germ at `x`.
    calc
      |thirdDirectionalDerivative
          (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) x u|
          = |thirdDirectionalDerivative (fun u' ↦ Φ (u', ψ u')) x u| := by
              rw [← hthird_eq]
      _ ≤ 2 * (Mf : ℝ) * hessianLocalNorm (fun u' ↦ Φ (u', ψ u')) x u ^ (3 : ℕ) :=
            hbranch
      _ = 2 * (Mf : ℝ) *
            hessianLocalNorm (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)))
              x u ^ (3 : ℕ) := by
            rw [(hnorm u).symm]
  let gψ : E₁ → ℝ := fun p ↦ Φ (p, ψ p)
  let A : E₁ → ℝ := fun p ↦
    inner ℝ (WithLp.toLp 2 (u, (fderiv ℝ ψ p) u))
      ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (p, ψ p)))
        (WithLp.toLp 2 (u, (fderiv ℝ ψ p) u)))
  have hgψ_contAt : ContDiffAt ℝ 3 gψ x := hcontAt.congr_of_eventuallyEq hEqAt.symm
  have hA_eq_branchQuadratic :
      A =ᶠ[nhds x] fun p ↦ inner ℝ u (hessian gψ p u) := by
    filter_upwards [hs_open.mem_nhds hsx] with p hp
    -- Rewrite the ambient graph quadratic form through the honest branch Hessian on the packet.
    simpa [A, gψ] using
      branchValue_graphQuadraticForm_eq_on_branchNeighborhood
        (Q := Q) (Mf := Mf) (Φ := Φ) (y := y)
        hself hs_open hψ_cont hpacket
        (selectedMinimizerTransport_onImplicitBranch
          (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
          hself hy_mem_interior hy_argmin hy_unique hpacket)
        hp u
  have hbranch_line :
      lineDeriv ℝ A x u = thirdDirectionalDerivative gψ x u := by
    calc
      lineDeriv ℝ A x u
          = lineDeriv ℝ (fun p ↦ inner ℝ u (hessian gψ p u)) x u := by
              exact Filter.EventuallyEq.lineDeriv_eq hA_eq_branchQuadratic
      _ = thirdDirectionalDerivative gψ x u := by
            exact branchValueQuadratic_lineDeriv_eq_thirdDirectionalDerivative
              (g := gψ) (x := x) (u := u) hgψ_contAt
  have hnorm_graph :
      hessianLocalNorm gψ x u =
        hessianLocalNorm (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x))
          (WithLp.toLp 2 (u, (fderiv ℝ ψ x) u)) := by
    -- The local norm is defined by the branch quadratic form, which matches the ambient graph
    -- quadratic form at the base point.
    rw [hessianLocalNorm_def, hessianLocalNorm_def]
    congr 1
    symm
    simpa [gψ] using
      branchValue_graphQuadraticForm_eq_on_branchNeighborhood
        (Q := Q) (Mf := Mf) (Φ := Φ) (y := y)
        hself hs_open hψ_cont hpacket
        (selectedMinimizerTransport_onImplicitBranch
          (Q := Q) (Mf := (Mf : NNReal)) (Φ := Φ) (y := y)
          hself hy_mem_interior hy_argmin hy_unique hpacket)
        hsx u
  have hx_mem_lift :
      WithLp.toLp 2 (x, ψ x) ∈ ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) := by
    simpa using (hpacket x hsx).1
  have hbranch_ambient :
      thirdDirectionalDerivative gψ x u =
        thirdDirectionalDerivative (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x))
          (WithLp.toLp 2 (u, (fderiv ℝ ψ x) u)) := by
    -- Route correction: the branch side is now reduced to the single ambient graph-derivative
    -- bridge, rather than the whole theorem body.
    calc
      thirdDirectionalDerivative gψ x u = lineDeriv ℝ A x u := by rw [hbranch_line]
      _ =
          thirdDirectionalDerivative (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x))
            (WithLp.toLp 2 (u, (fderiv ℝ ψ x) u)) := by
              exact branchGraphQuadratic_lineDeriv_eq_ambientThirdDirectionalDerivative
                (Q := Q) (Mf := Mf) (Φ := Φ) hself hs_open hψ_cont hpacket hsx u
  have hambient_bound :
      |thirdDirectionalDerivative (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x))
          (WithLp.toLp 2 (u, (fderiv ℝ ψ x) u))| ≤
        2 * (Mf : ℝ) *
          hessianLocalNorm (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x))
            (WithLp.toLp 2 (u, (fderiv ℝ ψ x) u)) ^ (3 : ℕ) :=
    hself.third_deriv_bound hx_mem_lift (WithLp.toLp 2 (u, (fderiv ℝ ψ x) u))
  -- The remaining branch-model estimate is now a direct ambient self-concordance bound after the
  -- single graph-derivative bridge above.
  calc
    |thirdDirectionalDerivative gψ x u|
        = |thirdDirectionalDerivative (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x))
            (WithLp.toLp 2 (u, (fderiv ℝ ψ x) u))| := by
              rw [hbranch_ambient]
    _ ≤ 2 * (Mf : ℝ) *
          hessianLocalNorm (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x))
            (WithLp.toLp 2 (u, (fderiv ℝ ψ x) u)) ^ (3 : ℕ) := hambient_bound
    _ = 2 * (Mf : ℝ) * hessianLocalNorm gψ x u ^ (3 : ℕ) := by
          rw [hnorm_graph]

/-- Theorem 5.1.11: let `Q ⊆ E₁ × E₂` be a nonempty convex set. If `Φ` is self-concordant with
positive constant `M_Φ` on `interior Q` for the canonical intrinsic `L²` product lift of
`E₁ × E₂`, and if for every `x` in the displayed source domain `partialMinimizationSourceDom Q`
the fiber minimum is attained at the chosen unique interior minimizer branch `y x` with
positive-definite frozen `yy` Hessian `∇² (Φ ∘ Prod.mk x) (y x)`, then the canonical real
partial-minimization objective is self-concordant on that source domain with the same constant.
The bridge `partialMinimizationSourceDom_eq_dom_of_attainedInteriorArgmin` records the
optional comparison with the canonical effective-domain owner. -/
theorem partialMinimizationObjective_isSelfConcordantOnWith
    {Q : Set (E₁ × E₂)} {Mf : NNRealˣ} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hQ_convex : Convex ℝ Q)
    (hQ_nonempty : Q.Nonempty)
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Mf : NNReal)
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v)) :
    IsSelfConcordantOnWith (partialMinimizationSourceDom Q) (Mf : NNReal)
      (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) := by
  let _ := hQ_nonempty
  -- Route correction: the final owner field is the diagonal cubic bound, so it is cleaner to
  -- close the theorem directly there instead of detouring through the stronger operator criterion.
  refine
    { isOpen_domain := partialMinimizationSourceDom_isOpen Q
      contDiffOn :=
        partialMinimizationObjective_contDiffOn_sourceDom
          (Q := Q) (Mf := Mf) (Φ := Φ) (y := y)
          hself hy_mem_interior hy_argmin hy_unique hyy_pos
      convexOn :=
        partialMinimizationObjective_convexOn_sourceDom
          hQ_convex hself hy_mem_interior hy_argmin
      third_deriv_bound := ?_ }
  intro x hx u
  exact
    partialMinimizationObjective_thirdDerivBound_on_sourceDom
      (Q := Q) (Mf := Mf) (Φ := Φ) (y := y)
      hself hy_mem_interior hy_argmin hy_unique hyy_pos hx u

end
