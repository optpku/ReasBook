/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_18
import Mathlib.Analysis.Calculus.ImplicitContDiff

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin ConvexAnalysis Gradient
open ContinuousLinearMap

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}

/- Proposition 5.0.19 lies in the chapter's partial-minimization / second-order calculus domain.

Sampled owner-style declarations:
- `partialInfProjection` in `Chap03/Theorem_3_1_2_3`, the chapter owner for constrained
  fiberwise infima;
- `extendedRealRealPart_partialInfProjection_eq_sInf_image` in `Chap05/Definition_5_0_18`, the
  real-valued bridge for that owner on finite fibers;
- `hessian` in `Chap01/Definition_1_4_16`, the canonical frozen-slice owner for the `yy`
  second-derivative block;
- `hessian` in `Chap01/Definition_1_4_16`, the intrinsic second-order owner on a real
  inner-product space, here used on the canonical `L²` product lift `Z = WithLp 2 (E₁ × E₂)`.

Best owner abstraction:
- source-facing: `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))`;
- core/canonical: `partialInfProjection Q (Real.toEReal ∘ Φ)`,
  `extendedRealRealPart`, and the frozen-slice Hessian
  `hessian (Φ ∘ Prod.mk x) y`;
- bridge/view: the `x`-slice gradient and the ambient Hessian block formulas obtained by
  composing `hessian (Φ ∘ WithLp.ofLp) (WithLp.toLp 2 (x, y))` with
  `WithLp.fstL`/`WithLp.sndL` and the canonical product-coordinate inclusions.

Primitive data:
- the feasible set `Q : Set (E₁ × E₂)`;
- the objective `Φ : E₁ × E₂ → ℝ`;
- the selected minimizing branch `y : E₁ → E₂`.

Derived API:
- the `x`-slice gradient `∇ (fun x' ↦ Φ (x', y)) x`;
- the inverse-Hessian-based implicit-derivative and Schur-complement operators
  `partialMinimizerImplicitFDeriv` and `partialMinimizationSchurHessian`.

Source/core/bridge triage:
- source-facing: Proposition 5.0.19 and its envelope / implicit-function / Schur-complement
  conclusions for the real surface of the canonical infimal projection;
- core/canonical: `partialInfProjection`, `extendedRealRealPart`,
  the frozen-slice Hessian `hessian (Φ ∘ Prod.mk x) y`, and `hessian` on the intrinsic
  product lift `Z`;
- bridge/view: the displayed `x`-slice gradient and the inverse-`yy` / Schur-complement
  constructions below, written directly from the ambient Hessian with internal mixed-block
  helpers.

This refinement keeps the proposition on the chapter's canonical infimal-projection owner,
uses the canonical frozen-slice Hessian for the `yy` second-order data directly, and packages the
remaining mixed-block formulas into the minimal derived operator API needed by the proposition.
-/

section Value

variable [TopologicalSpace E₁]

/-- Helper for Proposition 5.0.19: if a fiber minimizer is attained at `yy`, then the canonical
extended-real partial infimum itself evaluates to that attained fiber value. -/
private lemma partialInfProjection_eq_argmin_eReal
    (Q : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) {u : E₁} {yy : E₂}
    (hy : yy ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u)) :
    partialInfProjection Q (Real.toEReal ∘ Φ) u = (Φ (u, yy) : EReal) := by
  rcases mem_constrainedArgmin_iff.mp hy with ⟨hyy_mem, hyy_min⟩
  have himage_mem :
      ((Φ (u, yy) : ℝ) : EReal) ∈
        (Real.toEReal ∘ Φ) '' {z : E₁ × E₂ | z ∈ Q ∧ z.1 = u} := by
    refine ⟨(u, yy), ⟨hyy_mem, rfl⟩, by simp⟩
  have himage_nonempty :
      ((Real.toEReal ∘ Φ) '' {z : E₁ × E₂ | z ∈ Q ∧ z.1 = u}).Nonempty := ⟨_, himage_mem⟩
  -- The chosen minimizer gives both a witness in the image and a lower bound on every other
  -- feasible fiber value.
  rw [partialInfProjection_eq_sInf]
  refine le_antisymm ?_ ?_
  · exact sInf_le himage_mem
  · refine le_csInf himage_nonempty ?_
    rintro r ⟨⟨u', y'⟩, hz, rfl⟩
    rcases hz with ⟨hy'_mem, hu'⟩
    change u' = u at hu'
    subst u'
    have hmin : Φ (u, yy) ≤ Φ (u, y') := by
      simpa using hyy_min hy'_mem
    change (Φ (u, yy) : EReal) ≤ (Φ (u, y') : EReal)
    exact_mod_cast hmin

/-- Helper for Proposition 5.0.19: if a fiber minimizer is attained at `yy`, then the canonical
real surface of the partial infimal projection evaluates to the corresponding fiber value. -/
private lemma partialMinimizationObjective_eq_of_mem_argmin
    (Q : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) {u : E₁} {yy : E₂}
    (hy : yy ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u)) :
    extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)) u = Φ (u, yy) := by
  have hu_dom : u ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) := by
    -- Read the attained fiber value back as a finite extended real.
    rw [mem_extendedRealEffectiveDomain_iff, partialInfProjection_eq_argmin_eReal Q Φ hy]
    simp
  -- Once the partial infimum is known to be finite, the Chapter 5 real-part bridge recovers the
  -- attained value.
  apply EReal.coe_injective
  rw [coe_extendedRealRealPart hu_dom, partialInfProjection_eq_argmin_eReal Q Φ hy]

/-- Proposition 5.0.19 (1): on any neighborhood where `y` realizes the fiberwise minima of `Φ`
over `Q`, the canonical real surface of the partial infimal projection agrees with the minimizing
branch `u ↦ Φ (u, y u)`. -/
-- Proof sketch: for each nearby `u`, the hypothesis `hy_argmin` identifies `y u` as the canonical
-- fiber minimizer over `{z | (u, z) ∈ Q}`. The
-- canonical Chapter 5 bridge from `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘
-- Φ)) u` to the fiber infimum therefore evaluates to `Φ (u, y u)`, yielding eventual equality.
theorem partialMinimizationObjective_eventuallyEq_of_eventually_argmin
    (Q : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₁ → E₂)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u)) :
    extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)) =ᶠ[nhds x]
      fun u ↦ Φ (u, y u) := by
  -- Evaluate the reduced objective pointwise through the attained fiber minima supplied by `y`.
  filter_upwards [hy_argmin] with u hu
  exact partialMinimizationObjective_eq_of_mem_argmin Q Φ hu

end Value

section FirstOrder

variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

variable {Q : Set (E₁ × E₂)} {Φ : E₁ × E₂ → ℝ} {x : E₁} {y : E₁ → E₂}

local notation "f" => extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))

section

variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Helper for Proposition 5.0.19: an interior fiber minimizer of the frozen `y`-slice is an
ambient local minimizer, so Fermat's theorem forces its Fréchet derivative to vanish. -/
private lemma frozen_ySlice_hasFDerivAt_zero_of_mem_argmin_interior
    {yx : E₂}
    (hΦ : ContDiffAt ℝ 1 Φ (x, yx))
    (hxy_mem_interior : (x, yx) ∈ interior Q)
    (hy_argmin :
      yx ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    HasFDerivAt (Φ ∘ Prod.mk x) (0 : E₂ →L[ℝ] ℝ) yx := by
  rcases mem_constrainedArgmin_iff.mp hy_argmin with ⟨_, hy_min⟩
  have hΦdiff : DifferentiableAt ℝ Φ (x, yx) := hΦ.differentiableAt (by norm_num)
  have hQ_nhds : Q ∈ nhds (x, yx) := by
    exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hxy_mem_interior) interior_subset
  have hfiber_nhds : (Prod.mk x) ⁻¹' Q ∈ nhds yx := by
    exact (Continuous.prodMk continuous_const continuous_id).continuousAt.preimage_mem_nhds hQ_nhds
  have hlocal : IsLocalMin (Φ ∘ Prod.mk x) yx := hy_min.isLocalMin hfiber_nhds
  have hslice :
      HasFDerivAt (Φ ∘ Prod.mk x) (fderiv ℝ (Φ ∘ Prod.mk x) yx) yx :=
    (hΦdiff.comp yx (hasFDerivAt_prodMk_right x yx).differentiableAt).hasFDerivAt
  have hzero : fderiv ℝ (Φ ∘ Prod.mk x) yx = 0 := hlocal.hasFDerivAt_eq_zero hslice
  -- Route correction: we use Fermat on the frozen `y`-slice itself, instead of forcing a
  -- coordinate-gradient statement before `E₂` is assumed to be an inner-product space.
  simpa [hzero] using hslice

/-- Helper: if `Φ` is `C¹` at `(x, y x)`, the minimizing branch `y` is differentiable at `x`,
the point `(x, y x)` lies in `interior Q`, and `y x` realizes the fiberwise minimum of `Φ` over
the `x`-fiber of `Q`, then the branch `u ↦ Φ (u, y u)` has the envelope gradient
`∇ (fun u' ↦ Φ (u', y x)) x` at `x`. -/
theorem partialMinimizationBranch_hasGradientAt_xGradient_of_mem_argmin
    (hΦ : ContDiffAt ℝ 1 Φ (x, y x))
    (hy : DifferentiableAt ℝ y x)
    (hxy_mem_interior : (x, y x) ∈ interior Q)
    (hy_argmin :
      y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    HasGradientAt (fun u ↦ Φ (u, y u)) (∇ (fun u' ↦ Φ (u', y x)) x) x := by
  have hΦdiff : DifferentiableAt ℝ Φ (x, y x) := hΦ.differentiableAt (by norm_num)
  have hslice_zero :
      HasFDerivAt (Φ ∘ Prod.mk x) 0 (y x) :=
    frozen_ySlice_hasFDerivAt_zero_of_mem_argmin_interior hΦ hxy_mem_interior hy_argmin
  have hslice :
      HasFDerivAt (Φ ∘ Prod.mk x)
        ((fderiv ℝ Φ (x, y x)).comp (inr ℝ E₁ E₂)) (y x) := by
    -- Differentiate the frozen `y`-slice by composing `Φ` with the right-coordinate inclusion.
    simpa [Function.comp] using
      (hΦdiff.hasFDerivAt.comp (y x) (hasFDerivAt_prodMk_right x (y x)))
  have hslice_eq_zero :
      (fderiv ℝ Φ (x, y x)).comp (inr ℝ E₁ E₂) = 0 :=
    hslice.unique hslice_zero
  have hbranch :
      HasFDerivAt (fun u ↦ Φ (u, y u))
        ((fderiv ℝ Φ (x, y x)).comp ((1 : E₁ →L[ℝ] E₁).prod (fderiv ℝ y x))) x := by
    -- Differentiate the graph map `u ↦ (u, y u)` and then apply the chain rule.
    simpa [Function.comp] using
      (hΦdiff.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hy.hasFDerivAt))
  have hfrozen :
      HasFDerivAt (fun u ↦ Φ (u, y x))
        ((fderiv ℝ Φ (x, y x)).comp (inl ℝ E₁ E₂)) x := by
    -- The comparison branch keeps the second coordinate frozen at `y x`.
    simpa [Function.comp] using
      (hΦdiff.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x (y x)))
  have hbranch_inl :
      HasFDerivAt (fun u ↦ Φ (u, y u))
        ((fderiv ℝ Φ (x, y x)).comp (inl ℝ E₁ E₂)) x := by
    convert hbranch using 1
    ext h
    symm
    have hsplit :
        ((1 : E₁ →L[ℝ] E₁).prod (fderiv ℝ y x)) h =
          (inl ℝ E₁ E₂) h + (inr ℝ E₁ E₂) ((fderiv ℝ y x) h) := by
      ext <;> simp
    -- The `y`-slice derivative vanishes, so only the `x`-direction contribution survives.
    change
      (fderiv ℝ Φ (x, y x)) (((1 : E₁ →L[ℝ] E₁).prod (fderiv ℝ y x)) h) =
        ((fderiv ℝ Φ (x, y x)).comp (inl ℝ E₁ E₂)) h
    rw [hsplit]
    have hzero_apply :
        ((fderiv ℝ Φ (x, y x)).comp (inr ℝ E₁ E₂)) ((fderiv ℝ y x) h) = 0 := by
      rw [hslice_eq_zero]
      rfl
    rw [map_add]
    change
      (fderiv ℝ Φ (x, y x)) ((inl ℝ E₁ E₂) h) +
          ((fderiv ℝ Φ (x, y x)).comp (inr ℝ E₁ E₂)) ((fderiv ℝ y x) h) =
        ((fderiv ℝ Φ (x, y x)).comp (inl ℝ E₁ E₂)) h
    rw [hzero_apply, add_zero]
    rfl
  have hfrozen_grad :
      HasGradientAt (fun u' ↦ Φ (u', y x)) (∇ (fun u' ↦ Φ (u', y x)) x) x :=
    hfrozen.differentiableAt.hasGradientAt
  -- Replace the branch derivative by the already-identified derivative of the frozen comparison
  -- branch, then read the result back as a gradient statement.
  rw [hasGradientAt_iff_hasFDerivAt] at hfrozen_grad ⊢
  convert hbranch_inl using 1
  exact hfrozen_grad.unique hfrozen

/-- Proposition 5.0.19 (1): if `Φ` is `C¹` at `(x, y x)`, the minimizing branch `y` is
differentiable at `x`, the base point `(x, y x)` lies in `interior Q`, and `y` realizes the
fiberwise minima of `Φ` near `x`, then the partial-minimization objective has gradient
`∇ (fun u' ↦ Φ (u', y x)) x` at `x`. -/
theorem partialMinimizationObjective_hasGradientAt_of_eventually_argmin
    (hΦ : ContDiffAt ℝ 1 Φ (x, y x))
    (hy : DifferentiableAt ℝ y x)
    (hxy_mem_interior : (x, y x) ∈ interior Q)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u)) :
    HasGradientAt f (∇ (fun u' ↦ Φ (u', y x)) x) x := by
  exact
    (partialMinimizationBranch_hasGradientAt_xGradient_of_mem_argmin
      hΦ hy hxy_mem_interior hy_argmin.self_of_nhds).congr_of_eventuallyEq
      (partialMinimizationObjective_eventuallyEq_of_eventually_argmin Q Φ x y hy_argmin)

/-- Proposition 5.0.19 (1), pointwise form: if `Φ` is `C¹` at `(x, y x)`, the minimizing branch
`y` is differentiable at `x`, the base point `(x, y x)` lies in `interior Q`, and `y` realizes the
fiberwise minima of `Φ` near `x`, then the gradient of the partial-minimization objective is the
`x`-gradient of `Φ` with `y` frozen at `y x`. -/
theorem partialMinimizationObjective_gradient_eq_xGradient_of_eventually_argmin
    (hΦ : ContDiffAt ℝ 1 Φ (x, y x))
    (hy : DifferentiableAt ℝ y x)
    (hxy_mem_interior : (x, y x) ∈ interior Q)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u)) :
    ∇ f x = ∇ (fun u' ↦ Φ (u', y x)) x := by
  exact
    (partialMinimizationObjective_hasGradientAt_of_eventually_argmin
      hΦ hy hxy_mem_interior hy_argmin).gradient

end

end FirstOrder

section SecondOrder

variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

local notation "Z" => WithLp 2 (E₁ × E₂)

private abbrev partialMinimizationLift (Φ : E₁ × E₂ → ℝ) : Z → ℝ :=
  Φ ∘ (WithLp.ofLp : Z → E₁ × E₂)

/-- Helper for Proposition 5.0.19: the lifted `L²` product objective is `C²` at the canonical
product point whenever the original objective is `C²` at the corresponding raw pair. -/
private lemma partialMinimizationLift_contDiffAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, y)) :
    ContDiffAt ℝ 2 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y)) := by
  -- The lift is just `Φ` composed with the fixed `L²` product equivalence back to raw pairs.
  simpa [partialMinimizationLift, Function.comp] using
    hPhi.comp (WithLp.toLp 2 (x, y))
      ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂ : Z ≃L[ℝ] E₁ × E₂) :
          Z →L[ℝ] E₁ × E₂)).contDiff.contDiffAt)

/-- Helper for Proposition 5.0.19: a `C²` scalar objective on the lifted `L²` product has a
genuinely differentiable ambient gradient at the base point. -/
private lemma partialMinimizationLift_gradient_differentiableAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, y)) :
    DifferentiableAt ℝ (∇ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, y)) := by
  let D : StrongDual ℝ Z →L[ℝ] Z :=
    (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hLift : ContDiffAt ℝ 2 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y)) :=
    partialMinimizationLift_contDiffAt Φ x y hPhi
  have hfderiv_C1 :
      ContDiffAt ℝ 1 (fderiv ℝ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, y)) := by
    -- Differentiating once leaves a `C¹` family of Fréchet derivatives.
    exact hLift.fderiv_right (by norm_num)
  have hGrad_C1 :
      ContDiffAt ℝ 1 (∇ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, y)) := by
    -- Rewrite the gradient through the Riesz isomorphism and transport the `C¹` regularity of
    -- `fderiv`.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp (WithLp.toLp 2 (x, y)) hfderiv_C1
  -- Rewrite the gradient through the Riesz isomorphism and transport differentiability from
  -- `fderiv`.
  exact hGrad_C1.differentiableAt (by norm_num)

private abbrev partialMinimizationAmbientHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₁ × E₂ →L[ℝ] Z :=
  hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.toContinuousLinearMap

private abbrev partialMinimizationXXHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₁ →L[ℝ] E₁ :=
  WithLp.fstL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x y ∘L inl ℝ E₁ E₂

private abbrev partialMinimizationXYHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₂ →L[ℝ] E₁ :=
  WithLp.fstL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x y ∘L inr ℝ E₁ E₂

private abbrev partialMinimizationYXHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₁ →L[ℝ] E₂ :=
  WithLp.sndL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x y ∘L inl ℝ E₁ E₂

variable {Φ : E₁ × E₂ → ℝ} {x : E₁} {y : E₁ → E₂}

/-- The formal implicit-function linear map attached to a critical minimizing branch. When the
frozen-slice `yy` Hessian is invertible, Proposition 5.0.19 (2) identifies this operator with the
Fréchet derivative of the minimizing branch. -/
def partialMinimizerImplicitFDeriv
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₁ →L[ℝ] E₂ :=
  -((hessian (Φ ∘ Prod.mk x) y).inverse.comp
    (partialMinimizationYXHessian Φ x y))

/-- The formal Schur-complement operator governing the Hessian of the partial-minimization
objective along a critical minimizing branch. Under an invertible frozen-slice `yy` Hessian,
Proposition 5.0.19 (3) identifies the Hessian of the partial-minimization objective with this
operator. -/
def partialMinimizationSchurHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₁ →L[ℝ] E₁ :=
  partialMinimizationXXHessian Φ x y +
    (partialMinimizationXYHessian Φ x y).comp
      (partialMinimizerImplicitFDeriv Φ x y)

/-- Helper for Proposition 5.0.19: differentiating the ambient `y`-gradient of the lifted
objective produces the `y`-component of the canonical ambient Hessian block operator. -/
private lemma partialMinimizationYGradient_hasFDerivAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, y)) :
    HasFDerivAt
      (fun z : E₁ × E₂ ↦
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z)))
      ((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x y))
      (x, y) := by
  have hGrad :
      HasFDerivAt
        (fun z : Z ↦ ∇ (partialMinimizationLift Φ) z)
        (hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y)))
        (WithLp.toLp 2 (x, y)) := by
    -- The Hessian is, by definition, the Fréchet derivative of the ambient gradient.
      simpa [hessian] using
        (partialMinimizationLift_gradient_differentiableAt Φ x y hPhi).hasFDerivAt
  -- Compose the ambient gradient derivative with the `L²` product chart and then project to the
  -- `y`-component.
  have hToLp :
      HasFDerivAt
        (fun z : E₁ × E₂ ↦ ∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))
        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y))).comp
          ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm : (E₁ × E₂) →L[ℝ] Z))
        (x, y) := by
    simpa [Function.comp] using
      hGrad.comp (x, y)
        (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm : (E₁ × E₂) →L[ℝ] Z).hasFDerivAt)
  simpa [partialMinimizationAmbientHessian, Function.comp] using
    (WithLp.sndL 2 ℝ E₁ E₂).hasFDerivAt.comp (x, y) hToLp

/-- Helper for Proposition 5.0.19: the ambient `y`-gradient of the lifted objective is `C¹` at the
base point, so the implicit-function theorem can be applied to its critical-point equation. -/
private lemma partialMinimizationYGradient_contDiffAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, y)) :
    ContDiffAt ℝ 1
      (fun z : E₁ × E₂ ↦
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z)))
      (x, y) := by
  let D : StrongDual ℝ Z →L[ℝ] Z :=
    (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hLift : ContDiffAt ℝ 2 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y)) :=
    partialMinimizationLift_contDiffAt Φ x y hPhi
  have hfderiv_C1 :
      ContDiffAt ℝ 1 (fderiv ℝ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, y)) := by
    -- Differentiating the lifted objective once leaves a `C¹` field of Fréchet derivatives.
    exact hLift.fderiv_right (by norm_num)
  have hGrad_C1 :
      ContDiffAt ℝ 1 (∇ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, y)) := by
    -- The gradient is the Riesz-transport of `fderiv`, so it inherits the same local smoothness.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp (WithLp.toLp 2 (x, y)) hfderiv_C1
  -- Compose the ambient gradient with the fixed `L²` product chart and project to the
  -- `y`-component.
  simpa [Function.comp] using
    (WithLp.sndL 2 ℝ E₁ E₂).contDiff.contDiffAt.comp (x, y)
      (hGrad_C1.comp (x, y)
        (((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z) : (E₁ × E₂) →L[ℝ] Z)).contDiff.contDiffAt))

/-- Helper for Proposition 5.0.19: at a `C¹` point, the `y`-component of the ambient gradient of
the lifted product objective is exactly the gradient of the frozen `y`-slice. -/
private lemma partialMinimizationYGradient_eq_frozenYGradient
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂)
    (hPhi : ContDiffAt ℝ 1 Φ (x, y)) :
    WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y))) =
      ∇ (Φ ∘ Prod.mk x) y := by
  have hLiftDiff :
      DifferentiableAt ℝ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y)) :=
    by
      -- Only first-order differentiability is needed to compare the two gradient presentations.
      simpa [partialMinimizationLift, Function.comp] using
        (hPhi.differentiableAt (by norm_num)).comp (WithLp.toLp 2 (x, y))
          ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂ : Z ≃L[ℝ] E₁ × E₂) :
            Z →L[ℝ] E₁ × E₂)).hasFDerivAt.differentiableAt)
  have hAmbient :
      HasGradientAt (Φ ∘ Prod.mk x)
        (WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y)))) y := by
    rw [hasGradientAt_iff_hasFDerivAt]
    -- Differentiate the lifted objective along the right-coordinate inclusion and rewrite the
    -- resulting dual map as the dual of the ambient `y`-gradient component.
    convert
      (hLiftDiff.hasGradientAt.hasFDerivAt.comp y
        (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.hasFDerivAt.comp y
          (hasFDerivAt_prodMk_right x y)))) using 1
    ext k
    simp [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      partialMinimizationLift, WithLp.prod_inner_apply]
  have hSliceDiff :
      DifferentiableAt ℝ (Φ ∘ Prod.mk x) y := by
    -- Freeze the first coordinate and differentiate the original objective in the `y`-direction.
    simpa [Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp y (hasFDerivAt_prodMk_right x y).differentiableAt
  -- Both vectors give gradients of the same frozen slice at the same point, so they coincide.
  exact hAmbient.unique hSliceDiff.hasGradientAt

/-- Helper for Proposition 5.0.19: at a `C¹` point, the `x`-component of the ambient gradient of
the lifted product objective is exactly the gradient of the frozen `x`-slice. -/
private lemma partialMinimizationXGradient_eq_frozenXGradient
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂)
    (hPhi : ContDiffAt ℝ 1 Φ (x, y)) :
    WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y))) =
      ∇ (fun u : E₁ ↦ Φ (u, y)) x := by
  have hLiftDiff :
      DifferentiableAt ℝ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y)) :=
    by
      -- Only first-order differentiability is needed to compare the two gradient presentations.
      simpa [partialMinimizationLift, Function.comp] using
        (hPhi.differentiableAt (by norm_num)).comp (WithLp.toLp 2 (x, y))
          ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂ : Z ≃L[ℝ] E₁ × E₂) :
            Z →L[ℝ] E₁ × E₂)).hasFDerivAt.differentiableAt)
  have hAmbient :
      HasGradientAt (fun u : E₁ ↦ Φ (u, y))
        (WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y)))) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    -- Differentiate the lifted objective along the left-coordinate inclusion and rewrite the
    -- resulting dual map as the dual of the ambient `x`-gradient component.
    convert
      (hLiftDiff.hasGradientAt.hasFDerivAt.comp x
        (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left x y)))) using 1
    ext h
    simp [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      partialMinimizationLift, WithLp.prod_inner_apply]
  have hSliceDiff :
      DifferentiableAt ℝ (fun u : E₁ ↦ Φ (u, y)) x := by
    -- Freeze the second coordinate and differentiate the original objective in the `x`-direction.
    simpa [Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp x (hasFDerivAt_prodMk_left x y).differentiableAt
  -- Both vectors give gradients of the same frozen slice at the same point, so they coincide.
  exact hAmbient.unique hSliceDiff.hasGradientAt

/-- Helper for Proposition 5.0.19: near a `C²` base point, the ambient `y`-gradient of the lifted
product objective agrees with the gradient of the frozen `y`-slice. -/
private lemma partialMinimizationYGradient_eventuallyEq_frozenYGradient
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, y)) :
    (fun z : E₁ × E₂ ↦
      WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))) =ᶠ[nhds (x, y)]
        fun z : E₁ × E₂ ↦ ∇ (Φ ∘ Prod.mk z.1) z.2 := by
  rcases hPhi.contDiffOn (m := 1) (by norm_num) (by simp) with ⟨u, hu_nhds, hContU⟩
  rcases mem_nhds_iff.mp hu_nhds with ⟨v, hv_sub, hv_open, hv_mem⟩
  have hContV : ContDiffOn ℝ 1 Φ v := hContU.mono hv_sub
  -- Shrink to an open neighborhood where pointwise `C¹` control lets us compare the two
  -- gradient presentations directly.
  filter_upwards [hv_open.mem_nhds hv_mem] with z hz
  exact partialMinimizationYGradient_eq_frozenYGradient Φ z.1 z.2
    (hContV.contDiffAt (hv_open.mem_nhds hz))

/-- Helper for Proposition 5.0.19: the frozen `y`-gradient is differentiable at a `C²` point, and
its derivative is the frozen-slice Hessian. -/
private lemma frozenYGradient_hasFDerivAt_hessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, y)) :
    HasFDerivAt (fun yy : E₂ ↦ ∇ (Φ ∘ Prod.mk x) yy) (hessian (Φ ∘ Prod.mk x) y) y := by
  let D : StrongDual ℝ E₂ →L[ℝ] E₂ :=
    (InnerProductSpace.toDual ℝ E₂).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hSlice :
      ContDiffAt ℝ 2 (Φ ∘ Prod.mk x) y := by
    have hProdMkRight : ContDiffAt ℝ 2 (Prod.mk x : E₂ → E₁ × E₂) y := by
      fun_prop
    simpa [Function.comp] using
      hPhi.comp y hProdMkRight
  have hfderiv_C1 :
      ContDiffAt ℝ 1 (fderiv ℝ (Φ ∘ Prod.mk x)) y := by
    -- Differentiating the frozen slice once leaves a `C¹` field of Fréchet derivatives.
    exact hSlice.fderiv_right (by norm_num)
  have hGradDiff :
      DifferentiableAt ℝ (∇ (Φ ∘ Prod.mk x)) y := by
    -- The frozen-slice gradient is the Riesz transport of its `fderiv` field.
    have hGrad_C1 : ContDiffAt ℝ 1 (∇ (Φ ∘ Prod.mk x)) y := by
      simpa [gradient, D] using D.contDiff.contDiffAt.comp y hfderiv_C1
    exact hGrad_C1.differentiableAt (by norm_num)
  -- By definition, the frozen-slice Hessian is the derivative of this gradient map.
  simpa [hessian] using hGradDiff.hasFDerivAt

/-- Helper for Proposition 5.0.19: restricting the ambient `y`-gradient derivative to the
`y`-direction recovers the frozen-slice `yy` Hessian block. -/
private lemma partialMinimizationYGradient_comp_inr_eq_yyHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, y)) :
    (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x y)).comp
      (inr ℝ E₁ E₂)) = hessian (Φ ∘ Prod.mk x) y := by
  have hAmbientDeriv :
      HasFDerivAt
        (fun yy : E₂ ↦
          WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy))))
        (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x y)).comp
          (inr ℝ E₁ E₂))
        y := by
    -- Freeze `x` and differentiate the ambient `y`-gradient only in the `y`-direction.
    simpa [Function.comp] using
      (partialMinimizationYGradient_hasFDerivAt Φ x y hPhi).comp y (hasFDerivAt_prodMk_right x y)
  have hEventEq :
      (fun yy : E₂ ↦
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)))) =ᶠ[nhds y]
          fun yy : E₂ ↦ ∇ (Φ ∘ Prod.mk x) yy := by
    -- Specialize the neighborhood-level comparison of the two `y`-gradient presentations to the
    -- vertical line `yy ↦ (x, yy)`.
    exact
      (partialMinimizationYGradient_eventuallyEq_frozenYGradient Φ x y hPhi).comp_tendsto
        ((Continuous.prodMk continuous_const continuous_id).continuousAt.tendsto)
  have hFrozenDeriv :
      HasFDerivAt
        (fun yy : E₂ ↦
          WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy))))
        (hessian (Φ ∘ Prod.mk x) y) y := by
    -- Transfer the canonical frozen-slice Hessian formula through the local equality above.
    exact (frozenYGradient_hasFDerivAt_hessian Φ x y hPhi).congr_of_eventuallyEq hEventEq
  exact hAmbientDeriv.unique hFrozenDeriv

/-- Helper for Proposition 5.0.19: differentiating the ambient `x`-gradient along a branch
`u ↦ (u, b u)` yields the `XX + XY ∘ Db` block formula. -/
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
    -- Compose the ambient gradient derivative with the fixed `L²` product chart and then project
    -- to the `x`-component.
    have hToLp :
        HasFDerivAt
          (fun z : E₁ × E₂ ↦ ∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, b x))).comp
            ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm : (E₁ × E₂) →L[ℝ] Z))
          (x, b x) := by
      simpa [Function.comp] using
        hAmbient.comp (x, b x)
          (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm : (E₁ × E₂) →L[ℝ] Z).hasFDerivAt)
    simpa [partialMinimizationAmbientHessian, Function.comp] using
      (WithLp.fstL 2 ℝ E₁ E₂).hasFDerivAt.comp (x, b x) hToLp
  have hGraph :
      HasFDerivAt (fun u : E₁ ↦ (u, b u)) ((1 : E₁ →L[ℝ] E₁).prod b') x := by
    -- Differentiate the graph map of the branch.
    simpa using (hasFDerivAt_id x).prodMk hb
  have hComp := hGrad.comp x hGraph
  -- Split the product derivative into its `x`- and `y`-direction pieces.
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

variable {Q : Set (E₁ × E₂)}

local notation "f" => extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))

/-- Proposition 5.0.19 (2): if the frozen-slice `yy` Hessian
`hessian (Φ ∘ Prod.mk x) (y x)` is invertible and the branch `u ↦ y u` stays on the locally
unique fiberwise minimizer branch of `Φ` through interior points of `Q` near `(x, y x)`, then `y`
is Fréchet differentiable at `x` with derivative given by the implicit-equation formula. -/
-- Proof sketch: the minimizing-branch hypotheses identify `u ↦ y u` with the local implicit
-- minimizer branch near `(x, y x)`. The interior hypothesis turns these constrained fiberwise
-- minimizers into unconstrained local minimizers of the `y`-slice, so the branch satisfies the
-- `y`-gradient equation near `x`. Apply the implicit function theorem to that critical-point
-- equation and solve the `yy`-block linear equation using the inverse Hessian hypothesis.
theorem partialMinimizer_hasFDerivAt_of_isInvertible_yyHessian
    (hPhi : ContDiffAt ℝ 2 Φ (x, y x))
    (hy_tendsto : Filter.Tendsto y (nhds x) (nhds (y x)))
    (hy_mem_interior : ∀ᶠ u in nhds x, (u, y u) ∈ interior Q)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u))
    (hy_unique : ∀ᶠ u in nhds x,
      ∀ z : E₂, z ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) → z = y u)
    (hyy_inv : (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible) :
    HasFDerivAt y (partialMinimizerImplicitFDeriv Φ x (y x)) x := by
  let F : E₁ × E₂ → E₂ := fun z ↦
    WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))
  have hF_cont :
      ContDiffAt ℝ 1 F (x, y x) := by
    simpa [F] using partialMinimizationYGradient_contDiffAt Φ x (y x) hPhi
  have hF_deriv :
      HasFDerivAt F ((WithLp.sndL 2 ℝ E₁ E₂).comp
        (partialMinimizationAmbientHessian Φ x (y x))) (x, y x) := by
    simpa [F] using partialMinimizationYGradient_hasFDerivAt Φ x (y x) hPhi
  have hF_inr :
      fderiv ℝ F (x, y x) ∘L inr ℝ E₁ E₂ = hessian (Φ ∘ Prod.mk x) (y x) := by
    rw [hF_deriv.fderiv]
    exact partialMinimizationYGradient_comp_inr_eq_yyHessian Φ x (y x) hPhi
  have hF_inl :
      fderiv ℝ F (x, y x) ∘L inl ℝ E₁ E₂ = partialMinimizationYXHessian Φ x (y x) := by
    rw [hF_deriv.fderiv]
    rfl
  have hIf2 : (fderiv ℝ F (x, y x) ∘L inr ℝ E₁ E₂).IsInvertible := by
    rwa [hF_inr]
  have hbase_zero :
      F (x, y x) = 0 := by
    have hzero_deriv :
        HasFDerivAt (Φ ∘ Prod.mk x) 0 (y x) :=
      frozen_ySlice_hasFDerivAt_zero_of_mem_argmin_interior
        (x := x) (yx := y x) (hPhi.of_le (by norm_num))
        hy_mem_interior.self_of_nhds hy_argmin.self_of_nhds
    have hslice_diff :
        DifferentiableAt ℝ (Φ ∘ Prod.mk x) (y x) := by
      simpa [Function.comp] using
        (hPhi.differentiableAt (by norm_num)).comp (y x)
          (hasFDerivAt_prodMk_right x (y x)).differentiableAt
    have hgrad_zero : ∇ (Φ ∘ Prod.mk x) (y x) = 0 := by
      simpa using (hzero_deriv.hasGradientAt.unique hslice_diff.hasGradientAt).symm
    -- Route correction: compare the stationary map with the frozen-slice gradient at the base
    -- point, then use Fermat's vanishing derivative on the fiber minimizer.
    calc
      F (x, y x) = ∇ (Φ ∘ Prod.mk x) (y x) := by
        simpa [F] using
          partialMinimizationYGradient_eq_frozenYGradient Φ x (y x) (hPhi.of_le (by norm_num))
      _ = 0 := hgrad_zero
  have hpair_tendsto :
      Filter.Tendsto (fun u ↦ (u, y u)) (nhds x) (nhds (x, y x)) := by
    simpa [nhds_prod_eq] using continuousAt_id.tendsto.prodMk hy_tendsto
  rcases hPhi.contDiffOn (m := 1) (by norm_num) (by simp) with ⟨s, hs_nhds, hPhiOn_s⟩
  rcases mem_nhds_iff.mp hs_nhds with ⟨t, ht_sub, ht_open, ht_mem⟩
  have hPhiOn_t : ContDiffOn ℝ 1 Φ t := hPhiOn_s.mono ht_sub
  have hEventuallyInT : ∀ᶠ u in nhds x, (u, y u) ∈ t := by
    exact hpair_tendsto.eventually (ht_open.mem_nhds ht_mem)
  have hstationary_event :
      ∀ᶠ u in nhds x, F (u, y u) = 0 := by
    filter_upwards [hEventuallyInT, hy_mem_interior, hy_argmin] with u hu_t hu_int hu_arg
    have hPhiu : ContDiffAt ℝ 1 Φ (u, y u) := hPhiOn_t.contDiffAt (ht_open.mem_nhds hu_t)
    have hzero_deriv :
        HasFDerivAt (Φ ∘ Prod.mk u) 0 (y u) :=
      frozen_ySlice_hasFDerivAt_zero_of_mem_argmin_interior
        (x := u) (yx := y u) hPhiu hu_int hu_arg
    have hslice_diff :
        DifferentiableAt ℝ (Φ ∘ Prod.mk u) (y u) := by
      simpa [Function.comp] using
        (hPhiu.differentiableAt (by norm_num)).comp (y u)
          (hasFDerivAt_prodMk_right u (y u)).differentiableAt
    have hgrad_zero : ∇ (Φ ∘ Prod.mk u) (y u) = 0 := by
      simpa using (hzero_deriv.hasGradientAt.unique hslice_diff.hasGradientAt).symm
    calc
      F (u, y u) = ∇ (Φ ∘ Prod.mk u) (y u) := by
        simpa [F] using partialMinimizationYGradient_eq_frozenYGradient Φ u (y u) hPhiu
      _ = 0 := hgrad_zero
  have hstationary_eq :
      ∀ᶠ u in nhds x, F (u, y u) = F (x, y x) := by
    filter_upwards [hstationary_event] with u hu
    simpa [hbase_zero] using hu
  let ψ : E₁ → E₂ := hF_cont.implicitFunction (pn := by norm_num) hIf2
  have hψ_eq :
      y =ᶠ[nhds x] ψ := by
    have hEqIff :
        ∀ᶠ v in nhds (x, y x), F v = F (x, y x) ↔ ψ v.1 = v.2 := by
      simpa [ψ] using hF_cont.eventually_apply_eq_iff_implicitFunction (pn := by norm_num) hIf2
    have hEqAlong := hpair_tendsto.eventually hEqIff
    filter_upwards [hEqAlong, hstationary_eq] with u huIff huEq
    exact (huIff.mp huEq).symm
  have hψ_deriv :
      HasStrictFDerivAt ψ (partialMinimizerImplicitFDeriv Φ x (y x)) x := by
    simpa [ψ, partialMinimizerImplicitFDeriv, hF_inr, hF_inl] using
      (hF_cont.hasStrictFDerivAt_implicitFunction (pn := by norm_num) hIf2)
  exact hψ_deriv.hasFDerivAt.congr_of_eventuallyEq hψ_eq

/-- Helper for Proposition 5.0.19: affine lines through `x` in direction `h` have derivative
`h` at every parameter value. -/
private lemma partialMinimization_line_hasDerivAt
    (x h : E₁) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using (((hasDerivAt_id t).smul_const h).const_add x)

/-- Proposition 5.0.19 (2), linewise companion: the Fréchet derivative formula for the critical
branch yields the directional derivative of every line `t ↦ y (x + t • h)` through `x`. -/
theorem partialMinimizer_hasDerivAt_line_of_isInvertible_yyHessian
    (hPhi : ContDiffAt ℝ 2 Φ (x, y x))
    (hy_tendsto : Filter.Tendsto y (nhds x) (nhds (y x)))
    (hy_mem_interior : ∀ᶠ u in nhds x, (u, y u) ∈ interior Q)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u))
    (hy_unique : ∀ᶠ u in nhds x,
      ∀ z : E₂, z ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) → z = y u)
    (hyy_inv : (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible)
    (h : E₁) :
    HasDerivAt (fun t : ℝ ↦ y (x + t • h))
      ((partialMinimizerImplicitFDeriv Φ x (y x)) h) 0 := by
  have hy_fderiv :
      HasFDerivAt y (partialMinimizerImplicitFDeriv Φ x (y x)) x :=
    partialMinimizer_hasFDerivAt_of_isInvertible_yyHessian
      hPhi hy_tendsto hy_mem_interior hy_argmin hy_unique hyy_inv
  have hy_fderiv_zero :
      HasFDerivAt y (partialMinimizerImplicitFDeriv Φ x (y x)) (x + (0 : ℝ) • h) := by
    simpa using hy_fderiv
  -- Compose the branch derivative with the affine line through `x` in direction `h`.
  simpa using
    hy_fderiv_zero.comp_hasDerivAt (0 : ℝ) (partialMinimization_line_hasDerivAt x h 0)

/-- Proposition 5.0.19 (3): under the same local interior minimizer-branch and invertibility
hypotheses, the Hessian of the partial-minimization objective at `x` is the Schur complement of
the ambient Hessian of `Φ` at `(x, y x)`. -/
-- Proof sketch: first use the minimizing-branch hypotheses to identify the partial-minimization
-- objective with the canonical minimizing branch near `x`. The preceding differentiability formula
-- for `y`, together with the first-order envelope identity `∇ f(x) = ∇ₓ Φ(x, y(x))`, then yields
-- the Schur complement formula on the canonical Hessian owner `hessian`.
theorem partialMinimizationObjective_hessian_eq_schur_of_isInvertible_yyHessian
    (hPhi : ContDiffAt ℝ 2 Φ (x, y x))
    (hy_tendsto : Filter.Tendsto y (nhds x) (nhds (y x)))
    (hy_mem_interior : ∀ᶠ u in nhds x, (u, y u) ∈ interior Q)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u))
    (hy_unique : ∀ᶠ u in nhds x,
      ∀ z : E₂, z ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) → z = y u)
    (hyy_inv : (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible) :
    hessian f x = partialMinimizationSchurHessian Φ x (y x) := by
  have hPhi1 : ContDiffAt ℝ 1 Φ (x, y x) := hPhi.of_le (by norm_num)
  let F : E₁ × E₂ → E₂ := fun z ↦
    WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))
  let Gy : E₁ → E₁ := fun u ↦
    WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, y u)))
  have hF_cont :
      ContDiffAt ℝ 1 F (x, y x) := by
    -- Rebuild the stationary map used in the source-faithful implicit-function argument.
    simpa [F] using partialMinimizationYGradient_contDiffAt Φ x (y x) hPhi
  have hF_deriv :
      HasFDerivAt F ((WithLp.sndL 2 ℝ E₁ E₂).comp
        (partialMinimizationAmbientHessian Φ x (y x))) (x, y x) := by
    -- Its derivative is the `y`-block of the ambient Hessian.
    simpa [F] using partialMinimizationYGradient_hasFDerivAt Φ x (y x) hPhi
  have hF_inr :
      fderiv ℝ F (x, y x) ∘L inr ℝ E₁ E₂ = hessian (Φ ∘ Prod.mk x) (y x) := by
    rw [hF_deriv.fderiv]
    exact partialMinimizationYGradient_comp_inr_eq_yyHessian Φ x (y x) hPhi
  have hF_inl :
      fderiv ℝ F (x, y x) ∘L inl ℝ E₁ E₂ = partialMinimizationYXHessian Φ x (y x) := by
    rw [hF_deriv.fderiv]
    rfl
  have hIf2 : (fderiv ℝ F (x, y x) ∘L inr ℝ E₁ E₂).IsInvertible := by
    rwa [hF_inr]
  let ψ : E₁ → E₂ := hF_cont.implicitFunction (pn := by norm_num) hIf2
  let Gψ : E₁ → E₁ := fun u ↦
    WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u)))
  have hbase_zero :
      F (x, y x) = 0 := by
    have hzero_deriv :
        HasFDerivAt (Φ ∘ Prod.mk x) 0 (y x) :=
      frozen_ySlice_hasFDerivAt_zero_of_mem_argmin_interior
        (x := x) (yx := y x) hPhi1 hy_mem_interior.self_of_nhds hy_argmin.self_of_nhds
    have hslice_diff :
        DifferentiableAt ℝ (Φ ∘ Prod.mk x) (y x) := by
      -- The frozen `y`-slice is differentiable because `Φ` is `C¹` at the base point.
      simpa [Function.comp] using
        (hPhi1.differentiableAt (by norm_num)).comp (y x)
          (hasFDerivAt_prodMk_right x (y x)).differentiableAt
    have hgrad_zero : ∇ (Φ ∘ Prod.mk x) (y x) = 0 := by
      simpa using (hzero_deriv.hasGradientAt.unique hslice_diff.hasGradientAt).symm
    -- Compare the stationary map with the frozen-slice gradient at the base point.
    calc
      F (x, y x) = ∇ (Φ ∘ Prod.mk x) (y x) := by
        simpa [F] using partialMinimizationYGradient_eq_frozenYGradient Φ x (y x) hPhi1
      _ = 0 := hgrad_zero
  have hpair_tendsto :
      Filter.Tendsto (fun u ↦ (u, y u)) (nhds x) (nhds (x, y x)) := by
    simpa [nhds_prod_eq] using continuousAt_id.tendsto.prodMk hy_tendsto
  rcases hPhi.contDiffOn (m := 1) (by norm_num) (by simp) with ⟨sPhi, hsPhi_nhds, hPhiOn_sPhi⟩
  rcases mem_nhds_iff.mp hsPhi_nhds with ⟨tPhi, htPhi_sub, htPhi_open, htPhi_mem⟩
  have hPhiOn_tPhi : ContDiffOn ℝ 1 Φ tPhi := hPhiOn_sPhi.mono htPhi_sub
  have hEventuallyInTPhi : ∀ᶠ u in nhds x, (u, y u) ∈ tPhi := by
    exact hpair_tendsto.eventually (htPhi_open.mem_nhds htPhi_mem)
  have hstationary_event :
      ∀ᶠ u in nhds x, F (u, y u) = 0 := by
    filter_upwards [hEventuallyInTPhi, hy_mem_interior, hy_argmin] with u hu_tPhi hu_int hu_arg
    have hPhiu : ContDiffAt ℝ 1 Φ (u, y u) :=
      hPhiOn_tPhi.contDiffAt (htPhi_open.mem_nhds hu_tPhi)
    have hzero_deriv :
        HasFDerivAt (Φ ∘ Prod.mk u) 0 (y u) :=
      frozen_ySlice_hasFDerivAt_zero_of_mem_argmin_interior
        (x := u) (yx := y u) hPhiu hu_int hu_arg
    have hslice_diff :
        DifferentiableAt ℝ (Φ ∘ Prod.mk u) (y u) := by
      -- Near the base point, the same frozen-slice argument gives the stationary equation.
      simpa [Function.comp] using
        (hPhiu.differentiableAt (by norm_num)).comp (y u)
          (hasFDerivAt_prodMk_right u (y u)).differentiableAt
    have hgrad_zero : ∇ (Φ ∘ Prod.mk u) (y u) = 0 := by
      simpa using (hzero_deriv.hasGradientAt.unique hslice_diff.hasGradientAt).symm
    calc
      F (u, y u) = ∇ (Φ ∘ Prod.mk u) (y u) := by
        simpa [F] using partialMinimizationYGradient_eq_frozenYGradient Φ u (y u) hPhiu
      _ = 0 := hgrad_zero
  have hstationary_eq :
      ∀ᶠ u in nhds x, F (u, y u) = F (x, y x) := by
    filter_upwards [hstationary_event] with u hu
    simpa [hbase_zero] using hu
  have hψ_self : ψ x = y x := by
    -- The canonical implicit branch passes through the given minimizer at the base point.
    simpa [ψ] using hF_cont.implicitFunction_apply_self (pn := by norm_num) hIf2
  have hψ_eq :
      y =ᶠ[nhds x] ψ := by
    have hEqIff :
        ∀ᶠ v in nhds (x, y x), F v = F (x, y x) ↔ ψ v.1 = v.2 := by
      simpa [ψ] using
        hF_cont.eventually_apply_eq_iff_implicitFunction (pn := by norm_num) hIf2
    have hEqAlong := hpair_tendsto.eventually hEqIff
    filter_upwards [hEqAlong, hstationary_eq] with u huIff huEq
    exact (huIff.mp huEq).symm
  have hψ_cont : ContDiffAt ℝ 1 ψ x := by
    -- The implicit branch is itself `C¹` at the base point.
    simpa [ψ] using hF_cont.contDiffAt_implicitFunction (pn := by norm_num) hIf2
  have hψ_tendsto : Filter.Tendsto ψ (nhds x) (nhds (y x)) := by
    -- Continuity of the implicit branch keeps its graph near `(x, y x)`.
    simpa [hψ_self] using hψ_cont.continuousAt.tendsto
  have hpairψ_tendsto :
      Filter.Tendsto (fun u ↦ (u, ψ u)) (nhds x) (nhds (x, y x)) := by
    simpa [nhds_prod_eq] using continuousAt_id.tendsto.prodMk hψ_tendsto
  have hψ_mem_interior :
      ∀ᶠ u in nhds x, (u, ψ u) ∈ interior Q := by
    filter_upwards [hy_mem_interior, hψ_eq] with u hu_int hu_eq
    simpa [hu_eq] using hu_int
  have hψ_argmin :
      ∀ᶠ u in nhds x,
        ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) := by
    filter_upwards [hy_argmin, hψ_eq] with u hu_arg hu_eq
    simpa [hu_eq] using hu_arg
  rcases hψ_cont.contDiffOn (m := 1) le_rfl (by simp) with ⟨sψ, hsψ_nhds, hψOn_sψ⟩
  rcases mem_nhds_iff.mp hsψ_nhds with ⟨tψ, htψ_sub, htψ_open, htψ_mem⟩
  have hψOn_tψ : ContDiffOn ℝ 1 ψ tψ := hψOn_sψ.mono htψ_sub
  have hEventuallyInTPsi : ∀ᶠ u in nhds x, u ∈ tψ := htψ_open.mem_nhds htψ_mem
  have hEventuallyInTPhiPsi : ∀ᶠ u in nhds x, (u, ψ u) ∈ tPhi := by
    exact hpairψ_tendsto.eventually (htPhi_open.mem_nhds htPhi_mem)
  have hCore :
      ∀ᶠ u in nhds x,
        u ∈ tψ ∧ (u, ψ u) ∈ tPhi ∧ (u, ψ u) ∈ interior Q ∧
          ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) := by
    filter_upwards [hEventuallyInTPsi, hEventuallyInTPhiPsi, hψ_mem_interior, hψ_argmin] with
      u hu_tψ hu_tPhi hu_int hu_arg
    exact ⟨hu_tψ, hu_tPhi, hu_int, hu_arg⟩
  rcases mem_nhds_iff.mp hCore with ⟨s, hs_sub, hs_open, hs_mem⟩
  have hs_tψ : ∀ u ∈ s, u ∈ tψ := by
    intro u hu
    exact (hs_sub hu).1
  have hs_tPhi : ∀ u ∈ s, (u, ψ u) ∈ tPhi := by
    intro u hu
    exact (hs_sub hu).2.1
  have hs_interior : ∀ u ∈ s, (u, ψ u) ∈ interior Q := by
    intro u hu
    exact (hs_sub hu).2.2.1
  have hs_argmin :
      ∀ u ∈ s, ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) := by
    intro u hu
    exact (hs_sub hu).2.2.2
  have hgrad_event :
      ∇ f =ᶠ[nhds x] Gψ := by
    -- Route correction: first prove the first-order envelope identity on one honest open
    -- neighborhood where the canonical implicit branch is differentiable and remains minimizing.
    filter_upwards [hs_open.mem_nhds hs_mem] with u hu
    have hPhiu : ContDiffAt ℝ 1 Φ (u, ψ u) :=
      hPhiOn_tPhi.contDiffAt (htPhi_open.mem_nhds (hs_tPhi u hu))
    have hψu : DifferentiableAt ℝ ψ u :=
      (hψOn_tψ.contDiffAt (htψ_open.mem_nhds (hs_tψ u hu))).differentiableAt (by norm_num)
    have hψ_argmin_near_u :
        ∀ᶠ v in nhds u, ψ v ∈ argmin[(Prod.mk v) ⁻¹' Q] (Φ ∘ Prod.mk v) := by
      filter_upwards [hs_open.mem_nhds hu] with v hv
      exact hs_argmin v hv
    have hgrad_u :
        ∇ f u = ∇ (fun u' ↦ Φ (u', ψ u)) u :=
      partialMinimizationObjective_gradient_eq_xGradient_of_eventually_argmin
        (Q := Q) (Φ := Φ) (x := u) (y := ψ)
        hPhiu hψu (hs_interior u hu) hψ_argmin_near_u
    calc
      ∇ f u = ∇ (fun u' ↦ Φ (u', ψ u)) u := hgrad_u
      _ = Gψ u := by
        symm
        simpa [Gψ] using partialMinimizationXGradient_eq_frozenXGradient Φ u (ψ u) hPhiu
  have hG_eq : Gψ =ᶠ[nhds x] Gy := by
    -- After identifying `y` with the canonical implicit branch near `x`, the ambient `x`-gradient
    -- fields along these two branches also agree near `x`.
    filter_upwards [hψ_eq] with u hu_eq
    simp [Gψ, Gy, hu_eq]
  have hy_fderiv :
      HasFDerivAt y (partialMinimizerImplicitFDeriv Φ x (y x)) x :=
    partialMinimizer_hasFDerivAt_of_isInvertible_yyHessian
      hPhi hy_tendsto hy_mem_interior hy_argmin hy_unique hyy_inv
  have hGy_deriv :
      HasFDerivAt Gy (partialMinimizationSchurHessian Φ x (y x)) x := by
    -- Differentiate the ambient `x`-gradient along the actual minimizing branch and rewrite the
    -- resulting `XX + XY ∘ Dy` formula as the Schur complement.
    simpa [Gy, partialMinimizationSchurHessian] using
      (partialMinimizationXGradientAlongBranch_hasFDerivAt
        (b := y) (b' := partialMinimizerImplicitFDeriv Φ x (y x))
        Φ x hPhi hy_fderiv)
  -- Differentiate the neighborhood-level gradient identity and substitute the branch derivative.
  unfold hessian
  rw [hgrad_event.fderiv_eq, hG_eq.fderiv_eq, hGy_deriv.fderiv]

end SecondOrder

end
