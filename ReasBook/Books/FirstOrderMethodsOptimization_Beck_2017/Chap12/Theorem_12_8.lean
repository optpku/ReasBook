/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_12
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Proposition_2_3
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_13
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_6
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_11
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_12
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_15
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_67
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_2
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_2
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_5
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Theorem_12_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Gradient
open InnerProductSpace (toDualMap)

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V)

local notation "F" => fun z : V ↦ dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ V z)
local notation "G" => fun z : V ↦ dual_based_proximal_gradient_dual_G_term g (toDualMap ℝ V z)
local notation "pOpt" => dual_based_proximal_gradient_primal_optimal_value f g A
local notation "q" => dual_based_proximal_gradient_lagrange_dual_objective_primal f g A
local notation "qOpt" => dual_based_proximal_gradient_lagrange_dual_problem_value f g A

/- Theorem 12.8 has a `core/canonical` rate statement and a `source-facing` bridge.

Domain sampling in Chapter 12 identifies:
- `is_dual_based_proximal_gradient_dual_trajectory` from Algorithm 12.1 as the owner of the dual
  iterates that enter the objective-gap bound from Theorem 12.4;
- `dual_based_proximal_gradient_dual_F_term` and `dual_based_proximal_gradient_dual_G_term` from
  Definition 12.5 as the chapter owners of the split dual terms, viewed on the primal
  dual-variable space through `toDualMap`;
- `dual_proximal_gradient_primal_x_argmax` from Algorithm 12.2 as the owner of the primal point
  condition used by Lemma 12.7;
- `is_dual_proximal_gradient_primal_trajectory` as the heavier source trajectory wrapper that
  packages both pieces together.

The distance estimate itself only uses the canonical dual trajectory together with the pointwise
argmax condition for `x k`, so the source trajectory wrapper should appear only through a thin
bridge to those two primitive ingredients. -/

/-- Helper for Theorem 12.8: a Chapter 12 primal argmax witness induces the corresponding
conjugate-side subgradient at `A.adjoint yBar`. -/
lemma evalMemConjugateSubdifferential_of_memDualPrimalArgmax
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {yBar : V} {xBar : E}
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar) :
    Module.Dual.eval ℝ E xBar ∈
      subdifferential
        (conjugate_function f)
        (InnerProductSpace.toDualMap ℝ E (A.adjoint yBar)) := by
  have hf_convex_toReal :
      ConvexOn ℝ (effective_domain f) (fun z : E ↦ (f z).toReal) := by
    -- Strong convexity implies convexity of the real lift on the effective domain.
    exact (h_problem.f_strongly_convex.strictConvexOn σ.2).convexOn
  have hf_convex : is_convex_function f := by
    -- Convert the domainwise convexity statement back to the project owner `is_convex_function`.
    rw [is_convex_function_iff_convexOn_toReal
      (fun z _ ↦ h_problem.toIsProperExtendedRealFunction.ne_bot z)]
    exact hf_convex_toReal
  have hmax :
      IsMaxOn
        (fun x' : E ↦
          ((((InnerProductSpace.toDualMap ℝ E (A.adjoint yBar)) x' : ℝ) : EReal) - f x'))
        Set.univ
        xBar := by
    -- Rewrite the source-facing argmax owner into the Chapter 4 conjugate-subgradient owner.
    simpa [mem_dual_proximal_gradient_primal_x_argmax_iff,
      InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hxBar
  -- Theorem 4.12 sends primal argmax witnesses to conjugate-side subgradients.
  rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
    f
    h_problem.toIsProperExtendedRealFunction
    h_problem.f_closed
    hf_convex
    (InnerProductSpace.toDualMap ℝ E (A.adjoint yBar))]
  exact ⟨xBar, hmax, rfl⟩

/-- Helper for Theorem 12.8: a conjugate-side subgradient at `A.adjoint yBar` is the canonical
gradient point `∇ (f∗) (A.adjoint yBar)` on the primal model `E`. -/
lemma conjugateSubgradientEval_eqGradientPoint
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {yBar : V} {xBar : E}
    (hx :
      Module.Dual.eval ℝ E xBar ∈
        subdifferential (conjugate_function f) (InnerProductSpace.toDualMap ℝ E (A.adjoint yBar))) :
    xBar = ∇ (fun z : E ↦ ((f∗) z).toReal) (A.adjoint yBar) := by
  let φ : E →ₗ[ℝ] Module.Dual ℝ E :=
    ((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E).symm).toLinearMap.comp
      ((InnerProductSpace.toDual ℝ E).toLinearEquiv.toLinearMap)
  let xDual : Module.Dual ℝ E :=
    (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E).symm
      (InnerProductSpace.toDual ℝ E xBar)
  have hconj_finite :
      ∀ z : E, (f∗) z ≠ ⊥ ∧ (f∗) z < ⊤ := by
    intro z
    -- Strong convexity makes the primal conjugate finite-valued on all of `E`.
    simpa using
      dual_based_proximal_gradient_dual_F_primal_finite_valued
        (σ := σ)
        (f := f)
        (A := (LinearMap.id : E →ₗ[ℝ] E))
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex
        z
  have hconj_convex : is_convex_function (f∗) := by
    -- The conjugate remains convex on the primal model.
    simpa using
      dual_based_proximal_gradient_dual_F_primal_convex
        (f := f)
        (A := (LinearMap.id : E →ₗ[ℝ] E))
  have hconj_diff :
      DifferentiableAt ℝ (fun z : E ↦ ((f∗) z).toReal) (A.adjoint yBar) := by
    -- Theorem 12.4 supplies the global smoothness, hence differentiability, of `f∗`.
    exact
      (conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
        (σ := σ)
        (f := f)
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex).1
        (A.adjoint yBar)
        (by simp)
  have hv_interior : A.adjoint yBar ∈ interior (finite_domain (f∗)) := by
    have hfinite_domain_univ : finite_domain (f∗) = Set.univ := by
      ext z
      constructor
      · intro _
        simp
      · intro _
        rcases hconj_finite z with ⟨hz_ne_bot, hz_lt_top⟩
        exact ⟨hz_lt_top, hz_ne_bot⟩
    -- Finite-valuedness everywhere identifies the interior with all of `E`.
    simpa [hfinite_domain_univ]
  have hx_primal : xDual ∈ subdifferential (f∗) (A.adjoint yBar) := by
    have hφ_apply (z : E) : φ z = (InnerProductSpace.toDualMap ℝ E z : Module.Dual ℝ E) := by
      ext w
      simp [φ, InnerProductSpace.toDual_apply_eq_toDualMap_apply]
    have hφdual :
        φ.dualMap (Module.Dual.eval ℝ E xBar) = xDual := by
      ext z
      simp [xDual, φ, InnerProductSpace.toDual_apply_eq_toDualMap_apply, real_inner_comm]
    have hpullback :
        φ.dualMap (Module.Dual.eval ℝ E xBar) ∈
          subdifferential (fun z : E ↦ conjugate_function f (φ z)) (A.adjoint yBar) := by
      -- Pull the given subgradient through the Riesz identification.
      exact
        (subdifferential_precompose_affineMap_subset
          (f := conjugate_function f)
          (φ := φ.toAffineMap)
          (x := A.adjoint yBar))
          ⟨Module.Dual.eval ℝ E xBar, hx, rfl⟩
    have hsubset :
        (fun z : E ↦ conjugate_function f (φ z)) = (f∗) := by
      funext z
      simpa [hφ_apply z] using (conjugate_function_primal_apply f z).symm
    simpa [hsubset, hφdual] using hpullback
  have hx_strong :
      InnerProductSpace.toDual ℝ E xBar ∈ strongDualSubdifferential (f∗) (A.adjoint yBar) := by
    have hx_image :
        InnerProductSpace.toDual ℝ E xBar ∈
          (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
            subdifferential (f∗) (A.adjoint yBar) := by
      refine ⟨xDual, hx_primal, ?_⟩
      ext z
      simp [xDual, InnerProductSpace.toDual_apply_eq_toDualMap_apply]
    simpa [strongDualSubdifferential_eq_image_subdifferential] using hx_image
  have hsingleton :=
    subdifferential_eq_singleton_gradient_of_differentiableAt
      (f := (f∗))
      (A.adjoint yBar)
      hconj_convex
      ⟨hv_interior, hconj_diff⟩
  have hx_eq_dual :
      InnerProductSpace.toDual ℝ E xBar =
        InnerProductSpace.toDual ℝ E
          (∇ (fun z : E ↦ ((f∗) z).toReal) (A.adjoint yBar)) := by
    have :
        InnerProductSpace.toDual ℝ E xBar ∈
          ({InnerProductSpace.toDual ℝ E
              (∇ (fun z : E ↦ ((f∗) z).toReal) (A.adjoint yBar))} : Set (StrongDual ℝ E)) := by
      simpa [hsingleton] using hx_strong
    simpa using this
  -- Injectivity of the Riesz map identifies the primal witness with the canonical gradient point.
  exact (InnerProductSpace.toDual ℝ E).injective hx_eq_dual

/-- Helper for Theorem 12.8: every source primal argmax witness at `yBar` is the canonical
conjugate gradient point `∇ (f∗) (A.adjoint yBar)`. -/
lemma dualPrimalArgmax_eqConjugateGradient
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {yBar : V} {xBar : E}
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar) :
    xBar = ∇ (fun z : E ↦ ((f∗) z).toReal) (A.adjoint yBar) := by
  -- Convert the primal argmax witness to a conjugate subgradient, then collapse that
  -- subgradient to the singleton gradient point of `f∗`.
  exact
    conjugateSubgradientEval_eqGradientPoint
      (f := f)
      (g := g)
      (A := A)
      h_problem
      (evalMemConjugateSubdifferential_of_memDualPrimalArgmax
        (f := f)
        (g := g)
        (A := A)
        h_problem
        hxBar)

/-- Helper for Theorem 12.8: the gradient of the pulled-back conjugate
`z ↦ ((f∗) (A.adjoint z)).toReal` is the pushforward by `A` of the ambient conjugate gradient. -/
lemma gradientConjugatePullback_eq
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (v : V) :
    ∇ (fun z : V ↦ (((f∗) (A.adjoint z)).toReal)) v =
      A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v)) := by
  -- Route correction: keep the zero-shift transport theorem-local instead of reopening the broken
  -- `Lemma_12_5` import chain.
  let fStarReal : E → ℝ := fun x ↦ (((f∗) x).toReal)
  let AadjMap : V →L[ℝ] E := A.adjoint.toContinuousLinearMap
  have hdiffFStar : DifferentiableAt ℝ fStarReal (A.adjoint v) := by
    -- The Chapter 12 smoothness theorem already gives differentiability of the primal conjugate.
    simpa [fStarReal] using
      (conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
        (σ := σ)
        (f := f)
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex).1
        (A.adjoint v)
        (by simp)
  have hderiv :
      fderiv ℝ (fun z : V ↦ fStarReal (A.adjoint z)) v =
        (fderiv ℝ fStarReal (A.adjoint v)).comp AadjMap := by
    -- Differentiate the pullback along the linear map `A.adjoint`.
    change fderiv ℝ (fStarReal ∘ A.adjoint) v =
      (fderiv ℝ fStarReal (A.adjoint v)).comp AadjMap
    have hAderiv : fderiv ℝ (fun z : V ↦ A.adjoint z) v = AadjMap := by
      simpa [AadjMap] using AadjMap.fderiv
    rw [fderiv_comp v hdiffFStar]
    · rw [hAderiv]
    · simpa [AadjMap] using AadjMap.differentiableAt
  have hgradMap :
      (fderiv ℝ fStarReal (A.adjoint v)).comp AadjMap =
        (InnerProductSpace.toDual ℝ V)
          (A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v))) := by
    -- Identify the derivative with the Riesz image of the pushed-forward gradient.
    have hgradAt := hdiffFStar.hasGradientAt
    have hFDerivAt := hgradAt.hasFDerivAt
    have hgradFStar :
        fderiv ℝ fStarReal (A.adjoint v) =
          (InnerProductSpace.toDual ℝ E) (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v)) := by
      simpa [fStarReal] using hFDerivAt.fderiv
    ext y
    calc
      ((fderiv ℝ fStarReal (A.adjoint v)).comp AadjMap) y
          = fderiv ℝ fStarReal (A.adjoint v) (AadjMap y) := by
              rfl
      _ = fderiv ℝ fStarReal (A.adjoint v) (A.adjoint y) := by
            simp [AadjMap]
      _ = inner ℝ (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v)) (A.adjoint y) := by
            rw [hgradFStar, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ (A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v))) y := by
            rw [LinearMap.adjoint_inner_right]
      _ =
          (InnerProductSpace.toDual ℝ V)
            (A (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v))) y := by
            rfl
  -- Convert the derivative computation back to the gradient identity.
  simpa [gradient] using
    congrArg ((InnerProductSpace.toDual ℝ V).symm) (hderiv.trans hgradMap)

/-- Helper for Theorem 12.8: the scaled conjugate `((1 / L) • (g∗))` used in the dual-step
transport lemmas. -/
def scaledDualConjugate (L : PosReal) : V → EReal :=
  (((1 / L : PosReal) : EReal) • (g∗))

/-- Helper for Theorem 12.8: the scaled conjugate evaluated at the negated argument `-z`. -/
def scaledNegatedDualConjugate (L : PosReal) : V → EReal :=
  (((1 / L : PosReal) : EReal) • fun z : V ↦ (g∗) (-z))

/-- Helper for Theorem 12.8: the proximal mapping of `z ↦ (g∗) (-z)` is the negated image of the
proximal mapping of the scaled conjugate. -/
private lemma proxNegatedConjugate_eq_negImageScaledConjugateProx
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g) (L : PosReal) (w : V) :
    prox[((((1 / L : PosReal) : EReal) • fun z : V ↦ (g∗) (-z)))] w =
      (fun u ↦ -u) '' prox[((((1 / L : PosReal) : EReal) • (g∗)))] (-w) := by
  let gScaled : V → EReal := (((1 / L : PosReal) : EReal) • (g∗))
  let φ : V →ᴬ[ℝ] V := (-ContinuousLinearMap.id ℝ V).toContinuousAffineMap
  have hgConjProper : IsProperExtendedRealFunction (g∗) :=
    conjugate_function_primal_proper_of_proper_convex g hg_proper hg_convex
  have hgScaledProper : IsProperExtendedRealFunction gScaled :=
    scaled_function_proper_of_pos (g∗) (1 / L : PosReal) hgConjProper
  have hφ :
      φ.contLinear ∘L ContinuousLinearMap.adjoint φ.contLinear = (1 : ℝ) • (1 : V →L[ℝ] V) := by
    -- The negation map is an isometry, so composing it with its adjoint gives the identity.
    ext z
    simp [φ]
  calc
    prox[((((1 / L : PosReal) : EReal) • fun z : V ↦ (g∗) (-z)))] w
        = prox[gScaled ∘ φ] w := by
            congr 1
    _ =
        (fun z : V ↦ w + ((1 : ℝ)⁻¹ • ContinuousLinearMap.adjoint φ.contLinear) (z - φ w)) ''
          prox[((1 : EReal) • gScaled)] (φ w) := by
            simpa using
              proximal_mapping_precompose_continuousAffineMap
                gScaled hgScaledProper φ 1 zero_lt_one hφ w
    _ = (fun u ↦ -u) '' prox[((((1 / L : PosReal) : EReal) • (g∗)))] (-w) := by
      -- Simplify the affine correction for the special affine map `φ = -id`.
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z, ?_, ?_⟩
        · simpa [gScaled, φ] using hz
        · simp [φ]
      · rintro ⟨z, hz, hy⟩
        refine ⟨z, ?_, ?_⟩
        · simpa [gScaled, φ] using hz
        · simpa [φ] using hy

/-- Helper for Theorem 12.8: the negated scaled-conjugate proximal point is equivalent to the
Chapter 12 primal `y`-step owner. -/
private lemma negScaledConjugateProx_mem_iff_memDualPrimalYStep
    (x : E) (v yNext : V) (L : PosReal)
    (hg_proper : IsProperExtendedRealFunction g) (hg_closed : LowerSemicontinuous g)
    (hg_convex : is_convex_function g) :
    yNext ∈ (fun u ↦ -u) '' prox[((((1 / L : PosReal) : EReal) • (g∗)))] ((1 / L : ℝ) • A x - v) ↔
      yNext ∈ dual_proximal_gradient_primal_y_step g A x v L := by
  rcases scaled_function_proper_closed_convex_of_pos g hg_proper hg_closed hg_convex L with
    ⟨hgScaledProper, hgScaledClosed, hgScaledConvex⟩
  rcases prox_eq_singleton_of_proper_closed_convex
      (((L : EReal) • g)) hgScaledProper hgScaledClosed hgScaledConvex
      (A x - (L : ℝ) • v) with
    ⟨p, hpSingleton⟩
  have hdualSingleton :=
    dual_moreau_prox_eq_singleton
      g hg_proper hg_closed hg_convex L (A x - (L : ℝ) • v) p hpSingleton
  have hbase :
      ((L : ℝ)⁻¹ • (A x - (L : ℝ) • v)) = ((1 / L : ℝ) • A x - v) := by
    -- Normalize the Moreau base point into the textbook forward point.
    have hL : (L : ℝ) ≠ 0 := ne_of_gt L.2
    rw [smul_sub, smul_smul]
    simp [one_div, hL]
  have hdualSingletonBase :
      prox[((((1 / L : PosReal) : EReal) • (g∗)))] ((1 / L : ℝ) • A x - v) =
        {((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p))} := by
    simpa [hbase] using hdualSingleton
  have hnegResidual :
      -((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p)) =
        v - (1 / L : ℝ) • A x + (1 / L : ℝ) • p := by
    -- Expand the negated Moreau residual into the Chapter 12 affine dual update.
    have hL : (L : ℝ) ≠ 0 := ne_of_gt L.2
    calc
      -((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p))
          = (L : ℝ)⁻¹ • p - (L : ℝ)⁻¹ • (A x - (L : ℝ) • v) := by
              rw [smul_sub, neg_sub]
      _ = v - (1 / L : ℝ) • A x + (1 / L : ℝ) • p := by
            rw [smul_sub, smul_smul]
            simp [one_div, hL, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have huSingleton :
        u = (L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p) := by
      have : u ∈ ({((L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p))} : Set V) := by
        rw [hdualSingletonBase] at hu
        exact hu
      simpa using this
    rw [mem_dual_proximal_gradient_primal_y_step_iff]
    refine ⟨p, ?_, ?_⟩
    · have hpMem : p ∈ ({p} : Set V) := by simp
      simpa [hpSingleton] using hpMem
    · simp [huSingleton, hnegResidual]
  · intro hy
    rw [mem_dual_proximal_gradient_primal_y_step_iff] at hy
    rcases hy with ⟨p', hp', hyEq⟩
    have hp'Eq : p' = p := by
      have : p' ∈ ({p} : Set V) := by
        simpa [hpSingleton] using hp'
      simpa using this
    refine ⟨(L : ℝ)⁻¹ • ((A x - (L : ℝ) • v) - p), ?_, ?_⟩
    · rw [hdualSingletonBase]
      simp
    · simp [hyEq, hp'Eq, hnegResidual]

/-- Helper for Theorem 12.8: at zero shift, the Chapter 12 dual-step owner is equivalent to the
source primal-representation `y`-step owner built from the conjugate gradient point. -/
lemma dualBasedDualStep_iff_memDualPrimalYStepZeroShift
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yNext v : V) (L : PosReal) :
    yNext ∈ dual_based_proximal_gradient_dual_step
          (fun z : V ↦ (g∗) (-z))
          (fun w ↦ ∇ (fun z : V ↦ (((f∗) (A.adjoint z)).toReal)) w)
          L
          v ↔
    yNext ∈ dual_proximal_gradient_primal_y_step
        g
        A
        (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v))
        v
        L := by
  -- Rewrite the source owner into the proximal point with the explicit forward-gradient point.
  rw [mem_dual_based_proximal_gradient_dual_step_iff]
  -- Identify the smooth gradient term with the pushed-forward conjugate gradient `A xTilde`.
  rw [gradientConjugatePullback_eq (f := f) (g := g) (A := A) h_problem v]
  -- Transport the proximal set of `z ↦ (g∗) (-z)` through negation.
  rw [proxNegatedConjugate_eq_negImageScaledConjugateProx
    (g := g) h_problem.g_proper h_problem.g_convex L]
  -- Finish with the Moreau decomposition rendered on the Chapter 12 primal-step owner.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    negScaledConjugateProx_mem_iff_memDualPrimalYStep
      (g := g)
      (A := A)
      (∇ (fun x : E ↦ (((f∗) x).toReal)) (A.adjoint v))
      v
      yNext
      L
      h_problem.g_proper
      h_problem.g_closed
      h_problem.g_convex

/-- A source-facing Algorithm 12.2 primal trajectory canonically determines the underlying
Algorithm 12.1 dual proximal-gradient trajectory for the Chapter 12 dual composite `F + G`. -/
theorem is_dual_proximal_gradient_primal_trajectory.toDualTrajectory
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 : V} {x : ℕ → E} {y : ℕ → V}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (htraj : is_dual_proximal_gradient_primal_trajectory f g A L y0 x y) :
    is_dual_based_proximal_gradient_dual_trajectory F G L y y0 := by
  let Fexp : V → EReal := fun z ↦ (f∗) (A.adjoint z)
  let Gexp : V → EReal := fun z ↦ (g∗) (-z)
  have hF_eq : F = Fexp := by
    funext z
    exact dual_based_proximal_gradient_dual_F_primal_apply (f := f) (A := A) z
  have hG_eq : G = Gexp := by
    funext z
    exact dual_based_proximal_gradient_dual_G_primal_apply (g := g) z
  have hFexp_eff_univ : effective_domain Fexp = Set.univ := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      exact
        mem_effective_domain.mpr
          (by
            simpa [Fexp] using
              (dual_based_proximal_gradient_dual_F_primal_finite_valued
                (σ := σ)
                (f := f)
                (A := A)
                h_problem.toIsProperExtendedRealFunction
                h_problem.f_closed
                h_problem.f_strongly_convex
                z).2)
  refine
    { zero_eq := htraj.zero
      trajectory := ?_ }
  intro k
  constructor
  · -- The dual smooth term is finite everywhere, so the interior-domain condition is automatic.
    have hyk_int : y k ∈ interior (effective_domain Fexp) := by
      rw [hFexp_eff_univ]
      simp
    rw [hF_eq]
    exact hyk_int
  · have hxk_eq :
        x k = ∇ (fun z : E ↦ ((f∗) z).toReal) (A.adjoint (y k)) := by
      -- The source primal argmax witness is the canonical conjugate gradient point.
      exact
        dualPrimalArgmax_eqConjugateGradient
          (f := f)
          (g := g)
          (A := A)
          h_problem
          (htraj.primal_step k)
    have hy_step :
        y (k + 1) ∈
          dual_proximal_gradient_primal_y_step
            g
            A
            (∇ (fun z : E ↦ ((f∗) z).toReal) (A.adjoint (y k)))
            (y k)
            (L : PosReal) := by
      -- Rewrite the stored primal step into the gradient witness expected by the zero-shift bridge.
      simpa [hxk_eq] using htraj.dual_step k
    have hy_dual :
        y (k + 1) ∈
          dual_based_proximal_gradient_dual_step
            (fun z : V ↦ (g∗) (-z))
            (fun w ↦ ∇ (fun z : V ↦ (((f∗) (A.adjoint z)).toReal)) w)
            (L : PosReal)
            (y k) := by
      -- Transport the source primal y-step to the canonical dual proximal-gradient step owner.
      exact
        (dualBasedDualStep_iff_memDualPrimalYStepZeroShift
          (f := f)
          (g := g)
          (A := A)
          h_problem
          (y (k + 1))
          (y k)
          (L : PosReal)).2 hy_step
    have hy_prox :
        y (k + 1) ∈ proximal_gradient_step Fexp Gexp (y k) (L : PosReal) := by
      -- The explicit zero-shift owner is already the Chapter 10 prox-gradient step for
      -- `Fexp + Gexp`.
      have hy_dual_exp :
          y (k + 1) ∈
            dual_based_proximal_gradient_dual_step
              Gexp
              (fun w ↦ ∇ (fun z : V ↦ (Fexp z).toReal) w)
              (L : PosReal)
              (y k) := by
        simpa [Fexp, Gexp] using hy_dual
      rw [dual_based_proximal_gradient_dual_step_eq_proximal_gradient_step
        Fexp
        Gexp
        (L : PosReal)
        (y k)] at hy_dual_exp
      exact hy_dual_exp
    rw [hF_eq, hG_eq]
    exact hy_prox

/-- Helper for Theorem 12.8: every point of an affine subspace lies in the intrinsic interior of
its carrier set. -/
lemma memIntrinsicInterior_affineSubspace
    {W : Type*} {P : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MetricSpace P] [NormedAddTorsor W P]
    (s : AffineSubspace ℝ P) {x : P} (hx : x ∈ (s : Set P)) :
    x ∈ intrinsicInterior ℝ (s : Set P) := by
  -- Unfold the intrinsic interior inside the affine span, which is the affine subspace itself.
  rw [intrinsicInterior]
  refine ⟨⟨x, ?_⟩, ?_, rfl⟩
  · simpa [AffineSubspace.affineSpan_coe] using hx
  · have hpre :
        ((↑) : affineSpan ℝ (s : Set P) → P) ⁻¹' (s : Set P) = Set.univ := by
      ext y
      change (↑y ∈ (s : Set P)) ↔ True
      constructor
      · intro _
        trivial
      · intro _
        simpa [AffineSubspace.affineSpan_coe] using y.property
    rw [hpre]
    simp

/-- Helper for Theorem 12.8: relative-interior membership is preserved under Cartesian products. -/
lemma memIntrinsicInterior_prod
    {S : Set E} {T : Set V} {x : E} {z : V}
    (hx : x ∈ intrinsicInterior ℝ S)
    (hz : z ∈ intrinsicInterior ℝ T) :
    (x, z) ∈ intrinsicInterior ℝ (S ×ˢ T) := by
  -- Use the closed-ball characterization and project the product affine-span condition to each
  -- coordinate.
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_span, εS, hεS, hballS⟩
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hz with
    ⟨hz_span, εT, hεT, hballT⟩
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨subset_affineSpan ℝ (S ×ˢ T) ⟨intrinsicInterior_subset hx, intrinsicInterior_subset hz⟩,
    min εS εT, lt_min hεS hεT, ?_⟩
  intro uv huv
  rcases uv with ⟨u, v⟩
  rcases huv with ⟨huv_ball, huv_span⟩
  have huv_dist : max (dist u x) (dist v z) ≤ min εS εT := by
    simpa [Prod.dist_eq, max_comm, max_left_comm, max_assoc] using huv_ball
  have hu_ball : u ∈ Metric.closedBall x εS := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).1) (min_le_left εS εT)
  have hv_ball : v ∈ Metric.closedBall z εT := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).2) (min_le_right εS εT)
  have hu_span_prod :
      u ∈ affineSpan ℝ (((LinearMap.fst ℝ E V).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        u ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.fst ℝ E V).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem (f := (LinearMap.fst ℝ E V).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hv_span_prod :
      v ∈ affineSpan ℝ (((LinearMap.snd ℝ E V).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        v ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.snd ℝ E V).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem (f := (LinearMap.snd ℝ E V).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hu_span : u ∈ affineSpan ℝ S := by
    refine (affineSpan_mono ℝ ?_) hu_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  have hv_span : v ∈ affineSpan ℝ T := by
    refine (affineSpan_mono ℝ ?_) hv_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  exact ⟨hballS ⟨hu_ball, hu_span⟩, hballT ⟨hv_ball, hv_span⟩⟩

/-- Helper for Theorem 12.8: the split objective `(x, z) ↦ f x + g z` never takes the value
`-∞`. -/
lemma splitObjective_ne_bot
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (xz : E × V) :
    composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz ≠ ⊥ := by
  rcases xz with ⟨x, z⟩
  -- Each summand avoids `⊥`, so the split objective does as well.
  simpa [composite_model_objective_apply, EReal.add_ne_bot_iff] using
    And.intro (h_problem.ne_bot x) (h_problem.g_proper.ne_bot z)

/-- Helper for Theorem 12.8: the split objective is finite exactly on
`effective_domain f ×ˢ effective_domain g`. -/
lemma effectiveDomain_splitObjective
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    effective_domain (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) =
      effective_domain f ×ˢ effective_domain g := by
  ext xz
  rcases xz with ⟨x, z⟩
  -- Turn finiteness of the split sum into coordinatewise finiteness using the `ne_bot` owners.
  simp [effective_domain, lt_top_iff_ne_top, composite_model_objective_apply,
    EReal.add_ne_top_iff_ne_top₂, h_problem.ne_bot x, h_problem.g_proper.ne_bot z]

/-- Helper for Theorem 12.8: strong convexity of `f` and convexity of `g` make the split
objective convex on `E × V`. -/
lemma splitObjective_convex
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    is_convex_function (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) := by
  have hf_convex_toReal :
      ConvexOn ℝ (effective_domain f) (fun x : E ↦ (f x).toReal) := by
    -- Strong convexity implies convexity of the real lift on the effective domain.
    exact (h_problem.f_strongly_convex.strictConvexOn σ.2).convexOn
  have hf_convex : is_convex_function f := by
    -- Convert the domainwise convexity statement back to the project owner.
    rw [is_convex_function_iff_convexOn_toReal (fun x _ ↦ h_problem.ne_bot x)]
    exact hf_convex_toReal
  have hf_fst : is_convex_function (fun xz : E × V ↦ f xz.1) := by
    -- Pull the convexity of `f` back along the first-coordinate projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := f) hf_convex (LinearMap.fst ℝ E V) (0 : E)
  have hg_snd : is_convex_function (fun xz : E × V ↦ g xz.2) := by
    -- Pull the convexity of `g` back along the second-coordinate projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := g) h_problem.g_convex (LinearMap.snd ℝ E V) (0 : V)
  -- The split objective is the pointwise sum of the two coordinate pullbacks.
  simpa [composite_model_objective_eq_add] using
    (is_convex_function_pointwise_add
      hf_fst
      hg_snd
      (fun xz : E × V ↦ h_problem.ne_bot xz.1)
      (fun xz : E × V ↦ h_problem.g_proper.ne_bot xz.2))

/-- Helper for Theorem 12.8: the split objective is proper. -/
lemma splitObjective_proper
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    IsProperExtendedRealFunction (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) := by
  rcases h_problem.effective_domain_nonempty with ⟨x₀, hx₀⟩
  rcases h_problem.g_proper.effective_domain_nonempty with ⟨z₀, hz₀⟩
  refine
    { ne_bot := splitObjective_ne_bot (f := f) (g := g) (A := A) h_problem
      effective_domain_nonempty := ?_ }
  refine ⟨(x₀, z₀), ?_⟩
  simpa [effectiveDomain_splitObjective (f := f) (g := g) (A := A) h_problem]
    using And.intro hx₀ hz₀

/-- Helper for Theorem 12.8: the Chapter 12 primal value is the infimum of the split objective
with infeasible pairs sent to `⊤`. -/
lemma splitConstrainedPrimalValue_eq
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) :
    dual_based_proximal_gradient_primal_optimal_value f g A =
      sInf
        (Set.range
          (constrained_problem_objective
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (Set.univ.graphOn A))) := by
  -- First rewrite the Chapter 12 owner to the split infimum over graph-feasible pairs.
  rw [dual_based_proximal_gradient_primal_optimal_value_eq_split_infimum]
  -- Then compare the feasible-value image with the constrained-objective range.
  rw [show
      sInf
          (Set.image
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (Set.univ.graphOn A)) =
        sInf
          (Set.range
            (constrained_problem_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (Set.univ.graphOn A))) by
      apply le_antisymm
      · apply le_sInf
        rintro r ⟨xz, rfl⟩
        by_cases hxz : xz ∈ Set.univ.graphOn A
        · exact sInf_le ⟨xz, hxz, by
            simpa using
              (constrained_problem_objective_of_mem
                (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) hxz).symm⟩
        · simp [constrained_problem_objective_of_not_mem
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) hxz]
      · apply le_sInf
        rintro r ⟨xz, hxz, rfl⟩
        exact sInf_le ⟨xz, by
          simpa using
            constrained_problem_objective_of_mem
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) hxz⟩]

/-- Helper for Theorem 12.8: the graph of a linear map is convex in the product space. -/
lemma graphOn_convex
    (A : E →ₗ[ℝ] V) :
    Convex ℝ (Set.univ.graphOn A) := by
  intro x hx y hy a b ha hb hab
  rcases x with ⟨x₁, z₁⟩
  rcases y with ⟨x₂, z₂⟩
  have hz₁ : A x₁ = z₁ := by
    simpa using hx
  have hz₂ : A x₂ = z₂ := by
    simpa using hy
  -- Linear combinations preserve the defining graph relation.
  simp [Set.mem_graphOn, hz₁, hz₂, map_add]

/-- Helper for Theorem 12.8: the indicator of the graph constraint is proper. -/
lemma graphIndicator_proper
    (A : E →ₗ[ℝ] V) :
    IsProperExtendedRealFunction (extendedIndicator (Set.univ.graphOn A)) := by
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro xz
    by_cases hxz : xz ∈ Set.univ.graphOn A <;> simp [extendedIndicator, hxz]
  · refine ⟨(0, 0), ?_⟩
    simpa [effective_domain_extendedIndicator]

/-- Helper for Theorem 12.8: the graph indicator is convex because the graph of `A` is convex. -/
lemma graphIndicator_convex
    (A : E →ₗ[ℝ] V) :
    is_convex_function (extendedIndicator (Set.univ.graphOn A)) := by
  have h_zero_convex : is_convex_function (0 : E × V → EReal) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro x hx
      simp
    · simpa [effective_domain] using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set (E × V))))
  have h_constrained_convex :
      is_convex_function
        (constrained_problem_objective (0 : E × V → EReal) (Set.univ.graphOn A)) :=
    is_convex_function_constrained_problem_objective h_zero_convex (graphOn_convex A)
  -- Rewrite the constrained zero objective as `0 + δ_graph`, then cancel the zero summand.
  rw [constrained_problem_objective_eq_add_extendedIndicator
    (0 : E × V → EReal) (Set.univ.graphOn A) (fun _ _ ↦ by simp)] at h_constrained_convex
  simpa [composite_model_objective] using h_constrained_convex

/-- Helper for Theorem 12.8: the graph of a linear map is a cone. -/
lemma graphOn_isCone
    (A : E →ₗ[ℝ] V) :
    IsCone (Set.univ.graphOn A) := by
  rw [isCone_iff_smul_mem]
  intro a ha x hx
  rcases x with ⟨x, z⟩
  have hz : A x = z := by
    simpa using hx
  -- Scaling a graph point preserves the relation `z = A x`.
  simp [Set.mem_graphOn, hz, map_smul]

/-- Helper for Theorem 12.8: the set-theoretic graph agrees with the carrier of the linear-map
graph submodule. -/
lemma graphOn_eq_linearMap_graph
    (A : E →ₗ[ℝ] V) :
    Set.univ.graphOn A = (LinearMap.graph A : Set (E × V)) := by
  ext xz
  rcases xz with ⟨x, z⟩
  -- Compare the two graph presentations pointwise.
  simp [Set.mem_graphOn, LinearMap.mem_graph_iff, eq_comm]

/-- Helper for Theorem 12.8: every graph-feasible pair lies in the intrinsic interior of the
graph constraint set. -/
lemma memIntrinsicInterior_graphOn
    {xz : E × V} (hxz : xz ∈ Set.univ.graphOn A) :
    xz ∈ intrinsicInterior ℝ (Set.univ.graphOn A) := by
  have hgraph_set :
      (LinearMap.graph A : Set (E × V)) =
        (((LinearMap.graph A).toAffineSubspace : AffineSubspace ℝ (E × V)) : Set (E × V)) := by
    -- The linear graph submodule and its associated affine subspace have the same carrier set.
    ext yz
    simp
  have hmem :
      xz ∈
        (((LinearMap.graph A).toAffineSubspace : AffineSubspace ℝ (E × V)) : Set (E × V)) := by
    -- Rewrite the set-theoretic graph as the carrier of the linear graph submodule.
    simpa [graphOn_eq_linearMap_graph (A := A), hgraph_set] using hxz
  -- Rewrite the target set to the affine-subspace carrier and then apply the owner lemma.
  rw [graphOn_eq_linearMap_graph (A := A), hgraph_set]
  exact memIntrinsicInterior_affineSubspace ((LinearMap.graph A).toAffineSubspace) hmem

/-- Helper for Theorem 12.8: Assumption 12.1 provides a graph-feasible relative-interior witness
for the split formulation. -/
lemma splitGraphQualificationWitness
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ xHat zHat,
      xHat ∈ intrinsicInterior ℝ (effective_domain f) ∧
        zHat ∈ intrinsicInterior ℝ (effective_domain g) ∧
          (xHat, zHat) ∈ Set.univ.graphOn A := by
  -- Repackage the source qualification witness as a point on the graph of `A`.
  rcases h_problem.exists_mem_intrinsicInterior_map_eq with
    ⟨xHat, hxHat, zHat, hzHat, hAz⟩
  refine ⟨xHat, zHat, hxHat, hzHat, ?_⟩
  simp [hAz]

/-- Helper for Theorem 12.8: the Chapter 4 split-graph qualification follows from the source
qualification witness. -/
lemma splitGraphFenchelQualification_nonempty
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    (intrinsicInterior ℝ
        (effective_domain (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))) ∩
      intrinsicInterior ℝ
        (effective_domain (extendedIndicator (Set.univ.graphOn A)))).Nonempty := by
  rcases splitGraphQualificationWitness (f := f) (g := g) (A := A) h_problem with
    ⟨xHat, zHat, hxHat, hzHat, hgraph⟩
  refine ⟨(xHat, zHat), ?_⟩
  constructor
  · -- Place the witness in the product relative interior of the split effective domain.
    simpa [effectiveDomain_splitObjective (f := f) (g := g) (A := A) h_problem] using
      memIntrinsicInterior_prod (x := xHat) (z := zHat) hxHat hzHat
  · -- Rewrite the graph indicator domain to the graph itself and use the affine owner lemma.
    simpa [effective_domain_extendedIndicator] using
      memIntrinsicInterior_graphOn (A := A) hgraph

/-- Helper for Theorem 12.8: the Chapter 12 primal value is the Chapter 4 primal infimum for the
split objective plus the graph indicator. -/
lemma splitPrimalValue_eqFenchelPrimalInfimum
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    pOpt =
      sInf (Set.range
        (composite_model_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)))) := by
  have hconstrained_eq :
      constrained_problem_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (Set.univ.graphOn A) =
        composite_model_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) := by
    -- Rewrite the constrained split objective as `splitObjective + δ_graph`.
    simpa [composite_model_objective_eq_add] using
      constrained_problem_objective_eq_add_extendedIndicator
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (Set.univ.graphOn A)
        (fun xz _ ↦ splitObjective_ne_bot (f := f) (g := g) (A := A) h_problem xz)
  -- Substitute the canonical `splitObjective + δ_graph` owner into the normalized primal infimum.
  simpa [hconstrained_eq] using splitConstrainedPrimalValue_eq (f := f) (g := g) (A := A)

/-- Helper for Theorem 12.8: the graph-compatible dual vector attached to `y` annihilates
graph-feasible pairs `(x, A x)`. -/
def graphDual
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) :
    Module.Dual ℝ (E × V) :=
  (A.dualMap y).comp (LinearMap.fst ℝ E V) -
    y.comp (LinearMap.snd ℝ E V)

/-- Helper for Theorem 12.8: evaluating the graph-compatible dual vector gives
`⟨Aᵀ y, x⟩ - ⟨y, z⟩`. -/
@[simp] lemma graphDual_apply
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) (xz : E × V) :
    graphDual A y xz = ((A.dualMap y) xz.1 : ℝ) - y xz.2 := by
  -- Expand the product projections once so later graph identities simplify deterministically.
  simp [graphDual, sub_eq_add_neg]

/-- Helper for Theorem 12.8: the graph-compatible dual vector vanishes on the graph of `A`. -/
lemma graphDual_graph_eq_zero
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) (x : E) :
    graphDual A y (x, A x) = 0 := by
  -- On a feasible split pair `(x, A x)`, the two pairing terms cancel exactly.
  simp [graphDual_apply]

/-- Helper for Theorem 12.8: the polar cone of the graph consists exactly of graph-compatible
dual vectors. -/
lemma memPolarCone_graphOn_iff_exists_graphDual
    (A : E →ₗ[ℝ] V) (ψ : Module.Dual ℝ (E × V)) :
    ψ ∈ polar_cone (Set.univ.graphOn A) ↔ ∃ y : Module.Dual ℝ V, ψ = graphDual A y := by
  constructor
  · intro hψ
    have hψ_mem : ∀ x ∈ Set.univ.graphOn A, ψ x ≤ 0 :=
      (mem_polar_cone (Set.univ.graphOn A) ψ).1 hψ
    let y : Module.Dual ℝ V :=
      -(ψ.comp (LinearMap.inr ℝ E V))
    refine ⟨y, ?_⟩
    apply LinearMap.ext
    intro xz
    rcases xz with ⟨x, z⟩
    have hgraph_le : ψ (x, A x) ≤ 0 := hψ_mem (x, A x) (by simp)
    have hgraph_ge : 0 ≤ ψ (x, A x) := by
      have hneg_graph : ψ (-x, A (-x)) ≤ 0 := hψ_mem (-x, A (-x)) (by simp)
      have hneg_eval : ψ (-x, A (-x)) = -ψ (x, A x) := by
        calc
          ψ (-x, A (-x)) = ψ (-(x, A x)) := by simp
          _ = -ψ (x, A x) := by rw [map_neg]
      have hneg : -(ψ (x, A x)) ≤ 0 := by
        rw [← hneg_eval]
        exact hneg_graph
      exact neg_nonpos.mp hneg
    have hgraph_eq : ψ (x, A x) = 0 := le_antisymm hgraph_le hgraph_ge
    have hsplit : (x, z) = (x, A x) + (0, z - A x) := by
      ext <;> simp
    -- Decompose an arbitrary pair into a graph component plus a vertical correction.
    calc
      ψ (x, z) = ψ (x, A x) + ψ (0, z - A x) := by
        rw [hsplit, map_add]
      _ = ψ (0, z - A x) := by simp [hgraph_eq]
      _ = ψ (0, z) - ψ (0, A x) := by
        simpa using map_sub ψ (0, z) (0, A x)
      _ = ((A.dualMap y) x : ℝ) - y z := by
        change ψ (0, z) - ψ (0, A x) = y (A x) - y z
        simp [y, sub_eq_add_neg, add_comm]
  · rintro ⟨y, rfl⟩
    rw [mem_polar_cone]
    intro x hx
    rcases x with ⟨u, z⟩
    have hz : A u = z := by
      simpa using hx
    -- A graph-compatible dual vector evaluates to zero on every graph-feasible pair.
    simp [graphDual_apply, hz]

/-- Helper for Theorem 12.8: negating an affine perturbation turns its infimum into the negative
Fenchel conjugate. -/
lemma ereal_sInf_range_sub_pairing_eq_neg_conjugate
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (h : W → EReal) (η : Module.Dual ℝ W) :
    sInf (Set.range fun x : W ↦ h x - (η x : EReal)) = -conjugate_function h η := by
  have hrange :
      Set.range (fun x : W ↦ h x - (η x : EReal)) =
        -Set.range (fun x : W ↦ (η x : EReal) - h x) := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      rw [Set.mem_neg]
      refine ⟨x, ?_⟩
      have hneg : -(h x - (η x : EReal)) = ((η x : EReal) - h x) := by
        have hraw : -(h x - (η x : EReal)) = -h x + (η x : EReal) := by
          exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
        simpa [sub_eq_add_neg, add_comm] using hraw
      simpa using hneg.symm
    · rw [Set.mem_neg]
      rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hneg : -(h x - (η x : EReal)) = -r := by
        calc
          -(h x - (η x : EReal)) = ((η x : EReal) - h x) := by
            have hraw : -(h x - (η x : EReal)) = -h x + (η x : EReal) := by
              exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
            simpa [sub_eq_add_neg, add_comm] using hraw
          _ = -r := by simpa using hx
      have hr : -(-(h x - (η x : EReal))) = -(-r) := congrArg Neg.neg hneg
      simpa using hr
  -- Translate the infimum of the negated range into the negative supremum from the conjugate.
  rw [hrange]
  have hsInf_neg : sInf (-Set.range (fun x : W ↦ (η x : EReal) - h x)) =
      -sSup (Set.range fun x : W ↦ (η x : EReal) - h x) := by
    refine le_antisymm ?_ ?_
    · have hsSup :
        sSup (Set.range fun x : W ↦ (η x : EReal) - h x) ≤
          -sInf (-Set.range fun x : W ↦ (η x : EReal) - h x) := by
        refine sSup_le ?_
        intro x hx
        have hsInf :
            sInf (-Set.range fun x : W ↦ (η x : EReal) - h x) ≤ -x := by
          exact sInf_le
            (by
              simpa [Set.mem_neg] using hx :
                -x ∈ -Set.range fun x : W ↦ (η x : EReal) - h x)
        exact EReal.le_neg.mp hsInf
      exact EReal.le_neg.mpr hsSup
    · refine le_sInf ?_
      intro z hz
      exact EReal.neg_le.mpr
        (le_sSup
          (by
            simpa [Set.mem_neg] using hz :
              -z ∈ Set.range fun x : W ↦ (η x : EReal) - h x))
  rw [hsInf_neg, conjugate_function_apply]

/-- Helper for Theorem 12.8: negating the graph-compatible dual vector corresponds to negating the
underlying dual variable. -/
@[simp] lemma graphDual_neg
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) :
    graphDual A (-y) = -graphDual A y := by
  apply LinearMap.ext
  intro xz
  -- Expand both graph-dual evaluations pointwise and regroup the real terms.
  simp [graphDual_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.8: the support function of the graph constraint is exactly the indicator
of the graph-dual range. -/
lemma supportFunction_graphOn_eqIndicator_graphDualRange
    (A : E →ₗ[ℝ] V) :
    support_function (Set.univ.graphOn A) =
      extendedIndicator (Set.range (graphDual A)) := by
  funext ψ
  have hpolar :
      ψ ∈ polar_cone (Set.univ.graphOn A) ↔ ψ ∈ Set.range (graphDual A) := by
    have hpolar_raw := memPolarCone_graphOn_iff_exists_graphDual (A := A) ψ
    constructor
    · intro hmem
      rcases hpolar_raw.mp hmem with ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact hpolar_raw.mpr ⟨y, hy.symm⟩
  have hsupport :
      support_function (Set.univ.graphOn A) ψ =
        extendedIndicator (polar_cone (Set.univ.graphOn A)) ψ := by
    simpa using
      congrArg (fun h : Module.Dual ℝ (E × V) → EReal ↦ h ψ)
        (support_function_eq_indicatorFunction_polarCone
          (Set.univ.graphOn A) (graphOn_isCone A) (by simp))
  by_cases hψ : ψ ∈ Set.range (graphDual A)
  · have hpolar_mem : ψ ∈ polar_cone (Set.univ.graphOn A) := hpolar.mpr hψ
    simpa [extendedIndicator, hψ, hpolar_mem] using hsupport
  · have hpolar_not_mem : ψ ∉ polar_cone (Set.univ.graphOn A) := by
      intro hmem
      exact hψ (hpolar.mp hmem)
    simpa [extendedIndicator, hψ, hpolar_not_mem] using hsupport

/-- Helper for Theorem 12.8: membership in the graph-dual range is invariant under negation. -/
lemma neg_mem_graphDualRange_iff
    (A : E →ₗ[ℝ] V) (ψ : Module.Dual ℝ (E × V)) :
    -ψ ∈ Set.range (graphDual A) ↔ ψ ∈ Set.range (graphDual A) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    calc
      graphDual A (-y) = -(graphDual A y) := by
        simpa using (graphDual_neg (A := A) y)
      _ = -(-ψ) := by simpa [hy]
      _ = ψ := by simp
  · intro hψ
    rcases hψ with ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    calc
      graphDual A (-y) = -(graphDual A y) := by
        simpa using (graphDual_neg (A := A) y)
      _ = -ψ := by simpa [hy]

/-- Helper for Theorem 12.8: evaluating the split objective minus `graphDual A y` is exactly the
Chapter 12 Lagrangian integrand. -/
lemma splitObjective_sub_graphDual_eq_lagrangian
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y : Module.Dual ℝ V) (xz : E × V) :
    composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz -
        ((graphDual A y) xz : EReal) =
      dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y := by
  rcases xz with ⟨x, z⟩
  -- Normalize the graph-dual pairing into the same affine split used by the Lagrangian owner.
  rw [dual_based_proximal_gradient_lagrangian_eq_affine_split, graphDual_apply,
    composite_model_objective_apply]
  have hs :
      -((((A.dualMap y) x - y z : ℝ) : EReal)) =
        -(((A.dualMap y) x : EReal)) + (y z : EReal) := by
    change (((-(((A.dualMap y) x - y z)) : ℝ)) : EReal) =
        (((-((A.dualMap y) x) + y z : ℝ)) : EReal)
    norm_num [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [sub_eq_add_neg, hs]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.8: the negative conjugate of the split objective on `graphDual A y`
matches the Chapter 12 dual objective. -/
lemma negConjugate_splitObjective_graphDual_eqDualObjective
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y : Module.Dual ℝ V) :
    -conjugate_function (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) (graphDual A y) =
      dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
  -- Rewrite the conjugate via the affine-perturbation infimum, then identify it with the
  -- Chapter 12 Lagrangian infimum formula.
  calc
    -conjugate_function (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (graphDual A y)
        =
        sInf (Set.range fun xz : E × V ↦
          composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz -
            ((graphDual A y) xz : EReal)) := by
          symm
          exact ereal_sInf_range_sub_pairing_eq_neg_conjugate
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) (graphDual A y)
    _ =
        sInf (Set.range fun xz : E × V ↦
          dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y) := by
          congr 1
          ext r
          constructor
          · rintro ⟨xz, rfl⟩
            exact ⟨xz, by
              simpa using splitObjective_sub_graphDual_eq_lagrangian
                (f := f) (g := g) (A := A) h_problem y xz⟩
          · rintro ⟨xz, rfl⟩
            exact ⟨xz, by
              simpa using splitObjective_sub_graphDual_eq_lagrangian
                (f := f) (g := g) (A := A) h_problem y xz⟩
    _ = dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
      symm
      exact dual_based_proximal_gradient_lagrange_dual_objective_eq_sInf_lagrangian_formula
        f g A y h_problem.toIsProperExtendedRealFunction h_problem.g_proper

/-- Helper for Theorem 12.8: on the graph-dual range, the unrestricted Fenchel dual objective
agrees with the Chapter 12 dual objective `q`. -/
lemma splitGraphFenchelDualObjective_onGraphDual
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y : Module.Dual ℝ V) :
    fenchel_dual_objective
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        (graphDual A y) =
      dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
  -- Combine the split-objective conjugate bridge with the graph-support rewrite.
  rw [fenchel_dual_objective_apply, conjugate_function_extendedIndicator_apply_eq_support_function,
    supportFunction_graphOn_eqIndicator_graphDualRange,
    negConjugate_splitObjective_graphDual_eqDualObjective (f := f) (g := g) (A := A) h_problem]
  have hneg_mem : -graphDual A y ∈ Set.range (graphDual A) := by
    refine ⟨-y, ?_⟩
    simpa using (graphDual_neg (A := A) y)
  simp [extendedIndicator, hneg_mem]

/-- Helper for Theorem 12.8: away from the graph-dual range, the unrestricted Fenchel dual
objective collapses to `-∞`. -/
lemma splitGraphFenchelDualObjective_eqBot_of_notMemGraphDualRange
    (ψ : Module.Dual ℝ (E × V))
    (hψ : ψ ∉ Set.range (graphDual A)) :
    fenchel_dual_objective
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        ψ = ⊥ := by
  have hneg : -ψ ∉ Set.range (graphDual A) := by
    intro hmem
    exact hψ ((neg_mem_graphDualRange_iff (A := A) ψ).mp hmem)
  rw [fenchel_dual_objective_apply, conjugate_function_extendedIndicator_apply_eq_support_function,
    supportFunction_graphOn_eqIndicator_graphDualRange]
  simp [extendedIndicator, hneg]

/-- Helper for Theorem 12.8: the unrestricted Fenchel dual value of the split graph formulation
is exactly the Chapter 12 dual problem value `qOpt`. -/
lemma splitGraphFenchelDualProblemValue_eqLagrangeDualProblemValue
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    fenchel_dual_problem_value
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A)) =
      dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
  -- Compare the two suprema pointwise using the graph-dual on-range rewrite and the off-range
  -- collapse.
  rw [fenchel_dual_problem_value_eq_sSup, dual_based_proximal_gradient_lagrange_dual_problem_value]
  apply le_antisymm
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨ψ, rfl⟩
    by_cases hψ : ψ ∈ Set.range (graphDual A)
    · rcases hψ with ⟨y, rfl⟩
      rw [splitGraphFenchelDualObjective_onGraphDual (f := f) (g := g) (A := A) h_problem y]
      exact le_sSup ⟨y, rfl⟩
    · rw [splitGraphFenchelDualObjective_eqBot_of_notMemGraphDualRange
        (f := f) (g := g) (A := A) ψ hψ]
      exact bot_le
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨y, rfl⟩
    rw [← splitGraphFenchelDualObjective_onGraphDual (f := f) (g := g) (A := A) h_problem y]
    exact le_sSup ⟨graphDual A y, rfl⟩

/-- Helper for Theorem 12.8: the primal optimal value equals the Chapter 12 dual problem value. -/
lemma dualBasedProximalGradientProblemStrongDualityLocal
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    pOpt = qOpt := by
  -- Apply Chapter 4 value duality to the split objective plus graph indicator, then rewrite the
  -- unrestricted Fenchel dual value back to the Chapter 12 owner `qOpt`.
  calc
    pOpt =
        sInf (Set.range
          (composite_model_objective
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (extendedIndicator (Set.univ.graphOn A)))) :=
      splitPrimalValue_eqFenchelPrimalInfimum (f := f) (g := g) (A := A) h_problem
    _ =
        fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) :=
      fenchel_duality_value_eq
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        (splitObjective_proper (f := f) (g := g) (A := A) h_problem)
        (graphIndicator_proper (A := A))
        (splitObjective_convex (f := f) (g := g) (A := A) h_problem)
        (graphIndicator_convex (A := A))
        (splitGraphFenchelQualification_nonempty (f := f) (g := g) (A := A) h_problem)
    _ = qOpt :=
      splitGraphFenchelDualProblemValue_eqLagrangeDualProblemValue
        (f := f) (g := g) (A := A) h_problem

/-- Helper for Theorem 12.8: the value attained by a primal minimizer is the dual problem value
`qOpt`. -/
lemma primalMinimizerValue_eqDualProblemValue
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (xStar : E)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar) :
    composite_model_objective f (g ∘ A) xStar = qOpt := by
  have hglb :
      IsGLB
        (Set.range (composite_model_objective f (g ∘ A)))
        (composite_model_objective f (g ∘ A) xStar) := by
    simpa using hxStar.isGLB (by simp : xStar ∈ (Set.univ : Set E))
  have hpOpt :
      pOpt = composite_model_objective f (g ∘ A) xStar := by
    rw [dual_based_proximal_gradient_primal_optimal_value_eq_sInf]
    exact hglb.csInf_eq ⟨composite_model_objective f (g ∘ A) xStar, ⟨xStar, rfl⟩⟩
  -- Strong duality identifies the attained primal value with the Chapter 12 dual optimum.
  calc
    composite_model_objective f (g ∘ A) xStar = pOpt := hpOpt.symm
    _ = qOpt := dualBasedProximalGradientProblemStrongDualityLocal
      (f := f) (g := g) (A := A) h_problem

/-- Helper for Theorem 12.8: an argmax point of `x ↦ ⟪x, Aᵀ yBar⟫ - f x` attains the conjugate
value `(f∗) (A.adjoint yBar)`. -/
lemma conjugatePrimal_eqPairingSub_of_memPrimalArgmax
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (xBar : E)
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar) :
    (f∗) (A.adjoint yBar) =
      (((inner ℝ xBar (A.adjoint yBar) : ℝ) : EReal) - f xBar) := by
  have hmax :
      IsMaxOn
        (fun x : E ↦
          (((InnerProductSpace.toDualMap ℝ E (A.adjoint yBar)) x : EReal) - f x))
        Set.univ xBar := by
    -- Reinterpret the primal-space argmax condition as the Chapter 4 dual-attainment statement.
    simpa [mem_dual_proximal_gradient_primal_x_argmax_iff,
      InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hxBar
  -- Theorem 4.11 turns that argmax condition into the exact conjugate equality.
  have hconj :
      (f∗) (A.adjoint yBar) =
        ((((InnerProductSpace.toDualMap ℝ E (A.adjoint yBar)) xBar : ℝ) : EReal) - f xBar) := by
    rw [conjugate_function_primal_apply]
    exact
      (conjugate_function_eq_iff_isMaxOn_pairing_sub_function
        f xBar (InnerProductSpace.toDualMap ℝ E (A.adjoint yBar))).2 hmax
  simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hconj

/-- Helper for Theorem 12.8: negating `a - r` with a finite real term `r` gives `r - a`. -/
private lemma ereal_neg_sub_real (a : EReal) (r : ℝ) :
    -(a - (r : EReal)) = ((r : EReal) - a) := by
  -- The real term is finite, so `EReal.neg_sub` applies without mixed infinite cases.
  have hneg : -(a - (r : EReal)) = -a + (r : EReal) := by
    exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
  simpa [sub_eq_add_neg, add_comm] using hneg

/-- Helper for Theorem 12.8: negating `r - a` with a finite real term `r` gives `a - r`. -/
private lemma ereal_neg_real_sub (a : EReal) (r : ℝ) :
    -(((r : EReal)) - a) = a - (r : EReal) := by
  -- The finite left term keeps the negated subtraction in the stable `a - r` normal form.
  rw [EReal.neg_sub] <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.8: the Chapter 12 primal argmax point is the minimizer of the shifted
objective `x ↦ f x - ⟪x, Aᵀ yBar⟫`. -/
lemma isMinOn_shifted_objective_of_mem_primalArgmax
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (xBar : E)
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar) :
    IsMinOn
      (fun x : E ↦ f x - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal)))
      Set.univ xBar := by
  have hmax :
      IsMaxOn
        (fun x : E ↦
          -((f x) - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal))))
        Set.univ xBar := by
    -- Rewrite the argmax objective as the negation of the shifted objective.
    simpa [mem_dual_proximal_gradient_primal_x_argmax_iff, ereal_neg_sub_real] using hxBar
  -- Negating the max inequality turns it into the desired min inequality.
  rw [isMinOn_univ_iff]
  intro x
  have hle :
      -((f x) - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal))) ≤
        -((f xBar) - (((inner ℝ xBar (A.adjoint yBar) : ℝ) : EReal))) :=
    (isMaxOn_univ_iff.mp hmax) x
  simpa using (EReal.neg_le_neg_iff.mp hle)

/-- Helper for Theorem 12.8: every primal minimizer has finite `f`-value. -/
lemma primalMinimizer_mem_effectiveDomain
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (xStar : E)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar) :
    xStar ∈ effective_domain f := by
  obtain ⟨xHat, hxHat, zHat, hzHat, hAz⟩ := h_problem.exists_mem_intrinsicInterior_map_eq
  have hxHat_eff : xHat ∈ effective_domain f := intrinsicInterior_subset hxHat
  have hzHat_eff : zHat ∈ effective_domain g := intrinsicInterior_subset hzHat
  have hle :
      composite_model_objective f (g ∘ A) xStar ≤
        composite_model_objective f (g ∘ A) xHat :=
    (isMinOn_univ_iff.mp hxStar) xHat
  have hcomp_xHat_ne_top :
      composite_model_objective f (g ∘ A) xHat ≠ ⊤ := by
    -- The qualification point yields a finite comparison value for the minimizer.
    simpa [Function.comp, hAz] using
      (ne_of_lt (EReal.add_lt_top (ne_of_lt hxHat_eff) (ne_of_lt hzHat_eff)))
  have hcomp_xStar_ne_top :
      composite_model_objective f (g ∘ A) xStar ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hcomp_xHat_ne_top))
  have hfxStar_ne_top : f xStar ≠ ⊤ := by
    intro hfxStar_top
    have hcomp_top :
        composite_model_objective f (g ∘ A) xStar = ⊤ := by
      rw [composite_model_objective_apply, hfxStar_top]
      simp [h_problem.g_proper.ne_bot (A xStar)]
    exact hcomp_xStar_ne_top hcomp_top
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hfxStar_ne_top)

/-- Helper for Theorem 12.8: subtracting the finite linear term `⟪x, Aᵀ yBar⟫` does not change
the effective domain of `f`. -/
lemma shiftedObjective_effectiveDomain_eq
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V) :
    effective_domain
        (fun x : E ↦ f x - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal))) =
      effective_domain f := by
  ext x
  constructor
  · intro hx
    -- A finite subtraction can only be infinite above when `f x` already is.
    change f x < ⊤
    refine lt_top_iff_ne_top.mpr ?_
    intro hfx_top
    have hshift_top :
        f x - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal)) = ⊤ := by
      rw [hfx_top]
      simp
    exact (ne_of_lt hx) hshift_top
  · intro hx
    -- Adding a finite affine term preserves finiteness from above.
    simpa [sub_eq_add_neg] using
      (EReal.add_lt_top (ne_of_lt hx) (EReal.coe_ne_top (-inner ℝ x (A.adjoint yBar))))

/-- Helper for Theorem 12.8: the shifted objective inherits the strong-convexity quadratic gap
from `f`. -/
lemma shiftedObjective_gap_ge_halfSigmaSqdist_of_memPrimalArgmax
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (xBar : E)
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar)
    (x : E)
    (hx : x ∈ effective_domain f) :
    ((((σ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      (f x - (((inner ℝ x (A.adjoint yBar) : ℝ) : EReal))) -
        (f xBar - (((inner ℝ xBar (A.adjoint yBar) : ℝ) : EReal))) := by
  let φ : E → EReal := fun z ↦ f z - (((inner ℝ z (A.adjoint yBar) : ℝ) : EReal))
  have hdomShift : effective_domain φ = effective_domain f := by
    simpa [φ] using shiftedObjective_effectiveDomain_eq
      (f := f) (g := g) (A := A) h_problem yBar
  have hne_bot_shift : ∀ z : E, φ z ≠ ⊥ := by
    intro z
    -- The shifted objective is `f z` plus a finite real term, so it still avoids `⊥`.
    simpa [φ, sub_eq_add_neg, EReal.add_ne_bot_iff] using
      (show f z ≠ ⊥ ∧ (((-inner ℝ z (A.adjoint yBar) : ℝ) : EReal) ≠ ⊥) from
        ⟨h_problem.ne_bot z, EReal.coe_ne_bot _⟩)
  have htoRealShift :
      ∀ {z : E}, z ∈ effective_domain φ →
        (φ z).toReal = (f z).toReal - inner ℝ z (A.adjoint yBar) := by
    intro z hz
    have hz_dom : z ∈ effective_domain f := by
      simpa [hdomShift] using hz
    have hz_top : f z ≠ ⊤ := ne_of_lt hz_dom
    have hz_bot : f z ≠ ⊥ := h_problem.ne_bot z
    rw [show φ z = f z + (((-inner ℝ z (A.adjoint yBar) : ℝ) : EReal)) by
      simp [φ, sub_eq_add_neg],
      EReal.toReal_add hz_top hz_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp [EReal.coe_toReal hz_top hz_bot, sub_eq_add_neg]
  have hstrongShift :
      StrongConvexOn (effective_domain φ) (σ : ℝ) (fun z ↦ (φ z).toReal) := by
    refine ⟨?_, ?_⟩
    · simpa [hdomShift] using h_problem.f_strongly_convex.1
    · intro z hz w hw a b ha hb hab
      have hz_dom : z ∈ effective_domain f := by
        simpa [hdomShift] using hz
      have hw_dom : w ∈ effective_domain f := by
        simpa [hdomShift] using hw
      have hzw_dom : a • z + b • w ∈ effective_domain f :=
        h_problem.f_strongly_convex.1 hz_dom hw_dom ha hb hab
      have hzw_shift : a • z + b • w ∈ effective_domain φ := by
        simpa [hdomShift] using hzw_dom
      have hbase := h_problem.f_strongly_convex.2 hz_dom hw_dom ha hb hab
      have hinner :
          inner ℝ (a • z + b • w) (A.adjoint yBar) =
            a * inner ℝ z (A.adjoint yBar) + b * inner ℝ w (A.adjoint yBar) := by
        rw [inner_add_left, inner_smul_left, inner_smul_left]
        simp
      calc
        (φ (a • z + b • w)).toReal =
            (f (a • z + b • w)).toReal - inner ℝ (a • z + b • w) (A.adjoint yBar) := by
              exact htoRealShift hzw_shift
        _ ≤ a * (f z).toReal + b * (f w).toReal -
            a * b * (((σ : ℝ) / 2) * ‖z - w‖ ^ (2 : ℕ)) -
              inner ℝ (a • z + b • w) (A.adjoint yBar) := by
              exact sub_le_sub_right hbase _
        _ = a * (φ z).toReal + b * (φ w).toReal -
            a * b * (((σ : ℝ) / 2) * ‖z - w‖ ^ (2 : ℕ)) := by
              rw [htoRealShift hz, htoRealShift hw, hinner]
              ring
  have hminShift : IsMinOn φ Set.univ xBar := by
    -- The Chapter 12 argmax point is exactly the minimizer of the shifted objective.
    simpa [φ] using isMinOn_shifted_objective_of_mem_primalArgmax
      (f := f) (g := g) (A := A) h_problem yBar xBar hxBar
  have hxShift : x ∈ effective_domain φ := by
    simpa [hdomShift] using hx
  have hxBarShift : xBar ∈ effective_domain φ := by
    -- Compare against the finite value at `x` to see that the minimizer is finite as well.
    have hle : φ xBar ≤ φ x := (isMinOn_univ_iff.mp hminShift) x
    exact lt_top_iff_ne_top.mpr (lt_top_iff_ne_top.mp (lt_of_le_of_lt hle hxShift))
  let ψ : E → ℝ := fun z ↦ (φ z).toReal
  have hminReal : ∀ {z : E}, z ∈ effective_domain φ → ψ xBar ≤ ψ z := by
    intro z hz
    have hle : φ xBar ≤ φ z := (isMinOn_univ_iff.mp hminShift) z
    exact EReal.toReal_le_toReal hle (hne_bot_shift xBar) (ne_of_lt hz)
  let c : ℝ := ((σ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ)
  have happrox :
      ∀ n : ℕ, ψ x - ψ xBar ≥ (n : ℝ) / (n + 1 : ℝ) * c := by
    intro n
    let a : ℝ := (n : ℝ) / (n + 1 : ℝ)
    let b : ℝ := 1 / (n + 1 : ℝ)
    have ha : 0 ≤ a := by positivity
    have hb : 0 ≤ b := by positivity
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp
    have hm_dom : a • xBar + b • x ∈ effective_domain φ :=
      hstrongShift.1 hxBarShift hxShift ha hb hab
    have hmin_mid : ψ xBar ≤ ψ (a • xBar + b • x) := hminReal hm_dom
    have hstrong_mid :
        ψ (a • xBar + b • x) ≤
          a * ψ xBar + b * ψ x - a * b * c := by
      simpa [ψ, c, norm_sub_rev] using
        (hstrongShift.2 hxBarShift hxShift ha hb hab)
    have hcombine :
        ψ xBar ≤ a * ψ xBar + b * ψ x - a * b * c :=
      le_trans hmin_mid hstrong_mid
    have hb_pos : 0 < b := by positivity
    have hscaled :
        0 ≤ b * (ψ x - ψ xBar - a * c) := by
      have hcombine' : 0 ≤ a * ψ xBar + b * ψ x - a * b * c - ψ xBar := by
        linarith
      have hrewrite :
          a * ψ xBar + b * ψ x - a * b * c - ψ xBar =
            b * (ψ x - ψ xBar - a * c) := by
        have ha' : a = 1 - b := by linarith
        rw [ha']
        ring
      simpa [hrewrite] using hcombine'
    have hgoal_nonneg :
        0 ≤ ψ x - ψ xBar - a * c := by
      by_contra hneg
      have hneg' : ψ x - ψ xBar - a * c < 0 := lt_of_not_ge hneg
      have : b * (ψ x - ψ xBar - a * c) < 0 := by
        exact mul_neg_of_pos_of_neg hb_pos hneg'
      linarith
    simpa [a, c] using hgoal_nonneg
  have hquadReal :
      ψ x ≥ ψ xBar + c := by
    by_cases hxxBar : x = xBar
    · subst hxxBar
      simp [c]
    · have hc : 0 < c := by
        have hnorm_pos : 0 < ‖x - xBar‖ ^ (2 : ℕ) := by
          exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxxBar)) _
        have hσhalf_pos : 0 < ((σ : ℝ) / 2) := by
          exact div_pos σ.2 (by norm_num)
        exact mul_pos hσhalf_pos hnorm_pos
      by_contra hlt
      have hgap_pos : 0 < (c - (ψ x - ψ xBar)) / c := by
        have : 0 < c - (ψ x - ψ xBar) := by linarith
        exact div_pos this hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgap_pos
      have hfrac :
          (ψ x - ψ xBar) / c < (n : ℝ) / (n + 1 : ℝ) := by
        have hleft :
            1 - (1 / (n + 1 : ℝ)) > 1 - ((c - (ψ x - ψ xBar)) / c) := by
          linarith
        have hleft' : (n : ℝ) / (n + 1 : ℝ) = 1 - 1 / (n + 1 : ℝ) := by
          field_simp
          ring
        have hright' : 1 - ((c - (ψ x - ψ xBar)) / c) = (ψ x - ψ xBar) / c := by
          have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc
          field_simp [hc_ne]
          ring
        linarith
      have hlt' : ψ x - ψ xBar < (n : ℝ) / (n + 1 : ℝ) * c := by
        have hmul := mul_lt_mul_of_pos_right hfrac hc
        have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc
        field_simp [hc_ne] at hmul
        have hn1pos : 0 < (n + 1 : ℝ) := by positivity
        have hmul' : (ψ x - ψ xBar) * (n + 1 : ℝ) < (n : ℝ) * c := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        have hdiv :
            ψ x - ψ xBar < ((n : ℝ) * c) / (n + 1 : ℝ) := by
          have hmul'' :
              (ψ x - ψ xBar) * (n + 1 : ℝ) <
                (((n : ℝ) * c) / (n + 1 : ℝ)) * (n + 1 : ℝ) := by
            simpa [hn1pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul'
          have hdiv' :
              ((ψ x - ψ xBar) * (n + 1 : ℝ)) / (n + 1 : ℝ) <
                ((n : ℝ) * c) / (n + 1 : ℝ) := by
            exact (div_lt_iff₀ hn1pos).2 hmul''
          simpa [hn1pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv'
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
      have hge' := happrox n
      linarith
  have hx_toReal : ((ψ x : ℝ) : EReal) = φ x := by
    exact EReal.coe_toReal (ne_of_lt hxShift) (hne_bot_shift x)
  have hxBar_toReal : ((ψ xBar : ℝ) : EReal) = φ xBar := by
    exact EReal.coe_toReal (ne_of_lt hxBarShift) (hne_bot_shift xBar)
  have hquad :
      φ xBar + (((c : ℝ) : EReal)) ≤ φ x := by
    -- Push the real-valued quadratic gap back to `EReal` using finiteness on both endpoints.
    have hcoe :
        (((ψ xBar + c : ℝ) : EReal) ≤ ((ψ x : ℝ) : EReal)) := by
      exact EReal.coe_le_coe_iff.mpr hquadReal
    simpa [ψ, c, hx_toReal, hxBar_toReal, add_assoc] using hcoe
  -- Convert the additive lower bound into the subtraction form used in the target statement.
  exact
    (EReal.le_sub_iff_add_le
      (.inl (hne_bot_shift xBar))
      (.inr (ne_of_lt hxShift))).2 (by simpa [add_comm] using hquad)

/-- Helper for Theorem 12.8: Fenchel's inequality at `(-yBar)` gives
`-(g∗) (-yBar) ≤ g z + ⟪yBar, z⟫`. -/
private lemma fenchel_neg_conjugate_le_primal_plus_pairing
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (z : V) :
    -((g∗) (-yBar)) ≤ g z + (((inner ℝ yBar z : ℝ) : EReal)) := by
  have hconj_ne_bot : (g∗) (-yBar) ≠ ⊥ := by
    exact
      (dual_based_proximal_gradient_dual_G_primal_proper
        (g := g) h_problem.g_proper h_problem.g_convex).ne_bot yBar
  have hfenchel :
      (((-inner ℝ yBar z : ℝ) : EReal)) ≤ g z + (g∗) (-yBar) := by
    -- Start from Fenchel's inequality at the dual point `-yBar`.
    simpa [conjugate_function_primal_apply, InnerProductSpace.toDualMap_apply_apply,
      inner_neg_left, add_comm] using
      (fenchel_inequality g z (InnerProductSpace.toDualMap ℝ V (-yBar)) h_problem.g_proper)
  have hsub :
      -((g∗) (-yBar)) - (((inner ℝ yBar z : ℝ) : EReal)) ≤ g z := by
    have htmp :
        (((-inner ℝ yBar z : ℝ) : EReal) - (g∗) (-yBar)) ≤ g z :=
      (EReal.sub_le_iff_le_add
        (.inl hconj_ne_bot)
        (.inr (h_problem.g_proper.ne_bot z))).2 hfenchel
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
  exact
    (EReal.sub_le_iff_le_add
      (.inl (EReal.coe_ne_bot _))
      (.inr (h_problem.g_proper.ne_bot z))).1 hsub

/-- Helper for Theorem 12.8: the normalized `EReal` shape
`a + (r + (-r - b))` collapses to `a - b`. -/
private lemma ereal_add_real_cancel_sub (a b : EReal) (r : ℝ) :
    a + ((r : EReal) + (-((r : EReal)) - b)) = a - b := by
  have hzero : ((r : EReal) + -((r : EReal))) = 0 := by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    norm_num
  calc
    a + ((r : EReal) + (-((r : EReal)) - b)) =
        a + ((((r : EReal)) + -((r : EReal))) + -b) := by
          rw [sub_eq_add_neg, add_assoc]
    _ = a + (0 + -b) := by
          rw [hzero]
    _ = a - b := by
          rw [zero_add, sub_eq_add_neg]

/-- Helper for Theorem 12.8: the normalized `EReal` shape
`(a - r) + (b + r)` collapses to `a + b`. -/
private lemma ereal_sub_real_add_real_cancel (a b : EReal) (r : ℝ) :
    (a - ((r : EReal))) + (b + ((r : EReal))) = a + b := by
  have hzero : (-((r : EReal)) + ((r : EReal))) = 0 := by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    norm_num
  have hinner :
      -((r : EReal)) + (b + ((r : EReal))) =
        b + (-((r : EReal)) + ((r : EReal))) := by
    calc
      -((r : EReal)) + (b + ((r : EReal))) =
          (-((r : EReal)) + b) + ((r : EReal)) := by
            rw [add_assoc]
      _ = (b + -((r : EReal))) + ((r : EReal)) := by
            rw [add_comm (-((r : EReal))) b]
      _ = b + (-((r : EReal)) + ((r : EReal))) := by
            rw [← add_assoc]
  calc
    (a - ((r : EReal))) + (b + ((r : EReal))) =
        a + (-((r : EReal)) + (b + ((r : EReal)))) := by
          rw [sub_eq_add_neg, add_assoc]
    _ = a + (b + (-((r : EReal)) + ((r : EReal)))) := by
          simpa using congrArg (fun t : EReal ↦ a + t) hinner
    _ = a + (b + 0) := by
          rw [hzero]
    _ = a + b := by
          rw [add_zero]

/-- Helper for Theorem 12.8: every Chapter 12 primal-space dual objective value avoids `⊤`. -/
private lemma dual_objective_ne_top
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V) :
    q yBar ≠ ⊤ := by
  have hF_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ) (f := f) (A := A)
      h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex yBar
  have hG_ne_bot : (g∗) (-yBar) ≠ ⊥ := by
    exact
      (dual_based_proximal_gradient_dual_G_primal_proper
        (g := g) h_problem.g_proper h_problem.g_convex).ne_bot yBar
  by_cases hG_top : (g∗) (-yBar) = ⊤
  · -- If `g*(-yBar) = ⊤`, then the dual objective is `⊥`, hence not `⊤`.
    rw [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply, hG_top]
    simp
  · have hF_val :
        (((((f∗) (A.adjoint yBar)).toReal : ℝ) : EReal)) = (f∗) (A.adjoint yBar) := by
        exact EReal.coe_toReal hF_finite.2.ne hF_finite.1
    have hG_val :
        (((((g∗) (-yBar)).toReal : ℝ) : EReal)) = (g∗) (-yBar) := by
        exact EReal.coe_toReal hG_top hG_ne_bot
    have hfinite_ne_top :
        -(((((f∗) (A.adjoint yBar)).toReal : ℝ) : EReal)) -
          (((((g∗) (-yBar)).toReal : ℝ) : EReal)) ≠ ⊤ := by
      rw [sub_eq_add_neg]
      have hcoe :
          -(((((f∗) (A.adjoint yBar)).toReal : ℝ) : EReal)) +
            -(((((g∗) (-yBar)).toReal : ℝ) : EReal)) =
            (((-((f∗) (A.adjoint yBar)).toReal + -((g∗) (-yBar)).toReal : ℝ)) : EReal) := by
              rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add]
      rw [hcoe]
      exact EReal.coe_ne_top _
    intro htop
    have htop' :
        -(((((f∗) (A.adjoint yBar)).toReal : ℝ) : EReal)) -
          (((((g∗) (-yBar)).toReal : ℝ) : EReal)) = ⊤ := by
      calc
        -(((((f∗) (A.adjoint yBar)).toReal : ℝ) : EReal)) -
            (((((g∗) (-yBar)).toReal : ℝ) : EReal)) =
          -((f∗) (A.adjoint yBar)) - (g∗) (-yBar) := by
              rw [hF_val, hG_val]
        _ = ⊤ := by
              simpa [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply] using htop
    exact hfinite_ne_top htop'

/-- Helper for Theorem 12.8: the source proof naturally produces the additive inequality
`(σ / 2) ‖xBar - xStar‖² + q(yBar) ≤ f(xStar) + g(A xStar)`. -/
lemma half_sigma_sqdist_add_dualObjective_le_primalValue_of_primalArgmax
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (xBar xStar : E)
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar) :
    ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) + q yBar ≤
      composite_model_objective f (g ∘ A) xStar := by
  let innerBar : ℝ := inner ℝ xBar (A.adjoint yBar)
  let innerStar : ℝ := inner ℝ xStar (A.adjoint yBar)
  let dualCoeff : ℝ := ((f∗) (A.adjoint yBar)).toReal
  have hxStar_dom :
      xStar ∈ effective_domain f := by
    exact primalMinimizer_mem_effectiveDomain
      (f := f) (g := g) (A := A) h_problem xStar hxStar
  have hgap :=
    shiftedObjective_gap_ge_halfSigmaSqdist_of_memPrimalArgmax
      (f := f) (g := g) (A := A) σ h_problem yBar xBar hxBar xStar hxStar_dom
  have hF_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ) (f := f) (A := A)
      h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex yBar
  have hdualCoeff :
      (((dualCoeff : ℝ) : EReal)) = (f∗) (A.adjoint yBar) := by
    -- The Chapter 12 `F`-term is finite everywhere, so we can pass to its real value.
    exact EReal.coe_toReal hF_finite.2.ne hF_finite.1
  have hshift_bar :
      f xBar - (((innerBar : ℝ) : EReal)) = -((f∗) (A.adjoint yBar)) := by
    calc
      f xBar - (((innerBar : ℝ) : EReal)) =
          -((((innerBar : ℝ) : EReal) - f xBar)) := by
            simpa [innerBar] using (ereal_neg_real_sub (a := f xBar) (r := innerBar)).symm
      _ = -((f∗) (A.adjoint yBar)) := by
            rw [conjugatePrimal_eqPairingSub_of_memPrimalArgmax
              (f := f) (g := g) (A := A) h_problem yBar xBar hxBar]
  have hadj :
      inner ℝ xStar (A.adjoint yBar) = inner ℝ yBar (A xStar) := by
    -- Rewrite the primal-space pairing through the adjoint before the final cancellation step.
    simpa [real_inner_comm] using (LinearMap.adjoint_inner_right A xStar yBar)
  calc
    ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) + q yBar ≤
        ((f xStar - (((innerStar : ℝ) : EReal))) -
          (f xBar - (((innerBar : ℝ) : EReal)))) + q yBar := by
          simpa [add_assoc, add_left_comm, add_comm, innerBar, innerStar, norm_sub_rev] using
            add_le_add_left hgap (q yBar)
    _ = (f xStar - (((innerStar : ℝ) : EReal))) +
          (((dualCoeff : ℝ) : EReal) +
            (-(((dualCoeff : ℝ) : EReal)) - (g∗) (-yBar))) := by
          rw [hshift_bar, dual_based_proximal_gradient_lagrange_dual_objective_primal_apply,
            hdualCoeff]
          rw [sub_eq_add_neg, sub_eq_add_neg, neg_neg]
          ac_rfl
    _ = (f xStar - (((innerStar : ℝ) : EReal))) - (g∗) (-yBar) := by
          rw [ereal_add_real_cancel_sub]
    _ ≤ (f xStar - (((innerStar : ℝ) : EReal))) +
          (g (A xStar) + (((inner ℝ yBar (A xStar) : ℝ) : EReal))) := by
          -- Apply Fenchel to the `g`-term at `z = A xStar`.
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            add_le_add_left
              (fenchel_neg_conjugate_le_primal_plus_pairing
                (f := f) (g := g) (A := A) h_problem yBar (A xStar))
              (f xStar - (((innerStar : ℝ) : EReal)))
    _ = f xStar + g (A xStar) := by
          simpa [innerStar, hadj] using
            (ereal_sub_real_add_real_cancel
              (a := f xStar) (b := g (A xStar)) (r := inner ℝ yBar (A xStar)))
    _ = composite_model_objective f (g ∘ A) xStar := by
          rw [composite_model_objective_apply, Function.comp]

-- Proof sketch: combine Lemma 12.7, applied to the pointwise argmax hypothesis `hx k`, with the
-- dual-gap estimate from Theorem 12.4 for the canonical dual trajectory `htraj`. Lemma 12.7 gives
-- `‖x k - xStar‖² ≤ (2 / σ) (q_opt - q(y k))`, and Theorem 12.4 bounds the dual gap by
-- `L ‖y0 - yStar‖² / (2 k)`. Multiplying the bounds and simplifying cancels the factor `2`.
/-- Helper for Theorem 12.8: the local Lemma 12.7 inequality, stating that a primal argmax
point at `yBar` is controlled by the corresponding Chapter 12 dual gap. -/
theorem dualGap_dominates_halfSigmaSqdist_of_primalArgmax
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yBar : V)
    (xBar xStar : E)
    (hxBar : xBar ∈ dual_proximal_gradient_primal_x_argmax f A yBar)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar) :
    ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      qOpt - q yBar := by
  have hadd :
      ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) + q yBar ≤ qOpt := by
    -- First prove the additive inequality against the primal value, then identify that value with
    -- `qOpt` via the theorem-local strong-duality bridge.
    calc
      ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) + q yBar ≤
          composite_model_objective f (g ∘ A) xStar :=
        half_sigma_sqdist_add_dualObjective_le_primalValue_of_primalArgmax
          (f := f) (g := g) (A := A) σ h_problem yBar xBar xStar hxBar hxStar
      _ = qOpt := by
          simpa using primalMinimizerValue_eqDualProblemValue
            (f := f) (g := g) (A := A) h_problem xStar hxStar
  -- Convert the additive inequality into the dual-gap subtraction form.
  have hq_ne_top : q yBar ≠ ⊤ :=
    dual_objective_ne_top (f := f) (g := g) (A := A) h_problem yBar
  have hqOpt_ne_bot : qOpt ≠ ⊥ := by
    rw [← primalMinimizerValue_eqDualProblemValue
      (f := f) (g := g) (A := A) h_problem xStar hxStar]
    simp [Function.comp,
      h_problem.ne_bot xStar, h_problem.g_proper.ne_bot (A xStar)]
  exact
    (EReal.le_sub_iff_add_le
      (a := ((((σ : ℝ) / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) : ℝ) : EReal))
      (b := q yBar) (c := qOpt)
      (.inr hqOpt_ne_bot)
      (.inl hq_ne_top)).2 hadd

/-- The `core/canonical` primal-distance estimate over the Chapter 12 dual trajectory owner,
with the primal sequence supplied only through the pointwise argmax owner. -/
theorem dual_proximal_gradient_primal_sequence_sqdist_le_of_dual_trajectory
    (σ : PosReal)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y0 : V) (x : ℕ → E) (y : ℕ → V)
    (htraj : is_dual_based_proximal_gradient_dual_trajectory F G L y y0)
    (hx : ∀ k : ℕ, x k ∈ dual_proximal_gradient_primal_x_argmax f A (y k))
    (xStar : E)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar)
    (yStar : V)
    (hyStar : q yStar = qOpt)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((σ : ℝ) * (k : ℝ)) := by
  -- Route correction: isolate the missing Lemma 12.7 inequality as a single local helper, then
  -- finish the displayed `O(1 / k)` bound with the imported Theorem 12.4 dual-gap rate.
  have hhalf_gap :
      ((((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        qOpt - q (y k) := by
    -- The local Lemma 12.7 bridge compares the pointwise primal argmax witness `x k` with the
    -- same-iterate dual gap.
    simpa using
      dualGap_dominates_halfSigmaSqdist_of_primalArgmax
        (f := f)
        (g := g)
        (A := A)
        σ
        h_problem
        (y k)
        (x k)
        xStar
        (hx k)
        hxStar
  have hgap_rate :
      qOpt - q (y k) ≤
        (((L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / (2 * (k : ℝ)) : ℝ) : EReal) := by
    -- Theorem 12.4 supplies the `O(1 / k)` decay of the dual objective gap along the same dual
    -- trajectory.
    simpa using
      dual_based_proximal_gradient_dual_objective_gap_le
        (f := f)
        (g := g)
        (A := A)
        σ
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex
        h_problem.g_proper
        h_problem.g_convex
        L
        y
        y0
        yStar
        htraj
        hyStar
        k
        hk
  -- Chaining the two chapter-level inequalities leaves only scalar normalization in `ℝ`.
  have hbound_ereal :
      ((((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        (((L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / (2 * (k : ℝ)) : ℝ) : EReal) :=
    le_trans hhalf_gap hgap_rate
  have hbound_real :
      ((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) ≤
        (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / (2 * (k : ℝ)) := by
    exact EReal.coe_le_coe_iff.mp hbound_ereal
  have hσ_pos : 0 < (σ : ℝ) := σ.2
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hk_pos : 0 < (k : ℝ) := by
    linarith
  have hden_pos : 0 < 2 * (k : ℝ) := by
    positivity
  -- Clear the positive factor `2 * k`, then cancel the remaining factor `σ * k`.
  have hmul :
      (((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ)) * (2 * (k : ℝ)) ≤
        (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) := by
    exact (le_div_iff₀ hden_pos).mp hbound_real
  have hscaled :
      (σ : ℝ) * ‖x k - xStar‖ ^ (2 : ℕ) * (k : ℝ) ≤
        (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) := by
    nlinarith
  have htotal_pos : 0 < (σ : ℝ) * (k : ℝ) :=
    mul_pos hσ_pos hk_pos
  exact
    (le_div_iff₀ htotal_pos).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

-- Proof sketch: extract the pointwise argmax membership from the source-facing Algorithm 12.2
-- trajectory via the primitive field `htraj.primal_step`, pass to the canonical dual trajectory
-- owner with `is_dual_proximal_gradient_primal_trajectory.toDualTrajectory h_problem htraj`,
-- and apply the core theorem above.
/-- Theorem 12.8: under Assumption 12.1, if `(x^k, y^k)` is generated by the dual proximal
gradient method with an admissible constant parameter `L`, then for every primal optimal
solution `x*`, every dual optimal solution `y*`, and every `k ≥ 1`, the primal iterate satisfies
the sublinear estimate `‖x^k - x*‖² ≤ L ‖y^0 - y*‖² / (σ k)`. -/
theorem dual_proximal_gradient_primal_sequence_sqdist_le
    (σ : PosReal)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y0 : V) (x : ℕ → E) (y : ℕ → V)
    (htraj : is_dual_proximal_gradient_primal_trajectory f g A L y0 x y)
    (xStar : E)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar)
    (yStar : V)
    (hyStar : q yStar = qOpt)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((σ : ℝ) * (k : ℝ)) := by
  -- Pass from the source-facing Algorithm 12.2 trajectory owner to the canonical dual trajectory.
  simpa using
    dual_proximal_gradient_primal_sequence_sqdist_le_of_dual_trajectory
      f
      g
      A
      σ
      L
      h_problem
      y0
      x
      y
      (is_dual_proximal_gradient_primal_trajectory.toDualTrajectory
        (f := f)
        (g := g)
        (A := A)
        h_problem
        htraj)
      (fun k ↦ htraj.primal_step k)
      xStar
      hxStar
      yStar
      hyStar
      k
      hk

end
