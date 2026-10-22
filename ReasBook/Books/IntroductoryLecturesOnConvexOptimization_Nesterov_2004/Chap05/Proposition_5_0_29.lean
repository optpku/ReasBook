/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_27
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

/- Proposition 5.0.29 lies in the chapter's Fenchel-conjugacy / gradient-Hessian duality domain.

Primary domain:
- differentiability of the finite real part of the canonical Fenchel dual under a globally unique
  Fenchel-support maximizer hypothesis, together with the inverse-Hessian duality at interior
  maximizing primal points.

Relevant owner-style declarations sampled before refinement:
- `dom` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the chapter owners for the
  effective domain and finite real part of an `EReal`-valued function;
- `fenchelDual` / notation `f⋆` in `Chap05/Definition_5_0_27`, the chapter owner for the
  Fenchel conjugate of a `WithTop ℝ`-valued function;
- `hessian` in `Chap01/Definition_1_4_16`, the chapter owner for second derivatives of real-valued
  functions on complete real inner-product spaces;
- `IsMaxOn`, the canonical maximizer predicate for the Fenchel support functional
  `y ↦ ⟪s, y⟫ - f y` on `dom f`.

Best owner abstraction:
- source-facing: the unique Fenchel-support maximizer realization of the canonical Fenchel dual
  value and the resulting gradient / inverse-Hessian conclusions, with primal interiority entering
  only in the second-order part;
- core/canonical: `f⋆`, `dom (f⋆)`, `extendedRealRealPart (f⋆)`, `hessian`, and
  `IsMaxOn`;
- bridge/view: the derived Fenchel-dual value identity at a support maximizer.

Primitive data:
- a `WithTop ℝ`-valued primal function `f`;
- for the source-facing gradient statement, a primal-dual point pair `(x, s)` with a unique
  owner-level Fenchel-support maximizer at slope `s`;
- for the second-order bridge statements, a candidate maximizing-point field `xStar` together
  with interior membership of the chosen maximizing points.

Derived API:
- the value identity `extendedRealRealPart (f⋆) s = inner ℝ s (xStar s) - withTopRealPart f
  (xStar s)` at a maximizing point;
- the pointwise gradient and branchwise Hessian-identification conclusions of
  Proposition 5.0.29.

The previous version rebuilt a parallel dual-function parameter `fStar : E → WithTop ℝ` and a
local wrapper around the canonical support-maximizer predicate. Those notions are already owned
upstream by `f⋆`, `dom (f⋆)`, `extendedRealRealPart (f⋆)`, `hessian`, and `IsMaxOn`. This
refinement deletes the duplicate dual layer, rewrites the inverse-Hessian surface through the
chapter owner `hessian`, and states the proposition directly on the canonical support-maximizer
surface. The redundant dual-value equality and raw value-based uniqueness clause are also removed
from the primitive input data: they are downstream consequences of the maximizer hypotheses, not
separate source-level structure. The Euclidean model `EuclideanSpace ℝ (Fin n)` and
finite-dimensionality are not the same issue: the Euclidean display model is unnecessary, but the
chapter's available differentiability bridge for this Fenchel-maximizer argument is only
finite-dimensional. The file therefore stays on the canonical owner level of a finite-dimensional
real inner-product space rather than claiming a new infinite-dimensional theorem. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section

variable {f : E → WithTop ℝ} {xStar : E → E}

-- Semantic recall check: LeanSearch did not expose a direct owner theorem for differentiability
-- of Fenchel conjugates, so this file keeps the chapter-local bridge API.

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.0.29: a Fenchel-support maximizer realizes the canonical Fenchel
dual value by a single support term. -/
lemma fenchelDual_eq_support_value_of_isMaxOn
    {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    (f⋆) s = ((inner ℝ s x - withTopRealPart f x : ℝ) : EReal) := by
  -- Rewrite the dual value as the supremum over `dom f` and compare every support term with the
  -- maximizing value at `x`.
  rw [fenchelDual_apply_eq_sSup_image_dom]
  apply le_antisymm
  · refine sSup_le ?_
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have hsupport : inner ℝ s y - withTopRealPart f y ≤ inner ℝ s x - withTopRealPart f x :=
      hmax hy
    simpa only [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom hy,
      withTopToEReal_eq_coe_withTopRealPart_of_mem_dom hx, ← EReal.coe_sub] using
      (show (((inner ℝ s y - withTopRealPart f y : ℝ) : EReal)) ≤
          (((inner ℝ s x - withTopRealPart f x : ℝ) : EReal)) from by
        exact_mod_cast hsupport)
  · -- The maximizing support value is one admissible term in the defining supremum.
    simpa only [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom hx, ← EReal.coe_sub] using
      (show (inner ℝ s x : EReal) - withTopToEReal (f x) ≤
          sSup ((fun y : E ↦ (inner ℝ s y : EReal) - withTopToEReal (f y)) '' dom f) from by
        exact le_sSup ⟨x, hx, rfl⟩)

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.0.29: a Fenchel-support maximizer makes the dual value finite. -/
lemma mem_dom_fenchelDual_of_isMaxOn
    {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    s ∈ dom (f⋆) := by
  -- The realized support value is finite, so the dual lies in its effective domain.
  rw [mem_extendedRealEffectiveDomain_iff, fenchelDual_eq_support_value_of_isMaxOn hx hmax]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.0.29: after converting the dual value back to a real number on
`dom (f⋆)`, the maximizing support term gives the finite real part of the Fenchel dual. -/
lemma extendedRealRealPart_fenchelDual_eq_support_value_of_isMaxOn
    {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    extendedRealRealPart (f⋆) s = inner ℝ s x - withTopRealPart f x := by
  -- First put `s` in the effective domain of the dual, then coerce the realized `EReal` value
  -- back to the corresponding real number.
  have hs : s ∈ dom (f⋆) := mem_dom_fenchelDual_of_isMaxOn hx hmax
  have hcoe :
      (((extendedRealRealPart (f⋆) s : ℝ) : EReal)) =
        (((inner ℝ s x - withTopRealPart f x : ℝ) : EReal)) := by
    rw [coe_extendedRealRealPart hs, fenchelDual_eq_support_value_of_isMaxOn hx hmax]
  exact_mod_cast hcoe

/-- Helper for Proposition 5.0.29: at an interior Fenchel-support maximizer, the first-order
optimality equation identifies the primal gradient with the dual slope. -/
lemma gradient_eq_of_fenchelSupport_isMaxOn_interior
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    {s x : E}
    (hx : x ∈ interior (dom f))
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    ∇ (withTopRealPart f) x = s := by
  let φ : E → ℝ := fun y ↦ inner ℝ s y - withTopRealPart f y
  have hdom_nhds : dom f ∈ nhds x := by
    exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hx) interior_subset
  have hlocalMax : IsLocalMax φ x := by
    -- Global maximality on `dom f` becomes local maximality because `x` is interior to `dom f`.
    simpa [φ] using hmax.isLocalMax hdom_nhds
  have hcontDiffAt :
      ContDiffAt ℝ 1 (withTopRealPart f) x := by
    -- Restrict the `C²` hypothesis to the interior point `x`.
    exact (hf_contDiff.of_le (by norm_num)).contDiffAt (IsOpen.mem_nhds isOpen_interior hx)
  have hdiff :
      DifferentiableAt ℝ (withTopRealPart f) x := by
    -- The `C²` hypothesis gives differentiability of the primal finite real part at interior
    -- points.
    exact hcontDiffAt.differentiableAt (by norm_num)
  have hlin :
      HasFDerivAt (fun y : E ↦ inner ℝ s y) (innerSL ℝ s) x := by
    -- The support functional is linear, so its derivative is the same linear map everywhere.
    simpa using (innerSL ℝ s).hasFDerivAt
  have hφ :
      HasFDerivAt φ ((innerSL ℝ s) - fderiv ℝ (withTopRealPart f) x) x := by
    -- Differentiate the support functional minus the primal finite real part.
    simpa [φ] using hlin.sub hdiff.hasFDerivAt
  have hfrechet_zero :
      (innerSL ℝ s) - fderiv ℝ (withTopRealPart f) x = 0 :=
    hlocalMax.hasFDerivAt_eq_zero hφ
  have hs_eq_grad : s = ∇ (withTopRealPart f) x := by
    -- Equality of the Fréchet derivatives gives equality of all inner products against test
    -- vectors, hence equality of the representing vectors.
    apply ext_inner_right ℝ
    intro y
    have hzero_apply :
        ((innerSL ℝ s) - fderiv ℝ (withTopRealPart f) x) y = 0 := by
      exact congrArg (fun L : StrongDual ℝ E ↦ L y) hfrechet_zero
    exact sub_eq_zero.mp <| by
      simpa [ContinuousLinearMap.sub_apply, hdiff.hasGradientAt.fderiv_apply] using hzero_apply
  exact hs_eq_grad.symm

/-- Helper for Proposition 5.0.29: if an interior primal point has gradient `t`, then that point
maximizes the Fenchel support functional at slope `t` on `dom f`. -/
lemma fenchelSupport_isMaxOn_of_gradient_eq_interior
    (hf_closedConvex : ClosedConvexFunction f)
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    {t y : E}
    (hy : y ∈ interior (dom f))
    (hgrad : ∇ (withTopRealPart f) y = t) :
    IsMaxOn (fun z : E ↦ inner ℝ t z - withTopRealPart f z) (dom f) y := by
  have hy_dom : y ∈ dom f := interior_subset hy
  have hgradAt :
      HasGradientAt (withTopRealPart f) (∇ (withTopRealPart f) y) y := by
    -- Restrict the `C²` regularity to the interior point `y` to obtain the gradient witness.
    exact
      (((hf_contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt
        (IsOpen.mem_nhds isOpen_interior hy)).differentiableAt (by norm_num)).hasGradientAt
  have hsub : t ∈ ∂ f(y) := by
    -- Convert the gradient identity into the owner-level subgradient inequality on `dom f`.
    simpa [hgrad] using
      gradient_mem_subdifferential_of_hasGradientAt
        (f := f) hf_closedConvex.convexOn_withTopRealPart hy hgradAt
  rcases mem_subdifferential_iff.mp hsub with ⟨-, hminorant⟩
  intro z hz
  have hminorant_real :
      withTopRealPart f z ≥ withTopRealPart f y + inner ℝ t (z - y) := by
    have hminorant_withTop :
        f z ≥ f y + (inner ℝ t (z - y) : WithTop ℝ) := hminorant hz
    rw [← coe_withTopRealPart hz, ← coe_withTopRealPart hy_dom] at hminorant_withTop
    exact_mod_cast hminorant_withTop
  have hsupport :
      inner ℝ t z - withTopRealPart f z ≤ inner ℝ t y - withTopRealPart f y := by
    rw [inner_sub_right] at hminorant_real
    linarith
  exact hsupport

/-- Helper for Proposition 5.0.29: a `C²` primal finite real part gives a `C¹` primal gradient
map at each interior point. -/
private lemma primalGradient_contDiffAt_of_contDiffOn_two
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    {x : E} (hx : x ∈ interior (dom f)) :
    ContDiffAt ℝ 1 (∇ (withTopRealPart f)) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C1 : ContDiffAt ℝ 1 (fderiv ℝ (withTopRealPart f)) x := by
    -- Differentiate the primal finite real part once and keep the remaining first derivative.
    exact
      (hf_contDiff.contDiffAt (IsOpen.mem_nhds isOpen_interior hx)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  -- Rewrite the gradient through the Riesz map so the remaining regularity becomes `C¹`.
  simpa [gradient, D] using D.contDiff.contDiffAt.comp x hfderiv_C1

/-- Helper for Proposition 5.0.29: the `C²` primal finite real part differentiates its gradient
to the owner Hessian at each interior point. -/
private lemma primalGradient_hasFDerivAt_of_contDiffOn_two
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    {x : E} (hx : x ∈ interior (dom f)) :
    HasFDerivAt (∇ (withTopRealPart f)) (hessian (withTopRealPart f) x) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv :
      DifferentiableAt ℝ (fderiv ℝ (withTopRealPart f)) x := by
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ (withTopRealPart f)) x :=
      (hf_contDiff.contDiffAt (IsOpen.mem_nhds isOpen_interior hx)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ (withTopRealPart f)) x := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp x hfderiv
  -- The chapter owner `hessian` is definitionally the derivative of the gradient map.
  simpa [hessian] using hgrad.hasFDerivAt

/-- Helper for Proposition 5.0.29: once the primal Hessian at an interior support maximizer is
invertible, the primal gradient map admits a canonical local inverse branch near the dual slope. -/
private lemma primalGradient_localInverse_atSupportMaximizer
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    {s x : E}
    (hx : x ∈ interior (dom f))
    (hx_grad : ∇ (withTopRealPart f) x = s)
    (hinv : (hessian (withTopRealPart f) x).IsInvertible) :
    ∃ ψ : E → E,
      ψ s = x ∧
      HasFDerivAt ψ (hessian (withTopRealPart f) x).inverse s ∧
      Filter.Tendsto ψ (nhds s) (nhds x) ∧
      ∀ᶠ t in nhds s, ∇ (withTopRealPart f) (ψ t) = t := by
  let G : E → E := ∇ (withTopRealPart f)
  let H : E →L[ℝ] E := hessian (withTopRealPart f) x
  let e : E ≃L[ℝ] E := Classical.choose hinv
  have he : (e : E →L[ℝ] E) = H := Classical.choose_spec hinv
  have hgrad_C1 : ContDiffAt ℝ 1 G x := by
    -- The inverse-function theorem is applied to the primal gradient field itself.
    simpa [G] using primalGradient_contDiffAt_of_contDiffOn_two (f := f) hf_contDiff hx
  have hgrad_fderiv : HasFDerivAt G H x := by
    -- Normalize the derivative of `∇ (withTopRealPart f)` to the owner Hessian.
    simpa [G, H] using primalGradient_hasFDerivAt_of_contDiffOn_two (f := f) hf_contDiff hx
  have hgrad_fderiv_e : HasFDerivAt G (e : E →L[ℝ] E) x := by
    -- The chosen continuous linear equivalence is exactly the invertible Hessian.
    simpa [he] using hgrad_fderiv
  have hstrict : HasStrictFDerivAt G (e : E →L[ℝ] E) x := by
    -- Upgrade the `C¹` derivative at `x` to the strict derivative required by the inverse API.
    exact hgrad_C1.hasStrictFDerivAt' hgrad_fderiv_e one_ne_zero
  let ψ : E → E := hstrict.localInverse G e x
  have he_inverse : (e.symm : E →L[ℝ] E) = H.inverse := by
    -- Normalize the inverse-function derivative to the project's `ContinuousLinearMap.inverse`.
    calc
      (e.symm : E →L[ℝ] E) = (e : E →L[ℝ] E).inverse := by
        symm
        exact ContinuousLinearMap.inverse_equiv e
      _ = H.inverse := by
        simp [he]
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · -- The local inverse sends the base dual slope `s = G x` back to the maximizer `x`.
    simpa [ψ, G, hx_grad] using hstrict.localInverse_apply_image (f := G) (f' := e) (a := x)
  · -- The inverse-function theorem gives the derivative of the branch as the inverse Hessian.
    simpa [ψ, G, H, hx_grad, he_inverse] using
      (hstrict.to_localInverse (f := G) (f' := e) (a := x)).hasFDerivAt
  · -- The same inverse-function package also controls the branch's limit back to `x`.
    simpa [ψ, G, hx_grad] using hstrict.localInverse_tendsto (f := G) (f' := e) (a := x)
  · -- Near `s`, the branch is a genuine right inverse of the primal gradient map.
    simpa [ψ, G, hx_grad] using hstrict.eventually_right_inverse (f := G) (f' := e) (a := x)

/-- Helper for Proposition 5.0.29: a local inverse branch of the primal gradient rewrites the
Fenchel conjugate near the dual slope as the realized support-value model. -/
private lemma fenchelConjugate_eventuallyEq_supportModel_of_localInverse
    (hf_closedConvex : ClosedConvexFunction f)
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    {s x : E} {ψ : E → E}
    (hx : x ∈ interior (dom f))
    (hψ_tendsto : Filter.Tendsto ψ (nhds s) (nhds x))
    (hψ_right_inverse : ∀ᶠ t in nhds s, ∇ (withTopRealPart f) (ψ t) = t) :
    extendedRealRealPart (f⋆) =ᶠ[nhds s] fun t ↦ inner ℝ t (ψ t) - withTopRealPart f (ψ t) := by
  have hψ_memInterior : ∀ᶠ t in nhds s, ψ t ∈ interior (dom f) := by
    -- The branch converges back to the interior maximizer, so it stays interior nearby.
    exact hψ_tendsto (IsOpen.mem_nhds isOpen_interior hx)
  filter_upwards [hψ_memInterior, hψ_right_inverse] with t htInterior htGradient
  have htMax :
      IsMaxOn (fun y : E ↦ inner ℝ t y - withTopRealPart f y) (dom f) (ψ t) :=
    fenchelSupport_isMaxOn_of_gradient_eq_interior hf_closedConvex hf_contDiff htInterior htGradient
  -- Once `ψ t` is recognized as the support maximizer at slope `t`, the dual value is exactly
  -- the realized support term.
  simpa using
    extendedRealRealPart_fenchelDual_eq_support_value_of_isMaxOn
      (f := f) (s := t) (x := ψ t) (interior_subset htInterior) htMax

/-- Helper for Proposition 5.0.29: differentiating the local support-value model at the base
dual slope leaves only the explicit `inner ℝ · x` term after the chain-rule cancellation. -/
private lemma supportModel_hasGradientAt_of_localInverse
    {s x : E} {ψ : E → E}
    (hF_grad : HasGradientAt (withTopRealPart f) s x)
    (hψ : ψ s = x)
    (hψ_deriv : HasFDerivAt ψ (hessian (withTopRealPart f) x).inverse s) :
    HasGradientAt (fun t ↦ inner ℝ t (ψ t) - withTopRealPart f (ψ t)) x s := by
  have hInner :
      HasFDerivAt (fun t ↦ inner ℝ t (ψ t))
        ((fderivInnerCLM ℝ (s, x)).comp
          ((1 : E →L[ℝ] E).prod (hessian (withTopRealPart f) x).inverse)) s := by
    -- Differentiate the explicit support pairing `t ↦ ⟪t, ψ t⟫` by the product rule for `inner`.
    simpa [hψ] using (hasFDerivAt_id s).inner ℝ hψ_deriv
  have hPrimalComp :
      HasFDerivAt (fun t ↦ withTopRealPart f (ψ t))
        ((innerSL ℝ s).comp (hessian (withTopRealPart f) x).inverse) s := by
    -- The derivative of the primal term is the gradient functional at `x` postcomposed with `Dψ`.
    have hF_grad_at_ψs :
        HasFDerivAt (withTopRealPart f) (innerSL ℝ s) (ψ s) := by
      simpa [HasGradientAt, hψ] using hF_grad.hasFDerivAt
    simpa using hF_grad_at_ψs.comp s hψ_deriv
  have hModel :
      HasFDerivAt (fun t ↦ inner ℝ t (ψ t) - withTopRealPart f (ψ t))
        (innerSL ℝ x) s := by
    -- The `ψ`-dependent chain-rule terms cancel because both carry the same slope `s`.
    convert hInner.sub hPrimalComp using 1
    ext v
    simp [fderivInnerCLM_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      real_inner_comm, add_comm]
  simpa [HasGradientAt] using hModel

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.0.29: affine lines `t ↦ x + t • d` differentiate to the fixed
direction `d`. -/
private lemma affineLine_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using (((hasDerivAt_id t).smul_const d).const_add x)

/-- Helper for Proposition 5.0.29: differentiating a scalarized gradient line gives the Hessian
pairing with the line direction. -/
private lemma scalarizedGradientLine_hasDerivAt
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    {x d v : E} {t : ℝ} (hxt : x + t • d ∈ interior (dom f)) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ (withTopRealPart f) (x + s • d)) v)
      (inner ℝ (hessian (withTopRealPart f) (x + t • d) d) v) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv :
      DifferentiableAt ℝ (fderiv ℝ (withTopRealPart f)) (x + t • d) := by
    have hcont :
        ContDiffAt ℝ 1 (fderiv ℝ (withTopRealPart f)) (x + t • d) :=
      (hf_contDiff.contDiffAt (IsOpen.mem_nhds isOpen_interior hxt)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad :
      DifferentiableAt ℝ (∇ (withTopRealPart f)) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ (withTopRealPart f) (x + s • d))
        ((hessian (withTopRealPart f) (x + t • d)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Differentiate the gradient field and compose it with the affine-line derivative.
    simpa using (hgrad.hasFDerivAt.comp t (affineLine_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) v
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ (withTopRealPart f) (x + s • d)))
        (φ.comp ((hessian (withTopRealPart f) (x + t • d)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose the gradient line with the fixed scalar functional `w ↦ ⟪w, v⟫`.
    simpa [φ] using (φ.hasFDerivAt.comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Proposition 5.0.29: a Hessian-kernel direction forces the primal gradient to stay
equal to `s` along a short affine line through `x`. -/
private lemma localGradient_eq_s_onKernelLine
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    {s x u : E}
    (hx : x ∈ interior (dom f))
    (hx_grad : ∇ (withTopRealPart f) x = s)
    (hu_hess : hessian (withTopRealPart f) x u = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      x + t • u ∈ interior (dom f) ∧ ∇ (withTopRealPart f) (x + t • u) = s := by
  rcases hself with ⟨Mf0, hMf0⟩
  let Mf : NNReal := Mf0 + 1
  have hMf : IsSelfConcordantOnWith (interior (dom f)) Mf (withTopRealPart f) :=
    IsSelfConcordantOnWith.of_le hMf0 (by
      change Mf0 ≤ Mf0 + 1
      simp)
  have hMf_pos : 0 < (Mf : ℝ) := by
    dsimp [Mf]
    positivity
  have hx_nhds : interior (dom f) ∈ nhds x :=
    IsOpen.mem_nhds isOpen_interior hx
  rcases Metric.mem_nhds_iff.mp hx_nhds with ⟨εdom, hεdom_pos, hεdom_mem⟩
  let ε : ℝ := εdom / (‖u‖ + 1)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  let r : ℝ := (1 / (Mf : ℝ)) / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hr_lt_inv : r < 1 / (Mf : ℝ) := by
    simpa [r] using half_lt_self (one_div_pos.mpr hMf_pos)
  have hlineInterior : ∀ {t : ℝ}, |t| < ε → x + t • u ∈ interior (dom f) := by
    intro t ht
    have hden_pos : 0 < ‖u‖ + 1 := by positivity
    have hmul_lt :
        |t| * (‖u‖ + 1) < εdom := by
      have hbase : |t| < εdom / (‖u‖ + 1) := by
        simpa [ε] using ht
      exact (lt_div_iff₀ hden_pos).mp hbase
    have hnorm_lt : ‖(x + t • u) - x‖ < εdom := by
      have hmul_le : |t| * ‖u‖ ≤ |t| * (‖u‖ + 1) := by
        gcongr
        linarith
      have : ‖(x + t • u) - x‖ ≤ |t| * (‖u‖ + 1) := by
        simpa [norm_smul] using hmul_le
      exact lt_of_le_of_lt this hmul_lt
    exact hεdom_mem (by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hnorm_lt)
  have hlineHessian :
      ∀ {t : ℝ}, |t| < ε →
        hessian (withTopRealPart f) (x + t • u) = hessian (withTopRealPart f) x := by
    intro t ht
    have htInterior : x + t • u ∈ interior (dom f) := hlineInterior ht
    have hquad_nonneg :
        0 ≤ inner ℝ ((x + t • u) - x)
          (hessian (withTopRealPart f) x ((x + t • u) - x)) :=
      hMf.hessian_posSemidef hx ((x + t • u) - x)
    have hquad_zero :
        inner ℝ ((x + t • u) - x)
          (hessian (withTopRealPart f) x ((x + t • u) - x)) = 0 := by
      simp [hu_hess]
    have htDikin : x + t • u ∈ openDikinEllipsoid (withTopRealPart f) x r := by
      rw [mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq
        (f := withTopRealPart f) (x := x) (y := x + t • u) hquad_nonneg hr_nonneg]
      simpa [sub_eq_add_neg, hu_hess] using sq_pos_of_pos hr_pos
    rcases hMf.hessian_loewner_bounds_of_exact_local_radius hx htInterior hr_lt_inv htDikin with
      ⟨hlower, hupper⟩
    have hnorm_zero :
        hessianLocalNorm (withTopRealPart f) x (t • u) = 0 := by
      rw [hessianLocalNorm_def]
      simp [hu_hess]
    apply le_antisymm
    · simpa [hnorm_zero] using hupper
    · simpa [hnorm_zero] using hlower
  have hlineGradient : ∀ {t : ℝ}, |t| < ε → ∇ (withTopRealPart f) (x + t • u) = s := by
    intro t ht
    apply ext_inner_right ℝ
    intro v
    let φ : ℝ → ℝ := fun τ ↦ inner ℝ (∇ (withTopRealPart f) (x + τ • u)) v
    have hdiffOn : DifferentiableOn ℝ φ (Set.Ioo (-ε) ε) := by
      intro τ hτ
      have hτ_abs : |τ| < ε := by
        exact abs_lt.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hdiffτ :
          DifferentiableAt ℝ (fun s : ℝ ↦ inner ℝ (∇ (withTopRealPart f) (x + s • u)) v) τ :=
        (scalarizedGradientLine_hasDerivAt (f := f) hf_contDiff
          (x := x) (d := u) (v := v) (t := τ) (hlineInterior hτ_abs)).differentiableAt
      exact hdiffτ.differentiableWithinAt
    have hderiv_zero : Set.EqOn (deriv φ) 0 (Set.Ioo (-ε) ε) := by
      intro τ hτ
      have hτ_abs : |τ| < ε := by
        exact abs_lt.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hu_hessτ : hessian (withTopRealPart f) (x + τ • u) u = 0 := by
        simpa [hlineHessian hτ_abs] using hu_hess
      simpa [φ, hu_hessτ] using
        (scalarizedGradientLine_hasDerivAt (f := f) hf_contDiff
          (x := x) (d := u) (v := v) (t := τ) (hlineInterior hτ_abs)).deriv
    have hzero_mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
      constructor <;> linarith
    have ht_mem : t ∈ Set.Ioo (-ε) ε := by
      exact abs_lt.mp ht
    have hconst :
        φ t = φ 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiffOn hderiv_zero ht_mem
        hzero_mem
    calc
      inner ℝ (∇ (withTopRealPart f) (x + t • u)) v = φ t := rfl
      _ = φ 0 := hconst
      _ = inner ℝ (∇ (withTopRealPart f) x) v := by simp [φ]
      _ = inner ℝ s v := by simp [hx_grad]
  refine ⟨ε, hε_pos, ?_⟩
  intro t ht
  exact ⟨hlineInterior ht, hlineGradient ht⟩

/-- Helper for Proposition 5.0.29: uniqueness of the interior Fenchel-support maximizer forces
the primal Hessian at that maximizer to be invertible. -/
private lemma primalHessianInvertibleAtSupportMaximizer {s x : E}
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (_hinterior_nonempty : (interior (dom f)).Nonempty)
    (_hs : s ∈ dom (f⋆))
    (hx : x ∈ interior (dom f))
    (hx_isMaximizer :
      IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x)
    (hx_unique :
      ∀ ⦃y : E⦄, y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = x) :
    (hessian (withTopRealPart f) x).IsInvertible := by
  have hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)) := by
    -- Self-concordance already provides the `C²` regularity needed for the Hessian argument.
    rcases hself with ⟨Mf, hMf⟩
    exact hMf.contDiffOn.of_le (by norm_num)
  have hx_grad : ∇ (withTopRealPart f) x = s :=
    gradient_eq_of_fenchelSupport_isMaxOn_interior (f := f) hf_contDiff hx hx_isMaximizer
  have hinj : Function.Injective ⇑(hessian (withTopRealPart f) x) := by
    intro u v huv
    have huv_zero : hessian (withTopRealPart f) x (u - v) = 0 := by
      simp [map_sub, huv]
    obtain ⟨ε, hε_pos, hline⟩ :=
      localGradient_eq_s_onKernelLine (f := f) hf_contDiff hself hx hx_grad huv_zero
    let t : ℝ := ε / 2
    have ht_abs : |t| < ε := by
      dsimp [t]
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hy : x + t • (u - v) ∈ interior (dom f) := (hline t ht_abs).1
    have hy_grad : ∇ (withTopRealPart f) (x + t • (u - v)) = s := (hline t ht_abs).2
    have hy_isMaximizer :
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (x + t • (u - v)) :=
      fenchelSupport_isMaxOn_of_gradient_eq_interior hf_closedConvex hf_contDiff hy hy_grad
    have hy_eq : x + t • (u - v) = x := hx_unique (interior_subset hy) hy_isMaximizer
    have htuv : t • (u - v) = 0 := by
      exact add_eq_left.mp hy_eq
    have ht_ne : t ≠ 0 := by
      dsimp [t]
      linarith
    have huv_eq : u - v = 0 := (smul_eq_zero.mp htuv).resolve_left ht_ne
    exact sub_eq_zero.mp huv_eq
  have hker :
      (hessian (withTopRealPart f) x).ker = ⊥ := by
    exact LinearMap.ker_eq_bot.mpr (by simpa using hinj)
  have hrange :
      (hessian (withTopRealPart f) x).range = ⊤ := by
    exact LinearMap.range_eq_top.2 <|
      LinearMap.surjective_of_injective (f := (hessian (withTopRealPart f) x).toLinearMap)
        (by simpa using hinj)
  let e : E ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofBijective (hessian (withTopRealPart f) x) hker hrange
  -- Route correction: the local-inverse proof of the dual gradient theorem needs this
  -- invertibility before the later public wrapper theorem is available.
  exact ContinuousLinearMap.isInvertible_equiv (f := e)

/-- Helper for Proposition 5.0.29: at a single dual-domain slope `s`, a unique interior
Fenchel-support maximizer `x` gives the whole-space gradient formula
`∇ (extendedRealRealPart (f⋆)) s = x`. -/
theorem fenchelConjugate_hasGradientAt_of_fenchelSupport_isMaxOn
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    {s x : E}
    (hs : s ∈ dom (f⋆))
    (hx : x ∈ interior (dom f))
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x)
    (hunique :
      ∀ ⦃y : E⦄, y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = x) :
    HasGradientAt (extendedRealRealPart (f⋆)) x s := by
  have hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)) := by
    -- Self-concordance supplies the `C²` regularity needed both for the primal gradient field
    -- and for the support-model transport.
    rcases hself with ⟨Mf, hMf⟩
    exact hMf.contDiffOn.of_le (by norm_num)
  have hx_grad : ∇ (withTopRealPart f) x = s :=
    gradient_eq_of_fenchelSupport_isMaxOn_interior (f := f) hf_contDiff hx hmax
  have hinv :
      (hessian (withTopRealPart f) x).IsInvertible :=
    primalHessianInvertibleAtSupportMaximizer (f := f) hf_closedConvex hself
      hinterior_nonempty hs hx hmax hunique
  rcases primalGradient_localInverse_atSupportMaximizer (f := f) hf_contDiff hx hx_grad hinv with
    ⟨ψ, hψ, hψ_deriv, hψ_tendsto, hψ_right_inverse⟩
  have hsupportModelEq :
      extendedRealRealPart (f⋆) =ᶠ[nhds s] fun t ↦ inner ℝ t (ψ t) - withTopRealPart f (ψ t) :=
    fenchelConjugate_eventuallyEq_supportModel_of_localInverse
      (f := f) hf_closedConvex hf_contDiff hx hψ_tendsto hψ_right_inverse
  have hprimal_grad : HasGradientAt (withTopRealPart f) s x := by
    have hcontDiffAt :
        ContDiffAt ℝ 1 (withTopRealPart f) x := by
      -- Restrict the `C²` regularity to the maximizing primal point.
      exact (hf_contDiff.of_le (by norm_num)).contDiffAt (IsOpen.mem_nhds isOpen_interior hx)
    have hdiff :
        DifferentiableAt ℝ (withTopRealPart f) x := by
      -- The support-model calculation only needs the base-point gradient witness.
      exact hcontDiffAt.differentiableAt (by norm_num)
    simpa [hx_grad] using hdiff.hasGradientAt
  have hsupportModelGrad :
      HasGradientAt (fun t ↦ inner ℝ t (ψ t) - withTopRealPart f (ψ t)) x s :=
    supportModel_hasGradientAt_of_localInverse (s := s) (x := x)
      hprimal_grad hψ hψ_deriv
  -- The dual and the support model agree on a neighborhood of `s`, so they share the same
  -- gradient at that point.
  exact hsupportModelGrad.congr_of_eventuallyEq hsupportModelEq

/-- Helper for Proposition 5.0.29: at a single dual-domain slope `s`, a unique interior
Fenchel-support maximizer `x` gives the within-domain gradient formula
`∇ f_*(s) = x`. -/
theorem fenchelConjugate_hasGradientWithinAt_of_fenchelSupport_isMaxOn
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    {s x : E}
    (hs : s ∈ dom (f⋆))
    (hx : x ∈ interior (dom f))
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x)
    (hunique :
      ∀ ⦃y : E⦄, y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = x) :
    HasGradientWithinAt (extendedRealRealPart (f⋆)) x (dom (f⋆)) s := by
  have hgradAt :
      HasGradientAt (extendedRealRealPart (f⋆)) x s :=
    fenchelConjugate_hasGradientAt_of_fenchelSupport_isMaxOn
      (f := f) hf_closedConvex hself hinterior_nonempty hs hx hmax hunique
  -- Once the whole-space gradient identity is available, the relative-domain version is the
  -- immediate restriction to `dom (f⋆)`.
  simpa [HasGradientAt] using hgradAt.hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt

/-- Gradient branch of Proposition 5.0.29: for a proper closed convex self-concordant primal
function with
nonempty interior domain, if at every dual-domain slope `s ∈ dom (f⋆)` the Fenchel support
functional attains its maximum uniquely at the chosen interior point `xStar s ∈ interior (dom f)`,
then the finite real part of `f⋆` has gradient `xStar s` at `s` relative to the dual effective
domain `dom (f⋆)`. This is the source-facing branchwise differentiability formula
`∇ f_*(s) = x(s)` on `dom (f⋆)`. -/
theorem fenchelConjugate_hasGradientWithinAt
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    {s : E} (hs : s ∈ dom (f⋆)) :
    HasGradientWithinAt (extendedRealRealPart (f⋆)) (xStar s) (dom (f⋆)) s := by
  -- Specialize the single-slope theorem at the chosen maximizer branch `xStar s`.
  exact
    fenchelConjugate_hasGradientWithinAt_of_fenchelSupport_isMaxOn
      hf_closedConvex hself hinterior_nonempty hs (hxStar_mem hs) (hxStar_isMaximizer hs)
      (fun {y} hy hymax ↦ hxStar_unique hs hy hymax)

/-- Companion corollary to Proposition 5.0.29 (1): under the standing global unique-attainment
hypotheses, the finite real part of the Fenchel conjugate has the whole-space gradient witness
`HasGradientAt (extendedRealRealPart (f⋆)) (xStar s) s` at each dual-domain point. The source
statement itself is the within-domain differentiability formula recorded in
`fenchelConjugate_hasGradientWithinAt`. -/
theorem fenchelConjugate_hasGradientAt
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    {s : E} (hs : s ∈ dom (f⋆)) :
    HasGradientAt (extendedRealRealPart (f⋆)) (xStar s) s := by
  have hxStar_mem_dom : xStar s ∈ dom f := interior_subset (hxStar_mem hs)
  -- Specialize the single-slope whole-space gradient theorem at the chosen maximizing branch.
  exact
    fenchelConjugate_hasGradientAt_of_fenchelSupport_isMaxOn
      (f := f) hf_closedConvex hself hinterior_nonempty hs (hxStar_mem hs)
      (hxStar_isMaximizer hs) (fun {y} hy hymax ↦ hxStar_unique hs hy hymax)

section HessianTransfer

variable (f) (xStar)

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.0.29: the branchwise uniqueness hypothesis identifies any support
maximizer at a dual-domain slope with the chosen maximizer branch `xStar`. -/
lemma maximizer_eq_xStar
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    {s x : E} (hs : s ∈ dom (f⋆)) (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    x = xStar s := by
  -- This is exactly the owner-level uniqueness hypothesis specialized to the current slope.
  exact hxStar_unique hs hx hmax

/-- Helper for Proposition 5.0.29: under the standing source hypotheses, the primal Hessian at a
unique interior Fenchel-support maximizer is invertible. -/
theorem fenchelConjugate_primalHessian_isInvertible_of_fenchelSupport_isMaxOn {s x : E}
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    (hs : s ∈ dom (f⋆))
    (hx : x ∈ interior (dom f))
    (hx_isMaximizer :
      IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x)
    (hx_unique :
      ∀ ⦃y : E⦄, y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = x) :
    (hessian (withTopRealPart f) x).IsInvertible := by
  -- The public theorem is now just the single-slope wrapper around the earlier private helper,
  -- so later declarations can still reuse the owner-facing name.
  exact primalHessianInvertibleAtSupportMaximizer (f := f) hf_closedConvex hself
    hinterior_nonempty hs hx hx_isMaximizer hx_unique

/-- Proposition 5.0.29: at a single dual-domain slope `s`, a unique interior
Fenchel-support maximizer `x` gives the inverse-Hessian identity
`∇² (extendedRealRealPart (f⋆)) s = [∇² (withTopRealPart f) x]⁻¹`. -/
theorem fenchelConjugate_hessian_eq_inverse_atSupportMaximizer
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s y : E⦄, s ∈ dom (f⋆) → y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = xStar s)
    {s : E} (hs : s ∈ dom (f⋆)) :
    hessian (extendedRealRealPart (f⋆)) s =
      (hessian (withTopRealPart f) (xStar s)).inverse := by
  have hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)) := by
    -- Self-concordance supplies the `C²` regularity needed for the inverse-function theorem.
    rcases hself with ⟨Mf, hMf⟩
    exact hMf.contDiffOn.of_le (by norm_num)
  let G : E → E := ∇ (withTopRealPart f)
  let x : E := xStar s
  let H : E →L[ℝ] E := hessian (withTopRealPart f) x
  have hx_grad : G x = s := by
    -- The chosen branch point satisfies the source first-order optimality equation.
    simpa [G, x] using
      gradient_eq_of_fenchelSupport_isMaxOn_interior (f := f) hf_contDiff (hxStar_mem hs)
        (hxStar_isMaximizer hs)
  have hinv : H.IsInvertible := by
    -- Proposition 5.0.29 already shows the primal Hessian is invertible at the branch point.
    simpa [H, x] using
      primalHessianInvertibleAtSupportMaximizer (f := f) hf_closedConvex hself
        hinterior_nonempty hs (hxStar_mem hs) (hxStar_isMaximizer hs)
        (fun {y} hy hymax ↦ hxStar_unique hs hy hymax)
  let e : E ≃L[ℝ] E := Classical.choose hinv
  have he : (e : E →L[ℝ] E) = H := Classical.choose_spec hinv
  have hgrad_C1 : ContDiffAt ℝ 1 G x := by
    -- The inverse-function theorem is applied to the primal gradient field.
    simpa [G, x] using primalGradient_contDiffAt_of_contDiffOn_two (f := f) hf_contDiff
      (hxStar_mem hs)
  have hgrad_fderiv : HasFDerivAt G H x := by
    -- Normalize the derivative of the primal gradient to the chapter owner `hessian`.
    simpa [G, H, x] using primalGradient_hasFDerivAt_of_contDiffOn_two (f := f) hf_contDiff
      (hxStar_mem hs)
  have hgrad_fderiv_e : HasFDerivAt G (e : E →L[ℝ] E) x := by
    -- The chosen continuous linear equivalence is exactly the invertible primal Hessian.
    simpa [he] using hgrad_fderiv
  have hstrict : HasStrictFDerivAt G (e : E →L[ℝ] E) x := by
    -- Upgrade the `C¹` derivative at the branch point to the strict derivative used by the
    -- inverse-function theorem.
    exact hgrad_C1.hasStrictFDerivAt' hgrad_fderiv_e one_ne_zero
  have he_inverse : (e.symm : E →L[ℝ] E) = H.inverse := by
    -- Rewrite the inverse derivative using the project's totalized inverse operator.
    calc
      (e.symm : E →L[ℝ] E) = (e : E →L[ℝ] E).inverse := by
        symm
        exact ContinuousLinearMap.inverse_equiv e
      _ = H.inverse := by
        simp [he]
  have hleft :
      ∀ᶠ y in nhds x, ∇ (extendedRealRealPart (f⋆)) (G y) = y := by
    have hmemInterior : ∀ᶠ y in nhds x, y ∈ interior (dom f) := by
      -- The inverse-function theorem only needs a neighborhood where the primal points stay
      -- in the interior domain.
      exact IsOpen.mem_nhds isOpen_interior (hxStar_mem hs)
    filter_upwards [hmemInterior] with y hy
    let t : E := G y
    have hy_isMaximizer :
        IsMaxOn (fun z : E ↦ inner ℝ t z - withTopRealPart f z) (dom f) y := by
      -- Any interior point is the support maximizer at its own primal gradient.
      simpa [G, t] using
        fenchelSupport_isMaxOn_of_gradient_eq_interior (f := f) hf_closedConvex hf_contDiff hy
          (show ∇ (withTopRealPart f) y = t by rfl)
    have ht : t ∈ dom (f⋆) :=
      mem_dom_fenchelDual_of_isMaxOn (f := f) (s := t) (x := y) (interior_subset hy)
        hy_isMaximizer
    have hdual_grad :
        HasGradientAt (extendedRealRealPart (f⋆)) (xStar t) t :=
      fenchelConjugate_hasGradientAt (f := f) (xStar := xStar) hf_closedConvex hself
        hinterior_nonempty hxStar_mem hxStar_isMaximizer hxStar_unique ht
    have hy_eq : y = xStar t := hxStar_unique ht (interior_subset hy) hy_isMaximizer
    -- Uniqueness of the Fenchel-support maximizer identifies the dual gradient with the primal
    -- point near `xStar s`.
    simpa [G, t] using hdual_grad.gradient.trans hy_eq.symm
  have hdual_strict :
      HasStrictFDerivAt (∇ (extendedRealRealPart (f⋆))) H.inverse s := by
    -- The dual gradient is the local left inverse of the primal gradient near the branch point.
    simpa [G, H, x, hx_grad, he_inverse] using
      (hstrict.to_local_left_inverse (g := ∇ (extendedRealRealPart (f⋆))) hleft)
  -- Read the Hessian as the derivative of the dual gradient.
  simpa [hessian, H] using hdual_strict.hasFDerivAt.fderiv

/-- Hessian branch of Proposition 5.0.29: for a proper closed convex self-concordant primal
function with
nonempty interior domain, if `s ∈ dom (f⋆)` and the support functional at every dual-domain slope
has the chosen unique interior maximizer `xStar`, then the Hessian of the finite real part of
`f⋆` at `s` is the inverse Hessian operator of `f` at `xStar s`. This is the source-facing
formula `∇² f_*(s) = [∇² f(x(s))]⁻¹` written on the chapter owners `extendedRealRealPart (f⋆)`
and `hessian`; the needed invertibility is part of the standing proposition hypotheses rather
than an extra proposition-level assumption. -/
theorem fenchelConjugate_hessian_eq_inverse
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    {s : E} (hs : s ∈ dom (f⋆)) :
    hessian (extendedRealRealPart (f⋆)) s =
      (hessian (withTopRealPart f) (xStar s)).inverse := by
  -- Reuse the single-slope inverse-Hessian theorem at the chosen maximizing branch `xStar s`.
  exact
    fenchelConjugate_hessian_eq_inverse_atSupportMaximizer
      (f := f) (xStar := xStar) hf_closedConvex hself hinterior_nonempty hxStar_mem
      hxStar_isMaximizer hxStar_unique hs

/-- Helper for Proposition 5.0.29: the branchwise inverse-Hessian formula can be reused under the
same global maximizing-branch hypotheses without re-expanding the local inverse argument. -/
theorem fenchelConjugate_hessian_eq_inverse_of_fenchelSupport_isMaxOn
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s y : E⦄, s ∈ dom (f⋆) → y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = xStar s)
    {s : E} (hs : s ∈ dom (f⋆)) :
    hessian (extendedRealRealPart (f⋆)) s =
      (hessian (withTopRealPart f) (xStar s)).inverse := by
  -- This synonym keeps the branchwise inverse-Hessian formula available under the same
  -- proposition-level branch data.
  exact
    fenchelConjugate_hessian_eq_inverse_atSupportMaximizer
      (f := f) (xStar := xStar) hf_closedConvex hself hinterior_nonempty hxStar_mem
      hxStar_isMaximizer hxStar_unique hs

/-- Equivalent formulation of Proposition 5.0.29: under the same unique-attainment hypothesis at
the slope `s`, if
`s ∈ dom (f⋆)` and `s = ∇ (withTopRealPart f) x` for an interior point `x`, then the dual
Hessian at `s` is the inverse primal Hessian at `x`. This is the source's equivalent formulation
`∇² f_*(s) = [∇² f(x)]⁻¹`, stated using the standing global maximizing branch rather than
additional single-slope maximizer hypotheses. -/
theorem fenchelConjugate_hessian_eq_inverse_of_eq_gradient {s x : E}
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s y : E⦄, s ∈ dom (f⋆) → y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = xStar s)
    (hs : s ∈ dom (f⋆))
    (hx : x ∈ interior (dom f))
    (hs_eq_gradient : s = ∇ (withTopRealPart f) x) :
    hessian (extendedRealRealPart (f⋆)) s =
      (hessian (withTopRealPart f) x).inverse := by
  have hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)) := by
    -- Restrict self-concordance to the `C²` regularity needed for the first-order maximizer
    -- bridge.
    rcases hself with ⟨Mf, hMf⟩
    exact hMf.contDiffOn.of_le (by norm_num)
  have hx_isMaximizer :
      IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x :=
    fenchelSupport_isMaxOn_of_gradient_eq_interior hf_closedConvex hf_contDiff hx
      hs_eq_gradient.symm
  have hx_mem : x ∈ dom f := interior_subset hx
  have hx_eq_xStar : x = xStar s := hxStar_unique hs hx_mem hx_isMaximizer
  -- Reuse the single-slope inverse-Hessian theorem after identifying `x` with the chosen branch.
  have hcore :
      hessian (extendedRealRealPart (f⋆)) s =
        (hessian (withTopRealPart f) x).inverse := by
    simpa [hx_eq_xStar] using
      (fenchelConjugate_hessian_eq_inverse
        (f := f) (xStar := xStar) hf_closedConvex hself hinterior_nonempty hxStar_mem
        hxStar_isMaximizer hxStar_unique hs)
  exact hcore

end HessianTransfer

end
