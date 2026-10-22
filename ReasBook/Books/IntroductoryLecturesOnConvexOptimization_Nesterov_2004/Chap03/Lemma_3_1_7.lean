/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient Topology
open Filter

noncomputable section

universe u

open scoped WithTopConvexAnalysis

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Lemma 3.1.7 lies in the chapter's extended-valued convex-analysis / subdifferential-calculus
domain on real inner-product spaces.

Sampled owner-style declarations:
- `withTopEffectiveDomain` in `Definition_3_3`, the chapter owner for the finite-value domain;
- `withTopRealPart` in `Definition_3_3`, the canonical real-valued representative on that domain;
- `ConvexOn ℝ (dom f) (withTopRealPart f)` in `Definition_3_3`, the owner convexity surface;
- `subdifferential` in `Definition_3_1_5`, the owner set-valued subgradient API.

Best owner abstraction:
- source-facing: the singleton-subdifferential theorem below;
- core/canonical: `withTopEffectiveDomain`, `withTopRealPart`,
  `ConvexOn ℝ (dom f) (withTopRealPart f)`, and
  `subdifferential`;
- bridge/view: none beyond the theorem statement itself.

Primitive data:
- the ambient `WithTop ℝ`-valued function `f`;
- the base point `x`;
- convexity on the canonical owner surface;
- interior-point membership in the effective domain;
- the primitive gradient witness `HasGradientAt (withTopRealPart f) g x`.

Derived API:
- `subdifferential_eq_singleton_of_hasGradientAt`;
- `subdifferential_eq_singleton_gradient`.

The previous version duplicated the effective-domain, finite-real-part, convexity, and
subdifferential definitions locally. Those notions already have chapter owners upstream, so this
file states the source-facing theorem directly on that owner API instead of maintaining a
parallel wrapper layer. The textbook writes the result on `ℝⁿ`, but the owner declarations used
here only need a complete real inner-product space, and the scalar cannot be weakened away from
`ℝ` because both `gradient` and the chapter subgradient API are formulated through the real inner
product pairing.
-/

/-- Helper for Lemma 3.1.7: convexity along the line segment from `x` to `y` turns the gradient at
`x` into the expected affine support inequality at every point of the effective domain. -/
lemma gradient_support_inequality_of_hasGradientAt
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) {x : E}
    (hx : x ∈ interior (dom f)) {g : E}
    (hgrad : HasGradientAt (withTopRealPart f) g x) :
    ∀ ⦃y : E⦄, y ∈ dom f →
      withTopRealPart f y ≥ withTopRealPart f x + inner ℝ g (y - x) := by
  intro y hy
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let S : Set ℝ := line ⁻¹' dom f
  let φ : ℝ → ℝ := fun α ↦ withTopRealPart f (x + α • (y - x))
  have hline_apply (α : ℝ) : line α = x + α • (y - x) := by
    simpa [line, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x y α)
  have hconv : ConvexOn ℝ S φ := by
    -- Restrict the ambient convex function to the affine line through `x` and `y`.
    have hconvLine : ConvexOn ℝ S (withTopRealPart f ∘ line) := by
      simpa [S, Function.comp] using hf.comp_affineMap line
    convert hconvLine using 1
    ext α
    simp [φ, Function.comp, hline_apply]
  have hzero_mem : (0 : ℝ) ∈ S := by
    simpa [S, hline_apply] using interior_subset hx
  have hone_mem : (1 : ℝ) ∈ S := by
    simpa [S, hline_apply] using hy
  have hline :
      HasLineDerivAt ℝ (withTopRealPart f) (inner ℝ g (y - x)) x (y - x) := by
    -- The gradient witness identifies the derivative of the scalar slice at the left endpoint.
    simpa [hgrad.fderiv_apply] using hgrad.hasFDerivAt.hasLineDerivAt (y - x)
  have hderiv :
      HasDerivWithinAt φ (inner ℝ g (y - x)) (Set.Ioi (0 : ℝ)) 0 := by
    have hderivLineAt :
        HasDerivAt
          (fun α : ℝ ↦ withTopRealPart f (x + α • (y - x)))
          (inner ℝ g (y - x)) 0 := by
      simpa using hline
    have hderivLine :
        HasDerivWithinAt
          (fun α : ℝ ↦ withTopRealPart f (x + α • (y - x)))
          (inner ℝ g (y - x)) (Set.Ioi (0 : ℝ)) 0 :=
      hderivLineAt.hasDerivWithinAt
    simpa [φ] using hderivLine
  have hslope :
      inner ℝ g (y - x) ≤ withTopRealPart f y - withTopRealPart f x := by
    -- A convex scalar slice stays above every secant line issued from the right derivative.
    simpa [φ, slope_def_field] using
      hconv.le_slope_of_hasDerivWithinAt_Ioi hzero_mem hone_mem zero_lt_one hderiv
  linarith

/-- Helper for Lemma 3.1.7: the displayed gradient belongs to the subdifferential at the interior
point because its affine support inequality holds on the effective domain. -/
lemma gradient_mem_subdifferential_of_hasGradientAt
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) {x : E}
    (hx : x ∈ interior (dom f)) {g : E}
    (hgrad : HasGradientAt (withTopRealPart f) g x) :
    g ∈ ∂ f(x) := by
  -- Convert the real supporting inequality into the owner-level `WithTop` subgradient condition.
  refine mem_subdifferential_iff.mpr ?_
  constructor
  · exact interior_subset hx
  · intro y hy
    have hsupport :=
      gradient_support_inequality_of_hasGradientAt hf hx hgrad hy
    rw [← coe_withTopRealPart hy, ← coe_withTopRealPart (interior_subset hx)]
    exact_mod_cast hsupport

/-- Helper for Lemma 3.1.7: any subgradient at the interior point has pairing at most the pairing
of the true gradient against every direction. -/
lemma inner_le_inner_gradient_of_mem_subdifferential_of_hasGradientAt
    {f : E → WithTop ℝ} {x g h : E}
    (hx : x ∈ interior (dom f))
    (hgrad : HasGradientAt (withTopRealPart f) g x)
    (hh : h ∈ ∂ f(x)) :
    ∀ p : E, inner ℝ h p ≤ inner ℝ g p := by
  intro p
  have hx_dom : x ∈ dom f := interior_subset hx
  have hhsub := mem_subdifferential_iff.mp hh
  have hline_grad : HasLineDerivAt ℝ (withTopRealPart f) (inner ℝ g p) x p := by
    -- Read the Fréchet gradient as the derivative of the one-dimensional slice in direction `p`.
    simpa [hgrad.fderiv_apply] using hgrad.hasFDerivAt.hasLineDerivAt p
  have hpath : Tendsto (fun α : ℝ ↦ x + α • p) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hcont : ContinuousAt (fun α : ℝ ↦ x + α • p) (0 : ℝ) := by
      fun_prop
    simpa [nhdsWithin, zero_smul] using hcont.tendsto.mono_left inf_le_left
  have hdom : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f := by
    -- Interior points keep the whole ray inside the effective domain for small positive times.
    exact (hpath.eventually (IsOpen.mem_nhds isOpen_interior hx)).mono fun α hα ↦
      interior_subset hα
  have hlim :
      Tendsto (fun α : ℝ ↦ (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ g p)) := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hline_grad.tendsto_slope_zero_right
  have hineq :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        inner ℝ h p ≤ (withTopRealPart f (x + α • p) - withTopRealPart f x) / α := by
    filter_upwards [hdom, self_mem_nhdsWithin] with α hαdom hαpos
    have hsubineq :
        f (x + α • p) ≥ f x + (inner ℝ h (x + α • p - x) : WithTop ℝ) :=
      hhsub.2 hαdom
    have hreal :
        withTopRealPart f (x + α • p) ≥ withTopRealPart f x + α * inner ℝ h p := by
      rw [← coe_withTopRealPart hαdom, ← coe_withTopRealPart hx_dom] at hsubineq
      have hinner : inner ℝ h (x + α • p - x) = α * inner ℝ h p := by
        simp [inner_smul_right]
      rw [hinner] at hsubineq
      exact_mod_cast hsubineq
    have hdiff : α * inner ℝ h p ≤ withTopRealPart f (x + α • p) - withTopRealPart f x := by
      linarith
    rw [div_eq_mul_inv]
    exact (le_div_iff₀ hαpos).2 (by simpa [mul_comm] using hdiff)
  exact tendsto_le_of_eventuallyLE tendsto_const_nhds hlim hineq

/-- Helper for Lemma 3.1.7: every subgradient at the interior point agrees with the true
gradient, obtained by comparing the support inequality in directions `p` and `-p`. -/
lemma eq_gradient_of_mem_subdifferential_of_hasGradientAt
    {f : E → WithTop ℝ} {x g h : E}
    (hx : x ∈ interior (dom f))
    (hgrad : HasGradientAt (withTopRealPart f) g x)
    (hh : h ∈ ∂ f(x)) :
    h = g := by
  -- Equality of all inner products forces equality in the ambient real inner-product space.
  apply ext_inner_right ℝ
  intro p
  have hpos :
      inner ℝ h p ≤ inner ℝ g p :=
    inner_le_inner_gradient_of_mem_subdifferential_of_hasGradientAt hx hgrad hh p
  have hneg : inner ℝ h p ≥ inner ℝ g p := by
    -- Apply the same one-sided comparison to `-p` and use linearity of the inner product.
    have hneg' :
        inner ℝ h (-p) ≤ inner ℝ g (-p) :=
      inner_le_inner_gradient_of_mem_subdifferential_of_hasGradientAt hx hgrad hh (-p)
    simpa using hneg'
  linarith

/-- Core owner form of Lemma 3.1.7: if a convex extended-real-valued function on a complete real
inner-product space has gradient `g` at an interior point of its effective domain, then its
subdifferential there is the singleton `{g}`. -/
-- Proof sketch: convexity and the explicit gradient witness at `x` give the supporting-plane
-- inequality with slope `g`, so `g` lies in the subdifferential. For the reverse inclusion,
-- compare the subgradient inequality for an arbitrary `h ∈ ∂f(x)` along directions `p` and `-p`;
-- differentiability identifies the corresponding directional increments with the same linear
-- functional `p ↦ ⟪g, p⟫`, forcing `h = g`.
theorem subdifferential_eq_singleton_of_hasGradientAt
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) {x : E}
    (hx : x ∈ interior (dom f)) {g : E}
    (hgrad : HasGradientAt (withTopRealPart f) g x) :
    ∂ f(x) = {g} := by
  -- First show that the displayed gradient is a subgradient, then prove every subgradient
  -- coincides with it.
  ext h
  constructor
  · intro hh
    have hEq : h = g :=
      eq_gradient_of_mem_subdifferential_of_hasGradientAt hx hgrad hh
    simp [hEq]
  · intro hh
    rcases Set.mem_singleton_iff.mp hh with rfl
    exact gradient_mem_subdifferential_of_hasGradientAt hf hx hgrad

/-- Lemma 3.1.7, derived owner form: if a convex extended-real-valued function on a complete real
inner-product space is differentiable at an interior point of its effective domain, then its
subdifferential there is the singleton containing the gradient of its finite real part. -/
-- Proof sketch: convexity and differentiability at `x` give the supporting-plane inequality with
-- slope `∇ (withTopRealPart f) x`, so the gradient lies in the subdifferential. For the reverse
-- inclusion, compare the subgradient inequality for an arbitrary `g ∈ ∂f(x)` along directions
-- `p` and `-p`; differentiability identifies the directional derivatives with pairings against
-- `∇ (withTopRealPart f) x`, forcing `g = ∇ (withTopRealPart f) x`.
theorem subdifferential_eq_singleton_gradient
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) {x : E}
    (hx : x ∈ interior (dom f))
    (hfd : DifferentiableAt ℝ (withTopRealPart f) x) :
    ∂ f(x) = {∇ (withTopRealPart f) x} := by
  exact subdifferential_eq_singleton_of_hasGradientAt hf hx hfd.hasGradientAt

end
