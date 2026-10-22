/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

/-
Theorem 3.21 is the chapter owner file for convex directional derivatives of `ℝ ∪ {+∞}`-valued
functions.

Primary domain:
- convex analysis of extended-real-valued functions on real modules, with interior-point theorem
  surfaces on real topological modules, and subdifferential/max-formula surfaces on
  finite-dimensional real inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite real representative of an `ℝ ∪ {+∞}`-valued function;
- `subdifferential` in `Definition_3_1_5`, the chapter owner for extended-valued subgradients;
- `subdifferentialWithin` with the notation `∂[Q] f(x)` in `Theorem_3_44`, the project's
  real-valued whole-space/relative subdifferential view built on the same Chapter 3 owner;
- `isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous` in `Proposition_3_19`,
  the chapter's owner-style max formula at the source-faithful finite-dimensional ambient level;
- `HasDirectionalDerivAt` and `DirectionallyDifferentiableAt` in `Definition_3_1_3_1`, the
  chapter owners for finite one-sided directional derivatives;
- `exists_hasDirectionalDerivAt_of_mem_interior_dom` in `Theorem_3_1_3_2`, the chapter existence
  bridge from convexity at an interior point to the directional-derivative owner.

Best owner abstraction:
- the extended-valued directional derivative
  `convexDirectionalDerivative f x hx : E → EReal` at a finite base point `hx : x ∈ dom f`,
  defined as the infimum of the positive secant slopes;
- the source-facing finite interior-point surface `f′[hx] : E → ℝ`, which is the canonical
  real-valued theorem-level view of that owner and is the public theorem surface in this file.

Primitive data:
- `directionalSlopeSet`, the source-facing secant-slope set at a finite base point;
- `convexDirectionalDerivative`, the resulting `EReal` owner at that finite base point.

Derived API:
- the theorem-level finite owner surface `f′[hx]`, defined by the finite `toReal` view of
  `convexDirectionalDerivative f x (interior_subset hx)`;
- the bridge theorem identifying that finite view with
  `HasDirectionalDerivAt (withTopToEReal ∘ f) x p`;
- the convexity theorem on all directions for that finite view;
- the real-valued whole-space subdifferential comparison at the origin, on the
  finite-dimensional owner layer where vector-valued subgradients capture all supporting
  functionals;
- the max-formula theorem against the subdifferential on that same source-faithful owner layer.

Source/core/bridge triage:
- source-facing: the finite directional-derivative surface `f′[hx]` and its three theorem clauses
  under the interior hypotheses of Theorem 3.21, with clauses (2) and (3) kept on the
  finite-dimensional vector-subgradient layer used by the chapter owner `subdifferential`;
- core/canonical: `convexDirectionalDerivative`, `HasDirectionalDerivAt`, `subdifferential`, and
  `subdifferentialWithin`;
- bridge/view: the abbreviational real-valued view `f′[hx]` of the extended-valued secant-slope
  owner.

This refinement keeps the secant-slope construction as primitive support data and keeps the
extended-valued infimum as the public core owner. The finite real-valued directional derivative
appears on theorem surfaces through the source-facing notation `f′[hx]` under the interior-point
hypotheses that prove finiteness, while `HasDirectionalDerivAt` remains the finiteness witness and
the real-valued whole-space subdifferential surface `∂[Set.univ]` supplies the canonical
subdifferential view in clause (2). Because that subdifferential owner is vector-valued and written
through pairings `⟪g, ·⟫`, the subdifferential and max-formula clauses stay in the
finite-dimensional real inner-product setting already used by `Proposition_3_19`, rather than
overgeneralizing beyond the chapter's Riesz-representable ambient layer.
-/

noncomputable section

open Filter

open scoped WithTopConvexAnalysis

open scoped Topology

universe u

section CoreDefs

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Helper for Theorem 3.21: on the effective domain, coercing the finite real part back to
`EReal` recovers the canonical `EReal` image of the original `WithTop ℝ` value. -/
theorem coe_withTopRealPart_toEReal_eq
    {f : E → WithTop ℝ} {x : E} (hx : x ∈ dom f) :
    ((withTopRealPart f x : ℝ) : EReal) = withTopToEReal (f x) := by
  rw [← coe_withTopRealPart hx]
  rfl

/-- Helper for Theorem 3.21: on the effective domain, the default finite-value projection
`untop₀` agrees with the proof-dependent projection `untop`. -/
theorem untop₀_eq_untop_of_mem_dom
    {f : E → WithTop ℝ} {x : E} (hx : x ∈ dom f) :
    (f x).untop₀ = (f x).untop (ne_of_lt hx) := by
  apply WithTop.coe_injective
  rw [WithTop.coe_untop₀_of_ne_top (ne_of_lt hx), WithTop.coe_untop]

/-- The positive secant slopes of `f` at a finite base point `x` in direction `p`. -/
def directionalSlopeSet (f : E → WithTop ℝ) (x : E) (hx : x ∈ dom f) (p : E) : Set EReal :=
  {r | ∃ α : ℝ, 0 < α ∧
      ∃ hxα : x + α • p ∈ dom f,
        r =
          ((((((f (x + α • p)).untop (ne_of_lt hxα)) -
              (f x).untop (ne_of_lt hx)) / α : ℝ)) : EReal)}

/-- The directional derivative of a convex `ℝ ∪ {+∞}`-valued function at a finite base point `x`,
defined as the infimum of the positive secant slopes in direction `p`. -/
def convexDirectionalDerivative
    (f : E → WithTop ℝ) (x : E) (hx : x ∈ dom f) : E → EReal :=
  fun p ↦ sInf (directionalSlopeSet f x hx p)

/-- Helper for Theorem 3.21: the owner secant-slope set is exactly the `EReal` coercion of the
usual real slope set of the one-dimensional slice through `x`. -/
theorem directionalSlopeSet_eq_slope_image
    {f : E → WithTop ℝ} {x : E} (hx : x ∈ dom f) (p : E) :
    directionalSlopeSet f x hx p =
      ((fun r : ℝ ↦ (r : EReal)) ''
        (slope (fun α : ℝ ↦ withTopRealPart f (x + α • p)) 0 ''
          {α : ℝ | 0 < α ∧ x + α • p ∈ dom f})) := by
  ext r
  constructor
  · rintro ⟨α, hα, hxα, rfl⟩
    refine ⟨slope (fun β : ℝ ↦ withTopRealPart f (x + β • p)) 0 α, ?_, ?_⟩
    · refine ⟨α, ⟨hα, hxα⟩, rfl⟩
    · simpa [slope_def_field, withTopRealPart, zero_smul,
        untop₀_eq_untop_of_mem_dom hxα, untop₀_eq_untop_of_mem_dom hx]
  · rintro ⟨r', ⟨α, hαx, hr'⟩, rfl⟩
    rcases hαx with ⟨hα, hxα⟩
    refine ⟨α, hα, hxα, ?_⟩
    rw [← hr']
    simpa [slope_def_field, withTopRealPart, zero_smul,
      untop₀_eq_untop_of_mem_dom hxα, untop₀_eq_untop_of_mem_dom hx]

/-- Helper for Theorem 3.21: coercing the real infimum of a nonempty bounded-below set into
`EReal` agrees with taking the `EReal` infimum of the coerced image. -/
theorem ereal_sInf_coe_real_image_eq
    {A : Set ℝ} (hA_nonempty : A.Nonempty) (hA_bddBelow : BddBelow A) :
    sInf (((↑) : ℝ → EReal) '' A) = ((sInf A : ℝ) : EReal) := by
  -- Transport the real greatest-lower-bound characterization across the coercion `ℝ → EReal`.
  have hglb : IsGLB A (sInf A) := Real.isGLB_sInf hA_nonempty hA_bddBelow
  have hglb' : IsGLB (((↑) : ℝ → EReal) '' A) (((sInf A : ℝ) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact_mod_cast hglb.1 hy
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          rintro rfl
          rcases hA_nonempty with ⟨y, hy⟩
          have : (⊤ : EReal) ≤ (y : EReal) := hz ⟨y, hy, rfl⟩
          simp at this
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : r ≤ sInf A := by
          refine le_csInf hA_nonempty ?_
          intro y hy
          exact_mod_cast hz ⟨y, hy, rfl⟩
        exact_mod_cast hr
  -- `csInf_eq` now identifies the `EReal` infimum with the transported real one.
  exact hglb'.csInf_eq (hA_nonempty.image (fun r : ℝ ↦ (r : EReal)))

/-- Positive scaling of the extended-valued directional derivative at a finite base point. -/
-- Proof sketch: rewrite the positive secant slopes in direction `τ • p` by the change of
-- variables `β = τ α` and identify the resulting scaled infimum with
-- `τ * convexDirectionalDerivative f x hx p`.
theorem convexDirectionalDerivative_smul
    {f : E → WithTop ℝ} {x : E} (hx : x ∈ dom f)
    {τ : ℝ} (hτ : 0 < τ) (p : E) :
    convexDirectionalDerivative f x hx (τ • p) =
      (τ : EReal) * convexDirectionalDerivative f x hx p := by
  let A : Set ℝ :=
    slope (fun α : ℝ ↦ withTopRealPart f (x + α • p)) 0 ''
      {α : ℝ | 0 < α ∧ x + α • p ∈ dom f}
  have hscale_real :
      slope (fun α : ℝ ↦ withTopRealPart f (x + α • (τ • p))) 0 '' {α : ℝ |
          0 < α ∧ x + α • (τ • p) ∈ dom f} =
        (fun r : ℝ ↦ τ * r) '' A := by
    ext r
    constructor
    · rintro ⟨α, ⟨hα, hxα⟩, rfl⟩
      have hxβ : x + (α * τ) • p ∈ dom f := by
        simpa [smul_smul, mul_comm] using hxα
      refine ⟨slope (fun β : ℝ ↦ withTopRealPart f (x + β • p)) 0 (α * τ), ?_, ?_⟩
      · exact ⟨α * τ, ⟨mul_pos hα hτ, hxβ⟩, rfl⟩
      · have hquot :
          (withTopRealPart f (x + α • (τ • p)) - withTopRealPart f x) / α =
            τ *
              ((withTopRealPart f (x + (α * τ) • p) - withTopRealPart f x) / (α * τ)) := by
          rw [show x + α • (τ • p) = x + (α * τ) • p by
            simp [smul_smul, mul_comm]]
          field_simp [hα.ne', hτ.ne']
        simpa [A, slope_def_field, zero_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          hquot.symm
    · rintro ⟨r', ⟨β, ⟨hβ, hxβ⟩, rfl⟩, rfl⟩
      let α : ℝ := β / τ
      have hα : 0 < α := div_pos hβ hτ
      have hxα : x + α • (τ • p) ∈ dom f := by
        simpa [α, div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc, hτ.ne'] using
          hxβ
      refine ⟨α, ⟨hα, hxα⟩, ?_⟩
      have hquot :
          τ * ((withTopRealPart f (x + β • p) - withTopRealPart f x) / β) =
            (withTopRealPart f (x + α • (τ • p)) - withTopRealPart f x) / α := by
        change τ * ((withTopRealPart f (x + β • p) - withTopRealPart f x) / β) =
          (withTopRealPart f (x + (β / τ) • (τ • p)) - withTopRealPart f x) / (β / τ)
        rw [show x + (β / τ) • (τ • p) = x + β • p by
          simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc, hτ.ne']]
        field_simp [hβ.ne', hτ.ne']
      calc
        slope (fun α : ℝ ↦ withTopRealPart f (x + α • (τ • p))) 0 α =
            (withTopRealPart f (x + α • (τ • p)) - withTopRealPart f x) / α := by
              simp [slope_def_field, zero_smul]
        _ = τ * ((withTopRealPart f (x + β • p) - withTopRealPart f x) / β) := hquot.symm
        _ = τ * slope (fun β : ℝ ↦ withTopRealPart f (x + β • p)) 0 β := by
              simp [slope_def_field, zero_smul, hβ.ne']
  have hscale_ereal :
      ((fun r : ℝ ↦ (r : EReal)) '' ((fun r : ℝ ↦ τ * r) '' A)) =
        ((fun r : EReal ↦ (τ : EReal) * r) '' (((↑) : ℝ → EReal) '' A)) := by
    ext r
    simp [A, mul_comm, mul_left_comm, mul_assoc]
  -- The secant-slope sets differ by the positive order isomorphism `r ↦ τ * r`.
  rw [convexDirectionalDerivative, directionalSlopeSet_eq_slope_image (hx := hx) (p := τ • p),
    hscale_real, hscale_ereal]
  have hsInf_mul :
      sInf (((fun r : EReal ↦ (τ : EReal) * r) '' (((↑) : ℝ → EReal) '' A))) =
        (τ : EReal) * sInf (((↑) : ℝ → EReal) '' A) := by
    have hτE : 0 < (τ : EReal) := by
      exact_mod_cast hτ
    have hτE_top : (τ : EReal) ≠ ⊤ := by simp
    have hdiv_iff (a c : EReal) :
        a / (τ : EReal) ≤ c ↔ a ≤ (τ : EReal) * c := by
      simpa using
        (EReal.div_le_iff_le_mul (a := a) (b := (τ : EReal)) (c := c) hτE hτE_top)
    apply le_antisymm
    · have hdiv :
        sInf (((fun r : EReal ↦ (τ : EReal) * r) '' (((↑) : ℝ → EReal) '' A))) / (τ : EReal) ≤
          sInf (((↑) : ℝ → EReal) '' A) := by
        refine le_sInf ?_
        intro a ha
        exact (hdiv_iff _ _).2 (sInf_le ⟨a, ha, rfl⟩)
      exact (hdiv_iff _ _).1 hdiv
    · refine le_sInf ?_
      rintro _ ⟨a, ha, rfl⟩
      exact mul_le_mul_of_nonneg_left (sInf_le ha) hτE.le
  rw [hsInf_mul, convexDirectionalDerivative, directionalSlopeSet_eq_slope_image (hx := hx) (p := p)]

end CoreDefs

section Core

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Helper for Theorem 3.21: a finite `WithTop ℝ` value remains finite after applying the
canonical bridge into `EReal`. -/
theorem mem_dom_withTopToEReal_comp_of_mem_dom
    {f : E → WithTop ℝ} {y : E} (hy : y ∈ dom f) :
    y ∈ extendedRealEffectiveDomain (withTopToEReal ∘ f) := by
  rw [mem_extendedRealEffectiveDomain_iff]
  constructor
  · intro htop
    exact (ne_of_lt hy) (WithBot.coe_eq_top.mp htop)
  · exact WithBot.coe_ne_bot

/-- Helper for Theorem 3.21: reading the canonical `EReal` bridge through `toReal` reproduces the
finite real part of the original `WithTop ℝ` function. -/
theorem withTopToEReal_toReal_eq_withTopRealPart
    {f : E → WithTop ℝ} {z : E} :
    (withTopToEReal (f z)).toReal = withTopRealPart f z := by
  cases hfz : f z with
  | top =>
      rw [withTopRealPart, Function.comp_apply, hfz]
      exact EReal.toReal_top
  | coe a =>
      rw [withTopRealPart, Function.comp_apply, hfz]
      exact EReal.toReal_coe a

/-- The finite directional derivative of a convex `ℝ ∪ {+∞}`-valued function at an interior point
of its effective domain, viewed as a real-valued function of the direction variable. -/
abbrev convexDirectionalDerivativeReal
    (f : E → WithTop ℝ) {x : E} (hx : x ∈ interior (dom f)) : E → ℝ :=
  fun p ↦ (convexDirectionalDerivative f x (interior_subset hx) p).toReal

/- Lean surface notation for the textbook directional derivative `p ↦ f'(x; p)` at an interior
point `x`, reusing the proof `hx : x ∈ interior (dom f)` to recover the base point. -/
scoped[WithTopConvexAnalysis] notation:max f:arg "′[" hx:arg "]" =>
  convexDirectionalDerivativeReal f hx

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
@[simp] theorem convexDirectionalDerivativeReal_apply
    {f : E → WithTop ℝ} {x : E} (hx : x ∈ interior (dom f)) (p : E) :
    f′[hx] p = (convexDirectionalDerivative f x (interior_subset hx) p).toReal :=
  rfl

/-- Under the interior-point hypotheses, the extended-valued secant-slope owner is finite and
agrees with the chapter's one-sided directional-derivative owner. -/
theorem convexDirectionalDerivative_toReal_hasDirectionalDerivAt
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) (p : E) :
    HasDirectionalDerivAt (withTopToEReal ∘ f) x0 p (f′[hx0] p) := by
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x0 (x0 + p)
  let S : Set ℝ := g ⁻¹' dom f
  let φ : ℝ → ℝ := withTopRealPart f ∘ g
  have hg_apply (α : ℝ) : g α = x0 + α • p := by
    simpa [g, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x0 (x0 + p) α)
  have hphi : φ = fun α : ℝ ↦ withTopRealPart f (x0 + α • p) := by
    funext α
    simp [φ, hg_apply]
  have hconv : ConvexOn ℝ S φ := by
    -- Restrict the convex real slice to the affine line through `x0` in direction `p`.
    simpa [S, φ, g] using hf.comp_affineMap g
  have hcont : Continuous g := by
    simpa [g] using
      (AffineMap.lineMap_continuous : Continuous (AffineMap.lineMap x0 (x0 + p) : ℝ →ᵃ[ℝ] E))
  have h0dom : ∀ᶠ α : ℝ in 𝓝 (0 : ℝ), g α ∈ dom f :=
    hcont.continuousAt.eventually_mem
      (by simpa [g] using (mem_interior_iff_mem_nhds.mp hx0))
  have hS_nhds : S ∈ 𝓝 (0 : ℝ) := by
    simpa [S] using h0dom
  have hS0 : (0 : ℝ) ∈ interior S := mem_interior_iff_mem_nhds.mpr hS_nhds
  have hderiv_Ioi :
      HasDerivWithinAt φ (sInf (slope φ 0 '' {α : ℝ | α ∈ S ∧ 0 < α})) (Set.Ioi (0 : ℝ)) 0 := by
    simpa [S, φ, Set.setOf_and, and_left_comm, and_assoc] using
      hconv.hasDerivWithinAt_sInf_slope_of_mem_interior hS0
  have hslope_nonempty : (slope φ 0 '' {α : ℝ | α ∈ S ∧ 0 < α}).Nonempty := by
    have hS0' := hS0
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hS0'
    obtain ⟨a, b, hab, habS⟩ := hS0'
    obtain ⟨α, hα0, hαb⟩ := exists_between hab.2
    refine ⟨slope φ 0 α, ?_⟩
    exact ⟨α, ⟨habS ⟨hab.1.trans hα0, hαb⟩, hα0⟩, rfl⟩
  have hslope_bddBelow : BddBelow (slope φ 0 '' {α : ℝ | α ∈ S ∧ 0 < α}) := by
    simpa [Set.setOf_and, and_left_comm, and_assoc] using
      (bddBelow_slope_lt_of_mem_interior hconv hS0 :
        BddBelow (slope φ 0 '' {y : ℝ | y ∈ S ∧ 0 < y}))
  have howner_value :
      convexDirectionalDerivative f x0 (interior_subset hx0) p =
        ((sInf (slope φ 0 '' {α : ℝ | α ∈ S ∧ 0 < α}) : ℝ) : EReal) := by
    -- Route correction: the old proof stalled on the coercion transport from a real `sInf`
    -- to the `EReal` owner. The new route uses `ereal_sInf_coe_real_image_eq` explicitly.
    rw [convexDirectionalDerivative, directionalSlopeSet_eq_slope_image (hx := interior_subset hx0)
      (p := p)]
    have hset :
        {α : ℝ | 0 < α ∧ x0 + α • p ∈ dom f} = {α : ℝ | α ∈ S ∧ 0 < α} := by
      ext α
      constructor
      · rintro ⟨hα, hdom⟩
        exact ⟨by simpa [S, hg_apply] using hdom, hα⟩
      · rintro ⟨hdom, hα⟩
        exact ⟨hα, by simpa [S, hg_apply] using hdom⟩
    have hslope_eq :
        slope φ 0 '' {α : ℝ | α ∈ S ∧ 0 < α} =
          slope (fun α : ℝ ↦ withTopRealPart f (x0 + α • p)) 0 '' {α : ℝ | α ∈ S ∧ 0 < α} := by
      simpa [hphi]
    have hslope_nonempty' :
        (slope (fun α : ℝ ↦ withTopRealPart f (x0 + α • p)) 0 '' {α : ℝ | α ∈ S ∧ 0 < α}).Nonempty := by
      simpa [hslope_eq] using hslope_nonempty
    have hslope_bddBelow' :
        BddBelow (slope (fun α : ℝ ↦ withTopRealPart f (x0 + α • p)) 0 '' {α : ℝ | α ∈ S ∧ 0 < α}) := by
      simpa [hslope_eq] using hslope_bddBelow
    rw [hset]
    rw [hslope_eq]
    simpa [withTopRealPart] using
      (ereal_sInf_coe_real_image_eq hslope_nonempty' hslope_bddBelow' :
        sInf (((↑) : ℝ → EReal) ''
          (slope (fun α : ℝ ↦ withTopRealPart f (x0 + α • p)) 0 '' {α : ℝ | α ∈ S ∧ 0 < α})) =
            ((sInf
              (slope (fun α : ℝ ↦ withTopRealPart f (x0 + α • p)) 0 '' {α : ℝ | α ∈ S ∧ 0 < α}) :
                ℝ) : EReal))
  have hvalue :
      sInf (slope φ 0 '' {α : ℝ | α ∈ S ∧ 0 < α}) = f′[hx0] p := by
    rw [convexDirectionalDerivativeReal_apply, howner_value]
    simp
  refine ⟨?_, ?_, ?_⟩
  · exact mem_dom_withTopToEReal_comp_of_mem_dom (interior_subset hx0)
  · filter_upwards [h0dom.filter_mono nhdsWithin_le_nhds] with α hα
    simpa [hg_apply α] using mem_dom_withTopToEReal_comp_of_mem_dom hα
  · have hslice :
        (fun α : ℝ ↦ extendedRealRealPart (withTopToEReal ∘ f) (x0 + α • p)) = φ := by
      funext α
      rw [show x0 + α • p = g α by symm; exact hg_apply α]
      simp [φ, Function.comp, withTopToEReal_toReal_eq_withTopRealPart]
    -- Read the scalar derivative through the `withTopToEReal` bridge and upgrade from `Ioi` to `Ici`.
    rw [hslice]
    simpa [hvalue] using hderiv_Ioi.Ici_of_Ioi

/-- Helper for Theorem 3.21: the real secant quotients along a fixed direction converge to the
finite directional derivative at an interior point. -/
theorem tendsto_directionalSecantQuotient_of_mem_interior
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) (p : E) :
    Tendsto
      (fun α : ℝ ↦ (withTopRealPart f (x0 + α • p) - withTopRealPart f x0) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 (f′[hx0] p)) := by
  have hslice :
      (fun α : ℝ ↦ extendedRealRealPart (withTopToEReal ∘ f) (x0 + α • p)) =
        fun α : ℝ ↦ withTopRealPart f (x0 + α • p) := by
    funext α
    simp [Function.comp, withTopToEReal_toReal_eq_withTopRealPart]
  have hderiv_Ioi :
      HasDerivWithinAt
        (fun α : ℝ ↦ extendedRealRealPart (withTopToEReal ∘ f) (x0 + α • p))
        (f′[hx0] p) (Set.Ioi (0 : ℝ)) 0 := by
    exact
      (convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx0 p).hasDerivWithinAt.Ioi_of_Ici
  rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)] at hderiv_Ioi
  rw [hslice] at hderiv_Ioi
  simpa [slope_fun_def_field] using hderiv_Ioi

/-- Theorem 3.21 (1): if `f` is a convex proper extended-real-valued function on a real
topological module and `x₀` lies in the interior of its effective domain, then the directional
derivative `p ↦ f'(x₀; p)` is a finite convex function on all directions. -/
-- Proof sketch: the theorem-level real directional derivative is the direct finite `toReal` view
-- of the canonical
-- directional-derivative owner. Use the interior-point convexity theorem for convex directional
-- derivatives, and keep the bridge to the secant-slope owner explicit.
theorem convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ConvexOn ℝ Set.univ (f′[hx0]) := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb hab
  let r : E := a • p + b • q
  have hr_tendsto := tendsto_directionalSecantQuotient_of_mem_interior hf hx0 r
  have hp_tendsto := tendsto_directionalSecantQuotient_of_mem_interior hf hx0 p
  have hq_tendsto := tendsto_directionalSecantQuotient_of_mem_interior hf hx0 q
  have hsum_tendsto :
      Tendsto
        (fun α : ℝ ↦
          a * ((withTopRealPart f (x0 + α • p) - withTopRealPart f x0) / α) +
            b * ((withTopRealPart f (x0 + α • q) - withTopRealPart f x0) / α))
        (𝓝[>] (0 : ℝ))
        (𝓝 (a * f′[hx0] p + b * f′[hx0] q)) := by
    exact (hp_tendsto.const_mul a).add (hq_tendsto.const_mul b)
  have mem_dom_of_mem_owner {y : E} :
      y ∈ extendedRealEffectiveDomain (withTopToEReal ∘ f) → y ∈ dom f := by
    intro hy
    rcases mem_extendedRealEffectiveDomain_iff.mp hy with ⟨hy_top, _⟩
    show f y < ⊤
    refine lt_top_iff_ne_top.mpr ?_
    intro htop
    have htop' : withTopToEReal (f y) = ⊤ := by
      rw [htop]
      rfl
    exact hy_top htop'
  have hp_dom :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x0 + α • p ∈ dom f := by
    filter_upwards
      [(convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx0 p).eventually_mem_dom]
      with α hα
    exact mem_dom_of_mem_owner hα
  have hq_dom :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x0 + α • q ∈ dom f := by
    filter_upwards
      [(convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx0 q).eventually_mem_dom]
      with α hα
    exact mem_dom_of_mem_owner hα
  have hpos :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa using
      (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), x ∈ Set.Ioi (0 : ℝ))
  have hineq_eventually :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        (withTopRealPart f (x0 + α • r) - withTopRealPart f x0) / α ≤
          a * ((withTopRealPart f (x0 + α • p) - withTopRealPart f x0) / α) +
            b * ((withTopRealPart f (x0 + α • q) - withTopRealPart f x0) / α) := by
    filter_upwards [hp_dom, hq_dom, hpos] with α hpα hqα hα
    have hr_eq :
        a • (x0 + α • p) + b • (x0 + α • q) = x0 + α • r := by
      calc
        a • (x0 + α • p) + b • (x0 + α • q)
            = (a + b) • x0 + ((a * α) • p + (b * α) • q) := by
                simp [add_smul, smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc, add_assoc,
                  add_left_comm, add_comm]
        _ = x0 + ((a * α) • p + (b * α) • q) := by
              simpa [hab]
        _ = x0 + α • r := by
              simp [r, smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    have hrα :
        x0 + α • r ∈ dom f := by
      rw [← hr_eq]
      exact hf.1 hpα hqα ha hb hab
    have hconvα :
        withTopRealPart f (x0 + α • r) ≤
          a * withTopRealPart f (x0 + α • p) + b * withTopRealPart f (x0 + α • q) := by
      have hconvα' := hf.2 hpα hqα ha hb hab
      rwa [hr_eq] at hconvα'
    have hscaled :
        withTopRealPart f (x0 + α • r) - withTopRealPart f x0 ≤
          a * (withTopRealPart f (x0 + α • p) - withTopRealPart f x0) +
            b * (withTopRealPart f (x0 + α • q) - withTopRealPart f x0) := by
      have hx0_split : (a + b) * withTopRealPart f x0 = withTopRealPart f x0 := by
        rw [hab]
        ring
      calc
        withTopRealPart f (x0 + α • r) - withTopRealPart f x0
            ≤
              (a * withTopRealPart f (x0 + α • p) +
                  b * withTopRealPart f (x0 + α • q)) - withTopRealPart f x0 := by
                    linarith [hconvα]
        _ = (a * withTopRealPart f (x0 + α • p) +
              b * withTopRealPart f (x0 + α • q)) - (a + b) * withTopRealPart f x0 := by
                nth_rewrite 1 [← hx0_split]
                rfl
        _ = a * (withTopRealPart f (x0 + α • p) - withTopRealPart f x0) +
              b * (withTopRealPart f (x0 + α • q) - withTopRealPart f x0) := by
                ring
    apply (div_le_iff₀ hα).2
    field_simp [hα.ne']
    linarith [hscaled]
  have hlimit_ineq :=
    le_of_tendsto_of_tendsto hr_tendsto hsum_tendsto hineq_eventually
  simpa [r, smul_eq_mul] using hlimit_ineq

end Core

section Subdifferential

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Theorem 3.21 (2): the subdifferential with respect to the direction variable of
`p ↦ f'(x₀; p)` at `0` coincides with the subdifferential of `f` at `x₀` in the source-faithful
finite-dimensional real inner-product setting. -/
-- Proof sketch: one inclusion comes from the subgradient inequality
-- `⟪g, p⟫ ≤ f'(x₀; p)` for `g ∈ ∂f(x₀)`. For the reverse inclusion, evaluate the supporting
-- inequality for the directional derivative at `p = y - x₀` to recover the defining
-- subgradient inequality for `f`.
theorem subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∂[Set.univ] f′[hx0](0) = ∂ f(x0) := by
  have hzero : f′[hx0] (0 : E) = 0 := by
    -- Compare the owner derivative in the zero direction with the constant-ray derivative.
    have howner :
        HasDirectionalDerivAt (withTopToEReal ∘ f) x0 (0 : E) (f′[hx0] (0 : E)) :=
      convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx0 0
    have hconst :
        HasDirectionalDerivAt (withTopToEReal ∘ f) x0 (0 : E) 0 :=
      HasDirectionalDerivAt.zero
        (f := withTopToEReal ∘ f) (x := x0)
        (mem_dom_withTopToEReal_comp_of_mem_dom (interior_subset hx0))
    exact HasDirectionalDerivAt.unique howner hconst
  have hpos :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa using
      (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), x ∈ Set.Ioi (0 : ℝ))
  have hsupport :
      ∀ {y : E}, y ∈ dom f →
        withTopRealPart f y ≥ withTopRealPart f x0 + f′[hx0] (y - x0) := by
    intro y hy
    let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x0 y
    let S : Set ℝ := line ⁻¹' dom f
    let g : ℝ → ℝ := withTopRealPart f ∘ line
    have hline_apply (α : ℝ) : line α = x0 + α • (y - x0) := by
      simpa [line, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
        (AffineMap.lineMap_apply_module x0 y α)
    have hconv : ConvexOn ℝ S g := by
      -- Restrict the convex function to the segment through `x0` and `y`.
      simpa [S, g] using hf.comp_affineMap line
    have hzero_mem : (0 : ℝ) ∈ S := by
      simpa [S, hline_apply] using interior_subset hx0
    have hone_mem : (1 : ℝ) ∈ S := by
      simpa [S, hline_apply] using hy
    have hslice :
        (fun α : ℝ ↦ extendedRealRealPart (withTopToEReal ∘ f) (x0 + α • (y - x0))) = g := by
      funext α
      rw [show x0 + α • (y - x0) = line α by symm; exact hline_apply α]
      simp [g, Function.comp, withTopToEReal_toReal_eq_withTopRealPart]
    have hderiv_Ioi :
        HasDerivWithinAt g (f′[hx0] (y - x0)) (Set.Ioi (0 : ℝ)) 0 := by
      rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)]
      simpa [g, hline_apply, slope_fun_def_field] using
        (tendsto_directionalSecantQuotient_of_mem_interior hf hx0 (y - x0))
    have hslope :
        f′[hx0] (y - x0) ≤ withTopRealPart f y - withTopRealPart f x0 := by
      simpa [g, slope_def_field, hline_apply] using
        hconv.le_slope_of_hasDerivWithinAt_Ioi hzero_mem hone_mem zero_lt_one hderiv_Ioi
    linarith
  ext g
  constructor
  · intro hg
    rw [mem_subdifferentialWithin_iff] at hg
    rcases hg with ⟨_, hg⟩
    rw [mem_subdifferential_iff]
    refine ⟨interior_subset hx0, ?_⟩
    intro y hy
    have hpair : inner ℝ g (y - x0) ≤ f′[hx0] (y - x0) := by
      have := hg (show y - x0 ∈ Set.univ by simp)
      simpa [hzero] using this
    have hreal :
        withTopRealPart f y ≥ withTopRealPart f x0 + inner ℝ g (y - x0) := by
      linarith [hsupport hy, hpair]
    have htop :
        (((withTopRealPart f x0 + inner ℝ g (y - x0) : ℝ) : WithTop ℝ)) ≤ f y := by
      rw [← coe_withTopRealPart (f := f) hy]
      exact_mod_cast hreal
    have hleft :
        (((withTopRealPart f x0 + inner ℝ g (y - x0) : ℝ) : WithTop ℝ)) =
          f x0 + (inner ℝ g (y - x0) : WithTop ℝ) := by
      rw [← coe_withTopRealPart (f := f) (interior_subset hx0)]
      simp
    rw [hleft] at htop
    exact htop
  · intro hg
    have hsub : IsSubgradientAt f x0 g := mem_subdifferential_iff.mp hg
    rw [mem_subdifferentialWithin_iff]
    refine ⟨by simp, ?_⟩
    intro p hp
    have hdom :
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x0 + α • p ∈ dom f := by
      have howner_dom :=
        (convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx0 p).eventually_mem_dom
      filter_upwards [howner_dom] with α hα
      rcases mem_extendedRealEffectiveDomain_iff.mp hα with ⟨hα_top, _⟩
      exact lt_top_iff_ne_top.mpr fun htop ↦ hα_top (by rw [Function.comp, htop, withTopToEReal]; rfl)
    have hpair : inner ℝ g p ≤ f′[hx0] p := by
      have hconst : Tendsto (fun _ : ℝ ↦ inner ℝ g p) (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ g p)) :=
        tendsto_const_nhds
      have hquot_bound :
          ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
            inner ℝ g p ≤
              (withTopRealPart f (x0 + α • p) - withTopRealPart f x0) / α := by
        filter_upwards [hdom, hpos] with α hαdom hα
        have hineq : f (x0 + α • p) ≥ f x0 + (inner ℝ g ((x0 + α • p) - x0) : WithTop ℝ) :=
          hsub.2 hαdom
        have hreal :
            withTopRealPart f (x0 + α • p) ≥ withTopRealPart f x0 + α * inner ℝ g p := by
          rw [← coe_withTopRealPart (f := f) hαdom,
            ← coe_withTopRealPart (f := f) (interior_subset hx0)] at hineq
          have hineq_top :
              (((withTopRealPart f x0 + α * inner ℝ g p : ℝ) : WithTop ℝ)) ≤
                (((withTopRealPart f (x0 + α • p) : ℝ) : WithTop ℝ)) := by
              simpa [sub_eq_add_neg, inner_add_right, inner_neg_right, inner_smul_right] using
                hineq
          have hineq_real :
              withTopRealPart f x0 + α * inner ℝ g p ≤
                withTopRealPart f (x0 + α • p) := by
              exact_mod_cast hineq_top
          exact hineq_real
        apply (le_div_iff₀ hα).2
        have hmul :
            α * inner ℝ g p ≤ withTopRealPart f (x0 + α • p) - withTopRealPart f x0 := by
          linarith
        simpa [mul_comm, sub_eq_add_neg] using hmul
      exact
        le_of_tendsto_of_tendsto hconst
          (tendsto_directionalSecantQuotient_of_mem_interior hf hx0 p) hquot_bound
    simpa [hzero] using hpair

/-- Theorem 3.21 (3): for every direction `p`, the directional derivative at `x₀` is the maximum
of the pairings `⟪g, p⟫` over all subgradients `g ∈ ∂f(x₀)`, recorded as an `IsGreatest`
statement for the image of the subdifferential, again on the finite-dimensional owner layer where
supporting functionals are represented by vectors. -/
-- Proof sketch: every subgradient gives the lower bound
-- `inner ℝ g p ≤ (convexDirectionalDerivative f x₀ (interior_subset hx₀) p).toReal`.
-- Then use the subdifferential identity
-- at the origin together with positive homogeneity of the directional derivative to show that some
-- subgradient attains equality.
theorem convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) (p : E) :
    IsGreatest ((fun g : E ↦ inner ℝ g p) '' ∂ f(x0))
      (f′[hx0] p) := by
  have hzero : f′[hx0] (0 : E) = 0 := by
    have howner :
        HasDirectionalDerivAt (withTopToEReal ∘ f) x0 (0 : E) (f′[hx0] (0 : E)) :=
      convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx0 0
    have hconst :
        HasDirectionalDerivAt (withTopToEReal ∘ f) x0 (0 : E) 0 :=
      HasDirectionalDerivAt.zero
        (f := withTopToEReal ∘ f) (x := x0)
        (mem_dom_withTopToEReal_comp_of_mem_dom (interior_subset hx0))
    exact HasDirectionalDerivAt.unique howner hconst
  have hhom : IsPositivelyHomogeneousOn 1 Set.univ (f′[hx0]) := by
    refine ⟨?_, ?_⟩
    · intro y hy τ
      simp
    · intro y hy τ
      by_cases hτ : τ = 0
      · rw [hτ, zero_smul]
        simpa [Real.rpow_one] using hzero
      · have hτ_pos : 0 < (τ : ℝ) := by
          exact_mod_cast (show 0 < τ from pos_iff_ne_zero.mpr hτ)
        rw [convexDirectionalDerivativeReal_apply, convexDirectionalDerivativeReal_apply]
        change
          (convexDirectionalDerivative f x0 (interior_subset hx0) ((τ : ℝ) • y)).toReal =
            (τ : ℝ).rpow 1 * (convexDirectionalDerivative f x0 (interior_subset hx0) y).toReal
        rw [convexDirectionalDerivative_smul (f := f) (hx := interior_subset hx0) hτ_pos y]
        simpa [Real.rpow_one, smul_eq_mul, EReal.toReal_mul]
  have hsub_univ :
      ∂ (fun y ↦ (f′[hx0] y : WithTop ℝ))(0) = ∂[Set.univ] f′[hx0](0) := by
    ext g
    rw [mem_subdifferential_coe_real_iff, mem_subdifferentialWithin_iff]
    constructor
    · intro hg
      refine ⟨by simp, ?_⟩
      intro y hy
      simpa using hg y
    · rintro ⟨_, hg⟩
      intro y
      simpa using hg (show y ∈ Set.univ by simp)
  have horigin :
      ∂ (fun y ↦ (f′[hx0] y : WithTop ℝ))(0) = ∂ f(x0) := by
    rw [hsub_univ, subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential hf hx0]
  have hmax :=
    isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous
      (f := f′[hx0])
      (hf_convex := convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior hf hx0)
      (hf_hom := hhom) p
  simpa [horigin] using hmax

end Subdifferential

end
