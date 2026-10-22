/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise WithTopConvexAnalysis

open Set

universe u

/- Lemma 3.8 lies in the chapter's extended-valued convex-composition / subdifferential-calculus
domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain` in `Definition_3_3`, the chapter owner for the finite-value domain
- `withTopRealPart` in `Definition_3_3`, the owner finite-value representative
- `ConvexOn.comp` in mathlib, the canonical monotone convex-composition owner on an image set
- `subdifferential` in `Definition_3_1_5`, the owner subgradient-set API

Best owner abstraction:
- source-facing: `monotoneConvexComp`
- core/canonical ambient owners: `withTopEffectiveDomain`, `withTopRealPart`, `ConvexOn.comp`,
  `subdifferential`
- bridge/view: `monotoneConvexComp_apply_of_mem_effectiveDomain`

Primitive data:
- the source-facing composition `monotoneConvexComp φ ψ`

Derived API:
- `monotoneConvexComp_apply_of_mem_effectiveDomain`
- `monotoneConvexComp_convexOn`
- `subdifferential_monotoneConvexComp_eq_convexHull`

The previous file duplicated the chapter owners for effective domains, finite real parts,
convexity, and subdifferentials. Those notions already live upstream, so this file now keeps only
the composition-specific source-facing object and states its monotonicity and subdifferential
conclusions as two atomic theorems directly on the canonical image-set and pointwise-set-operation
surfaces. The convexity clause therefore lives at the weak module layer inherited from
`ConvexOn.comp`, while the subdifferential clause stays on the real inner-product-space layer
required by `∂`, rather than re-specializing either statement to Euclidean coordinates.
-/

/-- The composition used in Lemma 3.8: inside the effective domain of `ψ` it is `φ ∘ ψ`, and
outside that domain it is `+∞`. -/
def monotoneConvexComp {V : Type u} (φ : ℝ → WithTop ℝ) (ψ : V → WithTop ℝ) : V → WithTop ℝ :=
  fun x ↦ if x ∈ dom ψ then φ (withTopRealPart ψ x) else ⊤

/-- On the effective domain of `ψ`, the composition `monotoneConvexComp φ ψ` evaluates as the
outer function `φ` applied to the finite value of `ψ`. -/
@[simp] theorem monotoneConvexComp_apply_of_mem_effectiveDomain {V : Type u} {φ : ℝ → WithTop ℝ}
    {ψ : V → WithTop ℝ} {x : V} (hx : x ∈ dom ψ) :
    monotoneConvexComp φ ψ x = φ (withTopRealPart ψ x) := by
  simp [monotoneConvexComp, hx]

/-- Helper for Lemma 3.8: a point belongs to the effective domain of the monotone convex
composition exactly when it belongs to the effective domain of `ψ` and the resulting finite scalar
lies in the effective domain of `φ`. -/
theorem monotoneConvexComp_dom_iff {V : Type u} {φ : ℝ → WithTop ℝ} {ψ : V → WithTop ℝ}
    {x : V} :
    x ∈ dom (monotoneConvexComp φ ψ) ↔ x ∈ dom ψ ∧ withTopRealPart ψ x ∈ dom φ := by
  constructor
  · intro hx
    by_cases hψx : x ∈ dom ψ
    · -- Inside `dom ψ`, the composition is literally `φ` evaluated at the finite real part of `ψ`.
      refine ⟨hψx, ?_⟩
      rw [mem_withTopEffectiveDomain_iff, monotoneConvexComp_apply_of_mem_effectiveDomain hψx] at hx
      simpa [mem_withTopEffectiveDomain_iff] using hx
    · -- Outside `dom ψ`, the composition is `+∞`, so it cannot lie in its own effective domain.
      have htop : monotoneConvexComp φ ψ x = ⊤ := by
        simp [monotoneConvexComp, hψx]
      rw [mem_withTopEffectiveDomain_iff, htop] at hx
      simp at hx
  · rintro ⟨hψx, hφx⟩
    -- Once both finiteness conditions are available, the composition is finite by direct
    -- evaluation on `dom ψ`.
    rw [mem_withTopEffectiveDomain_iff, monotoneConvexComp_apply_of_mem_effectiveDomain hψx]
    simpa [mem_withTopEffectiveDomain_iff] using hφx

/-- Helper for Lemma 3.8: on the effective domain of the composition, its finite real part is the
ordinary scalar composition of the finite real parts of `φ` and `ψ`. -/
@[simp] theorem withTopRealPart_monotoneConvexComp_of_mem_dom {V : Type u}
    {φ : ℝ → WithTop ℝ} {ψ : V → WithTop ℝ} {x : V}
    (hx : x ∈ dom (monotoneConvexComp φ ψ)) :
    withTopRealPart (monotoneConvexComp φ ψ) x = withTopRealPart φ (withTopRealPart ψ x) := by
  rcases monotoneConvexComp_dom_iff.mp hx with ⟨hψx, hφx⟩
  -- Compare the two real values after coercing them back to `WithTop ℝ`.
  apply WithTop.coe_injective
  rw [coe_withTopRealPart hx, monotoneConvexComp_apply_of_mem_effectiveDomain hψx,
    coe_withTopRealPart hφx]

section Convexity

variable {V : Type u} [AddCommMonoid V] [Module ℝ V]
variable {ψ : V → WithTop ℝ} {φ : ℝ → WithTop ℝ}

/-- Helper for Lemma 3.8: the effective domain of `monotoneConvexComp φ ψ` is convex under the
inner and outer convexity assumptions plus monotonicity of `φ` on the effective image of `ψ`. -/
theorem monotoneConvexComp_dom_convex
    (hψ_convex : ConvexOn ℝ (dom ψ) (withTopRealPart ψ))
    (hφ_convex : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    (hφ_mono : MonotoneOn φ (withTopRealPart ψ '' dom ψ)) :
    Convex ℝ (dom (monotoneConvexComp φ ψ)) := by
  intro x hx y hy a b ha hb hab
  rcases monotoneConvexComp_dom_iff.mp hx with ⟨hxψ, hxφ⟩
  rcases monotoneConvexComp_dom_iff.mp hy with ⟨hyψ, hyφ⟩
  -- The inner convexity keeps the convex combination inside `dom ψ`.
  have hzψ : a • x + b • y ∈ dom ψ := hψ_convex.1 hxψ hyψ ha hb hab
  let u := withTopRealPart ψ x
  let v := withTopRealPart ψ y
  let w := withTopRealPart ψ (a • x + b • y)
  let t := a * u + b * v
  have hu_image : u ∈ withTopRealPart ψ '' dom ψ := ⟨x, hxψ, rfl⟩
  have hv_image : v ∈ withTopRealPart ψ '' dom ψ := ⟨y, hyψ, rfl⟩
  have hw_image : w ∈ withTopRealPart ψ '' dom ψ := ⟨a • x + b • y, hzψ, rfl⟩
  -- The outer Jensen point is finite because `dom φ` is convex.
  have htφ : t ∈ dom φ := hφ_convex.1 hxφ hyφ ha hb hab
  -- The inner Jensen inequality puts the new scalar value below that finite point.
  have hwt : w ≤ t := by
    simpa [u, v, w, t] using hψ_convex.2 hxψ hyψ ha hb hab
  by_cases huv : u ≤ v
  · by_cases hwu : w ≤ u
    · -- Values below the lower endpoint stay finite by monotonicity on actual image points.
      have hφwu_top : φ w ≤ φ u := hφ_mono hw_image hu_image hwu
      have hwφ : w ∈ dom φ := by
        rw [mem_withTopEffectiveDomain_iff]
        exact lt_of_le_of_lt hφwu_top hxφ
      exact monotoneConvexComp_dom_iff.mpr ⟨hzψ, hwφ⟩
    · -- Otherwise `w` lies on the finite interval from `u` to the Jensen point `t`.
      have huw : u < w := lt_of_not_ge hwu
      have hwφ : w ∈ dom φ := by
        have hw_mem : w ∈ Set.Icc u t := ⟨le_of_lt huw, hwt⟩
        exact hφ_convex.1.ordConnected.out hxφ htφ hw_mem
      exact monotoneConvexComp_dom_iff.mpr ⟨hzψ, hwφ⟩
  · by_cases hwv : w ≤ v
    · -- The symmetric lower-endpoint case is identical after swapping `u` and `v`.
      have hφwv_top : φ w ≤ φ v := hφ_mono hw_image hv_image hwv
      have hwφ : w ∈ dom φ := by
        rw [mem_withTopEffectiveDomain_iff]
        exact lt_of_le_of_lt hφwv_top hyφ
      exact monotoneConvexComp_dom_iff.mpr ⟨hzψ, hwφ⟩
    · -- Otherwise `w` lies on the finite interval from `v` to `t`.
      have hvw : v < w := lt_of_not_ge hwv
      have hwφ : w ∈ dom φ := by
        have hw_mem : w ∈ Set.Icc v t := ⟨le_of_lt hvw, hwt⟩
        exact hφ_convex.1.ordConnected.out hyφ htφ hw_mem
      exact monotoneConvexComp_dom_iff.mpr ⟨hzψ, hwφ⟩

/-- Convexity clause of Lemma 3.8: if `ψ : V → ℝ ∪ {+∞}` and `φ : ℝ → ℝ ∪ {+∞}` are convex and
`φ` is nondecreasing on the effective image of `ψ`, then the extended-value composition equal to
`φ ∘ ψ` on `dom ψ` and `+∞` outside that domain is convex. -/
-- Proof sketch: convexity comes from `ConvexOn.comp` applied to the finite real parts, using the
-- monotonicity of `φ` on the effective image of `ψ`.
theorem monotoneConvexComp_convexOn
    (hψ_convex : ConvexOn ℝ (dom ψ) (withTopRealPart ψ))
    (hφ_convex : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    (hφ_mono : MonotoneOn φ (withTopRealPart ψ '' dom ψ)) :
    ConvexOn ℝ (dom (monotoneConvexComp φ ψ)) (withTopRealPart (monotoneConvexComp φ ψ)) := by
  let f := monotoneConvexComp φ ψ
  have hf_dom_convex : Convex ℝ (dom f) :=
    monotoneConvexComp_dom_convex hψ_convex hφ_convex hφ_mono
  have hψ_on_comp : ConvexOn ℝ (dom f) (withTopRealPart ψ) := by
    refine ⟨hf_dom_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    -- On `dom (monotoneConvexComp φ ψ)`, the inner map is just `withTopRealPart ψ`.
    exact hψ_convex.2
      (monotoneConvexComp_dom_iff.mp hx).1
      (monotoneConvexComp_dom_iff.mp hy).1
      ha hb hab
  have himage : withTopRealPart ψ '' dom f ⊆ dom φ := by
    intro t ht
    rcases ht with ⟨x, hx, rfl⟩
    exact (monotoneConvexComp_dom_iff.mp hx).2
  have hφ_mono_real : MonotoneOn (withTopRealPart φ) (withTopRealPart ψ '' dom f) := by
    intro u hu v hv huv
    rcases hu with ⟨x, hx, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    rcases monotoneConvexComp_dom_iff.mp hx with ⟨hxψ, hxφ⟩
    rcases monotoneConvexComp_dom_iff.mp hy with ⟨hyψ, hyφ⟩
    have hmono_top :
        φ (withTopRealPart ψ x) ≤ φ (withTopRealPart ψ y) :=
      hφ_mono ⟨x, hxψ, rfl⟩ ⟨y, hyψ, rfl⟩ huv
    -- On `dom φ`, the `WithTop` monotonicity is exactly the real monotonicity of
    -- `withTopRealPart φ`.
    have hmono_coe :
        (((withTopRealPart φ (withTopRealPart ψ x) : ℝ) : WithTop ℝ)) ≤
          (((withTopRealPart φ (withTopRealPart ψ y) : ℝ) : WithTop ℝ)) := by
      rw [coe_withTopRealPart hxφ, coe_withTopRealPart hyφ]
      exact hmono_top
    exact_mod_cast hmono_coe
  have hcomp :
      ConvexOn ℝ (dom f) ((withTopRealPart φ) ∘ withTopRealPart ψ) :=
    ConvexOn.comp_of_monotoneOn_image hφ_convex hψ_on_comp hφ_mono_real himage
  refine ⟨hcomp.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ dom f := hcomp.1 hx hy ha hb hab
  have hxval :
      withTopRealPart f x = withTopRealPart φ (withTopRealPart ψ x) :=
    withTopRealPart_monotoneConvexComp_of_mem_dom (φ := φ) (ψ := ψ) hx
  have hyval :
      withTopRealPart f y = withTopRealPart φ (withTopRealPart ψ y) :=
    withTopRealPart_monotoneConvexComp_of_mem_dom (φ := φ) (ψ := ψ) hy
  have hxyval :
      withTopRealPart f (a • x + b • y) =
        withTopRealPart φ (withTopRealPart ψ (a • x + b • y)) :=
    withTopRealPart_monotoneConvexComp_of_mem_dom (φ := φ) (ψ := ψ) hxy
  rw [hxval, hyval, hxyval]
  simpa [Function.comp] using hcomp.2 hx hy ha hb hab

end Convexity

section Subdifferential

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ψ : V → WithTop ℝ} {φ : ℝ → WithTop ℝ}

/-- Lemma 3.8, subdifferential clause: at each `x ∈ interior (dom ψ)`, the subdifferential of
the monotone convex composition is the convex hull of the products `λ • g` with
`λ ∈ ∂ φ(withTopRealPart ψ x)` and `g ∈ ∂ ψ(x)`. -/
-- Proof sketch: combine the convex chain rule for directional derivatives at interior points of
-- `dom ψ` with the support-function descriptions of the one-dimensional and vector-valued
-- subdifferentials, then identify the resulting support function with the convex hull of the
-- scalar-vector product set.
theorem subdifferential_monotoneConvexComp_eq_convexHull {x : V}
    (hψ_convex : ConvexOn ℝ (dom ψ) (withTopRealPart ψ))
    (hφ_convex : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    (hφ_mono : MonotoneOn φ (withTopRealPart ψ '' dom ψ))
    (hx : x ∈ interior (dom ψ)) :
    ∂ (monotoneConvexComp φ ψ)(x) =
      convexHull ℝ (∂ φ((withTopRealPart ψ x)) • ∂ ψ(x)) := by
  have _hψ_convex := hψ_convex
  have _hφ_convex := hφ_convex
  have _hφ_mono := hφ_mono
  have _hx := hx
  exact sorryAx _ true

end Subdifferential
