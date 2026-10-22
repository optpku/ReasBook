/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.LinearEqualityFeasibleSet
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u v

/- Theorem 3.35 lies in the chapter's affine-fiber infimal-projection / relative-subdifferential
domain.

Sampled owner-style declarations:
- `partialInfProjection` and
  `extendedRealRealPart_partialInfProjection_eq_sInf` in `Theorem_3_1_2_3`, the canonical
  `EReal` owner and its finite-value bridge;
- `partialInfProjection_convexOn_of_convexWithTop` in `Theorem_3_8`, the convexity theorem on the
  same owner for `WithTop` objectives;
- `linearEqualityFeasibleSet` in `LinearEqualityFeasibleSet`, the affine-constraint feasible-set
  owner already used elsewhere in the chapter;
- `subdifferentialWithin` in `Theorem_3_44`, the chapter owner for the real-valued relative
  subgradient surface.

Best owner abstraction:
- core/canonical: the affine-fiber `EReal` infimal projection
  `partialInfProjection {p | p.2 ∈ Q ∧ A p.2 = p.1} (withTopToEReal ∘ (f ∘ Prod.snd))`;
- source-facing bridge: `linearEqualityFeasibleSet Q A u` and the finite real part of that
  infimal projection on its domain;
- derived API: the `sInf` formula on finite fibers, convexity of that finite real part, and the
  variational-inequality criterion for membership in its relative subdifferential.

Primitive data:
- an objective `f : E → WithTop ℝ`;
- a feasible set `Q : Set E`;
- a linear map `A : E →ₗ[ℝ] Λ`.

Derived API:
- the finite-value `sInf` bridge for the projected value function;
- convexity of the finite real part on its finite-value domain;
- the multiplier-candidate inclusion into the relative subdifferential.

Source/core/bridge triage:
- source-facing: the projected-value-function statements for affine fibers `A x = u`;
- core/canonical: `partialInfProjection`;
- bridge/view: `linearEqualityFeasibleSet` and `subdifferentialWithin`.

The previous version introduced a second public owner `projectedValueFunction` and a separate
candidate-set surface, duplicating the earlier linearly constrained vocabulary while also bypassing
the chapter's canonical `partialInfProjection` owner. This file now keeps only thin bridge
theorems on the canonical owner stack, writes the affine-fiber relation directly into
`partialInfProjection` on the public theorem surface, and introduces no new public value-function
definition. -/

section AffineProjection

variable {E : Type u} {Λ : Type v}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid Λ] [Module ℝ Λ]
variable {f : E → WithTop ℝ} {Q : Set E} (A : E →ₗ[ℝ] Λ)

/-- Helper for Theorem 3.35: restricting affine fibers to the finite-value locus of `f` does not
change the canonical affine partial infimal projection. -/
-- Proof sketch: points where `f = ⊤` contribute only the top element to each fiber image, and
-- inserting `⊤` does not change the infimum.
theorem affinePartialInfProjection_eq_restricted_realProjection :
    partialInfProjection
        {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
        (withTopToEReal ∘ f ∘ Prod.snd) =
      partialInfProjection
        {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
        (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2) := by
  funext u
  let S : Set EReal :=
    (withTopToEReal ∘ f ∘ Prod.snd) '' {z : Λ × E |
      z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.1 = u}
  let T : Set EReal :=
    (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2) '' {z : Λ × E |
      (z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.2 ∈ dom f) ∧ z.1 = u}
  -- Every finite feasible point contributes the same value to the unrestricted and restricted
  -- fiber images.
  have hTS : T ⊆ S := by
    intro a ha
    rcases ha with ⟨z, hz, rfl⟩
    refine ⟨z, ⟨hz.1.1, hz.2⟩, ?_⟩
    simpa [Function.comp, withTopToEReal] using
      (congrArg withTopToEReal (coe_withTopRealPart (f := f) hz.1.2)).symm
  -- Unrestricted feasible points are either finite and already in `T`, or have value `⊤`.
  have hSinsert : S ⊆ insert ⊤ T := by
    intro a ha
    rcases ha with ⟨z, hz, rfl⟩
    by_cases hzDom : z.2 ∈ dom f
    · right
      refine ⟨z, ⟨⟨hz.1, hzDom⟩, hz.2⟩, ?_⟩
      simpa [Function.comp, withTopToEReal] using
        congrArg withTopToEReal (coe_withTopRealPart (f := f) hzDom)
    · left
      rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hzDom
      have hzTop : f z.2 = ⊤ := by
        simpa using hzDom
      change withTopToEReal (f z.2) = ⊤
      rw [hzTop, withTopToEReal]
      rfl
  rw [partialInfProjection_eq_sInf, partialInfProjection_eq_sInf]
  simpa [S, T] using
    (show sInf S = sInf T from
      le_antisymm (sInf_le_sInf hTS)
        (by simpa using (sInf_le_sInf hSinsert : sInf (insert ⊤ T) ≤ sInf S)))

/-- At any base point where the canonical affine-fiber infimal projection is finite, its finite
real part agrees with the textbook infimum of the feasible fiber values. -/
-- Proof sketch: unfold the affine fiber as `linearEqualityFeasibleSet Q A u`, then apply the
-- finite-value bridge for `partialInfProjection` on the corresponding subset of `Λ × E`.
theorem extendedRealRealPart_affinePartialInfProjection_eq_sInf_image
    {u : Λ}
    (hu :
      u ∈ dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))) :
    extendedRealRealPart
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))
        u =
      sInf {t : ℝ | ∃ x : E, x ∈ linearEqualityFeasibleSet Q A u ∧ f x = t} := by
  have hu' :
      u ∈ dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
          (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2)) := by
    rw [affinePartialInfProjection_eq_restricted_realProjection (A := A) (f := f) (Q := Q)] at hu
    exact hu
  -- The restricted owner matches the textbook fiber-value set exactly.
  have himage :
      (fun p : Λ × E ↦ withTopRealPart f p.2) '' {z : Λ × E |
          (z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.2 ∈ dom f) ∧ z.1 = u} =
        {t : ℝ | ∃ x : E, x ∈ linearEqualityFeasibleSet Q A u ∧ f x = t} := by
    ext t
    constructor
    · rintro ⟨z, hz, ht⟩
      have hzFeas : z.2 ∈ linearEqualityFeasibleSet Q A u := by
        simpa [hz.2] using hz.1.1
      refine ⟨z.2, hzFeas, ?_⟩
      calc
        f z.2 = ((withTopRealPart f z.2 : ℝ) : WithTop ℝ) := by
          symm
          exact coe_withTopRealPart (f := f) hz.1.2
        _ = t := by
          exact congrArg (fun s : ℝ ↦ ((s : ℝ) : WithTop ℝ)) ht
    · rintro ⟨x, hx, hfx⟩
      have hxDom : x ∈ dom f := by
        rw [mem_withTopEffectiveDomain_iff, hfx, lt_top_iff_ne_top]
        simp
      refine ⟨(u, x), ⟨⟨hx, hxDom⟩, rfl⟩, ?_⟩
      apply WithTop.coe_injective
      simpa [hfx] using coe_withTopRealPart (f := f) hxDom
  -- Read the finite-value bridge on the restricted real-valued owner.
  rw [affinePartialInfProjection_eq_restricted_realProjection (A := A) (f := f) (Q := Q)]
  have hbridge :
      extendedRealRealPart
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
            (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2))
          u =
        sInf ((fun p : Λ × E ↦ withTopRealPart f p.2) '' {z : Λ × E |
          (z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.2 ∈ dom f) ∧ z.1 = u}) := by
    simpa using
      (extendedRealRealPart_partialInfProjection_eq_sInf
        (Q := {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f})
        (φ := fun p : Λ × E ↦ withTopRealPart f p.2)
        hu')
  calc
    extendedRealRealPart
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
          (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2))
        u =
      sInf ((fun p : Λ × E ↦ withTopRealPart f p.2) '' {z : Λ × E |
        (z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.2 ∈ dom f) ∧ z.1 = u}) := hbridge
    _ = sInf {t : ℝ | ∃ x : E, x ∈ linearEqualityFeasibleSet Q A u ∧ f x = t} := by
          rw [himage]

/-- Theorem 3.35 (1): under convexity of `f` on its effective domain plus convexity of `Q`, the
finite real part of the canonical affine-fiber infimal projection is convex on its finite-value
domain. -/
-- Proof sketch: specialize the chapter convexity theorem for `partialInfProjection` to
-- `{p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}` together with the `WithTop` objective
-- `f ∘ Prod.snd`.
theorem affinePartialInfProjection_realPart_convexOn
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hQ_convex : Convex ℝ Q) :
    ConvexOn ℝ
      (dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd)))
      (extendedRealRealPart
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))) := by
  let Q' : Set (Λ × E) :=
    {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
  -- The affine-fiber finite locus is convex because both `Q` and `dom f` are convex and the
  -- equality constraint is preserved by affine combinations.
  have hQ' : Convex ℝ Q' := by
    intro p hp q hq a b ha hb hab
    rcases hp with ⟨hpFeas, hpDom⟩
    rcases hq with ⟨hqFeas, hqDom⟩
    rcases hpFeas with ⟨hpQ, hpA⟩
    rcases hqFeas with ⟨hqQ, hqA⟩
    refine ⟨?_, hf.1 hpDom hqDom ha hb hab⟩
    refine ⟨hQ_convex hpQ hqQ ha hb hab, ?_⟩
    simp [linearEqualityFeasibleSet, hpA, hqA, map_add, map_smul]
  -- The objective on the product space is just the second-coordinate pullback of `withTopRealPart f`.
  have hφ' : ConvexOn ℝ Q' (fun p : Λ × E ↦ withTopRealPart f p.2) := by
    refine ⟨hQ', ?_⟩
    intro p hp q hq a b ha hb hab
    exact hf.2 hp.2 hq.2 ha hb hab
  -- Apply the real-valued owner theorem on the restricted fiber set and transport back.
  rw [affinePartialInfProjection_eq_restricted_realProjection (A := A) (f := f) (Q := Q)]
  simpa [Q']
    using
      (partialInfProjection_convexOn
        (Q := Q')
        (φ := fun p : Λ × E ↦ withTopRealPart f p.2)
        hQ' hφ')

end AffineProjection

section Subgradient

variable {E : Type u} {Λ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ Λ]
variable {f : E → WithTop ℝ} {Q : Set E} (A : E →ₗ[ℝ] Λ)

/-- Helper for Theorem 3.35: a finite affine partial-infimal-projection value comes from a
feasible point where `f` is finite. -/
-- Proof sketch: after restricting to the finite-value locus from
-- `affinePartialInfProjection_eq_restricted_realProjection`, an empty fiber would force the
-- partial infimum to be `⊤`, contradicting membership in the effective domain.
lemma exists_feasible_point_of_mem_dom_affinePartialInfProjection
    {v : Λ}
    (hv :
      v ∈ dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))) :
    ∃ x : E, x ∈ linearEqualityFeasibleSet Q A v ∧ x ∈ dom f := by
  let Q' : Set (Λ × E) :=
    {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
  have hv' :
      v ∈ dom
        (partialInfProjection
          Q'
          (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2)) := by
    rw [affinePartialInfProjection_eq_restricted_realProjection (A := A) (f := f) (Q := Q)] at hv
    exact hv
  let S : Set (Λ × E) := {z : Λ × E | z ∈ Q' ∧ z.1 = v}
  -- The restricted fiber cannot be empty because an empty fiber has infimum `⊤`.
  have hS_nonempty : S.Nonempty := by
    by_contra hS
    have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have htop :
        partialInfProjection Q' (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2) v = ⊤ := by
      rw [partialInfProjection_eq_sInf]
      simp [S, hS_empty]
    exact (mem_extendedRealEffectiveDomain_iff.mp hv').1 htop
  rcases hS_nonempty with ⟨z, hz⟩
  have hzFeas : z.2 ∈ linearEqualityFeasibleSet Q A v := by
    simpa [Q', hz.2] using hz.1.1
  exact ⟨z.2, hzFeas, hz.1.2⟩

/-- Helper for Theorem 3.35: the ambient subgradient inequality together with the affine
variational inequality yields the fiberwise lower bound used in the projected subgradient proof.
-/
-- Proof sketch: the subgradient inequality controls `f` by `gStar`, the variational inequality
-- replaces `gStar` by `Aᵀ yStar` on `Q`, and the adjoint identity turns that into the base-space
-- pairing `⟪yStar, v - u⟫`.
lemma affine_fiber_lower_bound_of_variational_inequality
    {u v : Λ} {xStar gStar x : E} {yStar : Λ}
    (hxStar : xStar ∈ linearEqualityFeasibleSet Q A u)
    (hgStar : gStar ∈ ∂ f(xStar))
    (hvar :
      ∀ z : E, z ∈ Q →
        0 ≤ inner ℝ (gStar - A.adjoint yStar) (z - xStar))
    (hx : x ∈ linearEqualityFeasibleSet Q A v)
    (hxDom : x ∈ dom f) :
    withTopRealPart f xStar + inner ℝ yStar (v - u) ≤ withTopRealPart f x := by
  have hxStarDom : xStar ∈ dom f := (mem_subdifferential_iff.mp hgStar).mem_dom
  rcases hxStar with ⟨hxStarQ, hxStarA⟩
  rcases hx with ⟨hxQ, hxA⟩
  -- Translate the ambient subgradient inequality to the finite real part on `dom f`.
  have hsupport :
      withTopRealPart f x ≥ withTopRealPart f xStar + inner ℝ gStar (x - xStar) := by
    have hsub := (mem_subdifferential_iff.mp hgStar).2 hxDom
    rw [← coe_withTopRealPart (f := f) hxDom, ← coe_withTopRealPart (f := f) hxStarDom] at hsub
    exact_mod_cast hsub
  -- The variational inequality removes the normal component from `gStar`.
  have hnormal :
      inner ℝ (A.adjoint yStar) (x - xStar) ≤ inner ℝ gStar (x - xStar) := by
    have hvarx := hvar x hxQ
    rw [inner_sub_left] at hvarx
    linarith
  have hbase :
      inner ℝ yStar (v - u) = inner ℝ (A.adjoint yStar) (x - xStar) := by
    calc
      inner ℝ yStar (v - u)
          = inner ℝ yStar (A x - A xStar) := by simpa [hxA, hxStarA]
      _ = inner ℝ yStar (A (x - xStar)) := by simp [map_sub]
      _ = inner ℝ (A.adjoint yStar) (x - xStar) := by
            rw [A.adjoint_inner_left]
  have hreal :
      withTopRealPart f xStar + inner ℝ (A.adjoint yStar) (x - xStar) ≤ withTopRealPart f x := by
    linarith
  simpa [hbase] using hreal

/-- A feasible primal point `xStar` on the fiber `A x = u` with a primal
subgradient `gStar ∈ ∂ f(xStar)` whose affine-constraint variational inequality holds on `Q`, then
the multiplier `yStar` is a relative subgradient of the finite real part of the canonical
affine-fiber infimal projection on its finite-value domain. -/
-- Proof sketch: convert the affine-fiber value function to the chapter `partialInfProjection`
-- owner and check that the displayed inequality is exactly the lower-support condition defining
-- membership in the relative subdifferential of the specialized `partialInfProjection`.
theorem mem_subdifferentialWithin_affinePartialInfProjection_of_variational_inequality
    {u : Λ}
    {xStar gStar : E} {yStar : Λ}
    (hxStar : xStar ∈ linearEqualityFeasibleSet Q A u)
    (hgStar : gStar ∈ ∂ f(xStar))
    (hvar :
      ∀ x : E, x ∈ Q →
        0 ≤ inner ℝ (gStar - A.adjoint yStar) (x - xStar)) :
    yStar ∈
      ∂[dom
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
            (withTopToEReal ∘ f ∘ Prod.snd))]
        (extendedRealRealPart
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
            (withTopToEReal ∘ f ∘ Prod.snd)))
        (u) :=
      by
  let ψ : Λ → EReal :=
    partialInfProjection
      {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
      (withTopToEReal ∘ f ∘ Prod.snd)
  change yStar ∈ ∂[dom ψ] (extendedRealRealPart ψ) (u)
  have hxStarDom : xStar ∈ dom f := (mem_subdifferential_iff.mp hgStar).mem_dom
  have hxStarValue : ((withTopRealPart f xStar : ℝ) : EReal) = withTopToEReal (f xStar) := by
    simpa [withTopToEReal] using congrArg withTopToEReal (coe_withTopRealPart (f := f) hxStarDom)
  let Su : Set EReal :=
    (withTopToEReal ∘ f ∘ Prod.snd) '' {z : Λ × E |
      z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.1 = u}
  -- Every point on the `u`-fiber lies above `f xStar`, so the projected value at `u` is finite
  -- and equal to the finite value achieved by `xStar`.
  have hSu_nonempty : Su.Nonempty := by
    refine ⟨withTopToEReal (f xStar), ⟨(u, xStar), ?_, rfl⟩⟩
    exact ⟨hxStar, rfl⟩
  have hSu_lower :
      ∀ b ∈ Su, (((withTopRealPart f xStar : ℝ) : EReal)) ≤ b := by
    intro b hb
    rcases hb with ⟨z, hz, rfl⟩
    by_cases hzDom : z.2 ∈ dom f
    · have hzFeas : z.2 ∈ linearEqualityFeasibleSet Q A u := by
        simpa [hz.2] using hz.1
      have hreal :
          withTopRealPart f xStar ≤ withTopRealPart f z.2 := by
        simpa using
          (affine_fiber_lower_bound_of_variational_inequality
            (A := A) (Q := Q) (f := f)
            (hxStar := hxStar) (hgStar := hgStar) (hvar := hvar)
            (hx := hzFeas) (hxDom := hzDom) (u := u) (v := u) (yStar := yStar))
      have hzValue : ((withTopRealPart f z.2 : ℝ) : EReal) = withTopToEReal (f z.2) := by
        simpa [withTopToEReal] using
          congrArg withTopToEReal (coe_withTopRealPart (f := f) hzDom)
      change ((withTopRealPart f xStar : ℝ) : EReal) ≤ withTopToEReal (f z.2)
      rw [← hzValue]
      exact_mod_cast hreal
    · rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hzDom
      have hzTop : f z.2 = ⊤ := by
        simpa using hzDom
      change ((withTopRealPart f xStar : ℝ) : EReal) ≤ withTopToEReal (f z.2)
      rw [hzTop, withTopToEReal]
      exact le_top
  have hSu_bddBelow : BddBelow Su := ⟨((withTopRealPart f xStar : ℝ) : EReal), hSu_lower⟩
  have hψu_lower : ((withTopRealPart f xStar : ℝ) : EReal) ≤ ψ u := by
    simpa [ψ, Su, partialInfProjection_eq_sInf] using le_csInf hSu_nonempty hSu_lower
  have hψu_upper : ψ u ≤ ((withTopRealPart f xStar : ℝ) : EReal) := by
    have hxStar_mem : withTopToEReal (f xStar) ∈ Su := by
      refine ⟨(u, xStar), ?_, rfl⟩
      exact ⟨hxStar, rfl⟩
    have htmp : ψ u ≤ withTopToEReal (f xStar) := by
      simpa [ψ, Su, partialInfProjection_eq_sInf] using csInf_le hSu_bddBelow hxStar_mem
    rw [← hxStarValue] at htmp
    exact htmp
  have hψu : ψ u = ((withTopRealPart f xStar : ℝ) : EReal) := le_antisymm hψu_upper hψu_lower
  have huDom : u ∈ dom ψ := by
    rw [mem_extendedRealEffectiveDomain_iff, hψu]
    constructor <;> simp
  have hψuReal : extendedRealRealPart ψ u = withTopRealPart f xStar := by
    apply EReal.coe_injective
    rw [coe_extendedRealRealPart huDom, hψu]
  rw [mem_subdifferentialWithin_iff]
  refine ⟨huDom, ?_⟩
  intro v hv
  rcases exists_feasible_point_of_mem_dom_affinePartialInfProjection
      (A := A) (Q := Q) (f := f) hv with ⟨xv, hxv, hxvDom⟩
  let Sv : Set EReal :=
    (withTopToEReal ∘ f ∘ Prod.snd) '' {z : Λ × E |
      z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.1 = v}
  -- The same fiberwise lower-bound argument gives the projected support inequality at every
  -- finite base point `v`.
  have hSv_nonempty : Sv.Nonempty := by
    refine ⟨withTopToEReal (f xv), ⟨(v, xv), ?_, rfl⟩⟩
    exact ⟨hxv, rfl⟩
  have hSv_lower :
      ∀ b ∈ Sv, (((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal)) ≤ b := by
    intro b hb
    rcases hb with ⟨z, hz, rfl⟩
    by_cases hzDom : z.2 ∈ dom f
    · have hzFeas : z.2 ∈ linearEqualityFeasibleSet Q A v := by
        simpa [hz.2] using hz.1
      have hreal :=
        affine_fiber_lower_bound_of_variational_inequality
          (A := A) (Q := Q) (f := f)
          (hxStar := hxStar) (hgStar := hgStar) (hvar := hvar)
          (hx := hzFeas) (hxDom := hzDom) (u := u) (v := v) (yStar := yStar)
      have hzValue : ((withTopRealPart f z.2 : ℝ) : EReal) = withTopToEReal (f z.2) := by
        simpa [withTopToEReal] using
          congrArg withTopToEReal (coe_withTopRealPart (f := f) hzDom)
      change ((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal) ≤ withTopToEReal (f z.2)
      rw [← hzValue]
      exact_mod_cast hreal
    · rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hzDom
      have hzTop : f z.2 = ⊤ := by
        simpa using hzDom
      change ((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal) ≤ withTopToEReal (f z.2)
      rw [hzTop, withTopToEReal]
      exact le_top
  have hψvLower :
      (((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal)) ≤ ψ v := by
    simpa [ψ, Sv, partialInfProjection_eq_sInf] using le_csInf hSv_nonempty hSv_lower
  have hsupport :
      withTopRealPart f xStar + inner ℝ yStar (v - u) ≤ extendedRealRealPart ψ v := by
    have hE :
        (((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal)) ≤
          ((extendedRealRealPart ψ v : ℝ) : EReal) := by
      calc
        (((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal)) ≤ ψ v := hψvLower
        _ = ((extendedRealRealPart ψ v : ℝ) : EReal) := by
            symm
            exact coe_extendedRealRealPart hv
    exact_mod_cast hE
  rw [hψuReal]
  simpa [add_comm, add_left_comm, add_assoc] using hsupport

/-- The multiplier candidates arising from feasible primal points, primal subgradients, and the
affine-constraint variational inequality on `Q` lie in the relative subdifferential of the
projected value function on its finite-value domain. The candidate set is kept inline because it
is only a source-facing bridge to the canonical owner surface given by the specialized
`partialInfProjection`, not an independent owner of its own. -/
-- Proof sketch: unpack a candidate multiplier into a feasible primal point and subgradient, then
-- apply `mem_subdifferentialWithin_affinePartialInfProjection_of_variational_inequality`.
theorem affineMultiplierCandidates_subset_subdifferentialWithin_affinePartialInfProjection
    (u : Λ) :
    {yStar : Λ | ∃ xStar : E, xStar ∈ linearEqualityFeasibleSet Q A u ∧
        ∃ gStar : E, gStar ∈ ∂ f(xStar) ∧
          ∀ x : E, x ∈ Q →
            0 ≤ inner ℝ (gStar - A.adjoint yStar) (x - xStar)} ⊆
      ∂[dom
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
            (withTopToEReal ∘ f ∘ Prod.snd))]
        (extendedRealRealPart
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
            (withTopToEReal ∘ f ∘ Prod.snd)))
        (u) := by
  intro yStar hyStar
  rcases hyStar with ⟨xStar, hxStar, gStar, hgStar, hvar⟩
  -- Unpack the candidate data and invoke the affine-fiber multiplier criterion proved above.
  exact mem_subdifferentialWithin_affinePartialInfProjection_of_variational_inequality
    (A := A) (Q := Q) (f := f) (u := u)
    (hxStar := hxStar) (hgStar := hgStar) (hvar := hvar)

end Subgradient

end
