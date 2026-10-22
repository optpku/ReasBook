/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin ConvexAnalysis WithTopConvexAnalysis

universe u v

/- Theorem 3.1.25 lies in the chapter's partial-infimal-projection / subdifferential-transfer
domain.

Sampled owner-style declarations:
- `partialInfProjection` in `Theorem_3_1_2_3`, the canonical `EReal` owner for fiberwise infima;
- `partialInfProjection_convexOn_of_convexWithTop` in `Theorem_3_8`, the canonical convexity
  theorem for `WithTop` objectives on that owner;
- `ClosedConvexOn.convexOn_withTopRealPart` in `Definition_3_1_1_5`, the chapter bridge from a
  closed-convex owner to the primitive convexity input `ConvexOn ℝ (dom φ) (withTopRealPart φ)`;
- `constrainedArgmin` with notation `argmin[Q]` in `Chap01/Definition_1_3_3`, the project owner
  for minimizer sets on a feasible set;
- `subdifferential` with notation `∂ f(x)` and `subdifferentialWithin` in `Definition_3_1_5` and
  `Theorem_3_44`, the chapter owners for ambient and relative subgradients.

Best owner abstraction:
- core/canonical: `partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)`, together with
  `ConvexOn ℝ (dom φ) (withTopRealPart φ)`, `argmin[Q₂] (fun y ↦ φ (x, y))`, the ambient
  subdifferential of the intrinsic `WithLp 2 (X × Y)` lift of `φ`, and `subdifferentialWithin`;
- bridge/view: the finite real part
  `extendedRealRealPart (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))`.

Primitive data:
- the fiber constraint `Q₂`;
- the product objective `φ : X × Y → WithTop ℝ`;
- a convex set `Q₁` on which the infimal projection is known to be finite.

Derived API:
- the convexity and subgradient-transfer theorems below for the finite real part of the canonical
  owner.

Source/core/bridge triage:
- source-facing: Theorem 3.1.25's real-valued partial value function and its subgradient
  consequence;
- core/canonical: `ConvexOn ℝ (dom φ) (withTopRealPart φ)`, `partialInfProjection`, `argmin`,
  `∂`, and `subdifferentialWithin`;
- bridge/view: `ClosedConvexOn.convexOn_withTopRealPart` and `extendedRealRealPart` applied to the
  owner `partialInfProjection`.

The previous file rebuilt local owners for the effective domain, closed convexity, fiberwise
argmin, ambient subdifferential, and relative subdifferential. Those notions are already owned
upstream, and the remaining one-off real-valued wrapper around `partialInfProjection` was also
redundant. This refinement deletes that wrapper and keeps the canonical owner expression directly
on the public theorem surface.
-/

section Convexity

variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]

variable {Q₁ : Set X} {Q₂ : Set Y} {φ : X × Y → WithTop ℝ}

/-- Theorem 3.1.25 (1): if `φ : X × Y → (-∞, +∞]` is convex on its effective domain and the
canonical infimal projection over `Q₂` is finite on `Q₁`, then its finite real part is convex on
`Q₁`. -/
-- Proof sketch: apply `partialInfProjection_convexOn_of_convexWithTop` to the convex feasible set
-- `Set.univ ×ˢ Q₂`, and then restrict the resulting owner `ConvexOn` statement from
-- `dom (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))` to the convex subset `Q₁`.
theorem partialInfProjection_realPart_convexOn_of_convexWithTop
    (hφ : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hfinite :
      Q₁ ⊆ dom (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))) :
    ConvexOn ℝ Q₁
      (extendedRealRealPart (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))) := by
  let ψ : X → EReal := partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)
  -- The owner convexity theorem already gives convexity on the finite-value domain of `ψ`.
  have hψ_convex : ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ) :=
    partialInfProjection_convexOn_of_convexWithTop
      (Q := Set.univ ×ˢ Q₂)
      (φ := φ)
      (convex_univ.prod hQ₂_convex) hφ
  -- Restrict the owner convexity statement from `dom ψ` to the prescribed finite subset `Q₁`.
  refine ⟨hQ₁_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  exact hψ_convex.2 (hfinite hx) (hfinite hy) ha hb hab

end Convexity

/-
Theorem 3.1.25 (2) is a direct subgradient-transfer statement. Its primitive data are the
finiteness of the projected value function on `Q₁`, the fiberwise argmin set, and the ambient
subgradient/variational-inequality hypotheses. The closed-convex and convex-set assumptions from
part (1) are derived proof context rather than part of this theorem's owner-level interface.
-/
section Subgradient

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

variable {Q₁ : Set X} {Q₂ : Set Y} {φ : X × Y → WithTop ℝ}

local notation "Z" => WithLp 2 (X × Y)
local notation "toZ" => WithLp.toLp 2

/-- Helper for Theorem 3.1.25: a fiber minimizer realizes the canonical partial-infimal-projection
value on that fiber. -/
lemma partialInfProjection_eq_value_of_mem_argmin
    {x : X} {yx : Y}
    (hyx : yx ∈ argmin[Q₂] (fun y ↦ φ (x, y))) :
    partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ) x =
      withTopToEReal (φ (x, yx)) := by
  let ψ : X → EReal := partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)
  let S : Set EReal :=
    (withTopToEReal ∘ φ) '' {z : X × Y | z ∈ Set.univ ×ˢ Q₂ ∧ z.1 = x}
  rcases mem_constrainedArgmin_iff.mp hyx with ⟨hyxQ, hyxMin⟩
  have hS_nonempty : S.Nonempty := by
    refine ⟨withTopToEReal (φ (x, yx)), ⟨(x, yx), ?_, rfl⟩⟩
    exact ⟨⟨by simp, hyxQ⟩, rfl⟩
  -- Every feasible fiber value lies above the value attained at the minimizing point `yx`.
  have hS_lower : ∀ b ∈ S, withTopToEReal (φ (x, yx)) ≤ b := by
    intro b hb
    rcases hb with ⟨⟨x', y'⟩, hz, rfl⟩
    rcases hz with ⟨hz, hx'⟩
    have hx'' : x' = x := by simpa using hx'
    subst x'
    have hy'Q : y' ∈ Q₂ := hz.2
    have hmin : φ (x, yx) ≤ φ (x, y') := hyxMin hy'Q
    exact
      (show Monotone (fun t : WithTop ℝ ↦ withTopToEReal t) from WithBot.coe_mono) hmin
  have hS_bddBelow : BddBelow S := ⟨withTopToEReal (φ (x, yx)), hS_lower⟩
  have hψ_upper : ψ x ≤ withTopToEReal (φ (x, yx)) := by
    have hmem : withTopToEReal (φ (x, yx)) ∈ S := by
      refine ⟨(x, yx), ?_, rfl⟩
      exact ⟨⟨by simp, hyxQ⟩, rfl⟩
    simpa [ψ, S, partialInfProjection_eq_sInf] using csInf_le hS_bddBelow hmem
  have hψ_lower : withTopToEReal (φ (x, yx)) ≤ ψ x := by
    simpa [ψ, S, partialInfProjection_eq_sInf] using le_csInf hS_nonempty hS_lower
  exact le_antisymm hψ_upper hψ_lower

/-- Helper for Theorem 3.1.25: the ambient product-space subgradient inequality together with the
variational inequality in the second variable yields the fiberwise lower bound used in the
projected subgradient proof. -/
lemma fiber_lower_bound_of_subgradient_and_variational_inequality
    {x x₁ : X} {yx y₁ : Y} {gx : X} {gy : Y}
    (hyx_dom : (x, yx) ∈ dom φ)
    (hy₁ : y₁ ∈ Q₂) (hy₁_dom : (x₁, y₁) ∈ dom φ)
    (hg :
      toZ (gx, gy) ∈
        ∂ (fun z : Z ↦ φ (z.fst, z.snd))((toZ (x, yx))))
    (hvar : ∀ ⦃y : Y⦄, y ∈ Q₂ → inner ℝ gy (y - yx) ≥ 0) :
    withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) ≤ withTopRealPart φ (x₁, y₁) := by
  have hyx_domZ : toZ (x, yx) ∈ dom (fun z : Z ↦ φ (z.fst, z.snd)) := by
    simpa using hyx_dom
  have hy₁_domZ : toZ (x₁, y₁) ∈ dom (fun z : Z ↦ φ (z.fst, z.snd)) := by
    simpa using hy₁_dom
  -- Rewrite the ambient subgradient inequality at the finite target point into ordinary real
  -- coordinates.
  have hsupport_withTop :=
    (mem_subdifferential_iff.mp hg).2 hy₁_domZ
  have hsupport :
      withTopRealPart φ (x₁, y₁) ≥
        withTopRealPart φ (x, yx) +
          inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) := by
    have hsupport_withTop' :
        φ (x₁, y₁) ≥
          φ (x, yx) +
            (inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : WithTop ℝ) := by
      simpa using hsupport_withTop
    have hyx_value :
        φ (x, yx) = ((withTopRealPart φ (x, yx) : ℝ) : WithTop ℝ) := by
      simpa using (coe_withTopRealPart (f := φ) hyx_dom).symm
    have hsupport_realTop :
        φ (x₁, y₁) ≥
          ((withTopRealPart φ (x, yx) +
              inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : ℝ) : WithTop ℝ) := by
      calc
        φ (x₁, y₁) ≥
            φ (x, yx) +
              (inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : WithTop ℝ) :=
          hsupport_withTop'
        _ = (((withTopRealPart φ (x, yx) : ℝ) : WithTop ℝ) +
              (inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : WithTop ℝ)) := by
            rw [hyx_value]
        _ = ((withTopRealPart φ (x, yx) +
              inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : ℝ) : WithTop ℝ) := by
            rw [WithTop.coe_add]
    have hy₁_value :
        φ (x₁, y₁) = ((withTopRealPart φ (x₁, y₁) : ℝ) : WithTop ℝ) := by
      simpa using (coe_withTopRealPart (f := φ) hy₁_dom).symm
    have hsupport_realTop' :
        ((withTopRealPart φ (x₁, y₁) : ℝ) : WithTop ℝ) ≥
          ((withTopRealPart φ (x, yx) +
              inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : ℝ) : WithTop ℝ) := by
      calc
        ((withTopRealPart φ (x₁, y₁) : ℝ) : WithTop ℝ) = φ (x₁, y₁) := by
          rw [hy₁_value]
        _ ≥ ((withTopRealPart φ (x, yx) +
            inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : ℝ) : WithTop ℝ) :=
          hsupport_realTop
    exact_mod_cast hsupport_realTop'
  have hsupport' :
      withTopRealPart φ (x₁, y₁) ≥
        withTopRealPart φ (x, yx) +
          inner ℝ gx (x₁ - x) +
            inner ℝ gy (y₁ - yx) := by
    simpa [WithLp.prod_inner_apply, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using
      hsupport
  -- The variational inequality says the second-coordinate contribution is nonnegative.
  have hgy_nonneg : 0 ≤ inner ℝ gy (y₁ - yx) := hvar hy₁
  linarith

/-- Theorem 3.1.25 (2): if `yₓ` minimizes the fiber objective `y ↦ φ (x, y)` on `Q₂`, and if an
ambient subgradient of the intrinsic product-space lift of `φ` at `(x, yₓ)` has components
`(gₓ, g_y)` and satisfies the variational inequality `⟪g_y, y - yₓ⟫ ≥ 0` on `Q₂`, then `gₓ`
belongs to the relative subdifferential of the finite real part of the canonical partial
infimal projection on `Q₁` at `x`. -/
-- Proof sketch: for `x₁ ∈ Q₁`, combine the subgradient inequality for
-- `WithLp.toLp 2 (gₓ, g_y) ∈
-- ∂ (fun z : Z ↦ φ (z.fst, z.snd))((WithLp.toLp 2 (x, yₓ)))` with an almost
-- minimizing fiber point over `x₁`; the
-- variational inequality for `g_y` removes the second-coordinate contribution, and the remaining
-- first-coordinate inequality is exactly the defining condition for
-- `∂[Q₁] (extendedRealRealPart
--   (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))) (x)`.
theorem mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient
    (hfinite :
      Q₁ ⊆ dom (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)))
    {x : X} (hx : x ∈ Q₁)
    {yx : Y} (hyx : yx ∈ argmin[Q₂] (fun y ↦ φ (x, y)))
    {gx : X} {gy : Y}
    (hg :
      WithLp.toLp 2 (gx, gy) ∈
        ∂ (fun z : Z ↦ φ (z.fst, z.snd))((WithLp.toLp 2 (x, yx))))
    (hvar : ∀ ⦃y : Y⦄, y ∈ Q₂ → inner ℝ gy (y - yx) ≥ 0) :
    gx ∈ ∂[Q₁]
      (extendedRealRealPart (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))) (x) :=
      by
  let ψ : X → EReal := partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)
  change gx ∈ ∂[Q₁] (extendedRealRealPart ψ) (x)
  have hxψ : x ∈ dom ψ := hfinite hx
  rcases mem_constrainedArgmin_iff.mp hyx with ⟨hyxQ, _⟩
  -- The minimizing fiber point `yx` realizes the projected value at `x`.
  have hψx : ψ x = withTopToEReal (φ (x, yx)) :=
    partialInfProjection_eq_value_of_mem_argmin (Q₂ := Q₂) (φ := φ) hyx
  have hyx_dom : (x, yx) ∈ dom φ := by
    by_contra hyx_dom
    rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hyx_dom
    have htop : φ (x, yx) = ⊤ := by
      simpa using hyx_dom
    have hψ_top : ψ x = ⊤ := by
      rw [hψx, htop, withTopToEReal]
      rfl
    exact (mem_extendedRealEffectiveDomain_iff.mp hxψ).1 hψ_top
  have hψx_real : extendedRealRealPart ψ x = withTopRealPart φ (x, yx) := by
    apply EReal.coe_injective
    rw [coe_extendedRealRealPart hxψ, hψx]
    simpa [withTopToEReal] using
      (congrArg withTopToEReal (coe_withTopRealPart (f := φ) hyx_dom)).symm
  rw [mem_subdifferentialWithin_iff]
  refine ⟨hx, ?_⟩
  intro x₁ hx₁
  have hx₁ψ : x₁ ∈ dom ψ := hfinite hx₁
  let S : Set EReal :=
    (withTopToEReal ∘ φ) '' {z : X × Y | z ∈ Set.univ ×ˢ Q₂ ∧ z.1 = x₁}
  -- The same feasible minimizer witness `yx ∈ Q₂` makes every fiber set nonempty.
  have hS_nonempty : S.Nonempty := by
    refine ⟨withTopToEReal (φ (x₁, yx)), ⟨(x₁, yx), ?_, rfl⟩⟩
    exact ⟨⟨by simp, hyxQ⟩, rfl⟩
  -- Every fiber value lies above the affine lower support term determined by `gx`.
  have hS_lower :
      ∀ b ∈ S,
        (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤ b := by
    intro b hb
    rcases hb with ⟨⟨x', y'⟩, hz, rfl⟩
    rcases hz with ⟨hz, hx'⟩
    have hx'' : x' = x₁ := by simpa using hx'
    subst x'
    by_cases hy'_dom : (x₁, y') ∈ dom φ
    · have hzQ : y' ∈ Q₂ := hz.2
      have hreal :
          withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) ≤ withTopRealPart φ (x₁, y') := by
        simpa using
          fiber_lower_bound_of_subgradient_and_variational_inequality
            (Q₂ := Q₂) (φ := φ)
            (hyx_dom := hyx_dom) (hy₁ := hzQ) (hy₁_dom := hy'_dom)
            (hg := hg) (hvar := hvar)
      have hzValue :
          ((withTopRealPart φ (x₁, y') : ℝ) : EReal) = withTopToEReal (φ (x₁, y')) := by
        simpa [withTopToEReal] using
          congrArg withTopToEReal (coe_withTopRealPart (f := φ) hy'_dom)
      change (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤
        withTopToEReal (φ (x₁, y'))
      rw [← hzValue]
      exact_mod_cast hreal
    · rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hy'_dom
      have htop : φ (x₁, y') = ⊤ := by
        simpa using hy'_dom
      change (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤
        withTopToEReal (φ (x₁, y'))
      rw [htop, withTopToEReal]
      exact le_top
  have hψx₁_lower :
      (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤ ψ x₁ := by
    simpa [ψ, S, partialInfProjection_eq_sInf] using le_csInf hS_nonempty hS_lower
  -- Convert the `EReal` lower bound back to the real-valued owner surface at the finite point `x₁`.
  have hsupport :
      withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) ≤ extendedRealRealPart ψ x₁ := by
    have hE :
        (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤
          ((extendedRealRealPart ψ x₁ : ℝ) : EReal) := by
      calc
        (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤ ψ x₁ := hψx₁_lower
        _ = ((extendedRealRealPart ψ x₁ : ℝ) : EReal) := by
            symm
            exact coe_extendedRealRealPart hx₁ψ
    exact_mod_cast hE
  rw [hψx_real]
  simpa [add_comm, add_left_comm, add_assoc] using hsupport

/-- A candidate-set repackaging of Theorem 3.1.25 (2): every first-coordinate component arising
from a minimizing fiber point, an ambient subgradient there, and the corresponding variational
inequality on `Q₂` lies in the relative subdifferential of the finite real part of the canonical
partial infimal projection on `Q₁` at `x`. This is a derived bridge, not the main source-facing
theorem. -/
theorem partialInfProjectionSubgradientCandidates_subset_subdifferentialWithin
    (hfinite :
      Q₁ ⊆ dom (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)))
    {x : X} (hx : x ∈ Q₁) :
    {gx : X | ∃ yx : Y, yx ∈ argmin[Q₂] (fun y ↦ φ (x, y)) ∧
        ∃ gy : Y, WithLp.toLp 2 (gx, gy) ∈
            ∂ (fun z : Z ↦ φ (z.fst, z.snd))((WithLp.toLp 2 (x, yx))) ∧
          ∀ ⦃y : Y⦄, y ∈ Q₂ → inner ℝ gy (y - yx) ≥ 0} ⊆
      ∂[Q₁]
        (extendedRealRealPart
          (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))) (x) := by
  intro gx hgx
  rcases hgx with ⟨yx, hyx, gy, hgy, hvar⟩
  exact mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient
    hfinite hx hyx hgy hvar

end Subgradient

end
