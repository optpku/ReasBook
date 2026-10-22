/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

open InnerProductSpace
open scoped Pointwise Set

/- Source/core/bridge triage:
- `source-facing`: `GateauxDifferentiableAt` is the Chapter 17 Gâteaux-differentiability owner for
  convex `]-∞,+∞]`-valued functions, namely the existence of a continuous linear map whose values
  realize all directional derivatives from Definition 17.1. Proposition 17.48 then records the
  regularity consequences of that source notion.
- `core/canonical`: the owner abstractions are `GateauxDifferentiableAt`,
  `directionalDerivative`, `∂`,
  `LowerSemicontinuousAt`, and `interior (effectiveDomain f)`.
- `bridge/view`: `ERealFunction.GateauxDifferentiableAt.toReal` sends the source
  directional-derivative formulation to the Chapter 2 owner `_root_.GateauxDifferentiableAt`.
  Proposition 17.2 identifies source directional derivatives with the canonical owner
  `directionalDerivative`, Proposition 17.14 turns the resulting linear minorant into a
  subgradient, Proposition 16.4 turns subdifferentiability into lower semicontinuity, and
  Fact 6.14 plus Corollary 8.39 supply the finite-dimensional interior/continuity
  consequences. -/

section DifferentiabilityAndContinuity

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Gâteaux differentiability for an extended-real-valued function at `x`: a continuous linear map
realizes all directional derivatives from Definition 17.1. -/
def GateauxDifferentiableAt (f : H → Set.Ioi (⊥ : EReal)) (x : H) : Prop :=
  ∃ A : H →L[ℝ] ℝ, ∀ y : H, HasDirectionalDerivativeAt f x y (A y : EReal)

/-- Unfolding `GateauxDifferentiableAt` recovers the source existential linear-map formulation. -/
theorem gateauxDifferentiableAt_iff
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    GateauxDifferentiableAt f x ↔
      ∃ A : H →L[ℝ] ℝ, ∀ y : H, HasDirectionalDerivativeAt f x y (A y : EReal) :=
  Iff.rfl

private theorem quotient_eq_coe_toReal_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H} (hx : x ∈ effectiveDomain f)
    {α : ℝ} (hα : 0 < α) (hαdom : x + α • y ∈ effectiveDomain f) :
    ((f (x + α • y) : EReal) - (f x : EReal)) / α =
      ((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
  have _ : α ≠ 0 := hα.ne'
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hαdom_top : (f (x + α • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hαdom)
  have hαdom_bot : (f (x + α • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + α • y) : EReal) from (f (x + α • y)).2)
  rw [← EReal.coe_toReal hαdom_top hαdom_bot, ← EReal.coe_toReal hx_top hx_bot,
    ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Gâteaux differentiability already places `x` in the effective domain because each directional
derivative in Definition 17.1 is only defined there. -/
theorem GateauxDifferentiableAt.mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hdiff : GateauxDifferentiableAt f x) :
    x ∈ effectiveDomain f := by
  rcases hdiff with ⟨_, hA⟩
  exact (hA 0).1

/-- Extended-real Gâteaux differentiability yields the Chapter 2 canonical
`_root_.GateauxDifferentiableAt` owner for the finite real representative of `f`. -/
theorem GateauxDifferentiableAt.toReal
    {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hdiff : GateauxDifferentiableAt f x) :
    _root_.GateauxDifferentiableAt (fun z ↦ (f z : EReal).toReal) x := by
  rcases hdiff with ⟨A, hA⟩
  refine ⟨A, (hasGateauxDerivativeAt_iff_tendsto_directionalDifferenceQuotient).2 ?_⟩
  intro y
  rcases hA y with ⟨hx, hA'⟩
  let q : ℝ → EReal := fun α ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α
  let r : ℝ → ℝ := fun α ↦ ((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α
  have hfinite :
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), q α ∈ Set.Ioo (⊥ : EReal) ⊤ := by
    refine hA' (isOpen_Ioo.mem_nhds ?_)
    simp
  have hdom :
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • y ∈ effectiveDomain f := by
    filter_upwards [hfinite, self_mem_nhdsWithin] with α hαfinite hα
    rw [mem_effectiveDomain_iff]
    by_contra hαdom
    have hαtop : (f (x + α • y) : EReal) = ⊤ := le_antisymm le_top (not_lt.mp hαdom)
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hqtop : q α = ⊤ := by
      dsimp [q]
      rw [hαtop, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top]
      · exact_mod_cast hα
      · exact EReal.coe_ne_top α
    exact hαfinite.2.ne hqtop
  have hEq :
      (fun α ↦ (r α : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] q := by
    filter_upwards [hdom, self_mem_nhdsWithin] with α hαdom hα
    dsimp [q, r]
    simpa using
      (quotient_eq_coe_toReal_of_mem_effectiveDomain f hx hα hαdom).symm
  have hEq' :
      q =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun α ↦ (r α : EReal)) :=
    hEq.symm
  have hcoe :
      Filter.Tendsto (fun α ↦ (r α : EReal)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (A y : EReal)) :=
    Filter.Tendsto.congr' hEq' hA'
  have hreal : Filter.Tendsto r (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) :=
    EReal.tendsto_coe.mp hcoe
  simpa [r, one_div, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hreal

-- Proof sketch: source Gâteaux differentiability gives a finite directional derivative in every
-- direction. Proposition 17.2 identifies those values with the canonical directional derivative,
-- so every direction lies in `dom (directionalDerivative f x)`. Proposition 17.2 (8) then yields
-- `cone (effectiveDomain f - {x}) = univ`, which is exactly `x ∈ core (effectiveDomain f)`.
/-- Source Gâteaux differentiability of a convex `]-∞,+∞]`-valued function forces the base point to
lie in the algebraic core of its effective domain. -/
theorem mem_core_effectiveDomain_of_convexOn_of_gateauxDifferentiableAt
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hdiff : GateauxDifferentiableAt f x) :
    x ∈ Set.core (effectiveDomain f) := by
  have hx : x ∈ effectiveDomain f := hdiff.mem_effectiveDomain
  rcases hdiff with ⟨A, hA⟩
  rw [Set.mem_core_iff]
  refine ⟨hx, ?_⟩
  ext y
  constructor
  · intro hy
    simp
  · intro hy
    have hy_dom : y ∈ dom (directionalDerivative f x) := by
      rw [mem_dom_iff]
      rw [directionalDerivative_eq_of_hasDirectionalDerivativeAt f hconv (hA y)]
      exact EReal.coe_lt_top (A y)
    rw [dom_directionalDerivative_eq_cone_effectiveDomain_sub_singleton hconv hx] at hy_dom
    simpa using hy_dom

end DifferentiabilityAndContinuity

section LowerSemicontinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H]

-- Proof sketch: represent the chosen source derivative map by its Riesz vector `gradf`. For each
-- direction `y`, Proposition 17.2 rewrites the source derivative value as `f′(x; y)`, so
-- Proposition 17.14 identifies `gradf` as a subgradient at `x`. Proposition 16.4 (5) then yields
-- lower semicontinuity at `x`.
/-- Proposition 17.48 (1): clause (i). If a convex `]-∞,+∞]`-valued function is Gâteaux
differentiable at an effective-domain point `x` in the source Chapter 17 sense, then it is lower
semicontinuous at `x`. -/
theorem lowerSemicontinuousAt_of_convexOn_of_gateauxDifferentiableAt
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hdiff : GateauxDifferentiableAt f x) :
    LowerSemicontinuousAt f.asEReal x := by
  have hx : x ∈ effectiveDomain f := hdiff.mem_effectiveDomain
  rcases hdiff with ⟨A, hA⟩
  let gradf : H := (toDual ℝ H).symm A
  have hgradf : toDual ℝ H gradf = A := by
    simp [gradf]
  have hsub : gradf ∈ (∂ f) x := by
    refine (mem_subdifferential_iff_inner_le_directionalDerivative f hx).2 ?_
    intro y
    have hdir : f′(x; y) = (A y : EReal) :=
      directionalDerivative_eq_of_hasDirectionalDerivativeAt f hconv (hA y)
    have hle : ((toDual ℝ H gradf) y : EReal) ≤ f′(x; y) := by
      simpa [hgradf] using (le_of_eq hdir.symm)
    simpa [toDual_apply_apply, real_inner_comm] using hle
  have hsubdiff : SubdifferentiableAt f x := ⟨gradf, hsub⟩
  exact hsubdiff.lowerSemicontinuousAt

end LowerSemicontinuity

section FiniteDimensional

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

omit [FiniteDimensional ℝ H] in
private theorem cone_eq_toCone_of_convex {C : Set H} (hC_convex : Convex ℝ C) :
    cone C = ((hC_convex.toCone C : ConvexCone ℝ H) : Set H) := by
  have hHull :
      (ConvexCone.hull ℝ C : Set H) = ((hC_convex.toCone C : ConvexCone ℝ H) : Set H) := by
    simpa [ConvexCone.hull] using
      congrArg (fun S : ConvexCone ℝ H ↦ (S : Set H)) hC_convex.toCone_eq_sInf.symm
  simpa [Set.cone_def] using hHull

omit [FiniteDimensional ℝ H] in
private theorem zero_mem_interior_of_convex_of_nonempty_interior_of_cone_eq_univ {C : Set H}
    (hC_convex : Convex ℝ C) (hC_int_nonempty : (interior C).Nonempty)
    (hcone : cone C = (Set.univ : Set H)) :
    (0 : H) ∈ interior C := by
  rcases hC_int_nonempty with ⟨z, hz⟩
  have hnegz : -z ∈ cone C := by
    rw [hcone]
    simp
  rw [cone_eq_toCone_of_convex hC_convex] at hnegz
  rcases (Convex.mem_toCone hC_convex).1 hnegz with ⟨c, hc, y, hy, hcy⟩
  have ha : 0 ≤ c / (c + 1) := by positivity
  have hb : 0 < 1 / (c + 1) := by positivity
  have hab : c / (c + 1) + 1 / (c + 1) = (1 : ℝ) := by
    field_simp [hc.ne']
  have hcombo :
      (c / (c + 1)) • y + (1 / (c + 1)) • z ∈ interior C :=
    hC_convex.combo_self_interior_mem_interior hy hz ha hb hab
  have hzero :
      (c / (c + 1)) • y + (1 / (c + 1)) • z = (0 : H) := by
    calc
      (c / (c + 1)) • y + (1 / (c + 1)) • z
          = (1 / (c + 1)) • (c • y) + (1 / (c + 1)) • z := by
              rw [div_eq_mul_inv, one_div, smul_smul, mul_comm c ((c + 1)⁻¹)]
      _ = (1 / (c + 1)) • (c • y + z) := by rw [smul_add]
      _ = (0 : H) := by rw [hcy, neg_add_cancel, smul_zero]
  exact hzero ▸ hcombo

omit [NormedSpace ℝ H] [FiniteDimensional ℝ H] in
private theorem preimage_addLeft_eq_sub_singleton (C : Set H) (a : H) :
    (Homeomorph.addLeft a) ⁻¹' C = C - ({a} : Set H) := by
  ext y
  constructor
  · intro hy
    refine Set.mem_sub.mpr ?_
    refine ⟨a + y, hy, a, by simp, ?_⟩
    simp [sub_eq_add_neg, add_assoc]
  · rintro ⟨u, hu, v, hv, huv⟩
    have huv' : u = v + y := by
      simpa [sub_eq_add_neg, add_assoc] using congrArg (fun z ↦ v + z) huv
    rcases Set.mem_singleton_iff.mp hv with rfl
    simpa [huv'] using hu

omit [FiniteDimensional ℝ H] in
private theorem mem_interior_of_mem_core_of_convex_of_nonempty_interior {C : Set H}
    (hC_convex : Convex ℝ C) (hC_int_nonempty : (interior C).Nonempty) {x : H}
    (hxcore : x ∈ Set.core C) :
    x ∈ interior C := by
  rcases Set.mem_core_iff.mp hxcore with ⟨hxC, hcone⟩
  let S : Set H := (Homeomorph.addLeft x) ⁻¹' C
  have hS_eq : S = C - ({x} : Set H) := preimage_addLeft_eq_sub_singleton C x
  have hS_convex : Convex ℝ S := by
    simpa [S, add_comm] using hC_convex.translate_preimage_right x
  have hS_int_nonempty : (interior S).Nonempty := by
    rcases hC_int_nonempty with ⟨z, hz⟩
    refine ⟨z - x, ?_⟩
    have hz_pre : z - x ∈ (Homeomorph.addLeft x) ⁻¹' interior C := by
      simpa [sub_eq_add_neg, add_assoc] using hz
    have hz_int : z - x ∈ interior ((Homeomorph.addLeft x) ⁻¹' C) := by
      rwa [(Homeomorph.addLeft x).preimage_interior C] at hz_pre
    simpa [S] using hz_int
  have h0S : (0 : H) ∈ S := by simpa [S] using hxC
  have h0_int : (0 : H) ∈ interior S := by
    have hconeS : cone S = (Set.univ : Set H) := by simpa [hS_eq] using hcone
    exact
      zero_mem_interior_of_convex_of_nonempty_interior_of_cone_eq_univ
        hS_convex hS_int_nonempty hconeS
  have hx_img : x ∈ (Homeomorph.addLeft x) '' interior S := ⟨0, h0_int, by simp⟩
  have himageS : (Homeomorph.addLeft x) '' S = C := by
    simpa [S] using Set.image_preimage_eq C (Homeomorph.addLeft x).surjective
  have himageInt : (Homeomorph.addLeft x) '' interior S = interior C := by
    rw [(Homeomorph.addLeft x).image_interior, himageS]
  rw [← himageInt]
  exact hx_img

-- Proof sketch: source Gâteaux differentiability gives a finite directional derivative in every
-- direction. Proposition 17.2 identifies those values with the canonical directional derivative,
-- so every direction lies in `dom (directionalDerivative f x)`. Proposition 17.2 (8) then yields
-- `cone (effectiveDomain f - {x}) = univ`, i.e. `x ∈ core (effectiveDomain f)`. In finite
-- dimension this cone equality forces the affine span of `effectiveDomain f` to be all of `H`,
-- hence `interior (effectiveDomain f)` is nonempty; the convex-set core/interior bridge then
-- upgrades core membership to interior membership.
/-- Proposition 17.48 (2): clause (ii). In finite dimension, a Gâteaux differentiability point of
a convex `]-∞,+∞]`-valued function lies in the interior of its effective domain. The
differentiability hypothesis is again the source Chapter 17 notion. -/
theorem mem_interior_effectiveDomain_of_convexOn_of_gateauxDifferentiableAt
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hdiff : GateauxDifferentiableAt f x) :
    x ∈ interior (effectiveDomain f) := by
  have hx : x ∈ effectiveDomain f := hdiff.mem_effectiveDomain
  have hxcore : x ∈ Set.core (effectiveDomain f) :=
    mem_core_effectiveDomain_of_convexOn_of_gateauxDifferentiableAt f hconv hdiff
  have hInt_nonempty : (interior (effectiveDomain f)).Nonempty := by
    rcases Set.mem_core_iff.mp hxcore with ⟨_, hcone⟩
    have hspanTopLe :
        (⊤ : Submodule ℝ H) ≤ Submodule.span ℝ (effectiveDomain f - ({x} : Set H)) := by
      intro y hy
      have hy_cone : y ∈ cone (effectiveDomain f - ({x} : Set H)) := by
        have hy_univ : y ∈ (Set.univ : Set H) := by simp
        rwa [← hcone] at hy_univ
      have hy_span :
          y ∈ ((Submodule.span ℝ (effectiveDomain f - ({x} : Set H))).toConvexCone : Set H) :=
        ConvexCone.hull_min (fun z hz ↦ Submodule.subset_span hz) hy_cone
      exact hy_span
    have hspanTop : Submodule.span ℝ (effectiveDomain f - ({x} : Set H)) = ⊤ :=
      top_le_iff.mp hspanTopLe
    have hvectorTop : vectorSpan ℝ (effectiveDomain f) = ⊤ := by
      rw [vectorSpan_eq_span_vsub_set_right ℝ hx]
      simpa [vsub_eq_sub] using hspanTop
    have haffTop : affineSpan ℝ (effectiveDomain f) = ⊤ := by
      exact
        (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ H H ⟨x, hx⟩).2
          hvectorTop
    exact (Convex.interior_nonempty_iff_affineSpan_eq_top hconv.convex_effectiveDomain).2 haffTop
  exact
    mem_interior_of_mem_core_of_convex_of_nonempty_interior
      hconv.convex_effectiveDomain hInt_nonempty hxcore

-- Proof sketch: clause (iii) is exactly the canonical finite-dimensional continuity theorem for
-- the finite representative of a convex function on the interior of its effective domain.
/- Proposition 17.48 (3): in finite dimension, the finite-valued representative of a convex
`]-∞,+∞]`-valued function is continuous on the interior of its effective domain. This is exactly
`_root_.ConvexOn.continuousOn_interior` applied to `hconv.toReal_convexOn_effectiveDomain`. -/
#check _root_.ConvexOn.continuousOn_interior

end FiniteDimensional

end ERealFunction
