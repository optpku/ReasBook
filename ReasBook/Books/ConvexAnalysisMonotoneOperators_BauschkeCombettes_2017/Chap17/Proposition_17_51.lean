/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_39
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Theorem_8_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_50

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityAndContinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.51 assumes Gâteaux differentiability of the extended-real
  function `f` on an open subset `U` of its effective domain in the Chapter 17 sense.
- `core/canonical`: the owner abstractions are `GateauxDifferentiableAt`,
  `LowerSemicontinuousAt`, `Γ₀(H)`, and `ContinuousOn` over `interior (effectiveDomain f)`.
- `bridge/view`: `_root_.GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) U` is only a
  bridge from the finite real representative back to the source owner `GateauxDifferentiableAt`.

Primitive data: the convex function `f`, the open subset `U ⊆ effectiveDomain f`, and source
pointwise Gâteaux differentiability on `U`.
Derived API: lower semicontinuity on the localized indicator sum, membership in `Γ₀(H)`, local
continuity, and finally continuity on `interior (effectiveDomain f)`. -/

omit [CompleteSpace H] in
private theorem quotient_eq_coe_toReal_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H} (hx : x ∈ effectiveDomain f)
    {α : ℝ} (hα : 0 < α) (hαdom : x + α • y ∈ effectiveDomain f) :
    (((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal)) =
      ((f (x + α • y) : EReal) - (f x : EReal)) / α := by
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

omit [CompleteSpace H] in
private theorem hasDirectionalDerivativeAt_of_hasGateauxDerivativeWithinAt_subset_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {U : Set H} {x : H} (hxU : x ∈ U)
    (hU_dom : U ⊆ effectiveDomain f) {A : H →L[ℝ] ℝ}
    (hA : HasGateauxDerivativeWithinAt (fun z ↦ (f z : EReal).toReal) A U x) (y : H) :
    HasDirectionalDerivativeAt f x y (A y : EReal) := by
  have hx : x ∈ effectiveDomain f := hU_dom hxU
  have hreal :
      Filter.Tendsto
        (fun α : ℝ ↦ (((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
    simpa [one_div, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hA.tendsto_directionalDifferenceQuotient y
  have hdom :
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • y ∈ effectiveDomain f := by
    rcases hA.hasRadialSegmentsAt y with ⟨δ, hδ, hseg⟩
    have hδmem : Set.Iio δ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
    filter_upwards [hδmem, self_mem_nhdsWithin] with α hα_lt hα
    exact hU_dom (hseg α ⟨le_of_lt hα, hα_lt.le⟩)
  have hcoe :
      Filter.Tendsto
        (fun α : ℝ ↦
          (((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y : EReal)) :=
    EReal.tendsto_coe.2 hreal
  have hEq :
      (fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun α : ℝ ↦
          (((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal))) := by
    filter_upwards [hdom, self_mem_nhdsWithin] with α hαdom hα
    simpa using
      (quotient_eq_coe_toReal_of_mem_effectiveDomain f hx hα hαdom).symm
  exact ⟨hx, Filter.Tendsto.congr' hEq.symm hcoe⟩

omit [CompleteSpace H] in
theorem gateauxDifferentiableAt_of_toReal_gateauxDifferentiableOn_subset_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {U : Set H} {x : H} (hxU : x ∈ U)
    (hU_dom : U ⊆ effectiveDomain f)
    (hgateaux : GateauxDifferentiableOn (fun z ↦ (f z : EReal).toReal) U) :
    GateauxDifferentiableAt f x := by
  rcases hgateaux x hxU with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  intro y
  exact
    hasDirectionalDerivativeAt_of_hasGateauxDerivativeWithinAt_subset_effectiveDomain
      f hxU hU_dom hA y

-- Proof sketch: choose `x ∈ U`; Proposition 17.48 gives lower semicontinuity of `f` at `x`. On a
-- small ball `C ⊆ U`, the localized function `g = f + ι_C` belongs to `Γ₀(H)`, so Corollary 8.39
-- gives continuity of the finite representative on `interior C`; hence `f` is continuous at `x`.
-- Theorem 8.38 then propagates this local continuity to all of `interior (effectiveDomain f)`.
/-- Proposition 17.51: if a convex `]-∞,+∞]`-valued function is Gâteaux differentiable on a
nonempty open subset `U` of its effective domain, then its finite-valued representative is
continuous on `interior (effectiveDomain f)`. -/
theorem continuousOn_interior_effectiveDomain_of_convexOn_of_nonempty_open_subset_gateauxDifferentiableOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (U : Set H)
    (hU_nonempty : U.Nonempty) (hU_open : IsOpen U) (hU_dom : U ⊆ effectiveDomain f)
    (hgateaux : ∀ x ∈ U, GateauxDifferentiableAt f x) :
    ContinuousOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) := by
  rcases hU_nonempty with ⟨x, hxU⟩
  have hx : x ∈ effectiveDomain f := hU_dom hxU
  rcases Metric.mem_nhds_iff.mp (hU_open.mem_nhds hxU) with ⟨ρ, hρ, hballU⟩
  let r : ℝ := ρ / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr_lt : r < ρ := by
    dsimp [r]
    linarith
  let C : Set H := Metric.closedBall x r
  have hC_nonempty : C.Nonempty := by
    refine ⟨x, ?_⟩
    simp [C, hr.le]
  have hC_closed : IsClosed C := by
    simpa [C] using Metric.isClosed_closedBall
  have hC_convex : Convex ℝ C := by
    simpa [C] using convex_closedBall x r
  have hC_subset_U : C ⊆ U := by
    intro y hy
    exact hballU ((Metric.closedBall_subset_ball hr_lt) hy)
  have hC_dom : C ⊆ effectiveDomain f := hC_subset_U.trans hU_dom
  let g : H → Set.Ioi (⊥ : EReal) := f + indicator C
  have hg_dom : effectiveDomain g = C := by
    ext y
    rw [mem_effectiveDomain_pointwiseAdd_iff, effectiveDomain_indicator]
    constructor
    · intro hy
      exact hy.2
    · intro hy
      exact ⟨hC_dom hy, hy⟩
  have hg_lsc : LowerSemicontinuous (fun y ↦ (g y : EReal)) := by
    rw [lowerSemicontinuous_iff]
    intro y
    by_cases hy : y ∈ C
    · have hyU : y ∈ U := hC_subset_U hy
      have hy_gateaux : GateauxDifferentiableAt f y := hgateaux y hyU
      have hflsc : LowerSemicontinuousAt f.asEReal y :=
        lowerSemicontinuousAt_of_convexOn_of_gateauxDifferentiableAt f hconv hy_gateaux
      rw [lowerSemicontinuousAt_iff] at hflsc ⊢
      intro a ha
      have ha' : a < (f y : EReal) := by
        simpa [g, pointwiseAdd_apply, hy] using ha
      filter_upwards [hflsc a ha'] with z hz
      by_cases hzC : z ∈ C
      · simpa [g, pointwiseAdd_apply, hzC] using hz
      · have hz_top : a < (⊤ : EReal) := lt_of_lt_of_le hz le_top
        have hgz_top : (g z : EReal) = ⊤ := by
          change ((f z : EReal) + (indicator C z : EReal)) = ⊤
          have hfz_ne_bot : (f z : EReal) ≠ ⊥ := by
            exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
          simp [hzC, EReal.add_top_of_ne_bot hfz_ne_bot]
        simpa [hgz_top] using hz_top
    · rw [lowerSemicontinuousAt_iff]
      intro a ha
      have hgy_top : (g y : EReal) = ⊤ := by
        change ((f y : EReal) + (indicator C y : EReal)) = ⊤
        have hfy_ne_bot : (f y : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
        simp [hy, EReal.add_top_of_ne_bot hfy_ne_bot]
      have ha_top : a < (⊤ : EReal) := by
        simpa [hgy_top] using ha
      have hCcompl : Cᶜ ∈ nhds y := hC_closed.isOpen_compl.mem_nhds hy
      filter_upwards [hCcompl] with z hz
      have hzC : z ∉ C := hz
      have hgz_top : (g z : EReal) = ⊤ := by
        change ((f z : EReal) + (indicator C z : EReal)) = ⊤
        have hfz_ne_bot : (f z : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
        simp [hzC, EReal.add_top_of_ne_bot hfz_ne_bot]
      simpa [hgz_top] using ha_top
  have hg_conv : ConvexOn g (effectiveDomain g) := by
    refine ⟨by simpa [hg_dom] using hC_nonempty, ?_, ?_⟩
    · simp [hg_dom]
    · intro y hy z hz α hα0 hα1
      have hyC : y ∈ C := by simpa [hg_dom] using hy
      have hzC : z ∈ C := by simpa [hg_dom] using hz
      have hyf : y ∈ effectiveDomain f := hC_dom hyC
      have hzf : z ∈ effectiveDomain f := hC_dom hzC
      have hαyz : α • y + (1 - α) • z ∈ C :=
        hC_convex hyC hzC hα0.le (sub_nonneg.mpr hα1.le) (by ring)
      simpa [g, pointwiseAdd_apply, hyC, hzC, hαyz] using hconv.ineq hyf hzf hα0 hα1
  have hg_gamma : g ∈ Γ₀(H) := ⟨hg_lsc, hg_conv⟩
  have hxC_int : x ∈ interior C := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds x hr) Metric.ball_subset_closedBall
  have hxg_int : x ∈ interior (effectiveDomain g) := by
    simpa [hg_dom] using hxC_int
  have hxg_cont : ContinuousAt (fun y ↦ (g y : EReal).toReal) x := by
    have hg_cont :
        ContinuousOn (fun y ↦ (g y : EReal).toReal) (interior (effectiveDomain g)) :=
      continuousOn_toReal_interior_effectiveDomain_of_mem_gammaZero hg_gamma
    exact (hg_cont x hxg_int).continuousAt (isOpen_interior.mem_nhds hxg_int)
  have hEq_fg :
      (fun y ↦ (g y : EReal).toReal) =ᶠ[nhds x] (fun y ↦ (f y : EReal).toReal) := by
    filter_upwards [isOpen_interior.mem_nhds hxC_int] with y hy
    have hyC : y ∈ C := interior_subset hy
    simp [g, hyC]
  have hxcont : ContinuousAt (fun y ↦ (f y : EReal).toReal) x := hxg_cont.congr hEq_fg
  have htwo :
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f ∧
        ContinuousAt (fun y ↦ (f y : EReal).toReal) x := by
    refine ⟨r, hr, ?_, hxcont⟩
    exact fun y hy ↦ hC_dom (Metric.ball_subset_closedBall hy)
  have hfinite :
      ∃ ρ : ℝ, 0 < ρ ∧ sSup ((fun y : H ↦ (f y : EReal)) '' Metric.ball x ρ) < ⊤ := by
    exact
      (List.TFAE.out
        (convex_tfae_locallyLipschitzNear_continuousAt_boundedBall_finiteSupBall f hconv hx)
        1 3).mp htwo
  have hcont_points :
      {y : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ effectiveDomain f ∧
        ContinuousAt (fun z ↦ (f z : EReal).toReal) y} = interior (effectiveDomain f) :=
    continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
      f hconv <| Or.inl <| by
        rcases hfinite with ⟨ρ', hρ', hsup⟩
        exact ⟨x, ρ', hρ', hsup⟩
  intro y hy
  have hy_cont :
      y ∈ {z : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ effectiveDomain f ∧
        ContinuousAt (fun z ↦ (f z : EReal).toReal) z} := by
    rw [hcont_points]
    exact hy
  rcases hy_cont with ⟨ρ, hρ, hball, hy_cont⟩
  exact hy_cont.continuousWithinAt

/-- Bridge companion to Proposition 17.51: the canonical source-facing hypothesis can be obtained
from Gâteaux differentiability of the finite real representative on `U`. -/
theorem continuousOn_interior_effectiveDomain_of_convexOn_of_toRealGateauxDifferentiableOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (U : Set H)
    (hU_nonempty : U.Nonempty) (hU_open : IsOpen U) (hU_dom : U ⊆ effectiveDomain f)
    (hgateaux : GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) U) :
    ContinuousOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) := by
  refine
    continuousOn_interior_effectiveDomain_of_convexOn_of_nonempty_open_subset_gateauxDifferentiableOn
      f hconv U hU_nonempty hU_open hU_dom ?_
  intro x hxU
  exact
    gateauxDifferentiableAt_of_toReal_gateauxDifferentiableOn_subset_effectiveDomain
      f hxU hU_dom hgateaux

end DifferentiabilityAndContinuity

end ERealFunction
