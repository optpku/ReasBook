/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction Filter
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H]

/- Proposition 11.18: the source-facing owner is the extended-real limsup squared-distance
objective attached to a sequence `zₙ`. This keeps the correct `+∞` behavior for unbounded
sequences, while boundedness is used later only for the finite real-valued bridge. -/
/-- The asymptotic-center objective attached to a sequence `zₙ`, namely
`x ↦ limsup ‖x - zₙ‖²`, viewed in `EReal`. -/
noncomputable def asymptoticCenterObjective (zₙ : ℕ → H) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop, by
      have hnonneg :
          (0 : EReal) ≤
            Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop := by
        refine Filter.le_limsup_of_le (by isBoundedDefault) ?_
        intro b hb
        rcases Filter.eventually_atTop.1 hb with ⟨N, hN⟩
        have hN_nonneg : (0 : EReal) ≤ ((‖x - zₙ N‖ ^ (2 : ℕ) : ℝ) : EReal) := by
          exact_mod_cast (show 0 ≤ ‖x - zₙ N‖ ^ (2 : ℕ) by positivity)
        exact le_trans hN_nonneg (hN N le_rfl)
      exact lt_of_lt_of_le (by simp) hnonneg⟩

/-- For a bounded sequence, the asymptotic-center objective is finite everywhere. -/
theorem asymptoticCenterObjective_lt_top
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) (x : H) :
    (asymptoticCenterObjective zₙ x : EReal) < ⊤ := sorry

/-- Any global minimizer of the indicator-augmented asymptotic-center objective lies in the
constraint set. -/
private theorem mem_constraint_of_mem_argmin_addIndicator_asymptoticCenterObjective
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) {z : H}
    (hz : z ∈ Argmin ((asymptoticCenterObjective zₙ + ι[C]).asEReal)) :
    z ∈ C := by
  rcases hC_nonempty with ⟨y, hyC⟩
  have hzmin :
      IsMinOn ((asymptoticCenterObjective zₙ + ι[C]).asEReal) Set.univ z :=
    mem_argmin_iff.1 hz
  have hzy : ((asymptoticCenterObjective zₙ + ι[C]).asEReal) z ≤
      ((asymptoticCenterObjective zₙ + ι[C]).asEReal) y :=
    (isMinOn_univ_iff).1 hzmin y
  have hy_lt_top : ((asymptoticCenterObjective zₙ + ι[C]).asEReal) y < ⊤ := by
    simpa [hyC] using asymptoticCenterObjective_lt_top hzₙ_bdd y
  by_contra hzC
  have hz_eq_top : ((asymptoticCenterObjective zₙ + ι[C]).asEReal) z = ⊤ := by
    have hz_ne_bot : (asymptoticCenterObjective zₙ z : EReal) ≠ ⊥ :=
      ne_of_gt (asymptoticCenterObjective zₙ z).2
    simpa [hzC] using EReal.add_top_of_ne_bot hz_ne_bot
  have : (⊤ : EReal) ≤ ((asymptoticCenterObjective zₙ + ι[C]).asEReal) y := by
    simpa [hz_eq_top] using hzy
  exact not_le_of_gt hy_lt_top this

section RealHilbert

variable [InnerProductSpace ℝ H]

-- Proof sketch: boundedness makes the canonical `EReal` owner finite everywhere, so its `toReal`
-- bridge satisfies the pointwise identity
-- `‖α x + (1 - α) y - zₙ‖² = α ‖x - zₙ‖² + (1 - α) ‖y - zₙ‖² - α (1 - α) ‖x - y‖²`;
-- passing to `Filter.limsup` yields the real-valued source clause.
/-- Proposition 11.18 (1): clause (i). For a bounded sequence, the real-valued bridge of the
asymptotic-center objective is strongly convex on the whole Hilbert space with constant `2`. -/
theorem asymptoticCenterObjective_strongConvexOn_univ
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) :
    StrongConvexOn (Set.univ : Set H) (2 : ℝ)
      (fun x ↦ (asymptoticCenterObjective zₙ x : EReal).toReal) := sorry

-- Proof sketch: boundedness identifies the effective domain of the canonical `EReal` owner with
-- the whole space, and the same Jensen-gap computation yields the chapter-10 strong-convexity
-- owner directly.
/-- For a bounded sequence, the canonical `EReal` asymptotic-center objective is strongly convex
with constant `2`. -/
theorem asymptoticCenterObjective_stronglyConvex
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) :
    ERealFunction.StronglyConvex (asymptoticCenterObjective zₙ) (2 : ℝ) := sorry

-- Proof sketch: boundedness of `zₙ` gives a quadratic lower bound on
-- `x ↦ limsup ‖x - zₙ‖²` as `‖x‖ → ∞`; dividing by `‖x‖` and sending `‖x‖` to infinity yields the
-- supercoercive growth condition.
/-- Proposition 11.18 (2): clause (ii). For a bounded sequence, the canonical `EReal`
asymptotic-center objective is supercoercive. -/
theorem asymptoticCenterObjective_supercoercive
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) :
    ERealFunction.Supercoercive (asymptoticCenterObjective zₙ).asEReal := sorry

-- Proof sketch: combine the strong convexity and supercoercivity of the asymptotic-center
-- objective with convexity of the indicator `ι[C]` to obtain the corresponding bridge facts for
-- the indicator-augmented objective `f + ι_C`.
/-- Proposition 11.18 (3): clause (iii). For a nonempty convex set `C`, the indicator-augmented
asymptotic-center objective `f + ι[C]` is strongly convex with constant `2`. -/
theorem asymptoticCenterObjective_addIndicator_stronglyConvex
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) :
    ERealFunction.StronglyConvex (asymptoticCenterObjective zₙ + ι[C]) (2 : ℝ) := by
  have hobjective :
      ERealFunction.StronglyConvex (asymptoticCenterObjective zₙ) (2 : ℝ) :=
    asymptoticCenterObjective_stronglyConvex hzₙ_bdd
  sorry

-- Proof sketch: adding the indicator `ι[C]` only increases the objective pointwise, so the
-- supercoercive growth from clause (ii) is preserved by the constrained objective.
/-- Proposition 11.18 (3): clause (iii). For any constraint set `C`, the indicator-augmented
asymptotic-center objective `f + ι[C]` remains supercoercive. -/
theorem asymptoticCenterObjective_addIndicator_supercoercive
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H} :
    ERealFunction.Supercoercive ((asymptoticCenterObjective zₙ + ι[C]).asEReal) := sorry

section CompleteSpace

variable [CompleteSpace H]

-- Proof sketch: apply the existence theory for strongly convex supercoercive constrained
-- objectives to the indicator-augmented bridge `f + ι_C`.
private theorem existsUnique_mem_argmin_addIndicator_asymptoticCenterObjective
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ∃! z : H, z ∈ Argmin ((asymptoticCenterObjective zₙ + ι[C]).asEReal) := sorry

/-- Proposition 11.18 (3): clause (iii). For a nonempty closed convex set `C`, the
asymptotic-center objective has a unique minimizer on `C`. -/
theorem existsUnique_mem_argminOn_asymptoticCenterObjective
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ∃! z : H, z ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal := by
  have hnot_bot : ∀ x ∉ C, (asymptoticCenterObjective zₙ).asEReal x ≠ ⊥ :=
    fun x _ ↦ ne_of_gt (asymptoticCenterObjective zₙ x).2
  rcases
      existsUnique_mem_argmin_addIndicator_asymptoticCenterObjective
        hzₙ_bdd hC_nonempty hC_closed hC_convex with
    ⟨z, hz, huniq⟩
  refine ⟨z, ?_, ?_⟩
  · rw [argminOn_eq_inter_argmin_add_indicator (asymptoticCenterObjective zₙ).asEReal C hnot_bot]
    exact ⟨mem_constraint_of_mem_argmin_addIndicator_asymptoticCenterObjective
      hzₙ_bdd hC_nonempty hz, hz⟩
  · intro w hw
    rw [argminOn_eq_inter_argmin_add_indicator (asymptoticCenterObjective zₙ).asEReal C hnot_bot] at hw
    exact huniq w hw.2

/-- The canonical asymptotic center of `zₙ` relative to `C`. -/
noncomputable def asymptoticCenter
    (zₙ : ℕ → H) (C : Set H) (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) : H :=
  (existsUnique_mem_argminOn_asymptoticCenterObjective
    hzₙ_bdd hC_nonempty hC_closed hC_convex).choose

-- Proof sketch: unfold `asymptoticCenter` as the chosen witness of the unique constrained
-- minimizer theorem.
/-- The canonical asymptotic center belongs to the minimizer set of the asymptotic-center
objective over `C`. -/
theorem asymptoticCenter_mem_argminOn
    {zₙ : ℕ → H} {C : Set H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex ∈
      Argmin[C] (asymptoticCenterObjective zₙ).asEReal := by
  exact
    (existsUnique_mem_argminOn_asymptoticCenterObjective
      hzₙ_bdd hC_nonempty hC_closed hC_convex).choose_spec.1

/-- Any constrained minimizer of the asymptotic-center objective is the canonical asymptotic
center. -/
theorem eq_asymptoticCenter_of_mem_argminOn
    {zₙ : ℕ → H} {C : Set H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {z : H}
    (hz : z ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal) :
    z = asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex := by
  exact ExistsUnique.unique
    (existsUnique_mem_argminOn_asymptoticCenterObjective
      hzₙ_bdd hC_nonempty hC_closed hC_convex)
    hz
    (asymptoticCenter_mem_argminOn hzₙ_bdd hC_nonempty hC_closed hC_convex)

-- Proof sketch: expand `‖x - zₙ‖²` around the weak limit `z`, pass to the limit superior using
-- weak convergence of the linear term, and then identify the unique minimizer on `C` with the
-- metric projection of `z` onto `C`.
/-- Proposition 11.18 (4): clause (iv). If `zₙ` converges weakly to `z`, then the asymptotic-center
objective splits as `‖x - z‖²` plus the constant `f(z)`, and the asymptotic center relative to `C`
is the metric projection of `z` onto `C`. -/
theorem asymptoticCenterObjective_formula_and_asymptoticCenter_eq_projectionPoint_of_tendsto_weakly
    {zₙ : ℕ → H} {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) {z : H}
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (zₙ n)) atTop (𝓝 (toWeakSpace ℝ H z))) :
    (∀ x : H,
        (asymptoticCenterObjective zₙ x : EReal) =
          ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + asymptoticCenterObjective zₙ z) ∧
      asymptoticCenter zₙ C (bounded_range_of_tendsto_weakly hweak)
        hC_nonempty hC_closed hC_convex =
        projectionPoint C (isChebyshev_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex) z := sorry

-- Proof sketch: Proposition 5.7 gives strong convergence of the projection shadows `P_C zₙ` for a
-- Fejér-monotone sequence; the limit point is characterized as the unique minimizer of the
-- asymptotic-center objective on `C`.
/-- Proposition 11.18 (5): clause (v). If `zₙ` is Fejér monotone with respect to `C`, then the
projection shadow sequence `P_C zₙ` converges strongly to the asymptotic center relative to `C`. -/
theorem tendsto_projectionPoint_to_asymptoticCenter_of_fejerMonotone
    {zₙ : ℕ → H} {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hfejer : FejerMonotone C zₙ) :
    Tendsto
      (fun n ↦
        projectionPoint C (isChebyshev_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex) (zₙ n))
      atTop (𝓝 (asymptoticCenter zₙ C (hfejer.isBounded hC_nonempty)
        hC_nonempty hC_closed hC_convex)) := sorry

-- Proof sketch: compare the asymptotic-center objective at `z_C` and at `T z_C` along the Picard
-- orbit `zₙ`; nonexpansiveness gives the inequality, and uniqueness of the minimizer forces
-- `T z_C = z_C`.
/-- Proposition 11.18 (6): clause (vi). If `zₙ` is the orbit of a nonexpansive self-map `T : C →
C`, then the asymptotic center relative to `C` is an ambient fixed point of `T`. -/
theorem asymptoticCenter_mem_fixedPoints_of_orbit
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {T : C → C} (hT : LipschitzWith 1 T) (hzₙ_mem : ∀ n, zₙ n ∈ C)
    (horbit : ∀ n, zₙ (n + 1) = T ⟨zₙ n, hzₙ_mem n⟩) :
    asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex ∈
      Subtype.val '' Function.fixedPoints T := sorry

-- Proof sketch: compare `T z_C` to the sequence `zₙ` by inserting and subtracting `T zₙ`; the
-- residual convergence together with nonexpansiveness shows that `T z_C` is no larger for the
-- asymptotic-center objective than `z_C`, so uniqueness forces fixed-point membership.
/-- Proposition 11.18 (7): clause (vii). If `zₙ - T zₙ → 0` for a nonexpansive self-map `T : C →
C`, then the asymptotic center relative to `C` is an ambient fixed point of `T`. -/
theorem asymptoticCenter_mem_fixedPoints_of_residual_tendsto_zero
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {T : C → C} (hT : LipschitzWith 1 T) (hzₙ_mem : ∀ n, zₙ n ∈ C)
    (hres :
      Tendsto (fun n ↦ zₙ n - (T ⟨zₙ n, hzₙ_mem n⟩ : H)) atTop (𝓝 (0 : H))) :
    asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex ∈
      Subtype.val '' Function.fixedPoints T := sorry

end CompleteSpace

end RealHilbert

end
