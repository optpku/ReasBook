/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_37

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Theorem 8.38: a finite `EReal` supremum on a ball forces each point of that
ball into the effective domain and bounds its real value by the real supremum. -/
private lemma mem_effectiveDomain_and_toReal_le_sSup_image_ball
    (f : H → Set.Ioi (⊥ : EReal))
    {x₀ : H} {ρ : ℝ} {u : H}
    (hsup : sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤)
    (hu : u ∈ Metric.ball x₀ ρ) :
    u ∈ effectiveDomain f ∧
      (f u : EReal).toReal ≤
        (sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ)).toReal := by
  -- Image membership places `f u` below the `EReal` supremum of the ball image.
  have hfu_le :
      (f u : EReal) ≤ sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) := by
    exact le_sSup (Set.mem_image_of_mem (fun y ↦ (f y : EReal)) hu)
  have hu_dom : u ∈ effectiveDomain f := by
    -- A value below a finite supremum is itself finite.
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hfu_le hsup
  have hfu_bot : (f u : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f u : EReal) from (f u).2)
  have hsup_ne_top :
      sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) ≠ ⊤ := ne_of_lt hsup
  refine ⟨hu_dom, ?_⟩
  -- `toReal` preserves the comparison against the finite supremum.
  simpa using EReal.toReal_le_toReal hfu_le hfu_bot hsup_ne_top

/-- Helper for Theorem 8.38: a finite weighted sum of two effective-domain values is the cast of
the corresponding real weighted sum of their `toReal` values. -/
private lemma weighted_value_sum_eq_coe_two_points
    (f : H → Set.Ioi (⊥ : EReal))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (α : ℝ) :
    (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) =
      ((α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal : ℝ) : EReal) := by
  -- Effective-domain membership lets us rewrite both endpoint values as real casts.
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  rw [← EReal.coe_toReal hx_top hx_bot,
    show (1 - α : EReal) = ((1 - α : ℝ) : EReal) by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub],
    ← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  simp

/-- Helper for Theorem 8.38: a finite supremum on a ball gives effective-domain membership on that
whole ball. -/
private lemma finite_sup_ball_subset_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal))
    {x₀ : H} {ρ : ℝ}
    (hsup : sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤) :
    Metric.ball x₀ ρ ⊆ effectiveDomain f := by
  intro u hu
  exact (mem_effectiveDomain_and_toReal_le_sSup_image_ball f hsup hu).1

/-- Helper for Theorem 8.38: boundedness of the real-valued image on a domain ball yields a finite
extended-real supremum on the same ball. -/
private lemma finite_sup_of_bounded_toReal_image_ball
    (f : H → Set.Ioi (⊥ : EReal))
    {x₀ : H} {ρ : ℝ}
    (hball_dom : Metric.ball x₀ ρ ⊆ effectiveDomain f)
    (hbounded : Bornology.IsBounded
      (((fun x ↦ (f x : EReal).toReal) '' Metric.ball x₀ ρ) : Set ℝ)) :
    sSup ((fun x ↦ (f x : EReal)) '' Metric.ball x₀ ρ) < ⊤ := by
  -- Extract a real upper bound for the bounded real image.
  rcases hbounded.bddAbove with ⟨M, hM⟩
  have hsSup_le :
      sSup ((fun x ↦ (f x : EReal)) '' Metric.ball x₀ ρ) ≤ (M : EReal) := by
    refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx_dom : x ∈ effectiveDomain f := hball_dom hx
    have hM_real :
        (f x : EReal).toReal ≤ M := by
      exact hM (Set.mem_image_of_mem (fun y ↦ (f y : EReal).toReal) hx)
    -- Rewrite the finite function value as a real cast and compare with the real upper bound.
    calc
      (f x : EReal) = (((f x : EReal).toReal : ℝ) : EReal) := by
        symm
        exact EReal.coe_toReal
          (ne_of_lt (mem_effectiveDomain_iff.mp hx_dom))
          (ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2))
      _ ≤ (M : EReal) := by
        exact_mod_cast hM_real
  exact lt_of_le_of_lt hsSup_le (EReal.coe_lt_top M)

/-- Helper for Theorem 8.38: a finite supremum on a ball gives continuity of the real-valued
representative at the center together with a domain ball. -/
private lemma continuousAt_of_finite_sup_ball
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x₀ : H} (hx₀ : x₀ ∈ effectiveDomain f)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsup : sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤) :
    ∃ r > 0,
      Metric.ball x₀ r ⊆ effectiveDomain f ∧
        ContinuousAt (fun x ↦ (f x : EReal).toReal) x₀ := by
  let g : H → ℝ := fun x ↦ (f x : EReal).toReal
  let η : EReal := sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ)
  let hball_dom : Metric.ball x₀ ρ ⊆ effectiveDomain f :=
    finite_sup_ball_subset_effectiveDomain f hsup
  have hx₀_ball : x₀ ∈ Metric.ball x₀ ρ := Metric.mem_ball_self hρ
  have hx₀_le_eta : (f x₀ : EReal).toReal ≤ η.toReal := by
    simpa [η] using
      (mem_effectiveDomain_and_toReal_le_sSup_image_ball f hsup hx₀_ball).2
  have hC_nonneg : 0 ≤ η.toReal - (f x₀ : EReal).toReal := by
    linarith
  refine ⟨ρ, hρ, hball_dom, ?_⟩
  -- The oscillation estimate from Proposition 8.37 gives an explicit continuity modulus.
  rw [Metric.continuousAt_iff]
  intro ε hε
  let α : ℝ := min (1 / 2) (ε / (2 * (η.toReal - (f x₀ : EReal).toReal + 1)))
  have hα0 : 0 < α := by
    dsimp [α]
    have hden : 0 < 2 * (η.toReal - (f x₀ : EReal).toReal + 1) := by
      positivity
    positivity
  have hα1 : α < 1 := by
    dsimp [α]
    have hhalf_lt_one : (1 / 2 : ℝ) < 1 := by norm_num
    exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt_one
  refine ⟨α * ρ, mul_pos hα0 hρ, ?_⟩
  intro x hx
  have hx_small : x ∈ Metric.ball x₀ (α * ρ) := by simpa [Metric.mem_ball] using hx
  have hx_large : x ∈ Metric.ball x₀ ρ := by
    rw [Metric.mem_ball] at hx_small ⊢
    have hαρ_lt : α * ρ < ρ := by
      nlinarith [hα1, hρ]
    exact lt_of_lt_of_le hx_small hαρ_lt.le
  have hx_dom : x ∈ effectiveDomain f := hball_dom hx_large
  have hosc :
      |g x - g x₀| ≤ α * (η.toReal - (f x₀ : EReal).toReal) := by
    simpa [g, η] using
      oscillation_bound_on_smaller_ball f hconv hρ hx₀ hsup hα0 hα1 hx_small hx_dom
  have hα_le :
      α ≤ ε / (2 * (η.toReal - (f x₀ : EReal).toReal + 1)) := by
    dsimp [α]
    exact min_le_right _ _
  have hscale_le :
      α * (η.toReal - (f x₀ : EReal).toReal) ≤ ε / 2 := by
    have hgap_le :
        η.toReal - (f x₀ : EReal).toReal ≤ η.toReal - (f x₀ : EReal).toReal + 1 := by
      linarith
    have hstep1 :
        α * (η.toReal - (f x₀ : EReal).toReal) ≤
          α * (η.toReal - (f x₀ : EReal).toReal + 1) := by
      exact mul_le_mul_of_nonneg_left hgap_le hα0.le
    have hstep2 :
        α * (η.toReal - (f x₀ : EReal).toReal + 1) ≤
          (ε / (2 * (η.toReal - (f x₀ : EReal).toReal + 1))) *
            (η.toReal - (f x₀ : EReal).toReal + 1) := by
      have hgap1_nonneg : 0 ≤ η.toReal - (f x₀ : EReal).toReal + 1 := by linarith
      exact mul_le_mul_of_nonneg_right hα_le hgap1_nonneg
    have hden_nonzero : 2 * (η.toReal - (f x₀ : EReal).toReal + 1) ≠ 0 := by
      positivity
    calc
      α * (η.toReal - (f x₀ : EReal).toReal)
          ≤ α * (η.toReal - (f x₀ : EReal).toReal + 1) := hstep1
      _ ≤ (ε / (2 * (η.toReal - (f x₀ : EReal).toReal + 1))) *
            (η.toReal - (f x₀ : EReal).toReal + 1) := hstep2
      _ = ε / 2 := by
            field_simp [hden_nonzero]
  have hscale_lt : α * (η.toReal - (f x₀ : EReal).toReal) < ε := by
    linarith
  -- Convert the explicit oscillation estimate into the metric continuity bound.
  simpa [g, Real.dist_eq] using lt_of_le_of_lt hosc hscale_lt

/-- Helper for Theorem 8.38: a finite supremum at one center transports to a smaller finite
supremum ball around any interior point of the effective domain. -/
private lemma transport_finite_sup_ball_to_interior_point
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x₀ : H} {ρ : ℝ} (hρ : 0 < ρ)
    (hsup₀ : sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤)
    {x : H} (hx : x ∈ interior (effectiveDomain f)) :
    ∃ r > 0, sSup ((fun z ↦ (f z : EReal)) '' Metric.ball x r) < ⊤ := by
  let η : EReal := sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ)
  let hball₀_dom : Metric.ball x₀ ρ ⊆ effectiveDomain f :=
    finite_sup_ball_subset_effectiveDomain f hsup₀
  by_cases hxx₀ : x = x₀
  · -- At the original center we can reuse the given finite-sup ball directly.
    subst hxx₀
    exact ⟨ρ, hρ, hsup₀⟩
  · have hx_dom : x ∈ effectiveDomain f := interior_subset hx
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx) with ⟨γ, hγ, hγball⟩
    let γ' : ℝ := γ / 2
    have hγ'_pos : 0 < γ' := by
      dsimp [γ']
      positivity
    let d : ℝ := ‖x - x₀‖
    have hd_pos : 0 < d := by
      dsimp [d]
      simpa [norm_pos_iff] using sub_ne_zero.mpr hxx₀
    let α : ℝ := γ' / (γ' + d)
    have hα0 : 0 < α := by
      dsimp [α]
      positivity
    have hα1 : α < 1 := by
      -- The transport coefficient lies strictly between `0` and `1`.
      dsimp [α]
      have hsum_pos : 0 < γ' + d := by
        positivity
      refine (div_lt_one hsum_pos).2 ?_
      linarith
    let y : H := x₀ + (1 / (1 - α)) • (x - x₀)
    have hy_ball : y ∈ Metric.ball x γ := by
      -- Choose the extrapolated point strictly inside the interior-domain ball.
      rw [Metric.mem_ball, dist_eq_norm]
      have hy_sub : y - x = (α / (1 - α)) • (x - x₀) := by
        dsimp [y]
        have hsub : x₀ + (1 / (1 - α)) • (x - x₀) - x =
            ((1 / (1 - α)) - 1) • (x - x₀) := by
          module
        rw [hsub]
        congr 1
        field_simp [sub_ne_zero.mpr (ne_of_gt hα1)]
        ring
      rw [hy_sub, norm_smul]
      have hcoeff_nonneg : 0 ≤ α / (1 - α) := by
        have h1α_pos : 0 < 1 - α := by
          linarith
        exact div_nonneg hα0.le h1α_pos.le
      rw [Real.norm_of_nonneg hcoeff_nonneg]
      have hcoeff_eq : (α / (1 - α)) * d = γ' := by
        have h1α_ne : 1 - α ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα1)
        have hd_ne : d ≠ 0 := ne_of_gt hd_pos
        dsimp [α, γ']
        field_simp [h1α_ne, hd_ne]
        ring
      have hγ'_lt_γ : γ' < γ := by
        dsimp [γ']
        linarith
      calc
        (α / (1 - α)) * ‖x - x₀‖ = γ' := by
          simpa [d] using hcoeff_eq
        _ < γ := hγ'_lt_γ
    have hy_dom : y ∈ effectiveDomain f := hγball hy_ball
    let r : ℝ := α * ρ
    have hr_pos : 0 < r := by
      dsimp [r]
      positivity
    refine ⟨r, hr_pos, ?_⟩
    let B : EReal :=
      ((α * η.toReal + (1 - α) * (f y : EReal).toReal : ℝ) : EReal)
    have hsSup_le : sSup ((fun z ↦ (f z : EReal)) '' Metric.ball x r) ≤ B := by
      refine sSup_le ?_
      rintro _ ⟨z, hz, rfl⟩
      let w : H := x₀ + α⁻¹ • (z - x)
      have hw_ball : w ∈ Metric.ball x₀ ρ := by
        -- The transported point lands back in the original finite-sup ball.
        rw [Metric.mem_ball, dist_eq_norm]
        have hw_sub : w - x₀ = α⁻¹ • (z - x) := by
          dsimp [w]
          abel_nf
        rw [hw_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hα0.le)]
        have hz_norm : ‖z - x‖ < α * ρ := by
          simpa [Metric.mem_ball, dist_eq_norm, r] using hz
        have hscale :
            α⁻¹ * ‖z - x‖ < α⁻¹ * (α * ρ) := by
          exact mul_lt_mul_of_pos_left hz_norm (inv_pos.mpr hα0)
        calc
          α⁻¹ * ‖z - x‖ < α⁻¹ * (α * ρ) := hscale
          _ = ρ := by
                field_simp [hα0.ne']
      have hw_dom : w ∈ effectiveDomain f := hball₀_dom hw_ball
      have hz_eq : z = α • w + (1 - α) • y := by
        -- This is the textbook convex decomposition of `z`.
        have hz_eq' : α • w + (1 - α) • y = z := by
          dsimp [w, y]
          rw [smul_add, smul_add, smul_smul, smul_smul]
          have hαinv : α * α⁻¹ = 1 := by
            field_simp [hα0.ne']
          have h1αinv : (1 - α) * (1 / (1 - α)) = 1 := by
            have h1α_ne : 1 - α ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα1)
            field_simp [h1α_ne]
          rw [hαinv, h1αinv, one_smul, one_smul]
          module
        exact hz_eq'.symm
      have hineq :
          (f z : EReal) ≤
            (α : EReal) * (f w : EReal) + (1 - α : EReal) * (f y : EReal) := by
        -- Convexity compares `f z` with the values at the transported endpoints.
        simpa [hz_eq] using hconv.ineq hw_dom hy_dom hα0 hα1
      have hw_le : (f w : EReal).toReal ≤ η.toReal := by
        simpa [η] using
          (mem_effectiveDomain_and_toReal_le_sSup_image_ball f hsup₀ hw_ball).2
      have hright_le :
          (α : EReal) * (f w : EReal) + (1 - α : EReal) * (f y : EReal) ≤ B := by
        dsimp [B]
        rw [weighted_value_sum_eq_coe_two_points f hw_dom hy_dom α]
        exact_mod_cast
          add_le_add
            (mul_le_mul_of_nonneg_left hw_le hα0.le)
            (le_rfl : (1 - α) * (f y : EReal).toReal ≤ (1 - α) * (f y : EReal).toReal)
      exact le_trans hineq hright_le
    exact lt_of_le_of_lt hsSup_le (by
      dsimp [B]
      exact EReal.coe_lt_top _)

/-- Theorem 8.38 (1): for a convex `]-∞,+∞]`-valued function at a point `x₀` of its effective
domain, the following are equivalent: local Lipschitz continuity of the real-valued representative
near `x₀`, continuity at `x₀`, boundedness on some open ball around `x₀`, and finiteness of the
supremum on some open ball around `x₀`. -/
-- Proof sketch: use Proposition 8.37 to show that a finite supremum on a ball controls the local
-- oscillation near `x₀`, giving continuity; use the bounded-image estimate from the same
-- proposition to deduce a local Lipschitz bound on a smaller ball; the remaining implications are
-- immediate.
theorem convex_tfae_locallyLipschitzNear_continuousAt_boundedBall_finiteSupBall
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x₀ : H} (hx₀ : x₀ ∈ effectiveDomain f) :
    List.TFAE
      [∃ β : NNReal, ∃ ρ > 0,
          Metric.ball x₀ ρ ⊆ effectiveDomain f ∧
            LipschitzOnWith β (fun x ↦ (f x : EReal).toReal) (Metric.ball x₀ ρ),
        ∃ ρ > 0,
          Metric.ball x₀ ρ ⊆ effectiveDomain f ∧
            ContinuousAt (fun x ↦ (f x : EReal).toReal) x₀,
        ∃ ρ > 0, Metric.ball x₀ ρ ⊆ effectiveDomain f ∧
          Bornology.IsBounded (((fun x ↦ (f x : EReal).toReal) '' Metric.ball x₀ ρ) : Set ℝ),
        ∃ ρ > 0, sSup ((fun x ↦ (f x : EReal)) '' Metric.ball x₀ ρ) < ⊤] := by
  tfae_have 1 → 2 := by
    rintro ⟨β, ρ, hρ, hball_dom, hlip⟩
    refine ⟨ρ, hρ, hball_dom, ?_⟩
    -- A Lipschitz map on a neighborhood ball is continuous at the center.
    exact hlip.continuousOn.continuousAt (Metric.ball_mem_nhds x₀ hρ)
  tfae_have 2 → 3 := by
    rintro ⟨ρ, hρ, hball_dom, hcont⟩
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hδprop⟩ := hcont 1 zero_lt_one
    let r : ℝ := min ρ δ
    have hr_pos : 0 < r := by
      dsimp [r]
      exact lt_min hρ hδ
    refine ⟨r, hr_pos, ?_⟩
    constructor
    · intro x hx
      apply hball_dom
      rw [Metric.mem_ball] at hx ⊢
      exact lt_of_lt_of_le hx (min_le_left _ _)
    · have himage_subset :
          ((fun x ↦ (f x : EReal).toReal) '' Metric.ball x₀ r) ⊆
            Set.Icc ((f x₀ : EReal).toReal - 1) ((f x₀ : EReal).toReal + 1) := by
        rintro _ ⟨x, hx, rfl⟩
        have hxδ : dist x x₀ < δ := by
          rw [Metric.mem_ball] at hx
          exact lt_of_lt_of_le hx (min_le_right _ _)
        have hdist : dist ((f x : EReal).toReal) ((f x₀ : EReal).toReal) < 1 := hδprop hxδ
        have habs := abs_lt.mp hdist
        constructor <;> linarith
      -- The image lies in a bounded real interval around the center value.
      exact (Metric.isBounded_Icc _ _).subset himage_subset
  tfae_have 3 → 4 := by
    rintro ⟨ρ, hρ, hball_dom, hbounded⟩
    refine ⟨ρ, hρ, ?_⟩
    -- A bounded real image gives a finite `EReal` supremum on the same ball.
    exact finite_sup_of_bounded_toReal_image_ball f hball_dom hbounded
  tfae_have 4 → 2 := by
    rintro ⟨ρ, hρ, hsup⟩
    -- Proposition 8.37 controls the oscillation on smaller balls, hence continuity at the center.
    exact continuousAt_of_finite_sup_ball f hconv hx₀ hρ hsup
  tfae_have 3 → 1 := by
    rintro ⟨ρ, hρ, hball_dom, hbounded⟩
    let K : ℝ :=
      Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ ρ) : Set ℝ) / (ρ / 2)
    have hhalf : 0 < ρ / 2 := by positivity
    have htwo : 2 * (ρ / 2) = ρ := by ring
    have hsmall_dom : Metric.ball x₀ (ρ / 2) ⊆ effectiveDomain f := by
      intro x hx
      apply hball_dom
      rw [Metric.mem_ball] at hx ⊢
      linarith
    refine ⟨Real.toNNReal K, ρ / 2, hhalf, hsmall_dom, ?_⟩
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    have hball_dom' : Metric.ball x₀ (2 * (ρ / 2)) ⊆ effectiveDomain f := by
      simpa [htwo] using hball_dom
    have hbounded' :
        Bornology.IsBounded
          (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * (ρ / 2))) : Set ℝ) := by
      simpa [htwo] using hbounded
    -- Proposition 8.37 gives the Lipschitz estimate on the half-radius ball.
    refine LipschitzOnWith.of_dist_le' ?_
    intro x hx y hy
    have hx_dom : x ∈ effectiveDomain f := hsmall_dom hx
    have hy_dom : y ∈ effectiveDomain f := hsmall_dom hy
    have hgap :
        |((f x : EReal).toReal - (f y : EReal).toReal)| ≤ K * ‖x - y‖ := by
      simpa [K, htwo] using
        lipschitz_bound_on_ball_of_bounded_image
          f hconv hhalf hx₀ hball_dom' hbounded' hx hy hx_dom hy_dom
    simpa [Real.toNNReal_of_nonneg hK_nonneg, dist_eq_norm, Real.norm_eq_abs, K] using hgap
  tfae_finish

/-- Theorem 8.38 (2): if a convex `]-∞,+∞]`-valued function has finite supremum on some open ball
around `x₀`, then its real-valued representative is locally Lipschitz near every point of
`interior (effectiveDomain f)`. -/
-- Proof sketch: transport a bounded-above ball near `x₀` to any interior point by convexity, then
-- apply the equivalence from clause (1) at that interior point.
theorem convex_locallyLipschitzNear_on_interior_of_finiteSupBall
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x₀ : H} :
    (∃ ρ > 0, sSup ((fun x ↦ (f x : EReal)) '' Metric.ball x₀ ρ) < ⊤) →
      ∀ x ∈ interior (effectiveDomain f),
        ∃ β : NNReal, ∃ ρ > 0,
          Metric.ball x ρ ⊆ effectiveDomain f ∧
            LipschitzOnWith β (fun y ↦ (f y : EReal).toReal) (Metric.ball x ρ) := by
  intro hsup₀ x hx
  obtain ⟨ρ, hρ, hsupρ⟩ := hsup₀
  have hx_dom : x ∈ effectiveDomain f := interior_subset hx
  have htfae :=
    convex_tfae_locallyLipschitzNear_continuousAt_boundedBall_finiteSupBall
      f hconv (x₀ := x) hx_dom
  obtain ⟨r, hr, hsupx⟩ :=
    transport_finite_sup_ball_to_interior_point f hconv hρ hsupρ hx
  -- Route correction: transport clause (4) to the interior point first, then read off clause (1)
  -- from the already established local `TFAE`.
  have hfour : ∃ ρ > 0, sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x ρ) < ⊤ := ⟨r, hr, hsupx⟩
  exact (List.TFAE.out htfae 3 0).mp hfour

end ERealFunction
