/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open WithLp

universe u

namespace ERealFunction

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_completeSpace_l2 prod_innerProductSpace_l2

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 9.19: a real-height epigraph point has base point in the effective
domain, and its ordinate dominates the finite real value there. -/
private lemma mem_effectiveDomain_and_toReal_le_of_mem_real_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} {η : ℝ}
    (hyη : (y, η) ∈ epigraph (fun z : H ↦ (f z : EReal))) :
    y ∈ effectiveDomain f ∧ (f y : EReal).toReal ≤ η := by
  -- Epigraph membership bounds `f y` by the finite ordinate `η`, so `y` lies in the effective
  -- domain and `toReal` preserves the comparison.
  have hfy_le : (f y : EReal) ≤ (η : EReal) := (mem_epigraph_iff _ _ _).mp hyη
  have hy : y ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hfy_le (EReal.coe_lt_top η)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hη_top : (η : EReal) ≠ ⊤ := EReal.coe_ne_top η
  have htoReal : (f y : EReal).toReal ≤ ((η : EReal)).toReal := by
    simpa using EReal.toReal_le_toReal hfy_le hfy_bot hη_top
  simpa using ⟨hy, htoReal⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 9.19: a point whose real ordinate lies strictly below the finite value
of `f` cannot lie in the real-height epigraph. -/
private lemma point_below_value_not_mem_real_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hx : x ∈ effectiveDomain f) (hξ : ξ < (f x : EReal).toReal) :
    (x, ξ) ∉ epigraph (fun y : H ↦ (f y : EReal)) := by
  -- The effective-domain hypothesis lets us rewrite `f x` back from `toReal`; epigraph membership
  -- would then force the forbidden inequality `(f x).toReal ≤ ξ`.
  intro hxξ
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hfx_le_ξ : (f x : EReal) ≤ (ξ : EReal) := (mem_epigraph_iff _ _ _).mp hxξ
  have hcast : (((f x : EReal).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
    simpa [EReal.coe_toReal hx_top hx_bot] using hfx_le_ξ
  exact not_le_of_gt hξ (by exact_mod_cast hcast)

-- Proof sketch: apply Proposition 9.18 to the real-height epigraph of `f`. The extra hypothesis
-- `ξ < (f x).toReal` rules out the case `π = ξ` in the max-majorization conclusion, so one obtains
-- the sharper scalar relation `ξ < (f p).toReal = π`.
/-- Proposition 9.19 (1): if `(p, π)` is the projection of `(x, ξ)` onto the real-height epigraph
of `f`, then `π` equals `f p` and this common value lies strictly above `ξ`. -/
theorem strict_lt_value_and_value_eq_height_of_eq_projectionPoint_epigraph_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hx : x ∈ effectiveDomain f) (hξ : ξ < (f x : EReal).toReal) :
    (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) →
      ξ < (f p : EReal).toReal ∧ (f p : EReal).toReal = π := by
  intro hproj
  rcases
      (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mp
        hproj with
    ⟨hmax, hvar⟩
  have hp_mem :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- The projection point itself lies in the epigraph.
    simpa [hproj] using
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  rcases mem_effectiveDomain_and_toReal_le_of_mem_real_epigraph (f := f) hp_mem with
    ⟨hp, hfp_le_pi⟩
  have hξ_le_pi : ξ ≤ π := by
    -- Proposition 9.18 already says that `π` dominates the starting height `ξ`.
    exact_mod_cast
      (le_trans (show (ξ : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_left _ _) hmax :
        (ξ : EReal) ≤ (π : EReal))
  have hscalar : ((f p : EReal).toReal - π) * (ξ - π) ≤ 0 := by
    -- Testing the variational inequality at `y = p` removes the Hilbert-space term.
    simpa using hvar p hp
  have hξ_lt_fp : ξ < (f p : EReal).toReal := by
    -- Route correction: follow the source contradiction argument rather than trying to close the
    -- scalar inequality directly.
    by_contra hfp_le_ξ_false
    have hfp_le_ξ : (f p : EReal).toReal ≤ ξ := not_lt.mp hfp_le_ξ_false
    have hsq_le :
        (ξ - π) * (ξ - π) ≤ ((f p : EReal).toReal - π) * (ξ - π) := by
      exact
        mul_le_mul_of_nonpos_right (sub_le_sub_right hfp_le_ξ π)
          (sub_nonpos.mpr hξ_le_pi)
    have hπ_eq_ξ : π = ξ := by
      have hsq_nonneg : 0 ≤ (ξ - π) * (ξ - π) := by nlinarith
      nlinarith [hsq_nonneg, hsq_le, hscalar]
    have hvarx : ⟪x - p, x - p⟫_ℝ ≤ 0 := by
      -- Once `π = ξ`, the scalar term at `y = x` vanishes.
      have hvarx_raw :
          ⟪x - p, x - p⟫_ℝ + ((f x : EReal).toReal - π) * (ξ - π) ≤ 0 :=
        hvar x hx
      rw [hπ_eq_ξ, sub_self, mul_zero, add_zero] at hvarx_raw
      exact hvarx_raw
    have hinner_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ := by
      simpa using (real_inner_self_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ)
    have hinner_eq_zero : ⟪x - p, x - p⟫_ℝ = 0 := by
      nlinarith [hinner_nonneg, hvarx]
    have hxp : x = p := by
      have hsub : x - p = 0 := by
        simpa using inner_self_eq_zero.mp hinner_eq_zero
      exact sub_eq_zero.mp hsub
    have hxξ_mem :
        (x, ξ) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
      simpa [hxp, hπ_eq_ξ] using hp_mem
    exact point_below_value_not_mem_real_epigraph (f := f) hx hξ hxξ_mem
  have hξ_lt_pi : ξ < π := lt_of_lt_of_le hξ_lt_fp hfp_le_pi
  have hfp_eq_pi : (f p : EReal).toReal = π := by
    -- If `(f p).toReal` were still strictly below `π`, the scalar inequality at `y = p` would
    -- have strictly positive left-hand side.
    by_contra hne
    have hfp_lt_pi : (f p : EReal).toReal < π := lt_of_le_of_ne hfp_le_pi hne
    have hprod_pos : 0 < ((f p : EReal).toReal - π) * (ξ - π) := by
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hfp_lt_pi) (sub_neg.mpr hξ_lt_pi)
    linarith
  exact ⟨hξ_lt_fp, hfp_eq_pi⟩

-- Proof sketch: this is the variational-inequality component of Proposition 9.18 specialized to
-- the real-height epigraph of `f`.
/-- Proposition 9.19 (2): if `(p, π)` is the projection of `(x, ξ)` onto the real-height epigraph
of `f`, then the associated variational inequality holds against every point of
`effectiveDomain f`. -/
theorem variational_inequality_of_eq_projectionPoint_epigraph_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ} :
    (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) →
      ∀ y ∈ effectiveDomain f,
        ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 := by
  intro hproj
  -- Proposition 9.18 already packages the desired variational inequality as its second component.
  exact
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mp
      hproj |>.2

/-- Helper for Proposition 9.19: the converse direction is valid once the epigraph contact is
stated as an actual `EReal` equality, which restores the missing finiteness of `f p`. -/
private theorem
    eq_projectionPoint_epigraph_of_strict_lt_value_eq_realHeight_of_variational_inequality
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hξp : ξ < (f p : EReal).toReal) (hπ : (f p : EReal) = π)
    (hvar :
      ∀ y ∈ effectiveDomain f,
        ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0) :
    (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) := by
  have hmax : max (ξ : EReal) (f p : EReal) ≤ (π : EReal) := by
    -- The strict inequality gives the `ξ` branch, and the exact epigraph contact gives the `f p`
    -- branch of the max-bound from Proposition 9.18.
    refine max_le ?_ ?_
    · have hξ_lt_pi : ξ < π := by
        simpa [hπ] using hξp
      exact_mod_cast (le_of_lt hξ_lt_pi)
    · simp [hπ]
  -- Feed the max-bound and the variational inequality back into Proposition 9.18.
  exact
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mpr
      ⟨hmax, hvar⟩

-- Proof sketch: combine the scalar relation `ξ < (f p).toReal = π` with Proposition 9.18. The
-- equality `(f p).toReal = π` turns the max-majorization condition there into the present strict
-- epigraph-height hypothesis.
/-- Proposition 9.19 (3): conversely, if `π = f p` lies strictly above `ξ` and the variational
inequality holds on `effectiveDomain f`, then `(p, π)` is the projection of `(x, ξ)` onto the
real-height epigraph of `f`. -/
theorem eq_projectionPoint_epigraph_of_strict_lt_value_eq_height_of_variational_inequality
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hξp : ξ < (f p : EReal).toReal) (hπ : (f p : EReal) = π)
    (hvar :
      ∀ y ∈ effectiveDomain f,
        ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0) :
    (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) := by
  -- Route correction: reuse the repaired local converse theorem instead of re-opening the
  -- Proposition 9.18 converse with the previously false `toReal` contact hypothesis.
  exact
    eq_projectionPoint_epigraph_of_strict_lt_value_eq_realHeight_of_variational_inequality
      hf hξp hπ hvar
-- The genuine epigraph-contact hypothesis `(f p : EReal) = π` is essential.  The weaker
-- statement `(f p).toReal = π` is false when `f p = ⊤`.

end ERealFunction
