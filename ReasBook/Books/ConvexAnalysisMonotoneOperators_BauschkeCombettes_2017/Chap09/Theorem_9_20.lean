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

/-- Helper for Theorem 9.20: a real-height epigraph point projects to a base point in the
effective domain, because any real ordinate is strictly below `⊤`. -/
private theorem mem_effectiveDomain_of_mem_real_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hxξ : (x, ξ) ∈ epigraph (fun y : H ↦ (f y : EReal))) :
    x ∈ effectiveDomain f := by
  -- Epigraph membership bounds `f x` by a real value, hence by something strictly below `⊤`.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (mem_epigraph_iff _ _ _ |>.mp hxξ) (EReal.coe_lt_top _)

/-- Helper for Theorem 9.20: outside the effective domain, the value of `f` must be `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∉ effectiveDomain f) :
    (f y : EReal) = ⊤ := by
  -- If the value were finite, it would put `y` back into the effective domain.
  by_contra htop
  exact hy (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

/-- Helper for Theorem 9.20: the projection inequality from Proposition 9.18 normalizes to an
affine lower support inequality on the effective domain. -/
private theorem affine_minorant_on_effectiveDomain_of_projection
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hx : x ∈ effectiveDomain f) (hξ : ξ < (f x : EReal).toReal)
    (hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)) :
    let u : H := ((π - ξ)⁻¹) • (x - p)
    ∀ y ∈ effectiveDomain f,
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (f y : EReal) := by
  have hproj_data :
      max (ξ : EReal) (f p : EReal) ≤ (π : EReal) ∧
        ∀ y ∈ effectiveDomain f,
          ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mp hproj
  rcases hproj_data with ⟨hmax, hvar⟩
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- The projection point lies in the real-height epigraph.
    simpa [hproj] using
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph hp_mem_epigraph
  have hξ_le_pi : ξ ≤ π := by
    -- The max-majorization from Proposition 9.18 already puts `π` above `ξ`.
    have hξ_le_pi' : (ξ : EReal) ≤ (π : EReal) := by
      exact le_trans
        (show (ξ : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_left _ _)
        hmax
    exact_mod_cast hξ_le_pi'
  have hfp_top : (f p : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (f p : EReal) > ⊥ from (f p).2)
  have hfp_le_pi : (f p : EReal).toReal ≤ π := by
    -- Epigraph membership identifies `π` as a real upper bound for the finite value `f p`.
    have hfp_le_pi' : (f p : EReal) ≤ (π : EReal) :=
      mem_epigraph_iff _ _ _ |>.mp hp_mem_epigraph
    have hcast :
        (((f p : EReal).toReal : ℝ) : EReal) ≤ (π : EReal) := by
      simpa [EReal.coe_toReal hfp_top hfp_bot] using hfp_le_pi'
    exact_mod_cast hcast
  have hξ_lt_pi : ξ < π := by
    -- Equality `π = ξ` would force `x = p`, contradicting the choice of `ξ < f x`.
    by_cases hπξ : π = ξ
    · have hvarx :
        ⟪x - p, x - p⟫_ℝ + ((f x : EReal).toReal - π) * (ξ - π) ≤ 0 :=
        hvar x hx
      rw [hπξ, sub_self, mul_zero, add_zero] at hvarx
      have hinner_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ := by
        simpa using (real_inner_self_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ)
      have hinner_eq_zero : ⟪x - p, x - p⟫_ℝ = 0 := by
        nlinarith [hinner_nonneg, hvarx]
      have hxp : x = p := by
        have hsub : x - p = 0 := by
          simpa using inner_self_eq_zero.mp hinner_eq_zero
        exact sub_eq_zero.mp hsub
      have hfp_le_xi : (f p : EReal) ≤ (ξ : EReal) := by
        have hmax_to_xi : max (ξ : EReal) (f p : EReal) ≤ (ξ : EReal) := by
          simpa [hπξ] using hmax
        exact le_trans
          (show (f p : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_right _ _)
          hmax_to_xi
      have hfx_le_xi : (f x : EReal).toReal ≤ ξ := by
        have hfx_top : (f x : EReal) ≠ ⊤ :=
          ne_of_lt (mem_effectiveDomain_iff.mp hx)
        have hfx_bot : (f x : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (f x : EReal) > ⊥ from (f x).2)
        have hfx_le_xi' : (f x : EReal) ≤ (ξ : EReal) := by
          simpa [hxp] using hfp_le_xi
        have hcast :
            (((f x : EReal).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
          simpa [EReal.coe_toReal hfx_top hfx_bot] using hfx_le_xi'
        exact_mod_cast hcast
      linarith
    · exact lt_of_le_of_ne hξ_le_pi (by
        intro hξπ
        exact hπξ hξπ.symm)
  dsimp
  intro y hy
  have hvar :
      ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    hvar y hy
  have hgap_pos : 0 < π - ξ := by
    -- The projection ordinate is strictly above the point chosen below the epigraph.
    exact sub_pos.mpr hξ_lt_pi
  have hinner_le :
      ⟪y - p, x - p⟫_ℝ ≤
        ((f y : EReal).toReal - π) * (π - ξ) := by
    -- Rewrite the variational inequality in terms of the positive gap `π - ξ`.
    nlinarith
  have hscaled :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ ≤
        (f y : EReal).toReal - π := by
    -- Divide by the positive gap to obtain the affine support slope.
    have hdiv : ⟪y - p, x - p⟫_ℝ / (π - ξ) ≤ (f y : EReal).toReal - π := by
      refine (div_le_iff₀ hgap_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hinner_le
    simpa [div_eq_mul_inv, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hreal :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + (f p : EReal).toReal ≤
        (f y : EReal).toReal := by
    -- Replace the intercept `π` by the smaller value `(f p).toReal`.
    linarith
  have hfy_top : (f y : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (f y : EReal) > ⊥ from (f y).2)
  have hcast :
      ((⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ
          + (f p : EReal).toReal : ℝ) : EReal) ≤
        (((f y : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hreal
  -- Replace the finite right-hand side by the original `EReal` value of `f y`.
  simpa [EReal.coe_toReal hfy_top hfy_bot] using hcast

-- Proof sketch: choose a point strictly below the epigraph of `f`, project it onto the closed
-- convex epigraph, and use the projection inequality to obtain a supporting affine functional
-- through the projected point that lies below `f`.
/-- Theorem 9.20: every function in `Γ₀(H)` on a real Hilbert space admits a continuous affine
minorant; more precisely, there exist a point `p ∈ dom f` and a vector `u` such that the affine
functional `y ↦ ⟪y - p, u⟫_ℝ + f(p)` is pointwise bounded above by `f`. -/
theorem exists_affine_minorant_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ p ∈ effectiveDomain f, ∃ u : H, ∀ y : H,
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (f y : EReal) := by
  -- Choose a point of the effective domain and move one unit strictly below the epigraph there.
  rcases hf.2.nonempty with ⟨x, hx⟩
  let ξ : ℝ := (f x : EReal).toReal - 1
  have hξ : ξ < (f x : EReal).toReal := by
    -- The chosen ordinate sits one unit below the finite value of `f x`.
    dsimp [ξ]
    linarith
  let z : H × ℝ :=
    projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  let p : H := z.1
  let π : ℝ := z.2
  have hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) := by
    -- The chosen coordinates are exactly the components of the projection point.
    simp [p, π, z]
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- The projection point lands in the target epigraph.
    simpa [hproj] using
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph hp_mem_epigraph
  have hproj_data :
      max (ξ : EReal) (f p : EReal) ≤ (π : EReal) ∧
        ∀ y ∈ effectiveDomain f,
          ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mp hproj
  have hξ_lt_pi : ξ < π := by
    -- The same contradiction argument as in the helper shows the projection height is strictly above `ξ`.
    rcases hproj_data with ⟨hmax, hvar⟩
    have hξ_le_pi : ξ ≤ π := by
      have hξ_le_pi' : (ξ : EReal) ≤ (π : EReal) := by
        exact le_trans
          (show (ξ : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_left _ _)
          hmax
      exact_mod_cast hξ_le_pi'
    by_cases hπξ : π = ξ
    · have hvarx :
          ⟪x - p, x - p⟫_ℝ + ((f x : EReal).toReal - π) * (ξ - π) ≤ 0 :=
        hvar x hx
      rw [hπξ, sub_self, mul_zero, add_zero] at hvarx
      have hinner_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ := by
        simpa using (real_inner_self_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ)
      have hinner_eq_zero : ⟪x - p, x - p⟫_ℝ = 0 := by
        nlinarith [hinner_nonneg, hvarx]
      have hxp : x = p := by
        have hsub : x - p = 0 := by
          simpa using inner_self_eq_zero.mp hinner_eq_zero
        exact sub_eq_zero.mp hsub
      have hfp_le_xi : (f p : EReal) ≤ (ξ : EReal) := by
        have hmax_to_xi : max (ξ : EReal) (f p : EReal) ≤ (ξ : EReal) := by
          simpa [hπξ] using hmax
        exact le_trans
          (show (f p : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_right _ _)
          hmax_to_xi
      have hfx_top : (f x : EReal) ≠ ⊤ :=
        ne_of_lt (mem_effectiveDomain_iff.mp hx)
      have hfx_bot : (f x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (f x : EReal) > ⊥ from (f x).2)
      have hfx_le_xi : (f x : EReal).toReal ≤ ξ := by
        have hfx_le_xi' : (f x : EReal) ≤ (ξ : EReal) := by
          simpa [hxp] using hfp_le_xi
        have hcast :
            (((f x : EReal).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
          simpa [EReal.coe_toReal hfx_top hfx_bot] using hfx_le_xi'
        exact_mod_cast hcast
      linarith
    · exact lt_of_le_of_ne hξ_le_pi (by
        intro hξπ
        exact hπξ hξπ.symm)
  let u : H := ((π - ξ)⁻¹) • (x - p)
  refine ⟨p, hp, u, ?_⟩
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · -- On the effective domain, the normalized projection inequality gives the affine support bound.
    simpa [u] using
      affine_minorant_on_effectiveDomain_of_projection hf hx hξ hproj y hy
  · -- Off the effective domain, the right-hand side is `⊤`, so the inequality is automatic.
    simpa [value_eq_top_of_not_mem_effectiveDomain hy] using
      (le_top :
        ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (⊤ : EReal))

end ERealFunction
