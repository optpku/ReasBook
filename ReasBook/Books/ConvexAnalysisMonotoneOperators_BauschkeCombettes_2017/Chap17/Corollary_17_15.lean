/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_47

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

private theorem mem_iff_of_inter_ball_eq {E : Type*} [PseudoMetricSpace E]
    {C D : Set E} {x z : E} {ε : ℝ}
    (hEq : C ∩ Metric.ball x ε = D ∩ Metric.ball x ε)
    (hz : z ∈ Metric.ball x ε) :
    z ∈ C ↔ z ∈ D := by
  constructor
  · intro hzC
    have hzCD : z ∈ C ∩ Metric.ball x ε := ⟨hzC, hz⟩
    rw [hEq] at hzCD
    exact hzCD.1
  · intro hzD
    have hzDC : z ∈ D ∩ Metric.ball x ε := ⟨hzD, hz⟩
    rw [← hEq] at hzDC
    exact hzDC.1

private theorem center_add_scale_sub_mem_of_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {C : Set E} {x y : E} {ε : ℝ}
    (hC_convex : Convex ℝ C) (hx : x ∈ C) (hy : y ∈ C) (hε : 0 < ε) :
    x + (ε / (ε + ‖y - x‖)) • (y - x) ∈ C := by
  let t : ℝ := ε / (ε + ‖y - x‖)
  have ht_le_one : t ≤ 1 := by
    dsimp [t]
    rw [div_le_iff₀]
    · nlinarith [hε, norm_nonneg (y - x)]
    · positivity
  have ht_nonneg : 0 ≤ t := by positivity
  have h_one_sub_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht_le_one
  have hsum : (1 - t) + t = 1 := by ring
  have hcombo : (1 - t) • x + t • y ∈ C :=
    hC_convex hx hy h_one_sub_nonneg ht_nonneg hsum
  have hxyt : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub, sub_eq_add_neg]
    calc
      x + (t • y + -(t • x)) = x + -(t • x) + t • y := by
        abel_nf
      _ = (1 - t) • x + t • y := by
        rw [sub_smul, one_smul, sub_eq_add_neg]
  rw [hxyt]
  exact hcombo

private theorem center_add_scale_sub_mem_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x y : E} {ε : ℝ} (hε : 0 < ε) :
    x + (ε / (ε + ‖y - x‖)) • (y - x) ∈ Metric.ball x ε := by
  let t : ℝ := ε / (ε + ‖y - x‖)
  have htnorm_lt : t * ‖y - x‖ < ε := by
    have hdiv_lt : ε * ‖y - x‖ / (ε + ‖y - x‖) < ε := by
      rw [div_lt_iff₀]
      · nlinarith [hε, norm_nonneg (y - x)]
      · positivity
    simpa [t, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv_lt
  have ht_nonneg : 0 ≤ t := by positivity
  have hz_sub : x + t • (y - x) - x = t • (y - x) := by
    rw [smul_sub, sub_eq_add_neg]
    abel_nf
  have hnorm_lt : ‖x + t • (y - x) - x‖ < ε := by
    simpa [hz_sub, norm_smul, Real.norm_of_nonneg ht_nonneg] using htnorm_lt
  simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C D : Set H} {x : H}

-- Proof sketch: assume `x ∈ C ∩ D`. For each `y` in one set, move from `x` a short convex
-- combination toward `y`; this point stays inside the local ball where `C` and `D` agree, so the
-- defining support inequalities for `N[C] x` and `N[D] x` transfer to each other.
/-- Corollary 17.15 (1): if `x ∈ C ∩ D` and convex subsets `C` and `D` agree on some open ball
around `x`, then their normal cones at `x` coincide. -/
theorem normalCone_eq_of_convex_inter_ball_eq
    (hC_convex : Convex ℝ C) (hD_convex : Convex ℝ D)
    (hx : x ∈ C ∩ D)
    (hlocal : ∃ ε : ℝ, 0 < ε ∧ C ∩ Metric.ball x ε = D ∩ Metric.ball x ε) :
    N[C] x = N[D] x := by
  rcases hlocal with ⟨ε, hε, hEq⟩
  have hxC : x ∈ C := hx.1
  have hxD : x ∈ D := hx.2
  rw [Set.normalCone_of_mem hxC, Set.normalCone_of_mem hxD]
  ext u
  simp only [Set.mem_setOf_eq]
  rw [innerSupremumOn_sub_singleton_le_zero_iff, innerSupremumOn_sub_singleton_le_zero_iff]
  constructor
  · intro hu y hyD
    let t : ℝ := ε / (ε + ‖y - x‖)
    let z : H := x + t • (y - x)
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    have hzD : z ∈ D :=
      center_add_scale_sub_mem_of_convex hD_convex hxD hyD hε
    have hzBall : z ∈ Metric.ball x ε :=
      center_add_scale_sub_mem_ball hε
    have hzC : z ∈ C := (mem_iff_of_inter_ball_eq hEq hzBall).2 hzD
    have hz_nonpos : ⟪z - x, u⟫_ℝ ≤ 0 := hu z hzC
    have hz_sub : z - x = t • (y - x) := by
      dsimp [z]
      rw [smul_sub, sub_eq_add_neg]
      abel_nf
    rw [hz_sub, real_inner_smul_left] at hz_nonpos
    by_contra hy_pos
    have : 0 < t * ⟪y - x, u⟫_ℝ := mul_pos ht_pos (lt_of_not_ge hy_pos)
    linarith
  · intro hu y hyC
    let t : ℝ := ε / (ε + ‖y - x‖)
    let z : H := x + t • (y - x)
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    have hzC : z ∈ C :=
      center_add_scale_sub_mem_of_convex hC_convex hxC hyC hε
    have hzBall : z ∈ Metric.ball x ε :=
      center_add_scale_sub_mem_ball hε
    have hzD : z ∈ D := (mem_iff_of_inter_ball_eq hEq hzBall).1 hzC
    have hz_nonpos : ⟪z - x, u⟫_ℝ ≤ 0 := hu z hzD
    have hz_sub : z - x = t • (y - x) := by
      dsimp [z]
      rw [smul_sub, sub_eq_add_neg]
      abel_nf
    rw [hz_sub, real_inner_smul_left] at hz_nonpos
    by_contra hy_pos
    have : 0 < t * ⟪y - x, u⟫_ℝ := mul_pos ht_pos (lt_of_not_ge hy_pos)
    linarith

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C D : Set E} {x : E}

-- Proof sketch: assume `x ∈ C ∩ D`. The local equality transports short translated rays between
-- `C` and `D`, so the generating cones of `C - {x}` and `D - {x}` coincide. Taking closures and
-- using the canonical owner formula `T[C] x = closure (cone (C - {x}))` at points of membership
-- gives the result.
/-- Corollary 17.15 (2): if `x ∈ C ∩ D` and convex subsets `C` and `D` agree on some open ball
around `x`, then their tangent cones at `x` coincide. -/
theorem tangentCone_eq_of_convex_inter_ball_eq
    (hC_convex : Convex ℝ C) (hD_convex : Convex ℝ D)
    (hx : x ∈ C ∩ D)
    (hlocal : ∃ ε : ℝ, 0 < ε ∧ C ∩ Metric.ball x ε = D ∩ Metric.ball x ε) :
    T[C] x = T[D] x := by
  rcases hlocal with ⟨ε, hε, hEq⟩
  have hxC : x ∈ C := hx.1
  have hxD : x ∈ D := hx.2
  have hCx_convex : Convex ℝ (C - ({x} : Set E)) := by
    simpa [sub_eq_add_neg] using hC_convex.add (convex_singleton (-x))
  have hDx_convex : Convex ℝ (D - ({x} : Set E)) := by
    simpa [sub_eq_add_neg] using hD_convex.add (convex_singleton (-x))
  have hcone_subset : cone (C - ({x} : Set E)) ⊆ cone (D - ({x} : Set E)) := by
    intro v hv
    rcases (mem_cone_iff_exists_pos_smul_mem hCx_convex).1 hv with ⟨a, ha, hv⟩
    rcases hv with ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hyC, x', hx', rfl⟩
    have hx' : x' = x := by simpa using hx'
    subst x'
    let t : ℝ := ε / (ε + ‖y - x‖)
    let z : E := x + t • (y - x)
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    have hzC : z ∈ C :=
      center_add_scale_sub_mem_of_convex hC_convex hxC hyC hε
    have hzBall : z ∈ Metric.ball x ε :=
      center_add_scale_sub_mem_ball hε
    have hzD : z ∈ D := (mem_iff_of_inter_ball_eq hEq hzBall).1 hzC
    refine (mem_cone_iff_exists_pos_smul_mem hDx_convex).2 ⟨a / t, div_pos ha ht_pos, ?_⟩
    refine ⟨z - x, ?_, ?_⟩
    · exact ⟨z, hzD, x, by simp, by simp [z, sub_eq_add_neg, add_assoc]⟩
    · have hz_sub : z - x = t • (y - x) := by
        dsimp [z]
        rw [smul_sub, sub_eq_add_neg]
        abel_nf
      have hscale : (a / t) * t = a := by
        field_simp [show t ≠ 0 by positivity]
      simp [hz_sub, smul_smul, hscale]
  have hcone_subset' : cone (D - ({x} : Set E)) ⊆ cone (C - ({x} : Set E)) := by
    intro v hv
    rcases (mem_cone_iff_exists_pos_smul_mem hDx_convex).1 hv with ⟨a, ha, hv⟩
    rcases hv with ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hyD, x', hx', rfl⟩
    have hx' : x' = x := by simpa using hx'
    subst x'
    let t : ℝ := ε / (ε + ‖y - x‖)
    let z : E := x + t • (y - x)
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    have hzD : z ∈ D :=
      center_add_scale_sub_mem_of_convex hD_convex hxD hyD hε
    have hzBall : z ∈ Metric.ball x ε :=
      center_add_scale_sub_mem_ball hε
    have hzC : z ∈ C := (mem_iff_of_inter_ball_eq hEq hzBall).2 hzD
    refine (mem_cone_iff_exists_pos_smul_mem hCx_convex).2 ⟨a / t, div_pos ha ht_pos, ?_⟩
    refine ⟨z - x, ?_, ?_⟩
    · exact ⟨z, hzC, x, by simp, by simp [z, sub_eq_add_neg, add_assoc]⟩
    · have hz_sub : z - x = t • (y - x) := by
        dsimp [z]
        rw [smul_sub, sub_eq_add_neg]
        abel_nf
      have hscale : (a / t) * t = a := by
        field_simp [show t ≠ 0 by positivity]
      simp [hz_sub, smul_smul, hscale]
  rw [Set.tangentCone_of_mem hxC, Set.tangentCone_of_mem hxD]
  apply congrArg closure
  exact Set.Subset.antisymm hcone_subset hcone_subset'

end
