/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Example_8_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Example_10_30

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open ERealFunction

section StrictConvex

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [StrictConvexSpace ℝ H]

-- Proof sketch: apply Example 10.30(2) to the norm with the monotone range map `t ↦ t ^ 2`.
-- The resulting composition is exactly `x ↦ ‖x‖ ^ 2`, which is strictly convex by Example 8.23.
/-- On a strictly convex real normed space, the norm is strictly quasiconvex. -/
theorem strictlyQuasiconvex_norm :
    StrictlyQuasiconvex ((norm : H → ℝ).toEReal.asEReal) := by
  let φ : Set.range (norm : H → ℝ) → ℝ := fun t ↦ (t : ℝ) ^ (2 : ℝ)
  have hφ : Monotone φ := by
    intro s t hst
    have hs0 : 0 ≤ (s : ℝ) := by
      rcases s.2 with ⟨x, hx⟩
      rw [← hx]
      exact norm_nonneg x
    exact Real.rpow_le_rpow hs0 hst (by positivity)
  have hcomp : StrictConvexOn ℝ Set.univ (φ ∘ Set.rangeFactorization (norm : H → ℝ)) := by
    simpa [φ] using (strictConvexOn_norm_rpow 2 (by norm_num : (1 : ℝ) < 2))
  simpa [φ] using
    (strictlyQuasiconvex_of_strictConvexOn_comp_range hφ hcomp)

-- Proof sketch: Example 8.23 gives strict convexity of `x ↦ ‖x‖ ^ 2` on a strictly convex real
-- normed space. Apply Example 10.30(2) with the increasing range map `t ↦ t ^ 2` to obtain
-- strict quasiconvexity of the norm itself, then compose with the strictly increasing range map
-- `t ↦ t ^ p` via Example 10.30(1).
/-- Example 10.31 (1): clause (i). For `p > 0`, the norm-power function is strictly
quasiconvex. -/
theorem strictlyQuasiconvex_norm_rpow (p : ℝ) (hp : 0 < p) :
    StrictlyQuasiconvex ((fun x : H ↦ ‖x‖ ^ p).toEReal.asEReal) := by
  let φ : Set.range (norm : H → ℝ) → ℝ := fun t ↦ (t : ℝ) ^ p
  have hφ : StrictMono φ := by
    intro s t hst
    have hs0 : 0 ≤ (s : ℝ) := by
      rcases s.2 with ⟨x, hx⟩
      rw [← hx]
      exact norm_nonneg x
    exact Real.rpow_lt_rpow hs0 hst hp
  have hnorm : StrictlyQuasiconvex ((norm : H → ℝ).toEReal.asEReal) := strictlyQuasiconvex_norm
  simpa [φ] using
    (strictlyQuasiconvex_comp_strictMono_range hnorm hφ)

end StrictConvex

section NontrivialNormed

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [Nontrivial H]

-- Proof sketch: evaluate Jensen convexity at a nonzero vector `z` and `0` with a coefficient
-- `α ∈ (0, 1)`; the required inequality becomes `α ^ p ≤ α`, which fails for `0 < p < 1`.
/-- Example 10.31 (2): clause (ii), first part. If `H` is nontrivial and `0 < p < 1`, then the
norm-power function is not convex on the whole space. -/
theorem not_convexOn_univ_norm_rpow_of_lt_one (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ¬ ConvexOn ℝ Set.univ (fun x : H ↦ ‖x‖ ^ p) := by
  intro hconv
  obtain ⟨z, hz⟩ := exists_ne (0 : H)
  have hineq :
      ‖(1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (0 : H)‖ ^ p ≤
        (1 / 2 : ℝ) * ‖z‖ ^ p + (1 / 2 : ℝ) * ‖(0 : H)‖ ^ p := by
    exact hconv.2 (by simp : z ∈ Set.univ) (by simp : (0 : H) ∈ Set.univ)
      (by norm_num) (by norm_num) (by norm_num)
  have hineq' : ((1 / 2 : ℝ) * ‖z‖) ^ p ≤ (1 / 2 : ℝ) * ‖z‖ ^ p := by
    rw [smul_zero, add_zero, norm_smul, Real.norm_of_nonneg (by norm_num), norm_zero,
      Real.zero_rpow hp.ne', mul_zero, add_zero] at hineq
    exact hineq
  have hpow :
      ((1 / 2 : ℝ) ^ p) * ‖z‖ ^ p ≤ (1 / 2 : ℝ) * ‖z‖ ^ p := by
    calc
      ((1 / 2 : ℝ) ^ p) * ‖z‖ ^ p = (((1 / 2 : ℝ) * ‖z‖) ^ p) := by
        symm
        exact Real.mul_rpow (by norm_num : 0 ≤ (1 / 2 : ℝ)) (norm_nonneg z)
      _ ≤ (1 / 2 : ℝ) * ‖z‖ ^ p := hineq'
  have hzpow_pos : 0 < ‖z‖ ^ p := by
    exact Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _
  have hhalf_le : (1 / 2 : ℝ) ^ p ≤ 1 / 2 := by
    exact _root_.le_of_mul_le_mul_right
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hpow) hzpow_pos
  exact not_le_of_gt (Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hp1) hhalf_le

-- Proof sketch: if a modulus `φ` made the canonical `EReal` lift of the norm-power uniformly
-- quasiconvex, then applying the defining inequality on a nonzero ray at the symmetric points
-- `(s - t) z` and `(s + t) z` would give `φ (2t) / 4 ≤ (s + t)^p - s^p`; letting `s → ∞` forces
-- `φ (2t) = 0` for every `t > 0`, contradicting the modulus axiom.
/-- Example 10.31 (3): clause (ii), second part. If `H` is nontrivial and `0 < p < 1`, then the
norm-power function is not uniformly quasiconvex. -/
theorem not_uniformlyQuasiconvex_norm_rpow_of_lt_one
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ¬ ∃ φ : NNReal → EReal,
      UniformlyQuasiconvex ((fun x : H ↦ ‖x‖ ^ p).toEReal.asEReal) φ := sorry

end NontrivialNormed
