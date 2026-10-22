/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section02_part1

/-- Unit-sphere values of a dual functional are bounded above (local version). -/
lemma dualNormDef_unitSphere_bddAbove_section02 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Module.Dual ℝ E) :
    BddAbove { r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = DualPairing s x } := by
  classical
  let s' : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap s
  refine ⟨‖s'‖, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  have hle_abs : DualPairing s x ≤ |DualPairing s x| := le_abs_self _
  have hle_norm : |DualPairing s x| ≤ ‖s'‖ * ‖x‖ := by
    simpa [DualPairing, s', Real.norm_eq_abs] using (s'.le_opNorm x)
  have hle : DualPairing s x ≤ ‖s'‖ * ‖x‖ := hle_abs.trans hle_norm
  simpa [hx] using hle

/-- Dual pairing is bounded by the dual norm times the primal norm (local version). -/
lemma dualPairing_le_dualNormDef_mul_norm_section02 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (s : Module.Dual ℝ E) (x : E) :
    DualPairing s x ≤ DualNormDef s * ‖x‖ := by
  classical
  by_cases hx : x = 0
  · simp [hx, DualPairing]
  · have hxnorm : ‖x‖ ≠ 0 := (norm_ne_zero_iff.mpr hx)
    let u : E := (‖x‖)⁻¹ • x
    have hu : ‖u‖ = 1 := by
      simpa [u] using (norm_smul_inv_norm (x := x) hx)
    have hmem :
        DualPairing s u ∈ { r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = DualPairing s x } := by
      exact ⟨u, hu, rfl⟩
    have hbdd :
        BddAbove { r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = DualPairing s x } :=
      dualNormDef_unitSphere_bddAbove_section02 (s := s)
    have hle_dual : DualPairing s u ≤ DualNormDef s := by
      simpa [DualNormDef] using (le_csSup hbdd hmem)
    have hmul :
        ‖x‖ * DualPairing s u ≤ ‖x‖ * DualNormDef s := by
      exact mul_le_mul_of_nonneg_left hle_dual (norm_nonneg _)
    have hxexpr : ‖x‖ • u = x := by
      simp [u, smul_smul, hxnorm]
    have hlin : DualPairing s x = ‖x‖ * DualPairing s u := by
      calc
        DualPairing s x = DualPairing s (‖x‖ • u) := by simp [hxexpr]
        _ = ‖x‖ * DualPairing s u := by simp [DualPairing, map_smul, smul_eq_mul]
    have hle : DualPairing s x ≤ ‖x‖ * DualNormDef s := by
      simpa [hlin] using hmul
    simpa [mul_comm] using hle

/-- Quadratic growth at a minimizer of a strongly convex function. -/
lemma strongConvexOn_lower_quadratic_of_isMinOn {E2 : Type*} [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] (Q2 : Set E2) (f : E2 → ℝ) (m : ℝ) (u0 : E2)
    (hconv : StrongConvexOn Q2 m f) (hu0mem : u0 ∈ Q2) (hu0 : IsMinOn f Q2 u0) :
    ∀ u ∈ Q2, f u0 + (m / 2) * ‖u - u0‖ ^ (2 : ℕ) ≤ f u := by
  intro u hu
  have haux : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      f u0 + (1 - t) * ((m / 2) * ‖u0 - u‖ ^ (2 : ℕ)) ≤ f u := by
    intro t ht
    rcases hconv with ⟨hQ2conv, hconvI⟩
    have ht0 : 0 < t := ht.1
    have hnonneg_t : 0 ≤ t := le_of_lt ht0
    have hnonneg_one_sub : 0 ≤ 1 - t := by linarith [ht.2]
    have hsum : (1 - t) + t = 1 := by linarith
    have hut : (1 - t) • u0 + t • u ∈ Q2 := by
      refine hQ2conv hu0mem hu hnonneg_one_sub hnonneg_t ?_
      linarith
    have hmin : f u0 ≤ f ((1 - t) • u0 + t • u) := (isMinOn_iff).1 hu0 _ hut
    have hsc0 := hconvI (x := u0) hu0mem (y := u) hu
    have hsc1 := hsc0 (a := 1 - t) (b := t) hnonneg_one_sub hnonneg_t hsum
    have hsc :
        f ((1 - t) • u0 + t • u) ≤ (1 - t) * f u0 + t * f u -
          (1 - t) * t * ((m / 2) * ‖u0 - u‖ ^ (2 : ℕ)) := by
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsc1
    have hle :
        f u0 ≤ (1 - t) * f u0 + t * f u -
          (1 - t) * t * ((m / 2) * ‖u0 - u‖ ^ (2 : ℕ)) := le_trans hmin hsc
    have hle' :
        t * (f u0 + (1 - t) * ((m / 2) * ‖u0 - u‖ ^ (2 : ℕ))) ≤ t * f u := by
      linarith
    have hle'' :
        f u0 + (1 - t) * ((m / 2) * ‖u0 - u‖ ^ (2 : ℕ)) ≤ f u := by
      exact le_of_mul_le_mul_left hle' ht0
    exact hle''
  have hle :
      f u0 + (m / 2) * ‖u0 - u‖ ^ (2 : ℕ) ≤ f u :=
    le_of_forall_one_sub_mul_le haux
  simpa [norm_sub_rev] using hle

/-- Smoothed maximizers minimize the negated objective. -/
lemma smoothedMaximizer_isMinOn {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ) (x : E1) (u : E2)
    (hU : IsSmoothedMaximizer Q2 A phihat d2 μ x u) :
    IsMinOn (fun v => phihat v + μ * d2 v - A x v) Q2 u := by
  intro v hv
  have hmax := hU.2 v hv
  have hmax' : -(A x u - phihat u - μ * d2 u) ≤ -(A x v - phihat v - μ * d2 v) := by
    exact neg_le_neg hmax
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmax'
