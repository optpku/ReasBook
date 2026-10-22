/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_60
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_43

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

-- Proof sketch: lift `h` canonically to `f := h.toEReal`. Chapter 6 already provides convexity
-- and `(1 / μ)`-smoothness of `x ↦ (M[μ, f] x).toReal`. The lower bound comes from evaluating the
-- Moreau infimum at `u = x`. For the upper bound, choose the canonical proximal point `u` of the
-- scaled lift `μ f` at `x`; the Moreau value then equals `h u + ‖x - u‖² / (2 μ)`, and the
-- global Lipschitz bound gives `h x ≤ h u + ℓ_h ‖x - u‖`. Optimizing the scalar quadratic
-- `-t² / (2 μ) + ℓ_h t` yields the error term `(ℓ_h² / 2) μ`.
/-- Theorem 10.51: if a real-valued convex function `h` is globally `ℓ_h`-Lipschitz, then for
every `μ > 0` its real-valued Moreau envelope is a `1 / μ`-smooth approximation of `h` with
nonnegative parameters `(1, ℓ_h^2 / 2)`. -/
theorem moreau_envelope_real_is_smooth_approximation
    (h : E → ℝ) (hconv : ConvexOn ℝ Set.univ h) (ℓh : NNReal) (hlip : LipschitzWith ℓh h)
    (μ : PosReal) :
    IsSmoothApproximationNonneg
      h
      (fun x ↦ (M[μ, h.toEReal] x).toReal)
      1
      (ℓh ^ 2 / 2)
      μ := by
  let f : E → EReal := h.toEReal
  have hf_proper : IsProperExtendedRealFunction f := Function.toEReal_isProper h
  have hf_closed : LowerSemicontinuous f := Function.toEReal_lowerSemicontinuous_of_lipschitz hlip
  have hf_convex : is_convex_function f := Function.toEReal_isConvexFunction hconv
  refine
    { convex := ?_
      lower_le := ?_
      upper_le := ?_
      smooth := ?_ }
  · simpa [f] using
      moreau_envelope_toReal_convexOn_of_proper_convex f μ hf_proper hf_closed hf_convex
  · intro x
    have hmoreau_le : M[μ, f] x ≤ (h x : EReal) := by
      rw [moreau_envelope_apply]
      simpa [f] using
        (iInf_le
          (fun u : E ↦
            f u + ((((1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) : ℝ) : EReal)))
          x)
    rcases moreau_envelope_eq_real_of_proper_convex f μ hf_proper hf_closed hf_convex x with
      ⟨r, hr⟩
    rw [hr] at hmoreau_le
    rw [hr]
    exact_mod_cast hmoreau_le
  · intro x
    rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex μ with
      ⟨hscaled_proper, hscaled_closed, hscaled_convex⟩
    rcases prox_eq_singleton_of_proper_closed_convex
        (((μ : EReal) • f)) hscaled_proper hscaled_closed hscaled_convex x with
      ⟨u, hprox⟩
    have hmoreau_eq :
        (M[μ, f] x).toReal =
          h u + (1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) := by
      have hmoreau_eqR :
          (M[μ, f] x).toReal =
            (((h u : EReal) +
              ((((1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) : ℝ) : EReal))).toReal) := by
        simpa [f] using congrArg EReal.toReal
          (moreau_envelope_eq_of_scaled_prox_eq_singleton hprox)
      rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
        (EReal.coe_ne_bot _), EReal.toReal_coe, EReal.toReal_coe] at hmoreau_eqR
      simpa using hmoreau_eqR
    have hlip_xu : h x ≤ h u + (ℓh : ℝ) * ‖x - u‖ := by
      have hdist : |h x - h u| ≤ (ℓh : ℝ) * ‖x - u‖ := by
        simpa [Real.dist_eq, dist_eq_norm] using hlip.dist_le_mul x u
      have hsub : h x - h u ≤ (ℓh : ℝ) * ‖x - u‖ := by
        exact le_trans (le_abs_self (h x - h u)) hdist
      linarith
    have hβ :
        (((ℓh ^ (2 : ℕ) / 2 : NNReal) : ℝ)) = (ℓh : ℝ) ^ (2 : ℕ) / 2 := by
      simp
    have hquad :
        -(1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) + (ℓh : ℝ) * ‖x - u‖ ≤
          (((ℓh ^ (2 : ℕ) / 2 : NNReal) : ℝ) * (μ : ℝ)) := by
      rw [hβ]
      have hsq :
          0 ≤ ‖x - u‖ ^ (2 : ℕ) - 2 * (μ : ℝ) * (ℓh : ℝ) * ‖x - u‖ +
            (μ : ℝ) ^ (2 : ℕ) * (ℓh : ℝ) ^ (2 : ℕ) := by
        nlinarith [sq_nonneg (‖x - u‖ - (μ : ℝ) * (ℓh : ℝ))]
      have hμne : (μ : ℝ) ≠ 0 := by
        exact_mod_cast μ.2.ne'
      field_simp [hμne]
      nlinarith [hsq]
    calc
      h x ≤ h u + (ℓh : ℝ) * ‖x - u‖ := hlip_xu
      _ = (M[μ, f] x).toReal +
            (-(1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) + (ℓh : ℝ) * ‖x - u‖) := by
          rw [hmoreau_eq]
          ring
      _ ≤ (M[μ, f] x).toReal + (((ℓh ^ (2 : ℕ) / 2 : NNReal) : ℝ) * (μ : ℝ)) := by
          simpa [add_assoc, add_comm, add_left_comm] using
            add_le_add_left hquad ((M[μ, f] x).toReal)
  · have hμinv : ((μ : ℝ)⁻¹).toNNReal = (PosReal.toNNReal μ)⁻¹ := by
      apply NNReal.coe_injective
      rw [NNReal.coe_inv, Real.coe_toNNReal _ (le_of_lt (inv_pos.mpr μ.2))]
      simp [PosReal.coe_toNNReal]
    simpa [f, hμinv] using
      moreau_envelope_toReal_is_inv_mu_smooth f hf_proper hf_closed hf_convex μ

end
