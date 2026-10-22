/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ScaledProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply Proposition 12.22(i) with `μ = 1` to rewrite `{}¹(γ f)` as
-- `γ ({}^γ f)`, then combine this with the proximal-point formula from Definition 12.23 for the
-- scaled function `γ f` and simplify the quadratic coefficient.
/-- Remark 12.24: equation `(12.24)` states that for `f ∈ Γ₀(H)`, `γ ∈ ℝ_{++}`, and `x ∈ H`, the
`γ`-Moreau envelope equals `f (Prox_{γ f} x)` plus the quadratic term
`‖x - Prox_{γ f} x‖² / (2γ)`. -/
theorem moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    ({}^[γ] f) x =
      (f (Prox[γ, f, hf] x) : EReal) +
        ((((‖x - Prox[γ, f, hf] x‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
  let p := Prox[γ, f, hf] x
  have hone : γ * (1 : PosReal) = γ := by
    ext
    simp
  have hscale := congrArg (fun g : H → EReal ↦ g x)
    (moreauEnvelope_smul_eq_smul_moreauEnvelope f γ (1 : PosReal))
  have hscale' : {}^[(1 : PosReal)] (γ • f) x = (γ : EReal) * ({}^[γ] f) x := by
    simpa [hone, smul_eq_mul] using hscale
  have hprox : IsProxPoint (γ • f) x p := by
    simpa [p, scaledProximityOperator] using
      proximityOperator_isProxPoint
        (γ • f)
        (hasUniqueProxPoint_of_mem_gammaZero (γ • f) (smul_mem_gammaZero f hf γ))
        x
  have hunit := (isProxPoint_iff_moreauEnvelope_eq (γ • f) x p).mp hprox
  have hγ_pos_real : 0 < (γ : ℝ) := γ.2
  have hγ_ne_zero_real : (γ : ℝ) ≠ 0 := ne_of_gt hγ_pos_real
  have hγ_pos : 0 < (γ : EReal) := by
    exact_mod_cast hγ_pos_real
  have hγ_ne_zero : (γ : EReal) ≠ 0 := ne_of_gt hγ_pos
  have hγ_ne_top : (γ : EReal) ≠ ⊤ := by
    simp
  have hscaled :
      (γ : EReal) * ({}^[γ] f) x =
        (γ : EReal) * (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
    calc
      (γ : EReal) * ({}^[γ] f) x = {}^[(1 : PosReal)] (γ • f) x := hscale'.symm
      _ = ((γ • f) p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := hunit
      _ = (γ : EReal) * (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
        simp
  calc
    ({}^[γ] f) x = (γ : EReal) * (({}^[γ] f) x / (γ : EReal)) := by
      symm
      exact EReal.mul_div_cancel (show (γ : EReal) ≠ ⊥ by simp) hγ_ne_top hγ_ne_zero
    _ = ((γ : EReal) * ({}^[γ] f) x) / (γ : EReal) := by
      rw [EReal.mul_div]
    _ =
        ((γ : EReal) * (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal))) /
          (γ : EReal) := by
      rw [hscaled]
    _ =
        ((γ : EReal) * (f p : EReal)) / (γ : EReal) +
          ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) / (γ : EReal) := by
      rw [EReal.add_div_of_nonneg_right (le_of_lt hγ_pos)]
    _ = (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) / (γ : EReal) := by
      rw [← EReal.mul_div]
      rw [EReal.mul_div_cancel (show (γ : EReal) ≠ ⊥ by simp) hγ_ne_top hγ_ne_zero]
    _ = (f p : EReal) + ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
      rw [← EReal.coe_div]
      ring_nf

end ERealFunction
