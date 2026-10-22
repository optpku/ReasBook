/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Pointwise

section

variable {E : Type u} [NormedAddCommGroup E]

/- Lemma 6.57 is `source-facing` in the Moreau-envelope API. The chapter already owns
`M[μ, f]` and `ω(μ)` in Definition 6.7, and `M[μ, f] = f □ ω(μ)` is already the canonical
`core/canonical` owner-level abstraction. This file should therefore keep only the textbook
scaling identity on that owner surface, rather than introducing a parallel scaled-objective
wrapper or reducing the public statement to a pointwise evaluation. The primitive data are just
`f`, `μ`, and `λ`; the scaled function is derived by the canonical pointwise scalar action on
`E → EReal`. -/

-- Proof sketch: unfold `M[μ, f]` to `f □ ω(μ)`, pull the positive scalar `λ` through the
-- defining infimum, and rewrite the quadratic term by
-- `λ * ((1 / (2 * μ)) ‖x - u‖²) = (1 / (2 * (μ / λ))) ‖x - u‖²`. The resulting objective is
-- exactly the Moreau-envelope owner for the pointwise scaled function `λ • f` with parameter
-- `μ / λ`.
/-- Helper for Lemma 6.57: multiplying an `EReal` infimum by a positive finite scalar can be
done pointwise under the infimum sign. -/
lemma smul_iInf_eq_iInf_smul_of_posreal {ι : Sort*} (g : ι → EReal) (lam : PosReal) :
    ((lam : EReal) * (⨅ i, g i)) = ⨅ i, (lam : EReal) * g i := by
  have hlam_pos : 0 < (lam : EReal) := by
    exact_mod_cast PosReal.coe_pos lam
  have hlam_nonneg : 0 ≤ (lam : EReal) := le_of_lt hlam_pos
  have hlam_ne_top : (lam : EReal) ≠ ⊤ := EReal.coe_ne_top (lam : ℝ)
  refine le_antisymm ?_ ?_
  · -- Every pointwise lower bound remains a lower bound after scaling by `λ`.
    refine le_iInf fun i ↦ ?_
    exact mul_le_mul_of_nonneg_left (iInf_le g i) hlam_nonneg
  · -- Divide the scaled infimum back by `λ` to recover a lower bound for the original family.
    have hdiv : (⨅ i, (lam : EReal) * g i) / (lam : EReal) ≤ ⨅ i, g i := by
      refine le_iInf fun i ↦ ?_
      rw [EReal.div_le_iff_le_mul hlam_pos hlam_ne_top]
      exact iInf_le (fun j ↦ (lam : EReal) * g j) i
    exact (EReal.div_le_iff_le_mul hlam_pos hlam_ne_top).1 hdiv

/-- Helper for Lemma 6.57: positive scaling distributes over infimal convolution. -/
lemma smul_infimal_convolution_eq_infimal_convolution_smul
    (h1 h2 : E → EReal) (lam : PosReal) :
    (lam : EReal) • (h1 □ h2) = ((lam : EReal) • h1) □ ((lam : EReal) • h2) := by
  ext x
  have hlam_nonneg : 0 ≤ (lam : EReal) := by
    exact_mod_cast le_of_lt (PosReal.coe_pos lam)
  have hlam_ne_top : (lam : EReal) ≠ ⊤ := EReal.coe_ne_top (lam : ℝ)
  -- Move the scalar through the defining infimum of the infimal convolution.
  calc
    (lam : EReal) * ((h1 □ h2) x)
        = (lam : EReal) * (⨅ u : E, h1 u + h2 (x - u)) := by
            rw [infimal_convolution_apply]
    _ = ⨅ u : E, (lam : EReal) * (h1 u + h2 (x - u)) :=
          smul_iInf_eq_iInf_smul_of_posreal (g := fun u : E ↦ h1 u + h2 (x - u)) lam
    _ = ⨅ u : E, ((lam : EReal) • h1) u + ((lam : EReal) • h2) (x - u) := by
          -- Distribute the positive scalar across the translated objective.
          refine iInf_congr fun u ↦ ?_
          rw [Pi.smul_apply, smul_eq_mul, Pi.smul_apply, smul_eq_mul,
            EReal.left_distrib_of_nonneg_of_ne_top hlam_nonneg hlam_ne_top]
    _ = (((lam : EReal) • h1) □ ((lam : EReal) • h2)) x := by
          rw [infimal_convolution_apply]

/-- Helper for Lemma 6.57: scaling the Moreau quadratic kernel by `λ` replaces `μ` with `μ / λ`.
-/
lemma smul_moreau_quadratic_kernel_eq_moreau_quadratic_kernel_div (μ lam : PosReal) :
    (lam : EReal) • (ω(μ) : E → EReal) = ω(μ / lam) := by
  ext x
  -- Rewrite both kernels to the same explicit quadratic penalty and compare coefficients in `ℝ`.
  rw [Pi.smul_apply, smul_eq_mul, moreau_quadratic_kernel_apply,
    moreau_quadratic_kernel_apply, ← EReal.coe_mul]
  congr 1
  rw [PosReal.coe_div]
  field_simp [show (μ : ℝ) ≠ 0 by exact ne_of_gt (PosReal.coe_pos μ),
    show (lam : ℝ) ≠ 0 by exact ne_of_gt (PosReal.coe_pos lam)]

/-- Lemma 6.57: scaling the Moreau envelope by a positive scalar `λ` is the same as taking the
Moreau envelope of the scaled function `λ f` with parameter `μ / λ`. The textbook proper,
closed, and convex hypotheses on `f` are redundant for this scaling identity, and the owner-level
equality itself does not need a separate positivity hypothesis on `μ` because that is already
encoded by `μ : PosReal`. -/
theorem smul_moreau_envelope_eq_moreau_envelope_scaled_function
    (f : E → EReal) (μ lam : PosReal) :
    (lam : EReal) • M[μ, f] =
      M[μ / lam, (lam : EReal) • f] := by
  -- Stay on the owner-level Moreau-envelope representation `M[μ, f] = f □ ω(μ)`.
  calc
    (lam : EReal) • M[μ, f]
        = (lam : EReal) • (f □ ω(μ)) := by
            rfl
    _ = ((lam : EReal) • f) □ ((lam : EReal) • ω(μ)) :=
          smul_infimal_convolution_eq_infimal_convolution_smul f (ω(μ)) lam
    _ = ((lam : EReal) • f) □ ω(μ / lam) := by
          rw [smul_moreau_quadratic_kernel_eq_moreau_quadratic_kernel_div (E := E)]
    _ = M[μ / lam, (lam : EReal) • f] := by
          rfl

end
