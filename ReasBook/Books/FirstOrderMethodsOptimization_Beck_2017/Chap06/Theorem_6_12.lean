/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Pointwise

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 6.12 is `source-facing` in the Chapter 6 proximal-mapping API. Domain sampling in the
minimal scaling-transport closure identifies:

- `prox[...]` and `proximal_objective` from Definition 6.1 as the `core/canonical` owners,
- `proximal_mapping_scaling_translation` from Theorem 6.11 as the direct upstream transport
  theorem of the same kind,
- `proximal_mapping_precompose_continuousAffineMap` from Theorem 6.15 as the later stronger
  `bridge/view` generalization.

The primitive data here are only `g`, `lam`, and `x`. The inverse-scaling formula is therefore a
specialization of the existing Chapter 6 transport theorem, not a second owner-level minimizer
comparison API. -/

-- Proof sketch: specialize Theorem 6.11 with scale `lam⁻¹`, zero translation, and the objective
-- `g' z = λ g z`. This gives the required proximal transport immediately, up to rewriting the
-- transported scaled objective `((lam⁻¹)^2 • g')` pointwise to `z ↦ g z / λ`.
/-- Theorem 6.12: for the scaled pullback `f y = λ g (λ⁻¹ • y)`, the proximal set of `f` at `x`
is the scalar multiple by `λ` of the proximal set of `z ↦ g z / λ` at `λ⁻¹ • x`. This is the
chapter's set-valued formulation of the textbook identity
`prox_f(x) = λ prox_{g / λ}(x / λ)`. The textbook properness hypothesis on `g` is redundant for
this minimizer-set identity, so the canonical Lean statement omits it. -/
theorem proximal_mapping_smul_precompose_inv_smul
    (g : E → EReal) (lam : ℝ) (hlam : lam ≠ 0) (x : E) :
    prox[fun y : E ↦ (lam : EReal) * g (lam⁻¹ • y)] x =
      lam • prox[fun z : E ↦ g z / (lam : EReal)] (lam⁻¹ • x) := by
  let g' : E → EReal := fun z ↦ (lam : EReal) * g z
  have htransport :=
    proximal_mapping_scaling_translation g' lam⁻¹ (inv_ne_zero hlam) (0 : E) x
  have hcoeff : (lam⁻¹ ^ 2 : ℝ) * lam = lam⁻¹ := by
    field_simp [hlam]
  have hscale :
      (((lam⁻¹) ^ 2 : ℝ) : EReal) • g' =
        fun z : E ↦ g z / (lam : EReal) := by
    funext z
    change ((((lam⁻¹) ^ 2 : ℝ) : EReal) * ((lam : EReal) * g z)) =
      g z / (lam : EReal)
    rw [← mul_assoc]
    rw [show ((((lam⁻¹) ^ 2 : ℝ) : EReal) * (lam : EReal)) =
        ((((lam⁻¹ ^ 2 : ℝ) * lam : ℝ) : EReal)) by
      norm_num [EReal.coe_mul]]
    rw [show ((((lam⁻¹ ^ 2 : ℝ) * lam : ℝ) : EReal)) = ((lam⁻¹ : ℝ) : EReal) by
      exact_mod_cast hcoeff]
    rw [show ((lam⁻¹ : ℝ) : EReal) = (lam : EReal)⁻¹ by
      simpa using (EReal.coe_inv lam)]
    rw [div_eq_mul_inv, mul_comm]
  rw [hscale] at htransport
  simpa [g', Set.image_smul, hlam] using htransport

end
