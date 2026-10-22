/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_54
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_58

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Example 6.59 is `source-facing`: the source object is the finite-product `ℓ¹` regularizer
`f(x) = ∑ i |x_i|`. Domain sampling in the chapter identifies the owner split:

- `‖x‖₁` from Example 6.8 is the chapter's source-facing owner for the finite-product `ℓ¹`
  regularizer, with `separableSum (fun _ ↦ absolute_value_penalty 1)` only as a bridge/view,
- `moreau_envelope_separableSum_eq_sum` from Theorem 6.58 is the core splitting theorem for the
  bridge presentation,
- `absolute_value_penalty 1` from Lemma 6.5 is the scalar summand `t ↦ |t|`,
- `H[μ]` from Definition 6.8 / Example 6.54 is the scalar Huber owner.

Accordingly, the public statements below are phrased for the canonical `ℓ¹` owner
`fun y : E ↦ (‖y‖₁ : EReal)`, and the separable-sum spelling is used only internally as the
bridge to Theorem 6.58. -/

-- Proof sketch: rewrite the Euclidean `ℓ¹` penalty `x ↦ ‖x‖₁` through the bridge theorem
-- `separableSum_absolute_value_penalty_eq_l1_norm_penalty` with `λ = 1`, then apply
-- `moreau_envelope_separableSum_eq_sum` to the canonical `PiLp.separableSum` bridge on the
-- constant scalar family
-- `fun _ : ι ↦ absolute_value_penalty 1`.
/-- The Moreau envelope of the finite-product `ℓ¹` penalty `x ↦ ‖x‖₁ = ∑ i |x_i|` splits as the
sum of the coordinatewise Moreau envelopes of the scalar absolute-value penalty `t ↦ |t|`. -/
theorem moreau_envelope_l1_sum_eq_sum_coordinate_moreau
    (μ : PosReal) (x : E) :
    M[μ, fun y : E ↦ (‖y‖₁ : EReal)] x = ∑ i, M[μ, absolute_value_penalty 1] (x i) := by
  have hl1 :
      (fun y : E ↦ (‖y‖₁ : EReal)) = PiLp.separableSum (fun _ : ι ↦ absolute_value_penalty 1) := by
    funext y
    simpa using (separableSum_absolute_value_penalty_eq_l1_norm_penalty 1 y).symm
  rw [hl1]
  exact moreau_envelope_separableSum_eq_sum
    (fun _ : ι ↦ absolute_value_penalty 1)
    (fun _ ↦ ⟨0, by simp [mem_effective_domain]⟩)
    μ x

-- Proof sketch: start from
-- `moreau_envelope_l1_sum_eq_sum_coordinate_moreau`. For each coordinate, specialize the scalar
-- bridge `moreau_envelope_norm_penalty_eq_huber_function` from Example 6.54 at `E = ℝ`, where
-- `norm_penalty 1` is definitionally the absolute-value penalty `t ↦ |t|`.
/-- Example 6.59: for the finite-product `ℓ¹` penalty `f(x) = ‖x‖₁ = ∑ i |x_i|`, the Moreau
envelope at `x` is the sum of the scalar Huber values on the coordinates:
`M_f^μ(x) = ∑ i, M_{|·|}^μ(x_i) = ∑ i, H[μ] (x_i)`. -/
theorem moreau_envelope_l1_sum_eq_sum_huber
    (μ : PosReal) (x : E) :
    M[μ, fun y : E ↦ (‖y‖₁ : EReal)] x = ∑ i, (H[μ] (x i) : EReal) := by
  rw [moreau_envelope_l1_sum_eq_sum_coordinate_moreau]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  simpa [absolute_value_penalty, norm_penalty] using
    (show M[μ, norm_penalty 1] (x i) = ((H[μ] (x i) : ℝ) : EReal) from
      congrFun (moreau_envelope_norm_penalty_eq_huber_function μ) (x i))

-- Proof sketch: apply `EReal.toReal` to `moreau_envelope_l1_sum_eq_sum_huber` and simplify the
-- finite sum of coerced real Huber values.
/-- Applying `EReal.toReal` to the finite-product `ℓ¹` Moreau-envelope identity yields the
real-valued Huber expansion `M_f^μ(x) = ∑ i, H[μ] (x_i)`. -/
theorem moreau_envelope_l1_sum_toReal_eq_sum_huber
    (μ : PosReal) (x : E) :
    (M[μ, fun y : E ↦ (‖y‖₁ : EReal)] x).toReal = ∑ i, H[μ] (x i) := by
  have hx : M[μ, fun y : E ↦ (‖y‖₁ : EReal)] x = ∑ i, (H[μ] (x i) : EReal) := by
    simpa using moreau_envelope_l1_sum_eq_sum_huber μ x
  have hsum :
      (∑ i, (H[μ] (x i) : EReal)) = (((∑ i, H[μ] (x i) : ℝ) : EReal)) := by
    simpa using (ereal_coe_sum Finset.univ (fun i : ι ↦ H[μ] (x i))).symm
  rw [hx, hsum]
  simp

end
