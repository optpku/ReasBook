/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_19

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Example 6.54 is `bridge/view`. Domain sampling:
- `norm_penalty` from Example 6.19 is the source-facing owner for the penalty `x ↦ ‖x‖`;
- `M[μ, f]` from Definition 6.7 is the chapter owner for Moreau envelopes;
- `H[μ]` from Definition 6.8 is the source-facing owner for the Huber function;
- `moreau_envelope_eq_of_scaled_prox_eq_singleton` from Definition 6.7 is the canonical
  Moreau/prox bridge at the envelope owner.

The primitive data already lives upstream in those owners. The new content here is only the bridge
identifying the `EReal`-valued Moreau envelope of `norm_penalty 1` with the canonical Huber owner
after the ambient coercion from `ℝ` to `EReal`. The pointwise piecewise formula and the real-valued
`toReal` restatement are derived API, not primitive data for this file. Although one proof route
can pass through the inner-product-space proximal singleton from Example 6.19, the bridge
statements themselves only use the normed-space owner layer, so the public ambient assumptions are
kept at `[NormedSpace ℝ E]`. -/

/-- Helper for Example 6.54: on the quadratic Huber branch, the triangle inequality gives the
required lower bound for every penalized norm objective. -/
lemma quadratic_branch_le_penalized_norm (μ : PosReal) (x u : E) (hball : ‖x‖ ≤ μ) :
    ‖x‖ ^ (2 : ℕ) / (2 * (μ : ℝ)) ≤ ‖u‖ + ‖x - u‖ ^ (2 : ℕ) / (2 * (μ : ℝ)) := by
  -- The triangle inequality isolates the scalar inequality that controls the infimum.
  have hμ_pos : 0 < (μ : ℝ) := PosReal.coe_pos μ
  have hμ_ne : (μ : ℝ) ≠ 0 := hμ_pos.ne'
  have htri : ‖x‖ ≤ ‖u‖ + ‖x - u‖ := by
    calc
      ‖x‖ = ‖u + (x - u)‖ := by abel_nf
      _ ≤ ‖u‖ + ‖x - u‖ := norm_add_le _ _
  have hu_lower : ‖x‖ - ‖x - u‖ ≤ ‖u‖ := by
    linarith
  have hsplit :
      ((2 : ℝ) * μ * ‖u‖ + ‖x - u‖ ^ (2 : ℕ)) / ((2 : ℝ) * μ) =
        ‖u‖ + ‖x - u‖ ^ (2 : ℕ) / ((2 : ℝ) * μ) := by
    field_simp [hμ_ne]
  by_cases hdist : ‖x - u‖ ≤ ‖x‖
  · -- When the residual norm is no larger than `‖x‖`, both radii stay inside the ball of radius `μ`.
    have hmul : ‖x‖ ^ (2 : ℕ) ≤ ((2 : ℝ) * μ) * ‖u‖ + ‖x - u‖ ^ (2 : ℕ) := by
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hmul (show 0 ≤ (2 : ℝ) * μ by positivity)
    simpa [hsplit] using hdiv
  · -- Otherwise the quadratic residual term alone already dominates the quadratic Huber branch.
    have hdist_lt : ‖x‖ < ‖x - u‖ := lt_of_not_ge hdist
    have hmul : ‖x‖ ^ (2 : ℕ) ≤ ((2 : ℝ) * μ) * ‖u‖ + ‖x - u‖ ^ (2 : ℕ) := by
      have hsq : ‖x‖ ^ (2 : ℕ) ≤ ‖x - u‖ ^ (2 : ℕ) := by
        nlinarith [norm_nonneg (x - u), norm_nonneg x, hdist_lt]
      nlinarith [norm_nonneg u, hsq]
    have hdiv := div_le_div_of_nonneg_right hmul (show 0 ≤ (2 : ℝ) * μ by positivity)
    simpa [hsplit] using hdiv

/-- Helper for Example 6.54: the affine Huber branch is always below the penalized norm
objective. -/
lemma affine_branch_le_penalized_norm (μ : PosReal) (x u : E) :
    ‖x‖ - (μ : ℝ) / 2 ≤ ‖u‖ + ‖x - u‖ ^ (2 : ℕ) / (2 * (μ : ℝ)) := by
  -- Triangle inequality again gives the linear term needed for the scalar completion.
  have hμ_pos : 0 < (μ : ℝ) := PosReal.coe_pos μ
  have hμ_ne : (μ : ℝ) ≠ 0 := hμ_pos.ne'
  have htri : ‖x‖ ≤ ‖u‖ + ‖x - u‖ := by
    calc
      ‖x‖ = ‖u + (x - u)‖ := by abel_nf
      _ ≤ ‖u‖ + ‖x - u‖ := norm_add_le _ _
  have hu_lower : ‖x‖ - ‖x - u‖ ≤ ‖u‖ := by
    linarith
  have hsq : 0 ≤ (‖x - u‖ - (μ : ℝ)) ^ (2 : ℕ) / (2 * (μ : ℝ)) := by
    positivity
  have haux : ‖x‖ - (μ : ℝ) / 2 ≤ ‖x‖ - ‖x - u‖ + ‖x - u‖ ^ (2 : ℕ) / (2 * (μ : ℝ)) := by
    have hident :
        ‖x‖ - ‖x - u‖ + ‖x - u‖ ^ (2 : ℕ) / (2 * (μ : ℝ)) =
          ‖x‖ - (μ : ℝ) / 2 + (‖x - u‖ - (μ : ℝ)) ^ (2 : ℕ) / (2 * (μ : ℝ)) := by
      field_simp [hμ_ne]
      ring
    rw [hident]
    linarith
  have hrewrite :
      ‖u‖ + ‖x - u‖ ^ (2 : ℕ) / (2 * (μ : ℝ)) =
        ‖u‖ + ‖x - u‖ ^ (2 : ℕ) / (2 * (μ : ℝ)) := rfl
  rw [hrewrite]
  linarith

/-- Helper for Example 6.54: every penalized norm value dominates the Huber value at the same
point. -/
lemma huber_function_le_norm_penalty_penalized (μ : PosReal) (x u : E) :
    ((H[μ] x : ℝ) : EReal) ≤
      norm_penalty 1 u + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Rewrite to a real inequality and then split on the Huber branch.
  rw [norm_penalty_apply, ← EReal.coe_add, EReal.coe_le_coe_iff, huber_function_apply]
  by_cases hball : ‖x‖ ≤ μ
  · simpa [hball, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      quadratic_branch_le_penalized_norm (μ := μ) (x := x) (u := u) hball
  · simpa [hball, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      affine_branch_le_penalized_norm (μ := μ) (x := x) (u := u)

/-- Helper for Example 6.54: the radial shrinkage candidate attains the Huber value in the
penalized norm objective. -/
lemma norm_penalty_penalized_eq_huber_at_radial_candidate (μ : PosReal) (x : E) :
    norm_penalty 1 ((1 - μ / max ‖x‖ μ) • x) +
      ((((1 / (2 * μ) : ℝ) * ‖x - ((1 - μ / max ‖x‖ μ) • x)‖ ^ (2 : ℕ)) : ℝ) : EReal) =
        ((H[μ] x : ℝ) : EReal) := by
  -- Rewrite to a real identity and compute the candidate in the two radial regimes.
  rw [norm_penalty_apply, ← EReal.coe_add, EReal.coe_eq_coe_iff, huber_function_apply]
  by_cases hball : ‖x‖ ≤ μ
  · have hμ_ne : (μ : ℝ) ≠ 0 := (PosReal.coe_pos μ).ne'
    rw [max_eq_right hball]
    have hcoeff : (1 - (μ : ℝ) / μ : ℝ) = 0 := by
      rw [div_self hμ_ne, sub_self]
    -- On the closed ball the candidate is the origin, so the value is purely quadratic.
    rw [if_pos hball]
    simp [hcoeff]
  · have houter : μ < ‖x‖ := lt_of_not_ge hball
    have hnorm_pos : 0 < ‖x‖ := lt_trans (PosReal.coe_pos μ) houter
    have hmax : max ‖x‖ μ = ‖x‖ := max_eq_left (le_of_lt houter)
    have hcoeff_nonneg : 0 ≤ 1 - μ / ‖x‖ := by
      have hrewrite : (1 - μ / ‖x‖ : ℝ) = (‖x‖ - μ) / ‖x‖ := by
        field_simp [hnorm_pos.ne']
      rw [hrewrite]
      exact div_nonneg (by linarith) hnorm_pos.le
    have hdist_coeff_nonneg : 0 ≤ μ / ‖x‖ := by
      exact div_nonneg (le_of_lt (PosReal.coe_pos μ)) hnorm_pos.le
    have hnorm_candidate : ‖((1 - μ / ‖x‖) • x : E)‖ = ‖x‖ - μ := by
      rw [norm_smul, Real.norm_of_nonneg hcoeff_nonneg]
      field_simp [hnorm_pos.ne']
    have hsub_eq : x - ((1 - μ / ‖x‖) • x) = (μ / ‖x‖) • x := by
      calc
        x - ((1 - μ / ‖x‖) • x) = (1 : ℝ) • x - ((1 - μ / ‖x‖) • x) := by simp
        _ = ((1 : ℝ) - (1 - μ / ‖x‖)) • x := by rw [← sub_smul]
        _ = (μ / ‖x‖) • x := by
          congr 1
          field_simp [hnorm_pos.ne']
          ring
    have hdist_candidate : ‖x - ((1 - μ / ‖x‖) • x)‖ = μ := by
      rw [hsub_eq, norm_smul, Real.norm_of_nonneg hdist_coeff_nonneg]
      have hscalar : (μ / ‖x‖ : ℝ) * ‖x‖ = μ := by
        field_simp [hnorm_pos.ne']
      exact hscalar
    -- Outside the ball the candidate has norm `‖x‖ - μ` and residual norm `μ`.
    rw [if_neg hball, hmax, hnorm_candidate, hdist_candidate]
    have hquad : ((1 / (2 * (μ : ℝ)) : ℝ) * μ ^ (2 : ℕ)) = μ / 2 := by
      field_simp [((PosReal.coe_pos μ).ne')]
    rw [hquad]
    ring

/-- Helper for Example 6.54: coercing the Huber function to `EReal` preserves its standard
piecewise formula. -/
lemma coe_huber_function_apply_piecewise (μ : PosReal) (x : E) :
    ((H[μ] x : ℝ) : EReal) =
      if ‖x‖ ≤ μ then
        ((‖x‖ ^ (2 : ℕ) / (2 * μ) : ℝ) : EReal)
      else
        ((‖x‖ - μ / 2 : ℝ) : EReal) := by
  -- This is the real Huber formula with each branch viewed in `EReal`.
  by_cases hball : ‖x‖ ≤ μ
  · rw [huber_function_apply, if_pos hball, if_pos hball]
    congr 1
    ring
  · rw [huber_function_apply, if_neg hball, if_neg hball]

-- Route correction: the singleton-prox bridge needs inner-product structure, so the proof here
-- works directly from `moreau_envelope_apply` by matching a universal lower bound with an
-- explicit radial candidate.
/-- Example 6.54 in owner form: in a real normed space, the Moreau envelope of the norm is the
canonical Huber function viewed in `EReal`. -/
theorem moreau_envelope_norm_penalty_eq_huber_function (μ : PosReal) :
    M[μ, norm_penalty 1] = fun x : E ↦ ((H[μ] x : ℝ) : EReal) := by
  funext x
  -- Compare the infimum with the radial candidate from both sides.
  rw [moreau_envelope_apply]
  refine le_antisymm ?_ ?_
  · calc
      ⨅ u : E, norm_penalty 1 u + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
          norm_penalty 1 ((1 - μ / max ‖x‖ μ) • x) +
            ((((1 / (2 * μ) : ℝ) * ‖x - ((1 - μ / max ‖x‖ μ) • x)‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
        exact iInf_le _ ((1 - μ / max ‖x‖ μ) • x)
      _ = ((H[μ] x : ℝ) : EReal) :=
        norm_penalty_penalized_eq_huber_at_radial_candidate (μ := μ) (x := x)
  · -- The lower bound holds for every candidate in the infimum.
    refine le_iInf ?_
    intro u
    exact huber_function_le_norm_penalty_penalized (μ := μ) (x := x) (u := u)

-- Proof sketch: evaluate
-- `moreau_envelope_norm_penalty_eq_huber_function` at `x` and unfold `H[μ]` via
-- `huber_function_apply`; the displayed `EReal` identity is the same piecewise formula after
-- coercing the real branches to `EReal`.
/-- Example 6.54 (1): in a real normed space, for `f(x) = ‖x‖` and `μ > 0`, the Moreau
envelope of `f` has the usual piecewise Huber form: it is `‖x‖² / (2 μ)` on `‖x‖ ≤ μ` and
`‖x‖ - μ / 2` on `‖x‖ > μ`. -/
theorem moreau_envelope_norm_penalty_eq_piecewise (μ : PosReal) (x : E) :
    M[μ, norm_penalty 1] x =
      if ‖x‖ ≤ μ then
        ((‖x‖ ^ (2 : ℕ) / (2 * μ) : ℝ) : EReal)
      else
        ((‖x‖ - μ / 2 : ℝ) : EReal) := by
  -- Evaluate the function identity at `x` and rewrite the Huber owner pointwise.
  calc
    M[μ, norm_penalty 1] x = ((H[μ] x : ℝ) : EReal) := by
      simpa using congrFun (moreau_envelope_norm_penalty_eq_huber_function (E := E) μ) x
    _ = if ‖x‖ ≤ μ then
          ((‖x‖ ^ (2 : ℕ) / (2 * μ) : ℝ) : EReal)
        else
          ((‖x‖ - μ / 2 : ℝ) : EReal) :=
      coe_huber_function_apply_piecewise (μ := μ) (x := x)

-- Proof sketch: apply `EReal.toReal` pointwise to
-- `moreau_envelope_norm_penalty_eq_huber_function` and simplify with `EReal.toReal_coe`.
/-- Example 6.54 (2): in a real normed space, for every `μ > 0`, the real-valued Moreau
envelope of the norm agrees pointwise with the canonical Huber function `H[μ]`. -/
theorem moreau_envelope_norm_penalty_toReal_eq_huber_function (μ : PosReal) :
    EReal.toReal ∘ M[μ, norm_penalty 1] = (H[μ] : E → ℝ) := by
  funext x
  -- Apply `EReal.toReal` to the `EReal`-valued identity pointwise.
  have hx : M[μ, norm_penalty 1] x = ((H[μ] x : ℝ) : EReal) := by
    simpa using congrFun (moreau_envelope_norm_penalty_eq_huber_function (E := E) μ) x
  simpa [Function.comp] using congrArg EReal.toReal hx

end
