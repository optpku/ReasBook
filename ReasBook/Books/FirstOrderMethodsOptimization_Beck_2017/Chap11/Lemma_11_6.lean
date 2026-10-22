/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {p : ℕ}
variable [Nonempty (Fin p)]

/- Lemma 11.6 is `source-facing`: it isolates the two textbook inequalities needed for the
convex CBPG descent estimate. The finite block extrema already have Chapter 11 owners upstream,
namely `cbpg_min_block_stepsize` and `cbpg_max_block_stepsize` from Lemma 11.4, so this file
should reuse those owners instead of re-spelling the finite `inf'`/`sup'` terms locally. -/

/-- The coefficient
`L_min / (2 p (L_f + L_max)^2 R^2)` from Lemma 11.6, using the Chapter 11 owners
`cbpg_min_block_stepsize Li` and `cbpg_max_block_stepsize Li` of the finite block extrema. -/
def cbpg_quadratic_gap_constant
    (Lf : NNReal) (Li : Fin p → PosReal) (R : PosReal) : ℝ :=
  ((cbpg_min_block_stepsize Li : PosReal) : ℝ) /
    (2 * (p : ℝ) *
      (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
      ((R : ℝ) ^ (2 : ℕ)))

/-- Expanding `cbpg_quadratic_gap_constant` yields the textbook coefficient
`L_min / (2 p (L_f + L_max)^2 R^2)` with
`L_min = cbpg_min_block_stepsize Li` and `L_max = cbpg_max_block_stepsize Li`. -/
@[simp] theorem cbpg_quadratic_gap_constant_def
    (Lf : NNReal) (Li : Fin p → PosReal) (R : PosReal) :
    cbpg_quadratic_gap_constant Lf Li R =
      ((cbpg_min_block_stepsize Li : PosReal) : ℝ) /
        (2 * (p : ℝ) *
          (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^
            (2 : ℕ)) *
          ((R : ℝ) ^ (2 : ℕ))) :=
  rfl

end

section

variable {p : ℕ}
variable [Nonempty (Fin p)]
variable {X : Type u} [NormedAddCommGroup X]
variable {Lf : NNReal} {Li : Fin p → PosReal}
variable {F : X → EReal} {x : ℕ → X} {FOpt : ℝ}

/-- The source quadratic gap estimate `(11.18)` used in Lemma 11.6. -/
def cbpgObjectiveGapSqBound
    (Lf : NNReal) (Li : Fin p → PosReal) (Rα : PosReal)
    (F : X → EReal) (x : ℕ → X) (FOpt : ℝ) (k : ℕ) : Prop :=
  (((F (x (k + 1))).toReal - FOpt) ^ (2 : ℕ)) ≤
    ((p : ℝ) *
      (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
      ((Rα : ℝ) ^ (2 : ℕ)) *
      (‖x k - x (k + 1)‖ ^ (2 : ℕ)))

/-- The source sufficient-decrease estimate `(11.11)` used in Lemma 11.6. -/
def cbpgStepDecreaseBound
    (Li : Fin p → PosReal) (F : X → EReal) (x : ℕ → X) (k : ℕ) : Prop :=
  (((((cbpg_min_block_stepsize Li : PosReal) : ℝ) / 2) *
      (‖x k - x (k + 1)‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
    (F (x k) - F (x (k + 1)))

/-- Helper for Lemma 11.6: the denominator in
`cbpg_quadratic_gap_constant Lf Li Rα` is strictly positive. -/
private lemma cbpgQuadraticGapDenominatorPos
    (Rα : PosReal) :
    0 <
      2 * (p : ℝ) *
        (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
        ((Rα : ℝ) ^ (2 : ℕ)) := by
  obtain ⟨i⟩ := ‹Nonempty (Fin p)›
  -- A witness of `Fin p` turns the nonempty-block hypothesis into `0 < p`.
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i.1) i.2)
  -- The smoothness and radius factors are nonnegative/positive by construction.
  have hLf_nonneg : 0 ≤ (Lf : ℝ) := by
    exact_mod_cast Lf.2
  have hmax_pos : 0 < ((cbpg_max_block_stepsize Li : PosReal) : ℝ) :=
    PosReal.coe_pos (cbpg_max_block_stepsize Li)
  have hsum_pos :
      0 < (Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ) :=
    add_pos_of_nonneg_of_pos hLf_nonneg hmax_pos
  have hsum_sq_pos :
      0 <
        (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) := by
    positivity
  have hR_sq_pos : 0 < ((Rα : ℝ) ^ (2 : ℕ)) := by
    have hR_pos : 0 < (Rα : ℝ) := PosReal.coe_pos Rα
    nlinarith [sq_pos_of_pos hR_pos]
  -- Combining the positive factors gives the desired denominator positivity.
  have hfront_pos : 0 < 2 * (p : ℝ) := by
    positivity
  have hleft_pos :
      0 <
        2 * (p : ℝ) *
          (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) :=
    mul_pos hfront_pos hsum_sq_pos
  exact mul_pos hleft_pos hR_sq_pos

/-- Helper for Lemma 11.6: the quadratic-gap coefficient is nonnegative. -/
private lemma cbpgQuadraticGapConstantNonneg
    (Rα : PosReal) :
    0 ≤ cbpg_quadratic_gap_constant Lf Li Rα := by
  -- The coefficient is a positive numerator divided by the positive denominator above.
  rw [cbpg_quadratic_gap_constant_def]
  exact div_nonneg
    (le_of_lt (PosReal.coe_pos (cbpg_min_block_stepsize Li)))
    (le_of_lt (cbpgQuadraticGapDenominatorPos (Lf := Lf) (Li := Li) Rα))

/-- Helper for Lemma 11.6: scaling the quadratic-gap estimate by the textbook constant produces
the real sufficient-decrease term. -/
private lemma cbpgQuadraticGapRealBound
    (Rα : PosReal) (k : ℕ)
    (hGapSq : cbpgObjectiveGapSqBound Lf Li Rα F x FOpt k) :
    cbpg_quadratic_gap_constant Lf Li Rα *
        (((F (x (k + 1))).toReal - FOpt) ^ (2 : ℕ)) ≤
      (((cbpg_min_block_stepsize Li : PosReal) : ℝ) / 2) *
        (‖x k - x (k + 1)‖ ^ (2 : ℕ)) := by
  let A : ℝ :=
    (p : ℝ) *
      (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
      ((Rα : ℝ) ^ (2 : ℕ))
  let c : ℝ := cbpg_quadratic_gap_constant Lf Li Rα
  let m : ℝ := ((cbpg_min_block_stepsize Li : PosReal) : ℝ)
  let n : ℝ := ‖x k - x (k + 1)‖ ^ (2 : ℕ)
  -- First rewrite the source inequality in terms of the condensed scalar `A`.
  have hGapSq' :
      (((F (x (k + 1))).toReal - FOpt) ^ (2 : ℕ)) ≤ A * n := by
    simpa [cbpgObjectiveGapSqBound, A, n, mul_assoc] using hGapSq
  -- The denominator is `2 * A`, so positivity of the textbook denominator gives `A > 0`.
  have htwoA_pos : 0 < 2 * A := by
    simpa [A, mul_assoc] using
      cbpgQuadraticGapDenominatorPos (Lf := Lf) (Li := Li) Rα
  have htwo_pos : 0 < (2 : ℝ) := by
    norm_num
  have hA_pos : 0 < A := by
    nlinarith
  have hA_ne : A ≠ 0 := hA_pos.ne'
  -- Scale the quadratic-gap estimate by the nonnegative coefficient.
  have hscaled :
      c * (((F (x (k + 1))).toReal - FOpt) ^ (2 : ℕ)) ≤ c * (A * n) := by
    exact mul_le_mul_of_nonneg_left hGapSq'
      (cbpgQuadraticGapConstantNonneg (Lf := Lf) (Li := Li) Rα)
  -- Then cancel the common factor `A` in the scaled right-hand side.
  have hcancel : c * (A * n) = (m / 2) * n := by
    calc
      c * (A * n) = ((m / (2 * A)) * A) * n := by
        simp [A, c, m, cbpg_quadratic_gap_constant_def, mul_assoc]
      _ = (((m * A) / (2 * A)) * n) := by
        rw [div_mul_eq_mul_div]
      _ = (m / 2) * n := by
        rw [mul_div_mul_right _ _ hA_ne]
  rw [hcancel] at hscaled
  simpa [c, m] using hscaled

/-- Lemma 11.6: abstracting the convex-CBPG proof to its two source inequalities,
the quadratic objective-gap control `(11.18)` together with the sufficient-decrease estimate
`(11.11)` implies the one-step lower bound
`F(xᵏ) - F(xᵏ⁺¹) ≥ c * (F(xᵏ⁺¹) - F_opt)^2`, where
`c = L_min / (2 p (L_f + L_max)^2 R_α^2)`. -/
theorem cbpg_step_decrease_ge_sq_objective_gap
    (Rα : PosReal) (k : ℕ)
    (hGapSq : cbpgObjectiveGapSqBound Lf Li Rα F x FOpt k)
    (hStep : cbpgStepDecreaseBound Li F x k) :
    F (x k) - F (x (k + 1)) ≥
      ((cbpg_quadratic_gap_constant Lf Li Rα *
          (((F (x (k + 1))).toReal - FOpt) ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Route correction: the source prox argument is already packaged in `hGapSq`,
  -- so the proof only needs scalar cancellation in `ℝ` and one final `EReal` cast.
  have hreal :
      cbpg_quadratic_gap_constant Lf Li Rα *
          (((F (x (k + 1))).toReal - FOpt) ^ (2 : ℕ)) ≤
        (((cbpg_min_block_stepsize Li : PosReal) : ℝ) / 2) *
          (‖x k - x (k + 1)‖ ^ (2 : ℕ)) :=
    cbpgQuadraticGapRealBound (Lf := Lf) (Li := Li) (F := F) (x := x)
      (FOpt := FOpt) Rα k hGapSq
  let lhs : ℝ :=
    cbpg_quadratic_gap_constant Lf Li Rα *
      (((F (x (k + 1))).toReal - FOpt) ^ (2 : ℕ))
  let rhs : ℝ :=
    (((cbpg_min_block_stepsize Li : PosReal) : ℝ) / 2) *
      (‖x k - x (k + 1)‖ ^ (2 : ℕ))
  -- Transport the real comparison into `EReal` and compose it with `(11.11)`.
  have hereal : (lhs : EReal) ≤ (rhs : EReal) := by
    exact EReal.coe_le_coe hreal
  simpa [lhs, rhs] using hereal.trans hStep

end
