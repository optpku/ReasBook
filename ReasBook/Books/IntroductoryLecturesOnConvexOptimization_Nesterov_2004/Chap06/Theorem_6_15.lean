/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_53
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_54
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_65
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_66
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Algorithm_6_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators StrongConvex WeightSequenceNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 6.15 lies in the Chapter 6 strong-convex conditional-gradient domain.

Mandatory domain-style sampling:
- `initialLinearizationGap` in `Definition_6_54`, the nearby chapter source-facing owner of the
  initial quantity `V₀`, contrasted with this theorem's zero-initialized error term;
- `Ψ ∈ 𝒮^0_σΨ(Q)` / `mem_S0On_iff` in `Definition_6_65`, the chapter owner for positive
  fixed-parameter strong convexity on the feasible set;
- `stronglyConvexCompositeErrorBound` in `Definition_6_66`, the nearby chapter owner with the
  nonzero initial term `a₀ V₀`;
- `LinearOracleCompositeMethod` in `Algorithm_6_4`, the chapter owner of the iterate/oracle data
  for method `(6.4.12)`.

Best owner abstraction:
- source-facing: the weighted upper bound for method `(6.4.12)` under the chapter strong-convexity
  owner, with the source-faithful zero-initialized recursive error term `\hat B_{v,t}`;
- core/canonical: `LinearOracleCompositeMethod`, `Ψ ∈ 𝒮^0_σΨ(Q)`,
  and the local recursion `zeroInitStronglyConvexCompositeErrorBound`;
- bridge/view: `mem_S0On_iff`, used only to recover `0 < σΨ` and `StrongConvexOn Q σΨ Ψ`
  internally, together with the nearby chapter owner `stronglyConvexCompositeErrorBound` for the
  non-source-normalized variant.

Primitive data:
- the feasible set `Q`, objective `f`, ambient regularizer `Ψ`, and method data;
- the weight sequence `a`, normalized by `a 0 = 0`, and the Hölder-style parameters `v`, `Gv`,
  `D`.

Derived API:
- the weighted affine-linearization upper bound at time `t`;
- the source recursion `\hat B_{v,0} = 0`,
  `\hat B_{v,t+1} = \hat B_{v,t} + (a_{t+1}^{1+2v} / A_{t+1}^{2v}) G_v^2 D^{2v} / (2 σ_Ψ)`.
-/

-- Semantic recall: `lean_leansearch` found no reusable nearby owner for the source recursion
-- `\hat B_{v,0} = 0`, so the corresponding error-term owner is kept local in this file.
/-- The zero-initialized error term `\hat B_{v,t}` from Theorem 6.15. -/
def zeroInitStronglyConvexCompositeErrorBound
    (a : ℕ → ℝ) (v Gv D sigmaPsi : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 =>
      zeroInitStronglyConvexCompositeErrorBound a v Gv D sigmaPsi t +
        (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * sigmaPsi))

/-- The source error term starts from `\hat B_{v,0} = 0`. -/
theorem zeroInitStronglyConvexCompositeErrorBound_zero
    (a : ℕ → ℝ) (v Gv D sigmaPsi : ℝ) :
    zeroInitStronglyConvexCompositeErrorBound a v Gv D sigmaPsi 0 = 0 :=
  rfl

/-- The recursive step for `\hat B_{v,t}` adds the source increment at time `t + 1`. -/
theorem zeroInitStronglyConvexCompositeErrorBound_succ
    (a : ℕ → ℝ) (v Gv D sigmaPsi : ℝ) (t : ℕ) :
    zeroInitStronglyConvexCompositeErrorBound a v Gv D sigmaPsi (t + 1) =
      zeroInitStronglyConvexCompositeErrorBound a v Gv D sigmaPsi t +
        (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * sigmaPsi)) :=
  rfl

/-- Helper for Theorem 6.15: the accumulated weights satisfy the one-step recursion
`A[a](t + 1) = A[a](t) + a (t + 1)`. -/
private lemma accumulatedWeights_succ
    (a : ℕ → ℝ) (t : ℕ) :
    A[a]((t + 1)) = A[a](t) + a (t + 1) := by
  -- Expand the defining sums and peel off the last term.
  rw [accumulatedWeights_apply, accumulatedWeights_apply, Finset.sum_range_succ]

/-- Helper for Theorem 6.15: the successor accumulated weight `A[a](t + 1)` and the
corresponding coefficient `a (t + 1)` are positive once `τ_t = a_{t+1} / A_{t+1}` lies in
`(0, 1]`. -/
private lemma successorWeightAndAccumulatedWeight_pos
    {Q : Set E} {f Ψ : E → ℝ}
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (a : ℕ → ℝ)
    (ha_nonneg : ∀ t : ℕ, 0 ≤ a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (t : ℕ) :
    0 < A[a]((t + 1)) ∧ 0 < a (t + 1) := by
  have hτ_pos : 0 < τ[a](t) := by
    simpa [h_step t] using (method.stepSize_mem_Ioc t).1
  rw [weightCoefficient_apply] at hτ_pos
  have ha_nonneg_succ : 0 ≤ a (t + 1) := ha_nonneg (t + 1)
  have hA_pos : 0 < A[a]((t + 1)) := by
    by_contra hA_pos
    have hA_nonpos : A[a]((t + 1)) ≤ 0 := le_of_not_gt hA_pos
    have hratio_nonpos : a (t + 1) / A[a]((t + 1)) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos ha_nonneg_succ hA_nonpos
    linarith
  have ha_pos : 0 < a (t + 1) := by
    by_contra ha_pos
    have ha_nonpos : a (t + 1) ≤ 0 := le_of_not_gt ha_pos
    have ha_eq_zero : a (t + 1) = 0 := le_antisymm ha_nonpos ha_nonneg_succ
    rw [ha_eq_zero, zero_div] at hτ_pos
    linarith
  exact ⟨hA_pos, ha_pos⟩

/-- Helper for Theorem 6.15: multiplying a normalized convex combination by `A[a](t + 1)`
recovers the weighted successor form, using only positivity of the successor denominator. -/
private lemma successorWeightedAverageRescaling
    {Q : Set E} {f Ψ : E → ℝ}
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (a : ℕ → ℝ)
    (ha_nonneg : ∀ t : ℕ, 0 ≤ a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (t : ℕ) (u v : ℝ) :
    A[a]((t + 1)) * ((1 - τ[a](t)) * u + τ[a](t) * v) =
      A[a](t) * u + a (t + 1) * v := by
  have hA_ne : A[a]((t + 1)) ≠ 0 :=
    (successorWeightAndAccumulatedWeight_pos
      (method := method) (a := a) ha_nonneg h_step t).1.ne'
  -- Rewrite `τ[a](t)` once and clear the single positive denominator.
  rw [weightCoefficient_apply]
  field_simp [hA_ne]
  rw [accumulatedWeights_succ]
  ring

/-- Helper for Theorem 6.15: the weighted strong-convex remainder rescales from
`τ[a](t)^(1 + 2 v)` to the displayed source increment
`a_{t+1}^{1 + 2 v} / A_{t+1}^{2 v}`. -/
private lemma weightCoefficientStrongConvexRescaling
    {Q : Set E} {f Ψ : E → ℝ} {σΨ : ℝ}
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (a : ℕ → ℝ) (v Gv D : ℝ)
    (ha_nonneg : ∀ t : ℕ, 0 ≤ a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (t : ℕ) :
    A[a]((t + 1)) *
        (τ[a](t) *
          (Real.rpow (τ[a](t)) (2 * v) *
            (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)))) =
      (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
        (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)) := by
  have hA_pos : 0 < A[a]((t + 1)) :=
    (successorWeightAndAccumulatedWeight_pos
      (method := method) (a := a) ha_nonneg h_step t).1
  have ha_nonneg_succ : 0 ≤ a (t + 1) := ha_nonneg (t + 1)
  have hA_nonneg : 0 ≤ A[a]((t + 1)) := hA_pos.le
  have hA_rpow_ne : Real.rpow (A[a]((t + 1))) (2 * v) ≠ 0 :=
    (Real.rpow_pos_of_pos hA_pos (2 * v)).ne'
  have hτ_pos : 0 < τ[a](t) := by
    simpa [h_step t] using (method.stepSize_mem_Ioc t).1
  have hτ_pow :
      τ[a](t) * Real.rpow (τ[a](t)) (2 * v) =
        Real.rpow (τ[a](t)) (1 + 2 * v) := by
    -- Merge the linear `τ_t` factor with `τ_t^(2 v)` before replacing `τ_t`.
    simpa [Real.rpow_one] using (Real.rpow_add hτ_pos 1 (2 * v)).symm
  have hA_pow :
      Real.rpow (A[a]((t + 1))) (1 + 2 * v) =
        A[a]((t + 1)) * Real.rpow (A[a]((t + 1))) (2 * v) := by
    -- Factor the positive power `A_{t+1}^{1 + 2 v}` into `A_{t+1} * A_{t+1}^{2 v}`.
    simpa [Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using
      (Real.rpow_add hA_pos 1 (2 * v))
  have hdiv :
      Real.rpow (a (t + 1) / A[a]((t + 1))) (1 + 2 * v) =
        Real.rpow (a (t + 1)) (1 + 2 * v) /
          Real.rpow (A[a]((t + 1))) (1 + 2 * v) := by
    simpa using Real.div_rpow ha_nonneg_succ hA_nonneg (1 + 2 * v)
  -- Convert the `τ_t`-version of the strong-convex term into the displayed `a_{t+1}` / `A_{t+1}`
  -- increment before returning to the weighted proof.
  calc
    A[a]((t + 1)) *
        (τ[a](t) *
          (Real.rpow (τ[a](t)) (2 * v) *
            (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)))) =
      A[a]((t + 1)) *
        (Real.rpow (τ[a](t)) (1 + 2 * v) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ))) := by
        rw [← hτ_pow]
        ring
    _ =
      A[a]((t + 1)) *
        ((Real.rpow (a (t + 1)) (1 + 2 * v) /
            Real.rpow (A[a]((t + 1))) (1 + 2 * v)) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ))) := by
        rw [weightCoefficient_apply, hdiv]
    _ =
      A[a]((t + 1)) *
        ((Real.rpow (a (t + 1)) (1 + 2 * v) /
            (A[a]((t + 1)) * Real.rpow (A[a]((t + 1))) (2 * v))) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ))) := by
        rw [hA_pow]
    _ =
      (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
        (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)) := by
        field_simp [hA_pos.ne', hA_rpow_ne]

/-- Helper for Theorem 6.15: Cauchy--Schwarz and scalar Young yield the quadratic lower bound
`⟪s, u⟫ + (σΨ / 2) ‖u‖² ≥ -‖s‖² / (2 σΨ)`. -/
private lemma pairingAddQuadraticLowerBound
    {σΨ : ℝ} (hσ : 0 < σΨ) (s u : E) :
    inner ℝ s u + (σΨ / 2) * ‖u‖ ^ (2 : ℕ) ≥
      -(‖s‖ ^ (2 : ℕ) / (2 * σΨ)) := by
  have hinner : inner ℝ s u ≥ -(‖s‖ * ‖u‖) := by
    -- Cauchy--Schwarz turns the pairing into the worst-case negative norm product.
    have habs : |inner ℝ s u| ≤ ‖s‖ * ‖u‖ := abs_real_inner_le_norm s u
    have hleft : -(‖s‖ * ‖u‖) ≤ -|inner ℝ s u| := by
      nlinarith
    have hright : -|inner ℝ s u| ≤ inner ℝ s u := by
      simpa using neg_abs_le (inner ℝ s u)
    exact le_trans hleft hright
  have hyoung :
      ‖s‖ * ‖u‖ ≤
        (σΨ / 2) * ‖u‖ ^ (2 : ℕ) + ‖s‖ ^ (2 : ℕ) / (2 * σΨ) := by
    -- Young's inequality with parameter `σΨ` matches the quadratic penalty exactly.
    have htwo :=
      two_mul_le_add_mul_sq (a := ‖u‖) (b := ‖s‖) (ε := σΨ) hσ
    have hσ_ne : σΨ ≠ 0 := ne_of_gt hσ
    have htwo' :
        2 * (‖s‖ * ‖u‖) ≤
          2 *
            ((σΨ / 2) * ‖u‖ ^ (2 : ℕ) + ‖s‖ ^ (2 : ℕ) / (2 * σΨ)) := by
      field_simp [pow_two, hσ_ne] at htwo ⊢
      nlinarith
    nlinarith
  -- Combine the pairing lower bound with the scalar Young inequality.
  nlinarith

/-- Helper for Theorem 6.15: squaring the raw `(6.4.3)` gradient-difference estimate yields the
stable `a_{t+1}^{2 v} / A_{t+1}^{2 v}` core needed for the strong-convex remainder. -/
private lemma gradientDifferenceSquareBound_le_normalizedStrongConvexCore
    {Q : Set E} {f Ψ : E → ℝ}
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (a : ℕ → ℝ) (v Gv D : ℝ)
    (ha_nonneg : ∀ t : ℕ, 0 ≤ a t)
    (hD_nonneg : 0 ≤ D)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ,
        ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ≤
          (Real.rpow (a (t + 1)) v /
              Real.rpow (A[a](t.succ)) v) *
            Gv * Real.rpow D v)
    (t : ℕ) :
    ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ^ (2 : ℕ) ≤
      (Real.rpow (a (t + 1)) (2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
        (Gv ^ (2 : ℕ) * Real.rpow D (2 * v)) := by
  let delta := gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)
  let rhs :=
    (Real.rpow (a (t + 1)) v / Real.rpow (A[a]((t + 1))) v) * Gv * Real.rpow D v
  have hA_pos : 0 < A[a]((t + 1)) :=
    (successorWeightAndAccumulatedWeight_pos
      (method := method) (a := a) ha_nonneg h_step t).1
  have ha_nonneg_succ : 0 ≤ a (t + 1) := ha_nonneg (t + 1)
  have hnorm_le_rhs : ‖delta‖ ≤ rhs := by
    simpa [delta, rhs] using h6043 t
  have hrhs_nonneg : 0 ≤ rhs := le_trans (norm_nonneg delta) hnorm_le_rhs
  have hsq : ‖delta‖ ^ (2 : ℕ) ≤ rhs ^ (2 : ℕ) := by
    exact (sq_le_sq).2 (by
      simpa [abs_of_nonneg (norm_nonneg delta), abs_of_nonneg hrhs_nonneg] using hnorm_le_rhs)
  have hA_rpow_ne_v : Real.rpow (A[a]((t + 1))) v ≠ 0 :=
    (Real.rpow_pos_of_pos hA_pos v).ne'
  have ha_sq :
      (Real.rpow (a (t + 1)) v) ^ (2 : ℕ) = Real.rpow (a (t + 1)) (2 * v) := by
    -- Rewrite the squared `a_{t+1}^v` factor as `a_{t+1}^{2 v}` once and reuse it.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.rpow_mul_natCast ha_nonneg_succ v 2).symm
  have hA_sq :
      (Real.rpow (A[a]((t + 1))) v) ^ (2 : ℕ) = Real.rpow (A[a]((t + 1))) (2 * v) := by
    -- The positive accumulated weight allows the same square-to-`2 v` rewrite for `A_{t+1}`.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.rpow_mul_natCast hA_pos.le v 2).symm
  have hD_sq :
      (Real.rpow D v) ^ (2 : ℕ) = Real.rpow D (2 * v) := by
    -- The diameter term is nonnegative, so its square also collapses to a single `rpow`.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.rpow_mul_natCast hD_nonneg v 2).symm
  have hrhs_sq :
      rhs ^ (2 : ℕ) =
        (Real.rpow (a (t + 1)) (2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v)) := by
    -- Normalize the square before the oracle proof reuses it as a single rewrite step.
    dsimp [rhs]
    calc
      (((Real.rpow (a (t + 1)) v / Real.rpow (A[a]((t + 1))) v) * Gv *
            Real.rpow D v) ^ (2 : ℕ)) =
          ((Real.rpow (a (t + 1)) v) ^ (2 : ℕ) /
              (Real.rpow (A[a]((t + 1))) v) ^ (2 : ℕ)) *
            (Gv ^ (2 : ℕ) * (Real.rpow D v) ^ (2 : ℕ)) := by
            field_simp [pow_two, hA_rpow_ne_v]
      _ =
          (Real.rpow (a (t + 1)) (2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
            (Gv ^ (2 : ℕ) * Real.rpow D (2 * v)) := by
            rw [ha_sq, hA_sq, hD_sq]
  -- The squared norm bound is now in the exact `(a_{t+1}, A_{t+1})` normal form.
  calc
    ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ^ (2 : ℕ)
        = ‖delta‖ ^ (2 : ℕ) := by rfl
    _ ≤ rhs ^ (2 : ℕ) := hsq
    _ =
        (Real.rpow (a (t + 1)) (2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v)) := hrhs_sq

/-- Helper for Theorem 6.15: the squared gradient-difference bound rewrites directly in the
Chapter 6 coefficient `τ[a](t)^(2 v)`. -/
private lemma gradientDifferenceSquareBound_le_weightCoefficientStrongConvexCore
    {Q : Set E} {f Ψ : E → ℝ}
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (a : ℕ → ℝ) (v Gv D : ℝ)
    (ha_nonneg : ∀ t : ℕ, 0 ≤ a t)
    (hD_nonneg : 0 ≤ D)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ,
        ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ≤
          (Real.rpow (a (t + 1)) v /
              Real.rpow (A[a](t.succ)) v) *
            Gv * Real.rpow D v)
    (t : ℕ) :
    ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ^ (2 : ℕ) ≤
      Real.rpow (τ[a](t)) (2 * v) * (Gv ^ (2 : ℕ) * Real.rpow D (2 * v)) := by
  have hA_pos : 0 < A[a]((t + 1)) :=
    (successorWeightAndAccumulatedWeight_pos
      (method := method) (a := a) ha_nonneg h_step t).1
  have ha_nonneg_succ : 0 ≤ a (t + 1) := ha_nonneg (t + 1)
  have hdiv :
      Real.rpow (τ[a](t)) (2 * v) =
        Real.rpow (a (t + 1)) (2 * v) / Real.rpow (A[a]((t + 1))) (2 * v) := by
    -- This is the thin adapter from the raw weight coordinates to the `τ_t` notation.
    rw [weightCoefficient_apply]
    simpa using Real.div_rpow ha_nonneg_succ hA_pos.le (2 * v)
  calc
    ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ^ (2 : ℕ) ≤
        (Real.rpow (a (t + 1)) (2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v)) :=
      gradientDifferenceSquareBound_le_normalizedStrongConvexCore
        (method := method) (a := a) (v := v) (Gv := Gv) (D := D)
        ha_nonneg hD_nonneg h_step h6043 t
    _ = Real.rpow (τ[a](t)) (2 * v) * (Gv ^ (2 : ℕ) * Real.rpow D (2 * v)) := by
      rw [← hdiv]

/-- Helper for Theorem 6.15: strong convexity of `Ψ` upgrades the oracle minimizer to the
variational inequality
`Ψ x + ⟪∇_Q f(x_t), x - v_t⟫ ≥ Ψ v_t + (σΨ / 2) ‖x - v_t‖²`. -/
private lemma oraclePointStrongConvexVariationalLowerBound
    {Q : Set E} {f Ψ : E → ℝ} {σΨ : ℝ}
    (hΨ : Ψ ∈ 𝒮^0_σΨ(Q))
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (t : ℕ) (x : Q) :
    Ψ x + inner ℝ (gradientWithin f Q (method t)) ((x : E) - method.oraclePoint t) ≥
      Ψ (method.oraclePoint t) +
        (σΨ / 2) * ‖(x : E) - method.oraclePoint t‖ ^ (2 : ℕ) := by
  rcases mem_S0On_iff.mp hΨ with ⟨_, hΨ_strong⟩
  let g := gradientWithin f Q (method t)
  have hinner_convex : ConvexOn ℝ Q (fun y : E ↦ inner ℝ g y) := by
    simpa using (innerSL ℝ g).convexOn hΨ_strong.1
  have hperturbed_strong : StrongConvexOn Q σΨ (fun y : E ↦ inner ℝ g y + Ψ y) := by
    -- Adding the affine oracle term preserves the strong-convex modulus.
    simpa [StrongConvexOn, Pi.add_apply, add_comm] using
      (hinner_convex.uniformConvexOn_zero.add hΨ_strong)
  have horacle_min :
      IsMinOn (fun y : E ↦ inner ℝ g y + Ψ y) Q (method.oraclePoint t : E) := by
    -- Transport the subtype oracle optimality back to the ambient feasible set `Q`.
    refine isMinOn_iff.mpr ?_
    intro y hy
    have horacle :=
      method.oraclePoint_linearOptimizationOracleObjective_le t ⟨y, hy⟩
    rw [linearOptimizationOracleObjective_apply, linearOptimizationOracleObjective_apply] at horacle
    simpa [g, InnerProductSpace.toDualMap_apply_apply, add_comm] using horacle
  have hquad :
      inner ℝ g (x : E) + Ψ x ≥
        inner ℝ g (method.oraclePoint t : E) + Ψ (method.oraclePoint t) +
          (σΨ / 2) * ‖(x : E) - method.oraclePoint t‖ ^ (2 : ℕ) := by
    exact hperturbed_strong.quadratic_growth_of_isMinOn_of_mem
      (method.oraclePoint_mem_feasibleSet t) horacle_min (x : E) x.property
  have hinner_sub :
      inner ℝ g ((x : E) - method.oraclePoint t) =
        inner ℝ g (x : E) - inner ℝ g (method.oraclePoint t : E) := by
    rw [inner_sub_right]
  -- Rearrange the affine perturbation bound into the source-facing variational inequality.
  nlinarith [hquad, hinner_sub]

/-- Helper for Theorem 6.15: the oracle term at time `t` is controlled by the next affine model
at `x`, and the only loss is the strong-convex increment produced by `(6.4.3)`. -/
private lemma oraclePointTermLeNextAffineModelAddStrongConvexIncrement
    {Q : Set E} {f Ψ : E → ℝ} {σΨ : ℝ}
    (hΨ : Ψ ∈ 𝒮^0_σΨ(Q))
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (a : ℕ → ℝ) (v Gv D : ℝ)
    (hv : v ∈ Set.Ioc (0 : ℝ) 1)
    (ha_nonneg : ∀ t : ℕ, 0 ≤ a t)
    (hD_nonneg : 0 ≤ D)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ,
        ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ≤
          (Real.rpow (a (t + 1)) v /
              Real.rpow (A[a](t.succ)) v) *
            Gv * Real.rpow D v)
    (t : ℕ) (x : Q) :
    f (method (t + 1)) +
        inner ℝ (gradientWithin f Q (method (t + 1)))
          ((method.oraclePoint t : E) - method (t + 1)) +
        Ψ (method.oraclePoint t) ≤
    f (method (t + 1)) +
        inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
        Ψ x +
        Real.rpow (τ[a](t)) (2 * v) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)) := by
  let gCurr := gradientWithin f Q (method t)
  let gNext := gradientWithin f Q (method (t + 1))
  let deltaG := gNext - gCurr
  let u : E := (x : E) - method.oraclePoint t
  let rem :=
    Real.rpow (τ[a](t)) (2 * v) *
      (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ))
  rcases mem_S0On_iff.mp hΨ with ⟨hσ_pos, _⟩
  have hvar :=
    oraclePointStrongConvexVariationalLowerBound
      (hΨ := hΨ) (method := method) t x
  have hsq :=
    gradientDifferenceSquareBound_le_weightCoefficientStrongConvexCore
      (method := method) (a := a) (v := v) (Gv := Gv) (D := D)
      ha_nonneg hD_nonneg h_step h6043 t
  have hpenalty :
      ‖deltaG‖ ^ (2 : ℕ) / (2 * σΨ) ≤ rem := by
    have hσ_nonneg : 0 ≤ 2 * σΨ := by linarith
    have hdiv_raw :
        ‖deltaG‖ ^ (2 : ℕ) / (2 * σΨ) ≤
          (Real.rpow (τ[a](t)) (2 * v) *
              (Gv ^ (2 : ℕ) * Real.rpow D (2 * v))) /
            (2 * σΨ) := by
      exact div_le_div_of_nonneg_right hsq hσ_nonneg
    -- Move the denominator into the textbook remainder shape before the final comparison.
    have hsplit_div :
        (Real.rpow (τ[a](t)) (2 * v) *
            (Gv ^ (2 : ℕ) * Real.rpow D (2 * v))) /
          (2 * σΨ) = rem := by
      dsimp [rem]
      ring
    exact hdiv_raw.trans_eq hsplit_div
  have hdelta_bound :
      inner ℝ deltaG u + (σΨ / 2) * ‖u‖ ^ (2 : ℕ) ≥ -rem := by
    have hpair := pairingAddQuadraticLowerBound (hσ := hσ_pos) deltaG u
    -- The quadratic term absorbs the gradient-difference pairing up to the squared core remainder.
    nlinarith [hpair, hpenalty]
  have hgrad_split : gCurr + deltaG = gNext := by
    dsimp [deltaG, gNext, gCurr]
    abel_nf
  have hnext_pair :
      inner ℝ gNext u = inner ℝ gCurr u + inner ℝ deltaG u := by
    -- Split the next gradient into the current gradient plus the single correction `Δg_t`.
    calc
      inner ℝ gNext u = inner ℝ (gCurr + deltaG) u := by rw [hgrad_split]
      _ = inner ℝ gCurr u + inner ℝ deltaG u := by rw [inner_add_left]
  have horacle :
      Ψ (method.oraclePoint t) ≤ Ψ x + inner ℝ gNext u + rem := by
    -- Combine the strong-convex oracle inequality with the quadratic pairing estimate.
    rw [hnext_pair]
    nlinarith [hvar, hdelta_bound]
  have hshift :
      inner ℝ gNext ((x : E) - method (t + 1)) =
        inner ℝ gNext u +
          inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)) := by
    -- Re-express the successor affine model by inserting the oracle point as the bridge point.
    calc
      inner ℝ gNext ((x : E) - method (t + 1)) =
          inner ℝ gNext (u + ((method.oraclePoint t : E) - method (t + 1))) := by
            congr 2
            dsimp [u]
            abel_nf
      _ = inner ℝ gNext u +
            inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)) := by
            rw [inner_add_right]
  -- Route correction: keep the strong-convex oracle bound and the squared `(6.4.3)` normalization
  -- separate until the last linear arithmetic step.
  rw [hshift]
  have hfinal :
      f (method (t + 1)) +
          inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)) +
          Ψ (method.oraclePoint t) ≤
        f (method (t + 1)) +
          (inner ℝ gNext u +
            inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1))) +
          Ψ x + rem := by
    nlinarith [horacle]
  simpa [u, rem] using hfinal

/-- Helper for Theorem 6.15: one step of method `(6.4.12)` satisfies the weighted affine-model
estimate with the exact strong-convex successor increment already written in the textbook
`a_{t+1}` / `A_{t+1}` form. -/
private lemma weightedObjectiveStronglyConvexStepBound
    {Q : Set E} {f Ψ : E → ℝ} {σΨ : ℝ}
    (hf_convex : ConvexOn ℝ Q f)
    (hΨ : Ψ ∈ 𝒮^0_σΨ(Q))
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (a : ℕ → ℝ) (v Gv D : ℝ)
    (hv : v ∈ Set.Ioc (0 : ℝ) 1)
    (hD_nonneg : 0 ≤ D)
    (ha_nonneg : ∀ t : ℕ, 0 ≤ a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ,
        ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ≤
          (Real.rpow (a (t + 1)) v /
              Real.rpow (A[a](t.succ)) v) *
            Gv * Real.rpow D v)
    (t : ℕ) (x : Q) :
    A[a]((t + 1)) * (f (method (t + 1)) + Ψ (method (t + 1))) ≤
      A[a](t) * (f (method t) + Ψ (method t)) +
        a (t + 1) *
          (f (method (t + 1)) +
            inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
            Ψ x) +
        (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)) := by
  let τ := τ[a](t)
  let u := f (method t) + Ψ (method t)
  let vNext :=
    f (method (t + 1)) +
      inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
      Ψ x
  let delta :=
    Real.rpow (τ[a](t)) (2 * v) *
      (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ))
  rcases mem_S0On_iff.mp hΨ with ⟨hσ_pos, hΨ_strong⟩
  have hΨ_convex : ConvexOn ℝ Q Ψ := by
    -- Positive strong convexity in particular implies convexity on the feasible set.
    simpa [StrongConvexOn] using
      (UniformConvexOn.convexOn (f := Ψ) (s := Q)
        (φ := fun r : ℝ ↦ σΨ / (2 : ℝ) * r ^ (2 : ℕ))
        hΨ_strong (by
          intro r
          positivity))
  have hτ_pos : 0 < τ := by
    simpa [τ, h_step t] using (method.stepSize_mem_Ioc t).1
  have hτ_nonneg : 0 ≤ τ := hτ_pos.le
  have hτ_le_one : τ ≤ 1 := by
    simpa [τ, h_step t] using (method.stepSize_mem_Ioc t).2
  have h_one_sub_nonneg : 0 ≤ 1 - τ := sub_nonneg.mpr hτ_le_one
  have hsum : (1 - τ) + τ = 1 := by
    dsimp [τ]
    ring
  have hΨ_raw :
      Ψ ((1 - τ) • (method t : E) + τ • (method.oraclePoint t : E)) ≤
        (1 - τ) * Ψ (method t) + τ * Ψ (method.oraclePoint t) := by
    -- Convexity of `Ψ` on `Q` gives the regularizer step at the natural `τ_t` scale.
    exact hΨ_convex.2
      (method.iterates_mem_feasibleSet t) (method.oraclePoint_mem_feasibleSet t)
      h_one_sub_nonneg hτ_nonneg hsum
  have hΨ_step :
      Ψ (method (t + 1)) ≤
        (1 - τ) * Ψ (method t) + τ * Ψ (method.oraclePoint t) := by
    -- Rewrite the convex-combination point back to the successor iterate `x_{t+1}`.
    have hiter :
        ((1 - τ) • (method t : E) + τ • (method.oraclePoint t : E)) =
          method (t + 1) := by
      calc
        ((1 - τ) • (method t : E) + τ • (method.oraclePoint t : E)) =
            ((1 - method.stepSize t) • (method t : E) +
              method.stepSize t • (method.oraclePoint t : E)) := by
              rw [h_step t]
        _ = method (t + 1) := by
              simpa using (LinearOracleCompositeMethod.iterates_succ (method := method) t)
    rw [hiter] at hΨ_raw
    simpa using hΨ_raw
  have htangent :
      f (method t) ≥
        f (method (t + 1)) +
          inner ℝ (gradientWithin f Q (method (t + 1)))
            ((method t : E) - method (t + 1)) := by
    -- Support the convex function `f` at the successor point.
    exact
      hf_convex.lower_tangent_plane_of_hasGradientWithinAt
        (method (t + 1)) (method.iterates_mem_feasibleSet (t + 1))
        (gradientWithin f Q (method (t + 1)))
        (method.hasGradientWithinAt (method (t + 1)))
        (method t) (method.iterates_mem_feasibleSet t)
  have horacle :=
    oraclePointTermLeNextAffineModelAddStrongConvexIncrement
      (hΨ := hΨ) (method := method) (a := a) (v := v) (Gv := Gv) (D := D)
      hv ha_nonneg hD_nonneg h_step h6043 t x
  have horacle_scaled :
      τ *
          (f (method (t + 1)) +
            inner ℝ (gradientWithin f Q (method (t + 1)))
              ((method.oraclePoint t : E) - method (t + 1)) +
            Ψ (method.oraclePoint t)) ≤
        τ * (vNext + delta) := by
    -- The oracle bridge is paid once, then scaled by the step size.
    dsimp [vNext, delta, τ]
    simpa [h_step t] using mul_le_mul_of_nonneg_left horacle hτ_nonneg
  let d : E := (method.oraclePoint t : E) - method t
  have hiter :
      (method (t + 1) : E) =
        (1 - τ) • (method t : E) + τ • (method.oraclePoint t : E) := by
    calc
      (method (t + 1) : E) =
          (1 - method.stepSize t) • (method t : E) +
            method.stepSize t • (method.oraclePoint t : E) := by
              simpa using (LinearOracleCompositeMethod.iterates_succ (method := method) t)
      _ = (1 - τ) • (method t : E) + τ • (method.oraclePoint t : E) := by
            rw [h_step t]
  have hprev_disp :
      ((method t : E) - method (t + 1)) = -τ • d := by
    -- Rewrite the predecessor displacement directly in the oracle direction `d`.
    calc
      ((method t : E) - method (t + 1)) =
          ((method t : E) - ((1 - τ) • (method t : E) + τ • (method.oraclePoint t : E))) := by
            rw [hiter]
      _ = τ • (method t : E) - τ • (method.oraclePoint t : E) := by
            rw [sub_eq_add_neg, sub_smul]
            simp
            abel_nf
      _ = -τ • d := by
            dsimp [d]
            simp [sub_eq_add_neg, smul_sub, smul_smul]
            ac_rfl
  have horacle_disp :
      ((method.oraclePoint t : E) - method (t + 1)) = (1 - τ) • d := by
    -- The oracle displacement is the residual `(1 - τ_t)` part of the same direction.
    rw [hiter]
    dsimp [d]
    simp [sub_eq_add_neg, smul_add, add_smul, smul_sub, add_assoc, add_left_comm, add_comm]
  have hcancel_vec :
      (1 - τ) • ((method t : E) - method (t + 1)) +
        τ • ((method.oraclePoint t : E) - method (t + 1)) = 0 := by
    -- The weighted predecessor and oracle displacements cancel exactly.
    rw [hprev_disp, horacle_disp]
    calc
      (1 - τ) • (-τ • d) + τ • ((1 - τ) • d) =
          ((1 - τ) * (-τ) + τ * (1 - τ)) • d := by
            rw [smul_smul, smul_smul, add_smul]
      _ = (0 : ℝ) • d := by
            have hcoeff : ((1 - τ) * (-τ) + τ * (1 - τ) : ℝ) = 0 := by ring
            rw [hcoeff]
      _ = 0 := by simp
  have hcancel :
      (1 - τ) *
          inner ℝ (gradientWithin f Q (method (t + 1))) ((method t : E) - method (t + 1)) +
        τ *
          inner ℝ (gradientWithin f Q (method (t + 1)))
            ((method.oraclePoint t : E) - method (t + 1)) = 0 := by
    -- Push the vector cancellation through the inner product.
    have hcancel_inner :=
      congrArg
        (fun z : E ↦ inner ℝ (gradientWithin f Q (method (t + 1))) z)
        hcancel_vec
    simpa [inner_add_right, inner_smul_right] using hcancel_inner
  have hsplit :
      f (method (t + 1)) =
        (1 - τ) *
            (f (method (t + 1)) +
              inner ℝ (gradientWithin f Q (method (t + 1)))
                ((method t : E) - method (t + 1))) +
          τ *
            (f (method (t + 1)) +
              inner ℝ (gradientWithin f Q (method (t + 1)))
                ((method.oraclePoint t : E) - method (t + 1))) := by
    -- Rewrite `f(x_{t+1})` into the two weighted pieces whose pairings cancel.
    linarith
  have hprev_scaled :
      (1 - τ) *
          (f (method (t + 1)) +
            inner ℝ (gradientWithin f Q (method (t + 1)))
              ((method t : E) - method (t + 1)) +
            Ψ (method t)) ≤
        (1 - τ) * (f (method t) + Ψ (method t)) := by
    -- The predecessor contribution is controlled by the tangent plane at `x_{t+1}`.
    have hprev :
        f (method (t + 1)) +
            inner ℝ (gradientWithin f Q (method (t + 1)))
              ((method t : E) - method (t + 1)) +
            Ψ (method t) ≤
          f (method t) + Ψ (method t) := by
      linarith
    exact mul_le_mul_of_nonneg_left hprev h_one_sub_nonneg
  have hnormalized :
      f (method (t + 1)) + Ψ (method (t + 1)) ≤
        (1 - τ) * u + τ * (vNext + delta) := by
    have hpre :
        f (method (t + 1)) + Ψ (method (t + 1)) ≤
          (1 - τ) *
              (f (method (t + 1)) +
                inner ℝ (gradientWithin f Q (method (t + 1)))
                  ((method t : E) - method (t + 1)) +
                Ψ (method t)) +
            τ *
              (f (method (t + 1)) +
                inner ℝ (gradientWithin f Q (method (t + 1)))
                  ((method.oraclePoint t : E) - method (t + 1)) +
                Ψ (method.oraclePoint t)) := by
      -- First combine convexity of `Ψ` with the exact decomposition of `f(x_{t+1})`.
      calc
        f (method (t + 1)) + Ψ (method (t + 1)) ≤
            f (method (t + 1)) +
              ((1 - τ) * Ψ (method t) + τ * Ψ (method.oraclePoint t)) := by
                linarith
        _ =
            ((1 - τ) *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1)))
                    ((method t : E) - method (t + 1))) +
              τ *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1)))
                    ((method.oraclePoint t : E) - method (t + 1)))) +
              ((1 - τ) * Ψ (method t) + τ * Ψ (method.oraclePoint t)) := by
                nth_rw 1 [hsplit]
        _ =
            (1 - τ) *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1)))
                    ((method t : E) - method (t + 1)) +
                  Ψ (method t)) +
              τ *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1)))
                    ((method.oraclePoint t : E) - method (t + 1)) +
                  Ψ (method.oraclePoint t)) := by
                ring
    -- Route correction: close the normalized successor step before any `A_{t+1}` rescaling.
    calc
      f (method (t + 1)) + Ψ (method (t + 1)) ≤
          (1 - τ) *
              (f (method (t + 1)) +
                inner ℝ (gradientWithin f Q (method (t + 1)))
                  ((method t : E) - method (t + 1)) +
                Ψ (method t)) +
            τ *
              (f (method (t + 1)) +
                inner ℝ (gradientWithin f Q (method (t + 1)))
                  ((method.oraclePoint t : E) - method (t + 1)) +
                Ψ (method.oraclePoint t)) := hpre
      _ ≤ (1 - τ) * u +
            τ *
              (f (method (t + 1)) +
                inner ℝ (gradientWithin f Q (method (t + 1)))
                  ((method.oraclePoint t : E) - method (t + 1)) +
                Ψ (method.oraclePoint t)) := by
            dsimp [u]
            simpa using add_le_add_right hprev_scaled
              (τ *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1)))
                    ((method.oraclePoint t : E) - method (t + 1)) +
                  Ψ (method.oraclePoint t)))
      _ ≤ (1 - τ) * u + τ * (vNext + delta) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left horacle_scaled ((1 - τ) * u)
  have hA_nonneg : 0 ≤ A[a]((t + 1)) :=
    (successorWeightAndAccumulatedWeight_pos
      (method := method) (a := a) ha_nonneg h_step t).1.le
  have hscaled := mul_le_mul_of_nonneg_left hnormalized hA_nonneg
  have hsplit_scaled :
      A[a]((t + 1)) * ((1 - τ) * u + τ * (vNext + delta)) =
        A[a]((t + 1)) * ((1 - τ) * u + τ * vNext) +
          A[a]((t + 1)) * (τ * delta) := by
    -- Separate the affine term from the single strong-convex remainder before rescaling.
    ring
  rw [hsplit_scaled] at hscaled
  have hiter_coeff :
      (method (t + 1) : E) =
        (1 - τ[a](t)) • (method t : E) + τ[a](t) • (method.oraclePoint t : E) := by
    simpa [τ] using hiter
  dsimp [τ, u, vNext, delta] at hscaled ⊢
  rw [h_step t, ← hiter_coeff] at hscaled
  rw [successorWeightedAverageRescaling
        (method := method) (a := a) ha_nonneg h_step t
        (f (method t) + Ψ (method t))
        (f (method (t + 1)) +
          inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
          Ψ x)] at hscaled
  have hrem_rewrite :
      A[a]((t + 1)) *
          (τ[a](t) *
            (Real.rpow (τ[a](t)) (2 * v) *
              (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)))) =
        (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)) := by
    simpa using
      weightCoefficientStrongConvexRescaling
        (method := method) (a := a) (v := v) (Gv := Gv) (D := D)
        ha_nonneg h_step t
  calc
    A[a]((t + 1)) * (f (method (t + 1)) + Ψ (method (t + 1))) ≤
        A[a](t) * (f (method t) + Ψ (method t)) +
          a (t + 1) *
            (f (method (t + 1)) +
              inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
              Ψ x) +
          A[a]((t + 1)) *
            (τ[a](t) *
              (Real.rpow (τ[a](t)) (2 * v) *
                (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)))) := by
          simpa [LinearOracleCompositeMethod.iterates_succ, h_step t] using hscaled
    _ =
        A[a](t) * (f (method t) + Ψ (method t)) +
          a (t + 1) *
            (f (method (t + 1)) +
              inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
              Ψ x) +
          (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
            (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)) := by
          rw [hrem_rewrite]

-- Proof sketch: argue by induction on `t`. For the induction step, combine the convexity
-- increment estimate for `f` with the one-step estimate from method `(6.4.12)`; the base case is
-- trivial because `a 0 = 0`. Then combine the resulting inequality with the strong convexity
-- lower bound for `Ψ` at the oracle point `v_t`, and apply the quadratic inequality
-- `⟪s, u⟫ + (σΨ / 2) ‖u‖² ≥ -(1 / (2 σΨ)) ‖s‖²` to
-- `s = ∇f(x_{t+1}) - ∇f(x_t)` and `u = x - v_t`. Finally insert the bound `(6.4.3)` and absorb
-- the resulting term into the source recursion
-- `zeroInitStronglyConvexCompositeErrorBound a v Gv D σΨ`.
/-- Theorem 6.15: if `f` is convex on `Q`, `Ψ` is `σ_Ψ`-strongly convex on the feasible set `Q`,
method `(6.4.12)` is run with weights `a_t` normalized by `a₀ = 0`, coefficients
`τ_t = a_{t+1} / A_{t+1}`, exponent `v ∈ (0, 1]`, and the gradient differences satisfy the bound
`(6.4.3)`, then for every `t ≥ 0` and every feasible comparison point `x ∈ Q` the weighted
composite objective at `x_t` is bounded by the weighted affine linearizations at `x` plus the
zero-initialized recursive error term `\hat B_{v,t}`. -/
theorem weighted_objective_upper_bound_of_strongly_convex_linear_oracle_composite_method
    {Q : Set E} {f Ψ : E → ℝ} {σΨ : ℝ}
    (hf_convex : ConvexOn ℝ Q f)
    (hΨ : Ψ ∈ 𝒮^0_σΨ(Q))
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (a : ℕ → ℝ) (v Gv D : ℝ)
    (hv : v ∈ Set.Ioc (0 : ℝ) 1)
    (ha_zero : a 0 = 0)
    (hD_nonneg : 0 ≤ D)
    (ha_nonneg : ∀ t : ℕ, 0 ≤ a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ,
        ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ≤
          (Real.rpow (a (t + 1)) v /
              Real.rpow (A[a](t.succ)) v) *
            Gv * Real.rpow D v)
    (t : ℕ) (x : Q) :
    A[a](t) * (f (method t) + Ψ (method t)) ≤
      (Finset.sum (Finset.range (t + 1)) fun k ↦
        a k *
          (f (method k) +
            inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
            Ψ x)) +
        zeroInitStronglyConvexCompositeErrorBound a v Gv D σΨ t := by
  induction t with
  | zero =>
      -- The base case collapses because `a₀ = 0`, so both the weighted objective and the first
      -- affine term vanish together with the zero-initialized error term.
      rw [accumulatedWeights_apply, zeroInitStronglyConvexCompositeErrorBound_zero]
      simp [ha_zero]
  | succ t ih =>
      have hstep :=
        weightedObjectiveStronglyConvexStepBound
          (hf_convex := hf_convex) (hΨ := hΨ) (method := method)
          (a := a) (v := v) (Gv := Gv) (D := D)
          hv hD_nonneg ha_nonneg h_step h6043 t x
      have hcombine :
          A[a](t) * (f (method t) + Ψ (method t)) +
              a (t + 1) *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                  Ψ x) +
              (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
                (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)) ≤
            (Finset.sum (Finset.range (t + 1)) fun k ↦
                a k *
                  (f (method k) +
                    inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                    Ψ x)) +
              zeroInitStronglyConvexCompositeErrorBound a v Gv D σΨ t +
              a (t + 1) *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                  Ψ x) +
              (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
                (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)) := by
        -- Add the induction hypothesis to the new affine term and the new error increment.
        linarith [ih]
      calc
        A[a]((t + 1)) * (f (method (t + 1)) + Ψ (method (t + 1))) ≤
            A[a](t) * (f (method t) + Ψ (method t)) +
              a (t + 1) *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                  Ψ x) +
              (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
                (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)) := hstep
        _ ≤
            (Finset.sum (Finset.range (t + 1)) fun k ↦
                a k *
                  (f (method k) +
                    inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                    Ψ x)) +
              zeroInitStronglyConvexCompositeErrorBound a v Gv D σΨ t +
              a (t + 1) *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                  Ψ x) +
              (Real.rpow (a (t + 1)) (1 + 2 * v) / Real.rpow (A[a]((t + 1))) (2 * v)) *
                (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * σΨ)) := hcombine
        _ =
            (Finset.sum (Finset.range ((t + 1) + 1)) fun k ↦
                a k *
                  (f (method k) +
                    inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                    Ψ x)) +
              zeroInitStronglyConvexCompositeErrorBound a v Gv D σΨ (t + 1) := by
              let affineTerm : ℕ → ℝ := fun k ↦
                a k *
                  (f (method k) +
                    inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                    Ψ x)
              have hsum_succ :
                  (Finset.sum (Finset.range ((t + 1) + 1)) fun k ↦ affineTerm k) =
                    (Finset.sum (Finset.range t) fun k ↦ affineTerm k) +
                      affineTerm t + affineTerm (t + 1) := by
                rw [Finset.sum_range_succ, Finset.sum_range_succ]
              rw [hsum_succ, zeroInitStronglyConvexCompositeErrorBound_succ]
              nth_rw 1 [Finset.sum_range_succ]
              dsimp [affineTerm]
              ac_rfl

end
