/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_20

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PositiveDefMatrixNorm RelativeScaleTransformNotation

variable {n : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin (n : ℕ))

/- Theorem 7.21 lies in the chapter's relative-scale / positive-definite weighted-norm /
estimating-sequence domain.

Sampled owner-style declarations:
- `positiveDefMatrixNorm` and the notations `‖·‖[G]`, `‖·‖[G,*]` in `Chap07/Definition_7_23`,
  the chapter owner for the primal and dual norms induced by a positive-definite matrix;
- `positiveDefMatrixNorm_quadraticDistanceTo_apply` in `Chap07/Definition_7_46`, the weighted
  quadratic-prox owner behind the term `(1 / 2) ‖x₀ - x*‖[G₀]^2`;
- `relativeScaleTransformedObjective` and the notation `f̂` in `Chap07/Lemma_7_20`, the chapter
  owner for the transformed objective `x ↦ (1 / 2) f(x)^2`;
- `estimating_function_le_weighted_transformed_objective_add_initial` in `Chap07/Lemma_7_21`,
  the nearby additive estimating-sequence recursion theorem.

Best owner abstraction:
- source-facing: Theorem 7.21's best-point and weighted-average bounds for the relative-scale
  high-order method;
- core/canonical: `positiveDefMatrixNorm`, `f̂`, and the accumulated-weight sequence `A`;
- bridge/view: the explicit exponential lower bound on `A_{k+1}` coming from the preceding
  quasi-Newton metric analysis.

Primitive data:
- the objective `f`, the positive-definite metric `G₀`, the base point `x₀`, and the comparison
  point `x*`;
- the source-facing sequences `x_k^*`, `\tilde x_k`, and `A_k`;
- the positive dimension `n : ℕ+`, the scalar parameter `δ`, and the positive smoothness owner
  `L : NNRealˣ`.

Derived API:
- the transformed-objective bound for the best points `x_k^*`;
- the parallel transformed-objective bound for the weighted-average points `\tilde x_{k+1}`.

The previous version rebuilt theorem-local primal and dual norm owners and packaged the three
source sequences into a second wrapper structure. This refinement reuses the Chapter 7 weighted
norm owner directly and keeps the primitive sequences separate from the scalar side conditions and
one-step estimates that drive the theorem.
-/

section RelativeScaleHighOrderMethod

variable {f : E → ℝ}
variable {G0 : {G : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ // G.PosDef}}
variable {x0 xStar : E} {δ : ℝ} {L : NNRealˣ}
variable {A : ℕ → ℝ}

/-- Helper for Theorem 7.21: the exponential gap in the denominator is strictly positive. -/
lemma relative_scale_exp_gap_pos
    (hδ : 0 < δ) (k : ℕ) :
    0 < Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 := by
  -- The exponent is positive because `δ`, `k + 1`, and `n` are all positive.
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have hk : 0 < (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos k
  have harg : 0 < δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
    positivity
  have hexp : 1 < Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    exact (Real.one_lt_exp_iff).2 harg
  linarith

/-- Helper for Theorem 7.21: the explicit lower bound forces the next accumulated weight to be
strictly positive. -/
lemma weight_sequence_succ_pos_of_lower_bound
    (hδ : 0 < δ)
    (hA_lower :
      ∀ k : ℕ,
        ((n : ℝ) / ((L : ℝ) ^ (2 : ℕ))) *
            (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) ≤
          A (k + 1))
    (k : ℕ) :
    0 < A (k + 1) := by
  -- The explicit lower bound is positive, so `A (k + 1)` is positive as well.
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have hL_nonneg : 0 ≤ (L : ℝ) := by
    positivity
  have hL_ne : (L : ℝ) ≠ 0 := by
    exact_mod_cast (Units.ne_zero L)
  have hL : 0 < (L : ℝ) := by
    exact lt_of_le_of_ne hL_nonneg hL_ne.symm
  have hL_pos : 0 < ((L : ℝ) ^ (2 : ℕ)) := by
    exact pow_pos hL 2
  have hgap_pos :
      0 < Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 :=
    relative_scale_exp_gap_pos (n := n) hδ k
  have hlower_pos :
      0 <
        ((n : ℝ) / ((L : ℝ) ^ (2 : ℕ))) *
          (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) := by
    exact mul_pos (div_pos hn hL_pos) hgap_pos
  exact lt_of_lt_of_le hlower_pos (hA_lower k)

/-- Helper for Theorem 7.21: the initial quadratic term is dominated by the explicit exponential
tail once the lower bound on `A (k + 1)` is inserted. -/
lemma initial_quadratic_term_le_exponential_tail
    {x0 xStar : E}
    (hδ : 0 < δ)
    (hA_lower :
      ∀ k : ℕ,
        ((n : ℝ) / ((L : ℝ) ^ (2 : ℕ))) *
            (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) ≤
          A (k + 1))
    (k : ℕ) :
    (‖x0 - xStar‖[G0] ^ (2 : ℕ)) / (2 * A (k + 1)) ≤
      (((L : ℝ) ^ (2 : ℕ)) * ‖x0 - xStar‖[G0] ^ (2 : ℕ)) /
        (2 * (n : ℝ) * (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1)) := by
  let e : ℝ := Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1
  let r : ℝ := ‖x0 - xStar‖[G0] ^ (2 : ℕ)
  let Lsq : ℝ := ((L : ℝ) ^ (2 : ℕ))
  -- The source lower bound gives a positive lower bound on the denominator in reciprocal form.
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have hL_nonneg : 0 ≤ (L : ℝ) := by
    positivity
  have hL_ne : (L : ℝ) ≠ 0 := by
    exact_mod_cast (Units.ne_zero L)
  have hL : 0 < (L : ℝ) := by
    exact lt_of_le_of_ne hL_nonneg hL_ne.symm
  have he_pos : 0 < e := by
    simpa [e] using relative_scale_exp_gap_pos (n := n) hδ k
  have hLsq_pos : 0 < Lsq := by
    dsimp [Lsq]
    exact pow_pos hL 2
  have hr_half_nonneg : 0 ≤ r / 2 := by
    dsimp [r]
    positivity
  have hbase :
      ((n : ℝ) * e) / Lsq ≤ A (k + 1) := by
    simpa [e, Lsq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hA_lower k
  have hbase_pos : 0 < ((n : ℝ) * e) / Lsq := by
    exact div_pos (mul_pos hn he_pos) hLsq_pos
  have hrecip :
      1 / A (k + 1) ≤ Lsq / ((n : ℝ) * e) := by
    have hrecip' :
        1 / A (k + 1) ≤ 1 / (((n : ℝ) * e) / Lsq) := by
      exact one_div_le_one_div_of_le hbase_pos hbase
    simpa [one_div_div] using hrecip'
  -- Multiplying the reciprocal estimate by the nonnegative prefactor `r / 2` yields the target.
  have hscaled :
      (r / 2) * (1 / A (k + 1)) ≤ (r / 2) * (Lsq / ((n : ℝ) * e)) := by
    exact mul_le_mul_of_nonneg_left hrecip hr_half_nonneg
  have htail :
      r / (2 * A (k + 1)) ≤ (Lsq * r) / (2 * (n : ℝ) * e) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  simpa [e, Lsq, r] using htail

-- Proof sketch: combine the one-step estimate for `x_k^*` with the lower bound on `A_{k+1}`,
-- then substitute `R = ‖x₀ - x⋆‖_{G₀}` and simplify the reciprocal factor.
/-- Theorem 7.21: for the high-order method in relative scale, if `\hat f(x) = (1 / 2) f(x)^2`,
the quasi-Newton estimating-sequence analysis provides the standard one-step bound for the best
points `x_k^*` together with the exponential lower bound on `A_{k+1}`, then
`(1 - δ) \hat f(x_k^*) ≤ \hat f(x^*) + L^2 ‖x₀ - x^*‖_{G₀}^2 /
  (2 n (e^{δ (k + 1) / n} - 1))` for every `δ > 0`. -/
theorem relativeScaleHighOrderMethod_best_point_bound
    {x0 : E}
    {xBest : ℕ → E}
    (hδ : 0 < δ)
    (hbest :
      ∀ k : ℕ,
        (1 - δ) * f̂ (xBest k) ≤
          f̂ xStar + (‖x0 - xStar‖[G0] ^ (2 : ℕ)) / (2 * A (k + 1)))
    (hA_lower :
      ∀ k : ℕ,
        ((n : ℝ) / ((L : ℝ) ^ (2 : ℕ))) *
            (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) ≤
          A (k + 1))
    (k : ℕ) :
    (1 - δ) * f̂ (xBest k) ≤
      f̂ xStar +
        (((L : ℝ) ^ (2 : ℕ)) * ‖x0 - xStar‖[G0] ^ (2 : ℕ)) /
          (2 * (n : ℝ) * (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1)) := by
  -- Replace the implicit `A (k + 1)` remainder by the explicit exponential tail.
  have htail := initial_quadratic_term_le_exponential_tail
    (n := n) (G0 := G0) (A := A) (L := L) (x0 := x0) (xStar := xStar) hδ hA_lower k
  -- The one-step estimate closes the proof once its remainder term is bounded by `htail`.
  exact (hbest k).trans (add_le_add_left htail (f̂ xStar))

-- Proof sketch: apply the same argument as for the best-point estimate, now starting from the
-- one-step inequality for the weighted-average points `\tilde x_{k+1}`.
/-- The weighted-average points satisfy the same transformed-objective estimate as the best
points, with `x_k^*` replaced by `\tilde x_{k+1}`. -/
theorem relativeScaleHighOrderMethod_weighted_average_bound
    {x0 : E}
    {xTilde : ℕ → E}
    (hδ : 0 < δ)
    (hweighted :
      ∀ k : ℕ,
        (1 - δ) * f̂ (xTilde (k + 1)) ≤
          f̂ xStar + (‖x0 - xStar‖[G0] ^ (2 : ℕ)) / (2 * A (k + 1)))
    (hA_lower :
      ∀ k : ℕ,
        ((n : ℝ) / ((L : ℝ) ^ (2 : ℕ))) *
            (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) ≤
          A (k + 1))
    (k : ℕ) :
    (1 - δ) * f̂ (xTilde (k + 1)) ≤
      f̂ xStar +
        (((L : ℝ) ^ (2 : ℕ)) * ‖x0 - xStar‖[G0] ^ (2 : ℕ)) /
          (2 * (n : ℝ) * (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1)) := by
  -- The weighted-average estimate uses the same tail-control lemma as the best-point estimate.
  have htail := initial_quadratic_term_le_exponential_tail
    (n := n) (G0 := G0) (A := A) (L := L) (x0 := x0) (xStar := xStar) hδ hA_lower k
  -- Once the remainder term is replaced, the weighted-average claim is immediate.
  exact (hweighted k).trans (add_le_add_left htail (f̂ xStar))

end RelativeScaleHighOrderMethod

end
