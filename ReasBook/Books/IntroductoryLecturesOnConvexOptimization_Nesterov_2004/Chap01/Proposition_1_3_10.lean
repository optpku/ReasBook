/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Corollary_1_3_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {L : NNReal} {ε : ℝ} {n : ℕ}

/- Proposition 1.3.10 stays at the source-facing numerical layer. The owner abstraction for the
underlying oracle-complexity statements is already fixed upstream by
`DeterministicValueOracleMethod.SolvesLinftyLipschitzProblemClassWithin`, together with the
canonical upper estimate `uniformGridMethod_analyticalComplexity_bound` and lower estimate
`linftyLipschitz_value_oracle_complexity_lower_bound`. The canonical Lipschitz parameter is
already owned upstream as `L : NNReal`, so this file keeps only the resulting numerical
comparison of the derived grid-cardinality bounds. -/

-- Proof sketch: write `m = Nat.floor ((L : ℝ) / (2 * ε))`. The lower bound is immediate from
-- `m ^ n ≤ (m + 1) ^ n`. For the upper bound, use the hypothesis
-- `ε ≤ (L : ℝ) / (4 n)` to obtain
-- `n ≤ m`, then bound `((m + 1 : ℝ) / m) ^ n = (1 + 1 / m) ^ n` by `(1 + 1 / n) ^ n ≤ exp 1`.
/-- Helper for Proposition 1.3.10: the small-scale condition forces the floor index
`⌊(L : ℝ) / (2 ε)⌋` to dominate `n`. -/
lemma index_le_floor_half_ratio_of_epsilon_le_quarter
    (hε : 0 < ε)
    (hsmall : ε ≤ (L : ℝ) / (4 * (n : ℝ))) :
    n ≤ Nat.floor ((L : ℝ) / (2 * ε)) := by
  by_cases hn : n = 0
  · -- The zero index case is immediate because every natural floor is nonnegative.
    simp [hn]
  · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hn)
    have hden_pos : 0 < 4 * (n : ℝ) := by positivity
    -- Clear the denominator in the hypothesis to get a direct linear bound on `L`.
    have hL : ε * (4 * (n : ℝ)) ≤ (L : ℝ) := by
      exact (le_div_iff₀ hden_pos).mp hsmall
    have hmain : (n : ℝ) * (2 * ε) ≤ (L : ℝ) := by
      nlinarith
    -- Convert the real inequality back into the desired floor lower bound.
    refine Nat.le_floor ?_
    exact (le_div_iff₀ (by positivity)).2 hmain

/-- Helper for Proposition 1.3.10: rewriting `(m + 1)^n` as the ratio factor
`(1 + 1 / m)^n` times `m^n`. -/
lemma succ_pow_eq_one_add_inv_mul_pow (m n : ℕ) (hm : 0 < m) :
    ((m + 1) ^ n : ℝ) = (1 + 1 / (m : ℝ)) ^ n * (m ^ n : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hbase : (m : ℝ) + 1 = (1 + 1 / (m : ℝ)) * (m : ℝ) := by
    field_simp [hmR]
  -- Rewrite the successor once so the power splits across a product.
  calc
    ((m + 1) ^ n : ℝ) = ((m : ℝ) + 1) ^ n := by rfl
    _ = (((1 + 1 / (m : ℝ)) * (m : ℝ)) ^ n) := by
      exact congrArg (fun x : ℝ ↦ x ^ n) hbase
    _ = (1 + 1 / (m : ℝ)) ^ n * (m : ℝ) ^ n := by rw [mul_pow]
    _ = (1 + 1 / (m : ℝ)) ^ n * (m ^ n : ℝ) := by rw [← Nat.cast_pow]

/-- Helper for Proposition 1.3.10: once `m` dominates `n`, the ratio
`((m + 1)^n) / (m^n)` is bounded by `exp 1`. -/
lemma succ_pow_le_exp_one_mul_pow (m n : ℕ) (hnm : n ≤ m) :
    ((m + 1) ^ n : ℝ) ≤ Real.exp 1 * (m ^ n : ℝ) := by
  by_cases hm : m = 0
  · have hn : n = 0 := Nat.eq_zero_of_le_zero (hm ▸ hnm)
    subst hm
    subst hn
    -- In the degenerate case `m = n = 0`, the claim reduces to `1 ≤ exp 1`.
    have h_one_le : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by positivity)
    nlinarith
  · have hm_pos : 0 < m := Nat.pos_iff_ne_zero.mpr hm
    have hpow_le :
        (1 + 1 / (m : ℝ)) ^ n ≤ Real.exp (1 / (m : ℝ)) ^ n := by
      -- Raise the pointwise bound `1 + 1 / m ≤ exp (1 / m)` to the `n`th power.
      simpa [add_comm] using
        (pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp (1 / (m : ℝ))) n)
    have hdiv_le_one : (n : ℝ) / (m : ℝ) ≤ 1 := by
      have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      exact (div_le_iff₀ (by exact_mod_cast hm_pos)).2 (by simpa using hcast)
    have hExp_le : Real.exp ((n : ℝ) / (m : ℝ)) ≤ Real.exp 1 := by
      exact Real.exp_le_exp_of_le hdiv_le_one
    -- Follow the source proof: rewrite by the ratio factor and then bound that factor by `exp 1`.
    calc
      ((m + 1) ^ n : ℝ) = (1 + 1 / (m : ℝ)) ^ n * (m ^ n : ℝ) := by
        rw [succ_pow_eq_one_add_inv_mul_pow m n hm_pos]
      _ ≤ Real.exp (1 / (m : ℝ)) ^ n * (m ^ n : ℝ) := by
        exact mul_le_mul_of_nonneg_right hpow_le (by positivity)
      _ = Real.exp ((n : ℝ) / (m : ℝ)) * (m ^ n : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp [div_eq_mul_inv]
      _ ≤ Real.exp 1 * (m ^ n : ℝ) := by
        exact mul_le_mul_of_nonneg_right hExp_le (by positivity)

/-- Under the small-scale hypothesis `0 < ε ≤ (L : ℝ) / (4 n)`, the canonical upper complexity
estimate `(⌊(L : ℝ) / (2 ε)⌋ + 1)^n` from Corollary 1.3.8 is comparable to the canonical lower
estimate `⌊(L : ℝ) / (2 ε)⌋^n` from Theorem 1.3.9. -/
theorem gridCardinality_bounds_of_epsilon_le_quarter_L_div_n
    (hε : 0 < ε)
    (hsmall : ε ≤ (L : ℝ) / (4 * (n : ℝ))) :
    let m := Nat.floor ((L : ℝ) / (2 * ε))
    (m ^ n : ℝ) ≤ ((m + 1) ^ n : ℝ) ∧
      ((m + 1) ^ n : ℝ) ≤ Real.exp 1 * (m ^ n : ℝ) := by
  set m : ℕ := Nat.floor ((L : ℝ) / (2 * ε))
  have hm_le : n ≤ m := by
    simpa [m] using
      index_le_floor_half_ratio_of_epsilon_le_quarter (L := L) (ε := ε) (n := n) hε hsmall
  have hlower_nat : m ^ n ≤ (m + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ m) n
  have hlower : (m ^ n : ℝ) ≤ ((m + 1) ^ n : ℝ) := by
    exact_mod_cast hlower_nat
  have hupper : ((m + 1) ^ n : ℝ) ≤ Real.exp 1 * (m ^ n : ℝ) :=
    succ_pow_le_exp_one_mul_pow m n hm_le
  -- Package the monotone lower bound and exponential upper bound for the chosen floor index.
  simpa [m] using And.intro hlower hupper

-- Proof sketch: choose the absolute constants `c = 1 / 4`, `C₁ = 1`, and `C₂ = exp 1`, then
-- apply `gridCardinality_bounds_of_epsilon_le_quarter_L_div_n`.
/-- Proposition 1.3.10: there are absolute constants `c`, `C₁`, and `C₂` such that whenever
`ε > 0` and `ε ≤ c (L : ℝ) / n`, the canonical upper and lower complexity estimates from
Corollary 1.3.8 and Theorem 1.3.9 are comparable up to the multiplicative constants `C₁`
and `C₂`. -/
theorem exists_absolute_constants_gridComplexity_bounds :
    ∃ c C₁ C₂ : Set.Ioi (0 : ℝ),
      ∀ {L : NNReal} {ε : ℝ} {n : ℕ}
        (_ : 0 < ε) (_ : ε ≤ (c : ℝ) * (L : ℝ) / (n : ℝ)),
          let m := Nat.floor ((L : ℝ) / (2 * ε))
          (C₁ : ℝ) * (m ^ n : ℝ) ≤ ((m + 1) ^ n : ℝ) ∧
            ((m + 1) ^ n : ℝ) ≤ (C₂ : ℝ) * (m ^ n : ℝ) := by
  refine ⟨⟨1 / 4, by norm_num⟩, ⟨1, by norm_num⟩, ⟨Real.exp 1, Real.exp_pos 1⟩, ?_⟩
  intro L ε n hε hsmall
  have hsmall' : ε ≤ (L : ℝ) / (4 * (n : ℝ)) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsmall
  simpa using gridCardinality_bounds_of_epsilon_le_quarter_L_div_n hε hsmall'
