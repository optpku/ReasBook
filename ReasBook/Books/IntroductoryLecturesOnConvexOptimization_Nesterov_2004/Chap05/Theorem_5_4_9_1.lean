/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_2

-- Declarations for this item will be appended below by the statement pipeline.

/-
Theorem 5.4.9.1 lies in the chapter's ellipsoid-method arithmetic-complexity domain.

Sampled owner declarations before refining:
* `HasEllipsoidMethodComplexityBounds` in `Definition_5_4_9_2`, the source-facing Chapter 5
  owner on the primitive iteration-count and per-iteration cost data;
* `HasLpBarrierShortStepTotalArithmeticComplexityBound` in `Theorem_5_4_9_3`, the nearby Chapter
  5 owner for a direct total arithmetic-complexity bound on primitive arithmetic-work data;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, the project
  pattern where the public complexity notion is a `Prop` on primitive data, with explicit bridge
  lemmas unpacking it.

Best owner abstraction:
* source-facing: the total arithmetic complexity of the ellipsoid method induced by the primitive
  iteration-count model and the two per-iteration cost functions;
* core/canonical: a direct `Prop`-valued owner expressing the final `O(n^3 (m + n) log (1 / ε))`
  bound on those primitive data;
* bridge/view: the theorem below deriving that total-complexity owner from the primitive bounds in
  `HasEllipsoidMethodComplexityBounds`.

Primitive data:
* the accuracy-indexed iteration count `N_it`;
* the oracle arithmetic cost per iteration;
* the additional per-iteration arithmetic overhead.

Derived API:
* the source-facing total arithmetic-complexity owner below;
* its explicit existential-constant unpacking lemma;
* the theorem deriving that owner from Definition 5.4.9.2.

Source/core/bridge triage:
* source-facing: `HasEllipsoidMethodTotalArithmeticComplexityBound`;
* core/canonical: the primitive complexity-model owner `HasEllipsoidMethodComplexityBounds`;
* bridge/view: `ellipsoidMethodTotalArithmeticComplexity_bound`.

The earlier version stated the final total-complexity estimate directly as a one-off existential
theorem. The surrounding chapter instead organizes complexity statements around `Prop`-valued
owners on primitive data. This refinement therefore keeps Definition 5.4.9.2 as the primitive
owner, introduces the direct source-facing total-complexity owner in this theorem file, and
rewrites the theorem as the canonical bridge from the primitive model to that owner. -/

/-- Theorem 5.4.9.1's source-facing total arithmetic-complexity owner for the ellipsoid method.
It records the textbook bound saying that the total arithmetic work induced by the primitive
iteration-count, oracle-cost, and extra-cost data is `O(n^3 (m + n) log (1 / ε))` with a
constant independent of the target accuracy `ε ∈ (0, 1)`. -/
def HasEllipsoidMethodTotalArithmeticComplexityBound
    (iterationCount : ℝ → ℕ → ℕ)
    (oracleCostPerIteration : ℕ → ℕ → ℕ)
    (extraCostPerIteration : ℕ → ℕ) : Prop :=
  ∃ C : ℝ,
    0 < C ∧
      ∀ {ε : ℝ} {m n : ℕ},
        ε ∈ Set.Ioo (0 : ℝ) 1 →
        0 < m →
        0 < n →
        (iterationCount ε n * (oracleCostPerIteration m n + extraCostPerIteration n) : ℝ) ≤
          C * (n : ℝ) ^ 3 * ((m : ℝ) + (n : ℝ)) * Real.log (1 / ε)

-- Proof sketch: unfold `HasEllipsoidMethodTotalArithmeticComplexityBound`; this is exactly the
-- explicit constant-factor form of the textbook total arithmetic estimate on the primitive
-- iteration-count and per-iteration arithmetic-work data.
/-- Unfolding `HasEllipsoidMethodTotalArithmeticComplexityBound` recovers the explicit
constant-factor form of the textbook ellipsoid-method total arithmetic bound. -/
theorem hasEllipsoidMethodTotalArithmeticComplexityBound_iff
    (iterationCount : ℝ → ℕ → ℕ)
    (oracleCostPerIteration : ℕ → ℕ → ℕ)
    (extraCostPerIteration : ℕ → ℕ) :
    HasEllipsoidMethodTotalArithmeticComplexityBound
        iterationCount oracleCostPerIteration extraCostPerIteration ↔
      ∃ C : ℝ,
        0 < C ∧
          ∀ {ε : ℝ} {m n : ℕ},
            ε ∈ Set.Ioo (0 : ℝ) 1 →
            0 < m →
            0 < n →
            (iterationCount ε n * (oracleCostPerIteration m n + extraCostPerIteration n) : ℝ) ≤
              C * (n : ℝ) ^ 3 * ((m : ℝ) + (n : ℝ)) * Real.log (1 / ε) := by
  rfl

/-- Helper for Theorem 5.4.9.1: for accuracies `ε ∈ (0, 1)`, the logarithmic factor
`log (1 / ε)` is nonnegative. -/
lemma log_inv_nonneg_of_mem_Ioo_zero_one
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ Real.log (1 / ε) := by
  -- Proof comment: `0 < ε < 1` implies `1 < 1 / ε`, and the real logarithm is nonnegative on
  -- inputs at least `1`.
  have h_inv : 1 < 1 / ε := by
    simpa [one_div] using (one_lt_inv₀ hε.1).2 hε.2
  exact Real.log_nonneg h_inv.le

/-- Helper for Theorem 5.4.9.1: the oracle and extra per-iteration arithmetic costs add after
casting the primitive nat-valued costs to `ℝ`. -/
lemma combined_step_cost_le_component_sum
    {oracleCostPerIteration : ℕ → ℕ → ℕ}
    {extraCostPerIteration : ℕ → ℕ}
    {C_oracle C_iter : ℝ}
    (horacle_bound : ∀ {m n : ℕ}, 0 < m → 0 < n →
      (oracleCostPerIteration m n : ℝ) ≤ C_oracle * (m : ℝ) * (n : ℝ))
    (hextra_bound : ∀ {n : ℕ}, 0 < n →
      (extraCostPerIteration n : ℝ) ≤ C_iter * (n : ℝ) ^ 2)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ((oracleCostPerIteration m n + extraCostPerIteration n : ℕ) : ℝ) ≤
      C_oracle * (m : ℝ) * (n : ℝ) + C_iter * (n : ℝ) ^ 2 := by
  -- Proof comment: after rewriting the cast of the nat sum, the desired estimate is the direct
  -- sum of the two component bounds from the complexity model.
  rw [Nat.cast_add]
  exact add_le_add (horacle_bound hm hn) (hextra_bound hn)

/-- Helper for Theorem 5.4.9.1: the textbook bound `O(m n) + O(n^2)` compresses to
`O(n (m + n))` with the summed constant. -/
lemma component_sum_le_scaled_dimension_sum
    {C_oracle C_iter : ℝ}
    (hC_oracle : 0 ≤ C_oracle)
    (hC_iter : 0 ≤ C_iter)
    (m n : ℕ) :
    C_oracle * (m : ℝ) * (n : ℝ) + C_iter * (n : ℝ) ^ 2 ≤
      (C_oracle + C_iter) * (n : ℝ) * ((m : ℝ) + (n : ℝ)) := by
  -- Proof comment: each summand is bounded by the same common factor `n * (m + n)`, since both
  -- `m` and `n` are at most `m + n` and the coefficients are nonnegative.
  have hm_nat : m ≤ m + n := by
    omega
  have hn_nat : n ≤ m + n := by
    omega
  have hm_le : (m : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
    exact_mod_cast hm_nat
  have hn_le : (n : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
    exact_mod_cast hn_nat
  have h_oracle_factor_nonneg : 0 ≤ C_oracle * (n : ℝ) := by
    positivity
  have h_oracle :
      C_oracle * (m : ℝ) * (n : ℝ) ≤
        C_oracle * (n : ℝ) * ((m : ℝ) + (n : ℝ)) := by
    have hmul :
        (C_oracle * (n : ℝ)) * (m : ℝ) ≤
          (C_oracle * (n : ℝ)) * ((m : ℝ) + (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hm_le h_oracle_factor_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have h_iter_factor_nonneg : 0 ≤ C_iter * (n : ℝ) := by
    positivity
  have h_iter :
      C_iter * (n : ℝ) ^ 2 ≤
        C_iter * (n : ℝ) * ((m : ℝ) + (n : ℝ)) := by
    have hmul :
        (C_iter * (n : ℝ)) * (n : ℝ) ≤
          (C_iter * (n : ℝ)) * ((m : ℝ) + (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hn_le h_iter_factor_nonneg
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    C_oracle * (m : ℝ) * (n : ℝ) + C_iter * (n : ℝ) ^ 2
      ≤ C_oracle * (n : ℝ) * ((m : ℝ) + (n : ℝ)) +
          C_iter * (n : ℝ) * ((m : ℝ) + (n : ℝ)) := by
            exact add_le_add h_oracle h_iter
    _ = (C_oracle + C_iter) * (n : ℝ) * ((m : ℝ) + (n : ℝ)) := by
      ring

-- Proof sketch: unpack the constants from `HasEllipsoidMethodComplexityBounds`, combine the
-- bounds `N_it = O(n^2 log (1 / ε))`, `C_oracle = O(m n)`, and `C_iter = O(n^2)` to obtain the
-- per-iteration estimate `O(m n + n^2) = O(n (m + n))`, and then multiply by the iteration-count
-- bound. The resulting total-complexity constant is still uniform in `ε ∈ (0, 1)`.
/-- Theorem 5.4.9.1: under the textbook iteration-count, oracle-cost, and per-iteration overhead
bounds from Definition 5.4.9.2, the total arithmetic complexity of the ellipsoid method satisfies
the source-facing owner `HasEllipsoidMethodTotalArithmeticComplexityBound`. -/
theorem ellipsoidMethodTotalArithmeticComplexity_bound
    (iterationCount : ℝ → ℕ → ℕ)
    (oracleCostPerIteration : ℕ → ℕ → ℕ)
    (extraCostPerIteration : ℕ → ℕ)
    (hmodel :
      HasEllipsoidMethodComplexityBounds
        iterationCount oracleCostPerIteration extraCostPerIteration) :
    HasEllipsoidMethodTotalArithmeticComplexityBound
      iterationCount oracleCostPerIteration extraCostPerIteration := by
  rcases hmodel with
    ⟨C_it, C_oracle, C_iter, hC_it, hC_oracle, hC_iter,
      hiter_bound, horacle_bound, hextra_bound⟩
  -- Proof comment: choose the product of the iteration-count constant and the compressed
  -- per-iteration constant as the final witness for the total arithmetic complexity.
  have hC :
      0 < C_it * (C_oracle + C_iter) := by
    positivity
  refine ⟨C_it * (C_oracle + C_iter), hC, ?_⟩
  intro ε m n hε hm hn
  -- Proof comment: the logarithm factor is nonnegative on the small-accuracy regime
  -- `ε ∈ (0, 1)`, so the iteration bound can be multiplied safely.
  have hlog_nonneg : 0 ≤ Real.log (1 / ε) :=
    log_inv_nonneg_of_mem_Ioo_zero_one hε
  -- Proof comment: first combine the primitive oracle and overhead bounds, then compress the
  -- resulting `m n + n^2` expression into the canonical `n (m + n)` factor.
  have hstep_sum :
      ((oracleCostPerIteration m n + extraCostPerIteration n : ℕ) : ℝ) ≤
        C_oracle * (m : ℝ) * (n : ℝ) + C_iter * (n : ℝ) ^ 2 :=
    combined_step_cost_le_component_sum horacle_bound hextra_bound hm hn
  have hstep_bound :
      ((oracleCostPerIteration m n + extraCostPerIteration n : ℕ) : ℝ) ≤
        (C_oracle + C_iter) * (n : ℝ) * ((m : ℝ) + (n : ℝ)) := by
    exact hstep_sum.trans
      (component_sum_le_scaled_dimension_sum hC_oracle.le hC_iter.le m n)
  have hstep_bound_expanded :
      (oracleCostPerIteration m n : ℝ) + (extraCostPerIteration n : ℝ) ≤
        (C_oracle + C_iter) * (n : ℝ) * ((m : ℝ) + (n : ℝ)) := by
    simpa [Nat.cast_add] using hstep_bound
  have hstep_nonneg :
      0 ≤ (oracleCostPerIteration m n : ℝ) + (extraCostPerIteration n : ℝ) := by
    positivity
  have hiter_nonneg :
      0 ≤ C_it * (n : ℝ) ^ 2 * Real.log (1 / ε) := by
    positivity
  have hproduct :
      (iterationCount ε n : ℝ) *
          ((oracleCostPerIteration m n : ℝ) + (extraCostPerIteration n : ℝ)) ≤
        (C_it * (n : ℝ) ^ 2 * Real.log (1 / ε)) *
          ((C_oracle + C_iter) * (n : ℝ) * ((m : ℝ) + (n : ℝ))) := by
    exact mul_le_mul (hiter_bound hε hn) hstep_bound_expanded hstep_nonneg hiter_nonneg
  -- Proof comment: rewrite the nat-valued total work as a product of real casts, apply the two
  -- factor bounds, and normalize the polynomial expression into the textbook `n^3 (m + n)` form.
  calc
    (iterationCount ε n : ℝ) *
          ((oracleCostPerIteration m n : ℝ) + (extraCostPerIteration n : ℝ))
      ≤ (C_it * (n : ℝ) ^ 2 * Real.log (1 / ε)) *
          ((C_oracle + C_iter) * (n : ℝ) * ((m : ℝ) + (n : ℝ))) := hproduct
    _ = (C_it * (C_oracle + C_iter)) * (n : ℝ) ^ 3 *
          ((m : ℝ) + (n : ℝ)) * Real.log (1 / ε) := by
            ring
