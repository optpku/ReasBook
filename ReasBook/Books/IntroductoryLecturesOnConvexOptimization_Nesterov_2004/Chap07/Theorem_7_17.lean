/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_73
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_74
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Theorem_7_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

section

variable {X : Type u}

/- Theorem 7.17 lies in the Chapter 7 finite-horizon geometric-mean / barrier-rate bridge
domain.

Mandatory domain-style sampling:
- `dynamicStrategyAverageRateOfGrowth` in `Chap07/Definition_7_74`, the source-facing owner for
  the realized dynamic geometric mean along a finite horizon;
- `staticProductionAverageEfficiency` in `Chap07/Definition_7_73`, the chapter owner for the
  static geometric mean on the same horizon;
- `positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate` in
  `Chap07/Theorem_7_16`, the canonical exponentiation bridge from a logarithmic average estimate
  to a geometric-mean lower bound;
- `barrierSubgradientRelativeAccuracyDelta` in `Chap07/Theorem_7_16`, the owner of the explicit
  Chapter 7 rate term.

Best owner abstraction:
- source-facing: the dynamic-vs-static finite-horizon comparison from Theorem 7.17;
- core/canonical: `dynamicStrategyAverageRateOfGrowth`, `staticProductionAverageEfficiency`, and
  the generic bridge theorem
  `positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate`;
- bridge/view: the conversion between the chapter's finite-horizon `Fin`-indexed trace and the
  generic `ℕ`-indexed geometric-mean bridge, together with the asymptotic theorem for
  `barrierSubgradientRelativeAccuracyDelta`.

Primitive data:
- the feasible subtype `P`;
- the horizon `N`;
- the positive outputs `ψ`;
- the realized dynamic trace `x`;
- the comparison static point `xStatic`.

Derived API:
- the dynamic geometric mean `dynamicStrategyAverageRateOfGrowth ψ x`;
- the static geometric mean `staticProductionAverageEfficiency ψ xStatic`;
- the explicit error rate `barrierSubgradientRelativeAccuracyDelta`.

Source/core/bridge triage:
- source-facing: `dynamicStrategyAverageRateOfGrowth_ge_optimalStaticEfficiency_mul_exp_neg_delta`,
  which compares the dynamic owner to the canonical optimal static efficiency;
- core/canonical: `IsMaxOn`, `sSup`, and the generic theorem from `Theorem_7_16`;
- bridge/view:
  `dynamicStrategyAverageRateOfGrowth_ge_staticEfficiency_mul_exp_neg_delta_of_log_gap`
  and the asymptotic vanishing statement for the explicit rate.
-/

-- Proof sketch: rewrite the logarithmic average of the dynamic outputs as the logarithm of
-- `dynamicStrategyAverageRateOfGrowth ψ x`, then exponentiate the assumed logarithmic comparison
-- with the static average efficiency at the supplied comparison point.
/-- Exponentiating a logarithmic comparison estimate at a fixed static strategy `xStatic` yields
the corresponding geometric-mean lower bound for the dynamic strategy. This is the bridge/view
step used in Theorem `7.17` after choosing an optimal static strategy via Definition `7.73`. -/
theorem dynamicStrategyAverageRateOfGrowth_ge_staticEfficiency_mul_exp_neg_delta_of_log_gap
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (x : Fin (N + 1) → P)
    (xStatic : P)
    {ν : ℝ}
    (hlog_rate :
      Real.log (staticProductionAverageEfficiency ψ xStatic) -
          (∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ)) / ((N : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν N) :
    dynamicStrategyAverageRateOfGrowth ψ x ≥
      staticProductionAverageEfficiency ψ xStatic *
        Real.exp (-barrierSubgradientRelativeAccuracyDelta ν N) := by
  let outputs : Fin (N + 1) → {r : ℝ // 0 < r} := fun k ↦ ψ k (x k)
  let indices : ℕ → Fin (N + 1) := fun i ↦ ⟨i % (N + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hStaticPos : 0 < staticProductionAverageEfficiency ψ xStatic := by
    rw [staticProductionAverageEfficiency_def, staticProductionTotalOutput_def]
    exact Real.rpow_pos_of_pos (Finset.prod_pos fun k _ ↦ (ψ k xStatic).property) _
  have hsum :
      Finset.sum (Finset.range (N + 1)) (fun i ↦ Real.log (outputs (indices i) : ℝ)) =
        ∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ) := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun i ↦ Real.log (outputs (indices i) : ℝ))
          = ∑ k : Fin (N + 1), Real.log (outputs (indices k) : ℝ) := by
              simpa using
                (Fin.sum_univ_eq_sum_range (fun i ↦ Real.log (outputs (indices i) : ℝ))
                  (N + 1)).symm
      _ = ∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        simp [outputs, indices, Nat.mod_eq_of_lt k.2]
  have hprod :
      (∏ k : Fin (N + 1), (ψ k (x k) : ℝ)) =
        Finset.prod (Finset.range (N + 1)) (fun i ↦ (outputs (indices i) : ℝ)) := by
    calc
      (∏ k : Fin (N + 1), (ψ k (x k) : ℝ))
          = ∏ k : Fin (N + 1), (outputs (indices k) : ℝ) := by
              refine Finset.prod_congr rfl fun k _ ↦ ?_
              simp [outputs, indices, Nat.mod_eq_of_lt k.2]
      _ = Finset.prod (Finset.range (N + 1)) (fun i ↦ (outputs (indices i) : ℝ)) := by
        simpa using
          (Fin.prod_univ_eq_prod_range (fun i ↦ (outputs (indices i) : ℝ)) (N + 1))
  have hlog_rate' :
      Real.log (staticProductionAverageEfficiency ψ xStatic) -
          (Finset.sum (Finset.range (N + 1)) fun i ↦ Real.log (outputs (indices i) : ℝ)) /
            ((N : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν N := by
    simpa [hsum] using hlog_rate
  have hbridge :=
    positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate
      outputs
      indices
      ⟨staticProductionAverageEfficiency ψ xStatic, hStaticPos⟩
      N
      hlog_rate'
  have hdynamic :
      dynamicStrategyAverageRateOfGrowth ψ x =
        Real.rpow
          (Finset.prod (Finset.range (N + 1)) fun i ↦ (outputs (indices i) : ℝ))
          ((1 : ℝ) / (N + 1 : ℝ)) := by
    rw [dynamicStrategyAverageRateOfGrowth_def, ← hprod]
  rw [positiveIterateGeometricMean_def] at hbridge
  simpa [hdynamic] using hbridge

/-- If `xStatic` maximizes the static cumulative output from Definition `7.73`, then it also
maximizes the derived static geometric-mean efficiency. -/
theorem staticProductionAverageEfficiency_isMaxOn_of_staticProductionTotalOutput_isMaxOn
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (xStatic : P)
    (hoptimal : IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic) :
    IsMaxOn (staticProductionAverageEfficiency ψ) Set.univ xStatic := by
  rw [isMaxOn_univ_iff] at hoptimal ⊢
  intro y
  rw [staticProductionAverageEfficiency_def, staticProductionAverageEfficiency_def]
  have hy_nonneg : 0 ≤ staticProductionTotalOutput ψ y := by
    rw [staticProductionTotalOutput_def]
    exact le_of_lt (Finset.prod_pos fun k _ ↦ (ψ k y).property)
  exact Real.rpow_le_rpow
    hy_nonneg
    (hoptimal y)
    (by positivity)

/-- An optimal static strategy realizes the canonical optimal static efficiency, expressed as the
supremum of all static geometric-mean efficiencies over the feasible subtype `P`. -/
theorem staticProductionAverageEfficiency_eq_sSup_of_optimalStaticStrategy
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (xStatic : P)
    (hoptimal : IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic) :
    sSup (Set.range (staticProductionAverageEfficiency ψ)) =
      staticProductionAverageEfficiency ψ xStatic := by
  have hoptimalEfficiency :
      IsMaxOn (staticProductionAverageEfficiency ψ) Set.univ xStatic :=
    staticProductionAverageEfficiency_isMaxOn_of_staticProductionTotalOutput_isMaxOn ψ xStatic
      hoptimal
  have hne : (Set.range (staticProductionAverageEfficiency ψ)).Nonempty :=
    ⟨_, xStatic, rfl⟩
  have hbdd : BddAbove (Set.range (staticProductionAverageEfficiency ψ)) := by
    refine ⟨staticProductionAverageEfficiency ψ xStatic, ?_⟩
    rintro y ⟨z, rfl⟩
    exact (isMaxOn_univ_iff.mp hoptimalEfficiency z)
  apply le_antisymm
  · refine csSup_le hne ?_
    rintro y ⟨z, rfl⟩
    exact (isMaxOn_univ_iff.mp hoptimalEfficiency z)
  · exact le_csSup hbdd ⟨xStatic, rfl⟩

-- Proof sketch: use Definition `7.73` to identify the comparison point with an optimal static
-- strategy, rewrite its efficiency as the canonical supremum of all static efficiencies, and then
-- apply the one-point exponentiation bridge above.
/-- Relative-efficiency clause of Theorem 7.17: if `xStatic` is an optimal static strategy in the
sense of Definition `7.73` and the barrier-subgradient logarithmic comparison estimate is
available at that optimizer, then the dynamic average rate of growth is at least the canonical
optimal static efficiency times `exp (-δ_N)`. -/
theorem dynamicStrategyAverageRateOfGrowth_ge_optimalStaticEfficiency_mul_exp_neg_delta
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (x : Fin (N + 1) → P)
    (xStatic : P)
    (hoptimal : IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic)
    {ν : ℝ}
    (hlog_rate :
      Real.log (staticProductionAverageEfficiency ψ xStatic) -
          (∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ)) / ((N : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν N) :
    dynamicStrategyAverageRateOfGrowth ψ x ≥
      sSup (Set.range (staticProductionAverageEfficiency ψ)) *
        Real.exp (-barrierSubgradientRelativeAccuracyDelta ν N) := by
  rw [staticProductionAverageEfficiency_eq_sSup_of_optimalStaticStrategy ψ xStatic hoptimal]
  exact
    dynamicStrategyAverageRateOfGrowth_ge_staticEfficiency_mul_exp_neg_delta_of_log_gap
      ψ x xStatic hlog_rate

-- Proof sketch: use that both `(N + 1)⁻¹/²` and `(N + 1)⁻¹` tend to `0` as `N → ∞`, the
-- logarithmic factor grows only like `log (√N)`, and then combine these asymptotics in the
-- owner `barrierSubgradientRelativeAccuracyDelta ν N`.
/-- Helper for Theorem 7.17: when `ν > 0`, the square-root growth term
`√(ν (N + 1))` tends to `∞`. -/
lemma barrier_rate_sqrt_argument_tendsto_atTop {ν : NNReal} (hν : 0 < (ν : ℝ)) :
    Filter.Tendsto
      (fun N : ℕ ↦ Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))
      Filter.atTop Filter.atTop := by
  -- The factor `N + 1` tends to `∞`, so multiplying by the positive constant `ν` preserves this.
  have hNp1 : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) + 1) Filter.atTop Filter.atTop := by
    simpa using
      tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds 1))
  have hmul : Filter.Tendsto
      (fun N : ℕ ↦ (ν : ℝ) * ((N : ℝ) + 1))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hν hNp1
  -- Taking square roots preserves divergence to `∞` on nonnegative reals.
  exact Real.tendsto_sqrt_atTop.comp hmul

/-- Helper for Theorem 7.17: the ratio `(1 + log w_N) / w_N` vanishes for the affine-sqrt growth
term `w_N = 2 + (3 / 2) √(ν (N + 1))`. -/
lemma one_add_log_affine_sqrt_rate_div_self_tendsto_zero {ν : NNReal} (hν : 0 < (ν : ℝ)) :
    Filter.Tendsto
      (fun N : ℕ ↦
        (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))) /
          (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))))
      Filter.atTop (nhds 0) := by
  let w : ℕ → ℝ := fun N ↦ 2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))
  have hw_atTop : Filter.Tendsto w Filter.atTop Filter.atTop := by
    have hscaled : Filter.Tendsto
        (fun N : ℕ ↦ (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity)
        (barrier_rate_sqrt_argument_tendsto_atTop hν)
    -- Adding a constant does not change divergence to `∞`.
    simpa [w] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (2 : ℝ)) Filter.atTop (nhds 2)).add_atTop
        hscaled
  have hInv : Filter.Tendsto (fun N : ℕ ↦ 1 / w N) Filter.atTop (nhds 0) := by
    -- The reciprocal of an `atTop` function vanishes.
    simpa [w, one_div, one_mul] using
      (tendsto_mul_add_inv_atTop_nhds_zero (1 : ℝ) 0 one_ne_zero).comp hw_atTop
  have hLogDiv : Filter.Tendsto (fun N : ℕ ↦ Real.log (w N) / w N) Filter.atTop (nhds 0) := by
    -- The logarithm is negligible compared with linear growth.
    simpa [w, one_mul] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hw_atTop
  have hSum : Filter.Tendsto
      (fun N : ℕ ↦ 1 / w N + Real.log (w N) / w N)
      Filter.atTop (nhds 0) := by
    simpa using hInv.add hLogDiv
  refine Filter.Tendsto.congr' ?_ hSum
  exact Filter.Eventually.of_forall fun N ↦ by
    simp [w, add_div, one_div]

/-- Helper for Theorem 7.17: the small prefactor `√(ν / (N + 1))` tends to `0`. -/
lemma barrier_rate_small_prefactor_tendsto_zero {ν : NNReal} :
    Filter.Tendsto
      (fun N : ℕ ↦ Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
  have hdiv : Filter.Tendsto
      (fun N : ℕ ↦ (ν : ℝ) / ((N : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    -- The factor `(N + 1)⁻¹` tends to `0`, so scaling by `ν` still tends to `0`.
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ν : ℝ))
  -- Square root is continuous at `0`.
  simpa only [Function.comp_apply, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hdiv

/-- Helper for Theorem 7.17: the normalized affine-square-root factor
`√(ν / (N + 1)) * (2 + (3 / 2) √(ν (N + 1)))` converges to `(3 / 2) ν`. -/
lemma sqrtPrefactor_mul_affineSqrtRate_tendsto {ν : NNReal} :
    Filter.Tendsto
      (fun N : ℕ ↦
        Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
          (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))))
      Filter.atTop (nhds ((3 / 2 : ℝ) * (ν : ℝ))) := by
  have hsmall := barrier_rate_small_prefactor_tendsto_zero (ν := ν)
  have hrewrite :
      ∀ N : ℕ,
        Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
            (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))) =
          2 * Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) + (3 / 2 : ℝ) * (ν : ℝ) := by
    intro N
    have hratio_nonneg : 0 ≤ (ν : ℝ) / ((N : ℝ) + 1) := by
      exact div_nonneg (NNReal.coe_nonneg ν) (Nat.cast_add_one_pos N).le
    have harg_nonneg : 0 ≤ (ν : ℝ) * ((N : ℝ) + 1) := by positivity
    have hmix :
        Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
            Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)) =
          (ν : ℝ) := by
      have hinside :
          ((ν : ℝ) / ((N : ℝ) + 1)) * ((ν : ℝ) * ((N : ℝ) + 1)) = (ν : ℝ) ^ 2 := by
        field_simp [show ((N : ℝ) + 1) ≠ 0 by positivity]
      -- Collapse the mixed product of square roots to the constant `ν`.
      calc
        Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
            Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)) =
          Real.sqrt (((ν : ℝ) / ((N : ℝ) + 1)) * ((ν : ℝ) * ((N : ℝ) + 1))) := by
            rw [← Real.sqrt_mul hratio_nonneg ((ν : ℝ) * ((N : ℝ) + 1))]
        _ = Real.sqrt ((ν : ℝ) ^ 2) := by
            rw [hinside]
        _ = (ν : ℝ) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (NNReal.coe_nonneg ν)]
    -- Expand the affine factor and use the mixed-product identity.
    calc
      Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
          (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))) =
        2 * Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) +
          (3 / 2 : ℝ) *
            (Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
              Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))) := by
          ring
      _ = 2 * Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) + (3 / 2 : ℝ) * (ν : ℝ) := by
          rw [hmix]
  have hscaled :
      Filter.Tendsto
        (fun N : ℕ ↦ 2 * Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)))
        Filter.atTop (nhds (2 * 0)) :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (2 : ℝ)) Filter.atTop (nhds 2)).mul hsmall
  have hsum :
      Filter.Tendsto
        (fun N : ℕ ↦ 2 * Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) + (3 / 2 : ℝ) * (ν : ℝ))
        Filter.atTop (nhds (2 * 0 + (3 / 2 : ℝ) * (ν : ℝ))) := by
    -- The vanishing square-root term leaves only the constant limit.
    exact hscaled.add (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ ↦ (3 / 2 : ℝ) * (ν : ℝ))
      Filter.atTop (nhds ((3 / 2 : ℝ) * (ν : ℝ))))
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ (hrewrite N).symm) ?_
  simpa using hsum

/-- Helper for Theorem 7.17: the dominant term
`√(ν / (N + 1)) (1 + log (2 + (3 / 2) √(ν (N + 1))))` tends to `0`. -/
lemma sqrt_prefactor_mul_log_term_tendsto_zero {ν : NNReal} (hν : 0 < (ν : ℝ)) :
    Filter.Tendsto
      (fun N : ℕ ↦
        Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
          (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))))
      Filter.atTop (nhds 0) := by
  let w : ℕ → ℝ := fun N ↦ 2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))
  have hratio := one_add_log_affine_sqrt_rate_div_self_tendsto_zero (ν := ν) hν
  have hfactor := sqrtPrefactor_mul_affineSqrtRate_tendsto (ν := ν)
  have hrewrite :
      ∀ N : ℕ,
        Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) * (1 + Real.log (w N)) =
          (Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) * w N) *
            ((1 + Real.log (w N)) / w N) := by
    intro N
    have hw_pos : 0 < w N := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)) := Real.sqrt_nonneg _
      positivity
    -- Rewrite the logarithmic term as a bounded factor times the vanishing ratio.
    calc
      Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) * (1 + Real.log (w N)) =
        Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) * (w N * ((1 + Real.log (w N)) / w N)) := by
          field_simp [hw_pos.ne']
      _ = (Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) * w N) *
            ((1 + Real.log (w N)) / w N) := by
          ring
  have hmul :
      Filter.Tendsto
        (fun N : ℕ ↦
          (Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) * w N) *
            ((1 + Real.log (w N)) / w N))
        Filter.atTop (nhds (((3 / 2 : ℝ) * (ν : ℝ)) * 0)) := by
    -- A finite normalization factor times a vanishing ratio still vanishes.
    simpa [w] using hfactor.mul hratio
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ (hrewrite N).symm) ?_
  simpa using hmul

/-- Helper for Theorem 7.17: the smaller summand
`(ν / (N + 1)) (1 + log (2 + (3 / 2) √(ν (N + 1))))` also tends to `0`. -/
lemma barrierRateRatio_mul_logTerm_tendsto_zero {ν : NNReal} (hν : 0 < (ν : ℝ)) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ((ν : ℝ) / ((N : ℝ) + 1)) *
          (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))))
      Filter.atTop (nhds 0) := by
  have hsmall := barrier_rate_small_prefactor_tendsto_zero (ν := ν)
  have hdominant := sqrt_prefactor_mul_log_term_tendsto_zero (ν := ν) hν
  have hrewrite :
      ∀ N : ℕ,
        ((ν : ℝ) / ((N : ℝ) + 1)) *
            (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))) =
          Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
            (Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
              (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))))) := by
    intro N
    have hratio_nonneg : 0 ≤ (ν : ℝ) / ((N : ℝ) + 1) := by
      exact div_nonneg (NNReal.coe_nonneg ν) (Nat.cast_add_one_pos N).le
    -- Replace the ratio by the square of its square root.
    calc
      ((ν : ℝ) / ((N : ℝ) + 1)) *
          (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))) =
        (Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1))) ^ 2 *
          (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))) := by
          congr 1
          exact (Real.sq_sqrt hratio_nonneg).symm
      _ = Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
            (Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
              (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))))) := by
          ring
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ (hrewrite N).symm) ?_
  simpa using hsmall.mul hdominant

/-- Theorem 7.17: the explicit barrier-subgradient relative-accuracy term tends to `0` as the
horizon tends to infinity. This is the source theorem's final “in particular” conclusion after the
relative-efficiency inequality above. -/
theorem barrierSubgradientRelativeAccuracyDelta_tendsto_zero
    (ν : NNReal) :
    Filter.Tendsto
      (fun N : ℕ ↦ barrierSubgradientRelativeAccuracyDelta (ν : ℝ) N)
      Filter.atTop (nhds 0) := by
  by_cases hν0 : (ν : ℝ) = 0
  · -- In the degenerate case `ν = 0`, the explicit rate vanishes identically.
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    exact Filter.Eventually.of_forall fun N ↦ by
      simp [barrierSubgradientRelativeAccuracyDelta, hν0]
  · have hν : 0 < (ν : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg ν) (Ne.symm hν0)
    have hdominant := sqrt_prefactor_mul_log_term_tendsto_zero (ν := ν) hν
    have hsecondary := barrierRateRatio_mul_logTerm_tendsto_zero (ν := ν) hν
    have hsum :
        Filter.Tendsto
          (fun N : ℕ ↦
            Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
                (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))) ) +
              ((ν : ℝ) / ((N : ℝ) + 1)) *
                (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1)))))
          Filter.atTop (nhds 0) := by
      -- Both summands vanish, so their sum does too.
      simpa using hdominant.add hsecondary
    have hscaled :
        Filter.Tendsto
          (fun N : ℕ ↦
            2 *
              (Real.sqrt ((ν : ℝ) / ((N : ℝ) + 1)) *
                  (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))) ) +
                ((ν : ℝ) / ((N : ℝ) + 1)) *
                  (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((N : ℝ) + 1))))))
          Filter.atTop (nhds 0) := by
      -- The outer constant factor preserves the zero limit.
      simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (2 : ℝ)) Filter.atTop (nhds 2)).mul
          hsum
    refine Filter.Tendsto.congr' ?_ hscaled
    exact Filter.Eventually.of_forall fun N ↦ by
      -- Expand the Chapter 7 rate into the two asymptotically vanishing summands.
      unfold barrierSubgradientRelativeAccuracyDelta
      ring

end
