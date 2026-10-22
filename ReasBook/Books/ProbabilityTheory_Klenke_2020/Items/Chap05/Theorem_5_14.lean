/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- Helper for Theorem 5.14: every centered empirical average has expectation `0`. -/
private lemma integral_centered_average_eq_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (h_memLp : ∀ n, MemLp (X (n + 1)) 2 P) (n : ℕ) :
    P[centered_average P (fun k ↦ X (k + 1)) n] = 0 := by
  -- Expand the centered average and reduce the claim to vanishing of each centered summand.
  have hterm_int :
      ∀ i ∈ Finset.range n, Integrable (fun ω ↦ X (i + 1) ω - P[X (i + 1)]) P := by
    intro i _
    exact ((h_memLp i).integrable (by simp)).sub (integrable_const _)
  have hsum_int :
      Integrable (fun ω ↦ ∑ i ∈ Finset.range n, (X (i + 1) ω - P[X (i + 1)])) P :=
    integrable_finset_sum _ hterm_int
  simp only [centered_average, centered_partial_sum, div_eq_inv_mul]
  rw [integral_const_mul, integral_finset_sum _ hterm_int]
  suffices
      hsum :
        ∑ i ∈ Finset.range n, P[fun ω ↦ X (i + 1) ω - P[X (i + 1)]] = 0 by
    simp [hsum]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [integral_sub ((h_memLp i).integrable (by simp)) (integrable_const _)]
  simp

/-- Helper for Theorem 5.14: centering preserves pairwise uncorrelatedness for the finite `Fin n`
family extracted from the sequence. -/
private lemma pairwise_cov_centered_family_eq_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (h_memLp : ∀ n, MemLp (X (n + 1)) 2 P)
    (h_uncorr : Pairwise fun i j ↦ cov[X (i + 1), X (j + 1); P] = 0) {n : ℕ} :
    Pairwise fun i j : Fin n ↦
      cov[fun ω ↦ X (i.1 + 1) ω - P[X (i.1 + 1)],
        fun ω ↦ X (j.1 + 1) ω - P[X (j.1 + 1)]; P] = 0 := by
  intro i j hij
  -- Remove the centering constants and appeal to the original pairwise uncorrelatedness hypothesis.
  have hXi_int : Integrable (X (i.1 + 1)) P := (h_memLp i.1).integrable (by simp)
  have hXj_int : Integrable (X (j.1 + 1)) P := (h_memLp j.1).integrable (by simp)
  have hij_nat : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
  simpa [hXi_int, hXj_int] using h_uncorr hij_nat

/-- Helper for Theorem 5.14: rewrite the chapter's centered average as a normalized finite `Fin n`
sum, matching the owner theorem for variances of finite families. -/
private lemma centered_average_eq_fin_sum
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (n : ℕ) :
    centered_average P (fun k ↦ X (k + 1)) n =
      fun ω ↦ (1 / (n : ℝ)) * ∑ i : Fin n, (X (i.1 + 1) ω - P[X (i.1 + 1)]) := by
  ext ω
  have hsum_eq :
      (∑ i : Fin n, (X (i.1 + 1) ω - P[X (i.1 + 1)])) =
        ∑ i ∈ Finset.range n, (X (i + 1) ω - P[X (i + 1)]) := by
    symm
    rw [Finset.sum_range]
  rw [centered_average, centered_partial_sum, div_eq_mul_inv, ← hsum_eq]
  simp [one_div, mul_comm]

/-- Helper for Theorem 5.14: Bienaymé's formula and the uniform variance bound imply the variance
estimate `Var[centered_average] ≤ sup Var / n`. -/
private lemma variance_centered_average_le_sSup_div
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (h_memLp : ∀ n, MemLp (X (n + 1)) 2 P)
    (h_uncorr : Pairwise fun i j ↦ cov[X (i + 1), X (j + 1); P] = 0)
    (h_var_bdd : BddAbove (Set.range fun n : ℕ ↦ Var[X (n + 1); P])) {n : ℕ} (hn : 0 < n) :
    Var[centered_average P (fun k ↦ X (k + 1)) n; P] ≤
      sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) / (n : ℝ) := by
  let Y : Fin n → Ω → ℝ := fun i ω ↦ X (i.1 + 1) ω - P[X (i.1 + 1)]
  have hY_memLp : ∀ i, MemLp (Y i) 2 P := by
    intro i
    exact (h_memLp i.1).sub (memLp_const _)
  have hY_uncorr : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0 := by
    -- Route correction: the variance theorem works on a `Fin n` family, so we translate the
    -- sequence hypotheses to that finite centered family before applying it.
    simpa [Y] using pairwise_cov_centered_family_eq_zero P X h_memLp h_uncorr
  have hsum_var' :
      Var[∑ i, Y i; P] = ∑ i, Var[Y i; P] := by
    simpa using variance_sum_eq_sum_variance_of_pairwise_uncorrelated hY_memLp hY_uncorr
  have hsum_fun : (fun ω ↦ ∑ i, Y i ω) = ∑ i, Y i := by
    ext ω
    simp
  have hsum_var :
      Var[fun ω ↦ ∑ i, Y i ω; P] = ∑ i, Var[Y i; P] := by
    simpa [hsum_fun] using hsum_var'
  have h_average_eq :
      centered_average P (fun k ↦ X (k + 1)) n = fun ω ↦ (1 / (n : ℝ)) * ∑ i, Y i ω := by
    simpa [Y] using centered_average_eq_fin_sum P X n
  have hvar_le :
      ∀ i : Fin n, Var[Y i; P] ≤ sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) := by
    intro i
    rw [show Var[Y i; P] = Var[X (i.1 + 1); P] by
      simp [Y, variance_sub_const (h_memLp i.1).aestronglyMeasurable]]
    exact le_csSup h_var_bdd (Set.mem_range_self _)
  have hsum_le :
      ∑ i, Var[Y i; P] ≤ n * sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) := by
    simpa [Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_card_nsmul Finset.univ (fun i : Fin n ↦ Var[Y i; P])
        (sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P])) (fun i _ ↦ hvar_le i)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    Var[centered_average P (fun k ↦ X (k + 1)) n; P]
        = Var[fun ω ↦ (1 / (n : ℝ)) * ∑ i, Y i ω; P] := by
          rw [h_average_eq]
    _ = (1 / (n : ℝ)) ^ 2 * Var[fun ω ↦ ∑ i, Y i ω; P] := by
          rw [variance_const_mul]
    _ = (1 / (n : ℝ)) ^ 2 * ∑ i, Var[Y i; P] := by
          rw [hsum_var]
    _ ≤ (1 / (n : ℝ)) ^ 2 * (n * sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P])) := by
          gcongr
    _ = sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) / (n : ℝ) := by
          field_simp [hnR]

-- Proof sketch: apply the pairwise-uncorrelated finite-sum variance formula to the centered family
-- `fun k ↦ X (k + 1) - P[X (k + 1)]`, use `Var[c • Y; P] = c^2 Var[Y; P]` for the normalized
-- average, bound the resulting variance sum by the supremum of the variance set, and conclude with
-- Chebyshev's inequality.
/-- Theorem 5.14: if the real random variables `X₁, X₂, …` are pairwise uncorrelated in
`ℒ²(P)` and have uniformly bounded variances, then every centered empirical average from
Definition 5.12 satisfies the quantitative weak-law bound
`P[|(1 / n) * ∑_{i=1}^n (Xᵢ - 𝔼[Xᵢ])| ≥ ε] ≤ V / (ε² n)` with
`V = sup_n Var[X_n; P]`. The theorem is stated directly with the chapter's canonical
`centered_average` API for the `0`-based Lean sequence `fun k ↦ X (k + 1)`. -/
theorem weak_law_of_large_numbers_of_pairwise_uncorrelated_bounded_variance
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (h_memLp : ∀ n, MemLp (X (n + 1)) 2 P)
    (h_uncorr : Pairwise fun i j ↦ cov[X (i + 1), X (j + 1); P] = 0)
    (h_var_bdd : BddAbove (Set.range fun n : ℕ ↦ Var[X (n + 1); P])) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 0 < n) :
    P {ω | ε ≤ |centered_average P (fun k ↦ X (k + 1)) n ω|} ≤
      ENNReal.ofReal
        (sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) / (ε ^ 2 * (n : ℝ))) := by
  let Y : Fin n → Ω → ℝ := fun i ω ↦ X (i.1 + 1) ω - P[X (i.1 + 1)]
  have hY_memLp : ∀ i, MemLp (Y i) 2 P := by
    intro i
    exact (h_memLp i.1).sub (memLp_const _)
  have h_average_eq :
      centered_average P (fun k ↦ X (k + 1)) n = fun ω ↦ (1 / (n : ℝ)) * ∑ i, Y i ω := by
    simpa [Y] using centered_average_eq_fin_sum P X n
  have h_average_memLp : MemLp (centered_average P (fun k ↦ X (k + 1)) n) 2 P := by
    -- Square-integrability is preserved under centering, finite summation, and scaling.
    have hsum_memLp : MemLp (∑ i, Y i) 2 P := by
      exact memLp_finset_sum' Finset.univ (fun i _ ↦ hY_memLp i)
    rw [h_average_eq]
    simpa using hsum_memLp.const_mul (1 / (n : ℝ))
  have hmean_zero : P[centered_average P (fun k ↦ X (k + 1)) n] = 0 :=
    integral_centered_average_eq_zero P X h_memLp n
  have hchebyshev :
      P {ω | ε ≤ |centered_average P (fun k ↦ X (k + 1)) n ω - P[centered_average P
        (fun k ↦ X (k + 1)) n]|} ≤
        ENNReal.ofReal (Var[centered_average P (fun k ↦ X (k + 1)) n; P] / ε ^ 2) := by
    simpa using meas_ge_le_variance_div_sq h_average_memLp hε
  have hvariance :
      Var[centered_average P (fun k ↦ X (k + 1)) n; P] ≤
        sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) / (n : ℝ) :=
    variance_centered_average_le_sSup_div P X h_memLp h_uncorr h_var_bdd hn
  have hset :
      {ω | ε ≤ |centered_average P (fun k ↦ X (k + 1)) n ω|} =
        {ω | ε ≤
          |centered_average P (fun k ↦ X (k + 1)) n ω -
            P[centered_average P (fun k ↦ X (k + 1)) n]|} := by
    -- The centered empirical average already has expectation `0`, so Chebyshev applies directly.
    ext ω
    simp [hmean_zero]
  calc
    P {ω | ε ≤ |centered_average P (fun k ↦ X (k + 1)) n ω|}
        = P {ω | ε ≤
            |centered_average P (fun k ↦ X (k + 1)) n ω -
              P[centered_average P (fun k ↦ X (k + 1)) n]|} := by
            rw [hset]
    _ ≤ ENNReal.ofReal (Var[centered_average P (fun k ↦ X (k + 1)) n; P] / ε ^ 2) := hchebyshev
    _ ≤ ENNReal.ofReal
          ((sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) / (n : ℝ)) / ε ^ 2) := by
            exact ENNReal.ofReal_le_ofReal <|
              div_le_div_of_nonneg_right hvariance (sq_nonneg ε)
    _ = ENNReal.ofReal
          (sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) / (ε ^ 2 * (n : ℝ))) := by
            congr 1
            field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne', hε.ne']

-- Proof sketch: combine the quantitative estimate above for each `ε > 0` with the fact that
-- `V / (ε^2 n) → 0` as `n → ∞`, and use `MemLp` to obtain the integrability required in
-- Definition 5.12.
/-- Theorem 5.14 in the chapter's canonical weak-law language: under the same hypotheses, the
`0`-based Lean sequence `fun n ↦ X (n + 1)` satisfies
`satisfies_weak_law_of_large_numbers`. -/
theorem satisfies_weak_law_of_large_numbers_of_pairwise_uncorrelated_bounded_variance
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (h_memLp : ∀ n, MemLp (X (n + 1)) 2 P)
    (h_uncorr : Pairwise fun i j ↦ cov[X (i + 1), X (j + 1); P] = 0)
    (h_var_bdd : BddAbove (Set.range fun n : ℕ ↦ Var[X (n + 1); P])) :
    satisfies_weak_law_of_large_numbers P (fun n ↦ X (n + 1)) := by
  refine ⟨fun n ↦ (h_memLp n).integrable (by simp), ?_⟩
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hshift_bound :
      ∀ n,
        P {ω | ε ≤ ‖centered_average P (fun k ↦ X (k + 1)) (n + 1) ω - (0 : ℝ)‖} ≤
        ENNReal.ofReal
          (sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) / (ε ^ 2 * ((n + 1 : ℕ) : ℝ))) := by
    intro n
    -- Route correction: apply the quantitative estimate at `n + 1` so the denominator is positive.
    simpa [Real.norm_eq_abs] using
      weak_law_of_large_numbers_of_pairwise_uncorrelated_bounded_variance
        P X h_memLp h_uncorr h_var_bdd hε (Nat.succ_pos n)
  have hbound_tendsto_real :
      Tendsto
        (fun n : ℕ ↦
          sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) / (ε ^ 2 * ((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    let C : ℝ := sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) / ε ^ 2
    have hbase :
        Tendsto (fun n : ℕ ↦ C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C
    have hbase_shift :
        Tendsto (fun n : ℕ ↦ C / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).2 hbase
    convert hbase_shift using 1
    ext n
    dsimp [C]
    have hnR : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hnR, hε.ne']
  have hbound_tendsto :
      Tendsto
        (fun n : ℕ ↦
          ENNReal.ofReal
            (sSup (Set.range fun k : ℕ ↦ Var[X (k + 1); P]) / (ε ^ 2 * ((n + 1 : ℕ) : ℝ))))
        atTop (𝓝 0) :=
    by simpa using ENNReal.tendsto_ofReal hbound_tendsto_real
  have hshift_tendsto :
      Tendsto
        (fun n ↦ P {ω | ε ≤ ‖centered_average P (fun k ↦ X (k + 1)) (n + 1) ω - (0 : ℝ)‖})
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound_tendsto
      (Eventually.of_forall fun n ↦ by simp)
      (Eventually.of_forall hshift_bound)
  exact (tendsto_add_atTop_iff_nat 1).1 hshift_tendsto
