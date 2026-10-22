/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- Helper for Theorem 5.30: normalize the `N₀`-tail of the sequence `X` by the weights `a`. -/
private def normalizedTail (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ) : ℕ → Ω → ℝ :=
  fun n ω ↦ ((a (n + N0) : ℝ)⁻¹) * X (n + N0) ω

/-- Helper for Theorem 5.30: a `NNReal` sequence tending to `∞` is eventually strictly positive. -/
private lemma eventually_pos_of_tendsto_atTop_nnreal
    (a : ℕ → NNReal) (ha_tendsto : Tendsto a atTop atTop) :
    ∃ N0, ∀ n ≥ N0, 0 < a n := by
  -- Proof comment: since `a n → ∞`, the tail eventually dominates `1`, hence it is positive.
  have h_tail : ∀ᶠ n in atTop, (1 : NNReal) ≤ a n := (tendsto_atTop.1 ha_tendsto) 1
  rcases Filter.mem_atTop_sets.1 h_tail with ⟨N0, hN0⟩
  refine ⟨N0, fun n hn ↦ ?_⟩
  exact zero_lt_one.trans_le (hN0 n hn)

/-- Helper for Theorem 5.30: the normalized tail remains square-integrable termwise. -/
private lemma normalizedTail_memLp
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ)
    (hX_memLp : ∀ n, MemLp (X n) 2 P) :
    ∀ n, MemLp (normalizedTail X a N0 n) 2 P := by
  intro n
  -- Proof comment: multiplying an `L²` random variable by a scalar preserves membership in `L²`.
  simpa [normalizedTail] using (hX_memLp (n + N0)).const_mul (((a (n + N0) : ℝ)⁻¹))

/-- Helper for Theorem 5.30: centering is preserved by the tail normalization. -/
private lemma normalizedTail_mean_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ)
    (hX_centered : ∀ n, P[X n] = 0) :
    ∀ n, P[normalizedTail X a N0 n] = 0 := by
  intro n
  -- Proof comment: expectation is linear, so the scalar normalization factors out immediately.
  change P[fun ω ↦ ((a (n + N0) : ℝ)⁻¹) * X (n + N0) ω] = 0
  rw [integral_const_mul, hX_centered]
  simp

/-- Helper for Theorem 5.30: covariance of two normalized tail terms is the rescaled covariance of
the original tail terms. -/
private lemma normalizedTail_covariance_eq
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 i j : ℕ) :
    cov[normalizedTail X a N0 i, normalizedTail X a N0 j; P] =
      ((((a (i + N0) : ℝ)⁻¹) * ((a (j + N0) : ℝ)⁻¹)) *
        cov[X (i + N0), X (j + N0); P]) := by
  -- Proof comment: pull the two deterministic normalization factors through covariance.
  change cov[fun ω ↦ ((a (i + N0) : ℝ)⁻¹) * X (i + N0) ω,
      fun ω ↦ ((a (j + N0) : ℝ)⁻¹) * X (j + N0) ω; P] = _
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- Helper for Theorem 5.30: pairwise uncorrelatedness is preserved by the tail normalization. -/
private lemma normalizedTail_pairwise_uncorrelated
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0) :
    Pairwise fun i j ↦ cov[normalizedTail X a N0 i, normalizedTail X a N0 j; P] = 0 := by
  intro i j hij
  have hij_shift : i + N0 ≠ j + N0 := by
    exact fun hEq ↦ hij (Nat.add_right_cancel hEq)
  -- Proof comment: after shifting indices, the original covariance hypothesis still applies.
  rw [normalizedTail_covariance_eq]
  simp [hX_uncorrelated hij_shift]

/-- Bridge from the chapter's sequential `partialSum` to the owner `Fin n` finite-sum API. -/
private lemma partialSum_eq_sum_univ {α : Type u} [MeasurableSpace α] (X : ℕ → α → ℝ) (n : ℕ) :
    partialSum X n = ∑ i : Fin n, X i := by
  ext ω
  simpa [partialSum] using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) n).symm

/-- Helper for Theorem 5.30: the variance of a normalized tail term rescales quadratically. -/
private lemma normalizedTail_variance_eq
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 n : ℕ) :
    Var[normalizedTail X a N0 n; P] =
      (((a (n + N0) : ℝ) ^ (2 : ℕ))⁻¹) * Var[X (n + N0); P] := by
  -- Proof comment: variance is homogeneous of degree two under scalar multiplication.
  change Var[fun ω ↦ ((a (n + N0) : ℝ)⁻¹) * X (n + N0) ω; P] = _
  rw [ProbabilityTheory.variance_const_mul]
  simp [inv_pow]

/-- Helper for Theorem 5.30: the variance of a finite normalized-tail partial sum is the sum of
the term variances. -/
private lemma normalizedTail_partialSum_variance_eq_sum
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 n : ℕ)
    (hX_memLp : ∀ k, MemLp (X k) 2 P)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0) :
    Var[partialSum (normalizedTail X a N0) n; P] =
      ∑ i ∈ Finset.range n, Var[normalizedTail X a N0 i; P] := by
  let Y : Fin n → Ω → ℝ := fun i ↦ normalizedTail X a N0 i
  have hY_memLp : ∀ i, MemLp (Y i) 2 P := by
    intro i
    simpa [Y] using normalizedTail_memLp P X a N0 hX_memLp i
  have hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0 := by
    intro i j hij
    have hval : (i : ℕ) ≠ j := by
      intro hEq
      exact hij (Fin.ext hEq)
    simpa [Y] using normalizedTail_pairwise_uncorrelated P X a N0 hX_uncorrelated hval
  calc
    Var[partialSum (normalizedTail X a N0) n; P]
      = Var[∑ i, Y i; P] := by
          rw [partialSum_eq_sum_univ (normalizedTail X a N0) n]
    _ = ∑ i, Var[Y i; P] := by
          simpa using variance_sum_eq_sum_variance_of_pairwise_uncorrelated hY_memLp hY_uncorrelated
    _ = ∑ i ∈ Finset.range n, Var[normalizedTail X a N0 i; P] := by
          simpa [Y] using
            (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ Var[normalizedTail X a N0 i; P]) n)

/-- Helper for Theorem 5.30: the variance of a finite normalized-tail partial sum is the shifted
logarithmically weighted variance prefix from the hypothesis. -/
private lemma normalizedTail_partialSum_variance_eq_weighted_sum
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 n : ℕ)
    (hX_memLp : ∀ k, MemLp (X k) 2 P)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0) :
    Var[partialSum (normalizedTail X a N0) n; P] =
      ∑ i ∈ Finset.range n,
        ((((a (i + N0) : ℝ) ^ (2 : ℕ))⁻¹) * Var[X (i + N0); P]) := by
  -- Proof comment: combine orthogonal additivity of variance with the quadratic rescaling formula.
  rw [normalizedTail_partialSum_variance_eq_sum P X a N0 n hX_memLp hX_uncorrelated]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact normalizedTail_variance_eq P X a N0 i

/-- Helper for Theorem 5.30: after shifting by `N₀`, the logarithmically weighted variance series
for the normalized tail is still summable. -/
private lemma normalizedTail_weighted_variance_summable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ)
    (hseries :
      Summable (fun n : ℕ ↦
        ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹) * Var[X n; P])) :
    Summable (fun n : ℕ ↦ ((Real.log (n + N0 + 1)) ^ 2) * Var[normalizedTail X a N0 n; P]) := by
  -- Proof comment: shift the original series by `N₀`, then rewrite the normalized-tail variances.
  have hshift :
      Summable (fun n : ℕ ↦
        ((Real.log (n + N0 + 1)) ^ 2) *
          (((a (n + N0) : ℝ) ^ (2 : ℕ))⁻¹) * Var[X (n + N0); P]) := by
    simpa [add_assoc] using
      ((summable_nat_add_iff N0).2 hseries)
  simpa [normalizedTail_variance_eq, mul_assoc] using hshift

/-- Helper for Theorem 5.30: multiplying the normalized tail by the tail weights recovers the
corresponding tail increment of the original partial sums. -/
private lemma weighted_normalizedTail_partialSum_eq_tail_increment
    (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 n : ℕ) (ω : Ω)
    (hN0_pos : ∀ k, 0 < a (k + N0)) :
    ∑ i ∈ Finset.range n, (a (i + N0) : ℝ) * normalizedTail X a N0 i ω =
      partialSum X (n + N0) ω - partialSum X N0 ω := by
  -- Proof comment: positivity on the tail lets the weight cancel the normalization factor
  -- termwise, and the remaining shifted sum is exactly the tail increment.
  calc
    ∑ i ∈ Finset.range n, (a (i + N0) : ℝ) * normalizedTail X a N0 i ω
      = ∑ i ∈ Finset.range n, X (i + N0) ω := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hne : (a (i + N0) : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt (hN0_pos i))
          rw [normalizedTail, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = ∑ i ∈ Finset.range n, X (N0 + i) ω := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Nat.add_comm]
    _ = ∑ i ∈ Finset.Ico N0 (n + N0), X i ω := by
          symm
          simpa using (Finset.sum_Ico_eq_sum_range (fun i : ℕ ↦ X i ω) N0 (n + N0))
    _ = partialSum X (n + N0) ω - partialSum X N0 ω := by
          symm
          exact partialSum_sub_eq_sum_Ico X (Nat.le_add_left _ _) ω

/-- Helper for Theorem 5.30: discrete summation by parts for a weighted finite difference sum. -/
private lemma weightedSumByParts_eq
    (b u : ℕ → ℝ) :
    ∀ n,
      ∑ i ∈ Finset.range n, b i * (u i - u (i + 1)) =
        b 0 * u 0 + ∑ i ∈ Finset.Icc 1 (n - 1), (b i - b (i - 1)) * u i - b (n - 1) * u n
  | 0 => by
      -- Proof comment: the empty weighted sum matches the degenerate boundary expression.
      simp
  | n + 1 => by
      -- Proof comment: split off the final term and reinsert it into the boundary sum.
      calc
        ∑ i ∈ Finset.range (n + 1), b i * (u i - u (i + 1))
          = (∑ i ∈ Finset.range n, b i * (u i - u (i + 1))) + b n * (u n - u (n + 1)) := by
              rw [Finset.sum_range_succ]
        _ = b 0 * u 0 + ∑ i ∈ Finset.Icc 1 (n - 1), (b i - b (i - 1)) * u i
              - b (n - 1) * u n + b n * (u n - u (n + 1)) := by
              rw [weightedSumByParts_eq b u n]
        _ = b 0 * u 0 + ∑ i ∈ Finset.Icc 1 n, (b i - b (i - 1)) * u i - b n * u (n + 1) := by
              by_cases hn : n = 0
              · subst hn
                ring
              · have hsplit : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
                  ext i
                  simp [Finset.mem_insert, Finset.mem_Icc]
                  omega
                rw [hsplit, Finset.sum_insert]
                · ring
                · simp [Nat.pos_iff_ne_zero.mpr hn]

/-- Helper for Theorem 5.30: adjacent differences telescope across a finite interval. -/
private lemma sum_Icc_adjacent_sub
    (b : ℕ → ℝ) (K m : ℕ) :
    ∑ i ∈ Finset.Icc (K + 1) (K + m), (b i - b (i - 1)) = b (K + m) - b K := by
  induction m with
  | zero =>
      -- Proof comment: the interval is empty, so the telescoping sum vanishes.
      simp
  | succ m ih =>
      -- Proof comment: append the top endpoint and collapse the new adjacent difference.
      rw [show K + (m + 1) = K + m + 1 by omega]
      rw [Finset.sum_Icc_succ_top (show K + 1 ≤ K + m + 1 by omega), ih]
      have hpred : K + m + 1 - 1 = K + m := by omega
      rw [hpred]
      ring

/-- Helper for Theorem 5.30: Kronecker's lemma turns convergence of the normalized-tail series into
vanishing weighted averages against an increasing divergent weight sequence. -/
private lemma weightedPartialSumDiv_tendstoZero_of_monotone
    (b : ℕ → NNReal) (hb_mono : Monotone b) (hb_tendsto : Tendsto b atTop atTop)
    (y : ℕ → ℝ) {l : ℝ}
    (hy_tendsto : Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, y i) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ ↦ ((b n : ℝ)⁻¹) * ∑ i ∈ Finset.range n, (b i : ℝ) * y i) atTop (𝓝 0) := by
  let s : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range n, y i
  let u : ℕ → ℝ := fun n ↦ l - s n
  have hu_tendsto : Tendsto u atTop (𝓝 0) := by
    -- Proof comment: the remainder sequence is exactly the limit minus the convergent partial sum.
    have hconst : Tendsto (fun _ : ℕ ↦ l) atTop (𝓝 l) := tendsto_const_nhds
    simpa [u, s] using hconst.sub hy_tendsto
  have hb_real_tendsto : Tendsto (fun n : ℕ ↦ (b n : ℝ)) atTop atTop := by
    -- Proof comment: pass from the `NNReal` weights to their real-valued coercions once.
    exact (NNReal.tendsto_coe_atTop).2 hb_tendsto
  have hy_eq : ∀ i, y i = u i - u (i + 1) := by
    intro i
    -- Proof comment: the remainder differences recover the original summands by telescoping the
    -- partial sums.
    dsimp [u, s]
    rw [Finset.sum_range_succ]
    ring
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨K0, hK0⟩ := (Metric.tendsto_atTop.1 hu_tendsto) (ε / 4) (by positivity)
  let K : ℕ := max K0 1
  let head : ℝ :=
    (b 0 : ℝ) * u 0 + ∑ i ∈ Finset.Icc 1 K, ((b i : ℝ) - b (i - 1)) * u i
  have hlarge_event : ∀ᶠ n in atTop, max 1 (4 * |head| / ε) ≤ (b n : ℝ) :=
    (tendsto_atTop.1 hb_real_tendsto) (max 1 (4 * |head| / ε))
  rcases Filter.mem_atTop_sets.1 hlarge_event with ⟨N0, hN0⟩
  refine ⟨max (K + 1) N0, fun n hn ↦ ?_⟩
  have hnK : K + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnN0 : N0 ≤ n := le_trans (le_max_right _ _) hn
  have hb_large : max 1 (4 * |head| / ε) ≤ (b n : ℝ) := hN0 n hnN0
  have hb_pos : 0 < (b n : ℝ) := by
    have h_one : (1 : ℝ) ≤ (b n : ℝ) := le_trans (le_max_left _ _) hb_large
    linarith
  have hu_small : ∀ i ≥ K, |u i| < ε / 4 := by
    intro i hi
    simpa [Real.dist_eq] using hK0 i (le_trans (le_max_left _ _) hi)
  have hsplit :
      ∑ i ∈ Finset.Icc 1 (n - 1), ((b i : ℝ) - b (i - 1)) * u i =
        ∑ i ∈ Finset.Icc 1 K, ((b i : ℝ) - b (i - 1)) * u i +
          ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i := by
    have hEq :
        Finset.Icc 1 (n - 1) = Finset.Icc 1 K ∪ Finset.Icc (K + 1) (n - 1) := by
      ext i
      simp [Finset.mem_union, Finset.mem_Icc]
      omega
    rw [hEq, Finset.sum_union]
    · refine Finset.disjoint_left.2 ?_
      intro i hi1 hi2
      simp at hi1 hi2
      omega
  have hdecomp :
      ∑ i ∈ Finset.range n, (b i : ℝ) * y i =
        head + ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i -
          (b (n - 1) : ℝ) * u n := by
    -- Proof comment: the summation-by-parts identity isolates a fixed head, a small tail, and the
    -- final boundary remainder.
    have hsummand :
        ∑ i ∈ Finset.range n, (b i : ℝ) * y i =
          ∑ i ∈ Finset.range n, (b i : ℝ) * (u i - u (i + 1)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hy_eq i]
    calc
      ∑ i ∈ Finset.range n, (b i : ℝ) * y i =
          ∑ i ∈ Finset.range n, (b i : ℝ) * (u i - u (i + 1)) := hsummand
      _ =
          (b 0 : ℝ) * u 0 +
            ∑ i ∈ Finset.Icc 1 (n - 1), ((b i : ℝ) - b (i - 1)) * u i -
              (b (n - 1) : ℝ) * u n := by
            rw [weightedSumByParts_eq (fun k ↦ (b k : ℝ)) u n]
      _ = head + ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i -
            (b (n - 1) : ℝ) * u n := by
            rw [hsplit]
            dsimp [head]
            ring
  have hhead_div : |head| / (b n : ℝ) ≤ ε / 4 := by
    have hbound : 4 * |head| / ε ≤ (b n : ℝ) := le_trans (le_max_right _ _) hb_large
    have hmul : 4 * |head| ≤ ε * (b n : ℝ) := by
      simpa [mul_comm] using (div_le_iff₀ hε).1 hbound
    exact (div_le_iff₀ hb_pos).2 <| by nlinarith
  have hcoeff_nonneg :
      ∀ i ∈ Finset.Icc (K + 1) (n - 1), 0 ≤ ((b i : ℝ) - b (i - 1)) := by
    intro i hi
    have hleNN : b (i - 1) ≤ b i := hb_mono (Nat.sub_le i 1)
    exact sub_nonneg.mpr (by exact_mod_cast hleNN)
  have htail_telescopes :
      ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) =
        (b (n - 1) : ℝ) - b K := by
    have haux := sum_Icc_adjacent_sub (fun k ↦ (b k : ℝ)) K (n - (K + 1))
    have htop : K + (n - (K + 1)) = n - 1 := by omega
    simpa [htop] using haux
  have htail_div :
      |∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| / (b n : ℝ) ≤ ε / 4 := by
    have htail_abs :
        |∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| ≤
          ((∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1))) * (ε / 4)) := by
      calc
        |∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| ≤
            ∑ i ∈ Finset.Icc (K + 1) (n - 1), |((b i : ℝ) - b (i - 1)) * u i| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.Icc (K + 1) (n - 1), (((b i : ℝ) - b (i - 1)) * (ε / 4)) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hi_geK : K ≤ i := le_trans (Nat.le_succ K) (Finset.mem_Icc.mp hi).1
              have hu_i : |u i| ≤ ε / 4 := le_of_lt (hu_small i hi_geK)
              rw [abs_mul, abs_of_nonneg (hcoeff_nonneg i hi)]
              exact mul_le_mul_of_nonneg_left hu_i (hcoeff_nonneg i hi)
        _ = (∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1))) * (ε / 4) := by
              simpa using
                (Finset.sum_mul (Finset.Icc (K + 1) (n - 1))
                  (fun i ↦ ((b i : ℝ) - b (i - 1))) (ε / 4)).symm
    have hpred_le : (b (n - 1) : ℝ) ≤ (b n : ℝ) := by
      exact_mod_cast hb_mono (Nat.sub_le n 1)
    have hK_nonneg : 0 ≤ (b K : ℝ) := by positivity
    have htail_mul :
        |∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| ≤
          (ε / 4) * (b n : ℝ) := by
      calc
        |∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| ≤
            ((∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1))) * (ε / 4)) := htail_abs
        _ = (((b (n - 1) : ℝ) - b K) * (ε / 4)) := by rw [htail_telescopes]
        _ ≤ (ε / 4) * (b n : ℝ) := by
            have hdiff_le : ((b (n - 1) : ℝ) - b K) ≤ (b n : ℝ) := by
              nlinarith
            nlinarith
    exact (div_le_iff₀ hb_pos).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using htail_mul
  have hboundary_div : |(b (n - 1) : ℝ) * u n| / (b n : ℝ) ≤ ε / 4 := by
    have hpred_le : (b (n - 1) : ℝ) ≤ (b n : ℝ) := by
      exact_mod_cast hb_mono (Nat.sub_le n 1)
    have hu_n : |u n| ≤ ε / 4 := le_of_lt (hu_small n (by omega))
    have hmul :
        |(b (n - 1) : ℝ) * u n| ≤ (ε / 4) * (b n : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      nlinarith
    exact (div_le_iff₀ hb_pos).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have htriangle :
      |head + ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i -
          (b (n - 1) : ℝ) * u n| ≤
        |head| +
          |∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| +
            |(b (n - 1) : ℝ) * u n| := by
    have h1 :
        |head + ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i -
            (b (n - 1) : ℝ) * u n| ≤
          |head + ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| +
            |(b (n - 1) : ℝ) * u n| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le
          (head + ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i)
          (-(b (n - 1) : ℝ) * u n)
    have h2 :
        |head + ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| ≤
          |head| +
            |∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| := by
      exact abs_add_le _ _
    linarith
  have hnum_div :
      |head + ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i -
          (b (n - 1) : ℝ) * u n| / (b n : ℝ) < ε := by
    have hhead_mul : |head| ≤ (ε / 4) * (b n : ℝ) := (div_le_iff₀ hb_pos).1 hhead_div
    have htail_mul :
        |∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| ≤
          (ε / 4) * (b n : ℝ) := (div_le_iff₀ hb_pos).1 htail_div
    have hboundary_mul : |(b (n - 1) : ℝ) * u n| ≤ (ε / 4) * (b n : ℝ) :=
      (div_le_iff₀ hb_pos).1 hboundary_div
    have hle :
        |head + ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i -
            (b (n - 1) : ℝ) * u n| / (b n : ℝ) ≤ 3 * ε / 4 := by
      apply (div_le_iff₀ hb_pos).2
      calc
        |head + ∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i -
            (b (n - 1) : ℝ) * u n| ≤
              |head| +
                |∑ i ∈ Finset.Icc (K + 1) (n - 1), ((b i : ℝ) - b (i - 1)) * u i| +
                  |(b (n - 1) : ℝ) * u n| := htriangle
        _ ≤ (ε / 4) * (b n : ℝ) + (ε / 4) * (b n : ℝ) + (ε / 4) * (b n : ℝ) := by
              nlinarith
        _ = (3 * ε / 4) * (b n : ℝ) := by ring
    have hlt : 3 * ε / 4 < ε := by nlinarith
    exact lt_of_le_of_lt hle hlt
  have habs_eq :
      |((b n : ℝ)⁻¹) * ∑ i ∈ Finset.range n, (b i : ℝ) * y i| =
        |∑ i ∈ Finset.range n, (b i : ℝ) * y i| / (b n : ℝ) := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hb_pos), div_eq_mul_inv, mul_comm]
  have habs_lt : |((b n : ℝ)⁻¹) * ∑ i ∈ Finset.range n, (b i : ℝ) * y i| < ε := by
    rw [habs_eq]
    simpa [hdecomp] using hnum_div
  simpa [Real.dist_eq] using habs_lt

/-- Helper for Theorem 5.30: dyadic powers turn logarithms into linear factors in the block
index. -/
private lemma dyadicLog_pow_eq
    (m : ℕ) :
    Real.log ((2 ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log 2 := by
  -- Proof comment: cast the dyadic natural power to `ℝ` and apply `Real.log_pow`.
  rw [Nat.cast_pow]
  exact Real.log_pow (2 : ℝ) m

/-- Helper for Theorem 5.30: summing over the first `N` dyadic blocks is the same as summing over
the prefix from `1` through `2 ^ N - 1`. -/
private lemma sum_dyadicBlocks_eq_sum_Icc
    (f : ℕ → ℝ) :
    ∀ N,
      ∑ m ∈ Finset.range N, ∑ i ∈ Finset.Icc (2 ^ m) (2 ^ (m + 1) - 1), f i =
        ∑ i ∈ Finset.Icc 1 (2 ^ N - 1), f i
  | 0 => by
      -- Proof comment: the empty family of dyadic blocks matches the empty prefix interval.
      simp
  | N + 1 => by
      -- Proof comment: append the next dyadic block and merge the two consecutive `Ico` intervals.
      rw [Finset.sum_range_succ, sum_dyadicBlocks_eq_sum_Icc f N]
      have hleft : Finset.Icc 1 (2 ^ N - 1) = Finset.Ico 1 (2 ^ N) := by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_Icc.mp hi with ⟨hlo, hhi⟩
          exact Finset.mem_Ico.mpr ⟨hlo, by omega⟩
        · intro hi
          rcases Finset.mem_Ico.mp hi with ⟨hlo, hhi⟩
          exact Finset.mem_Icc.mpr ⟨hlo, by omega⟩
      have hblock : Finset.Icc (2 ^ N) (2 ^ (N + 1) - 1) = Finset.Ico (2 ^ N) (2 ^ (N + 1)) := by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_Icc.mp hi with ⟨hlo, hhi⟩
          have hpos : 0 < 2 ^ (N + 1) := by
            exact pow_pos (by norm_num) _
          have htop : 2 ^ (N + 1) - 1 + 1 = 2 ^ (N + 1) := by
            exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))
          exact Finset.mem_Ico.mpr ⟨hlo, by
            have : i + 1 ≤ 2 ^ (N + 1) := by simpa [htop] using Nat.succ_le_succ hhi
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) this⟩
        · intro hi
          rcases Finset.mem_Ico.mp hi with ⟨hlo, hhi⟩
          exact Finset.mem_Icc.mpr ⟨hlo, Nat.le_pred_of_lt hhi⟩
      have hright : Finset.Icc 1 (2 ^ (N + 1) - 1) = Finset.Ico 1 (2 ^ (N + 1)) := by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_Icc.mp hi with ⟨hlo, hhi⟩
          exact Finset.mem_Ico.mpr ⟨hlo, by omega⟩
        · intro hi
          rcases Finset.mem_Ico.mp hi with ⟨hlo, hhi⟩
          exact Finset.mem_Icc.mpr ⟨hlo, by omega⟩
      rw [hleft, hblock, hright]
      simpa using
        (Finset.sum_Ico_consecutive (fun i ↦ f i)
          (show 1 ≤ 2 ^ N by exact Nat.one_le_two_pow)
          (show 2 ^ N ≤ 2 ^ (N + 1) by
            have hpow : 2 ^ N ≤ 2 ^ N * 2 := Nat.le_mul_of_pos_right (2 ^ N) (by norm_num)
            change 2 ^ N ≤ 2 ^ N * 2
            exact hpow))

/-- Helper for Theorem 5.30: grouping a nonnegative summable series into dyadic blocks preserves
summability. -/
private lemma summable_dyadicBlockSums_of_summable_nonneg
    {f : ℕ → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
    Summable (fun m : ℕ ↦ ∑ i ∈ Finset.Icc (2 ^ m) (2 ^ (m + 1) - 1), f i) := by
  have hblock_nonneg :
      ∀ m, 0 ≤ ∑ i ∈ Finset.Icc (2 ^ m) (2 ^ (m + 1) - 1), f i := by
    intro m
    -- Proof comment: each dyadic block sum is nonnegative because every term of `f` is.
    exact Finset.sum_nonneg fun i hi ↦ hf_nonneg i
  have hblock_bound :
      ∀ N,
        ∑ m ∈ Finset.range N, ∑ i ∈ Finset.Icc (2 ^ m) (2 ^ (m + 1) - 1), f i ≤ ∑' n, f n := by
    intro N
    -- Proof comment: regrouping the first `N` dyadic blocks gives a prefix of the original
    -- nonnegative summable series, so its value is bounded by the total sum.
    rw [sum_dyadicBlocks_eq_sum_Icc f N]
    exact hf.sum_le_tsum _ fun i hi ↦ hf_nonneg i
  exact summable_of_sum_range_le hblock_nonneg hblock_bound

/-- Helper for Theorem 5.30: on a shifted dyadic block, the quadratic block index is controlled by
the corresponding logarithmic weight. -/
private lemma shiftedDyadicWeight_le_logSqWeight
    (N0 m i : ℕ) (hi : 2 ^ (m + 1) ≤ i + 1) :
    ((m + 2 : ℝ) ^ 2) ≤
      (4 / (Real.log 2) ^ 2) * (Real.log (i + N0 + 1)) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num)
  have harg_pos : 0 < (i + N0 + 1 : ℝ) := by positivity
  have harg_one : 1 ≤ (i + N0 + 1 : ℝ) := by
    exact_mod_cast (show 1 ≤ i + N0 + 1 by omega)
  have hpow_le : ((2 ^ (m + 1) : ℕ) : ℝ) ≤ i + N0 + 1 := by
    exact_mod_cast (show 2 ^ (m + 1) ≤ i + N0 + 1 by omega)
  have hlog :
      ((m + 1 : ℝ) * Real.log 2) ≤ Real.log (i + N0 + 1) := by
    -- Proof comment: on the dyadic block, the logarithm is at least the dyadic scale.
    have h :=
      Real.log_le_log (show 0 < (((2 ^ (m + 1) : ℕ) : ℝ)) by positivity) hpow_le
    simpa using (show Real.log (((2 ^ (m + 1) : ℕ) : ℝ)) ≤ Real.log (i + N0 + 1) from h)
  have hlog_nonneg : 0 ≤ Real.log (i + N0 + 1) := Real.log_nonneg harg_one
  have hsquare :
      (((m + 2 : ℝ) * Real.log 2) ^ 2) ≤ (2 * Real.log (i + N0 + 1)) ^ 2 := by
    -- Proof comment: `m + 2 ≤ 2 (m + 1)` converts the dyadic index into the logarithmic weight.
    have hmul : ((m + 2 : ℝ) * Real.log 2) ≤ 2 * Real.log (i + N0 + 1) := by
      nlinarith
    have hleft_nonneg : 0 ≤ (m + 2 : ℝ) * Real.log 2 := by positivity
    have hright_nonneg : 0 ≤ 2 * Real.log (i + N0 + 1) := by positivity
    have habs :
        |(m + 2 : ℝ) * Real.log 2| ≤ |2 * Real.log (i + N0 + 1)| := by
      rwa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
    exact sq_le_sq.2 habs
  have hlog2sq : 0 < (Real.log 2) ^ 2 := by positivity
  have hdiv :
      ((m + 2 : ℝ) ^ 2) ≤ (4 * (Real.log (i + N0 + 1)) ^ 2) / (Real.log 2) ^ 2 := by
    refine (le_div_iff₀ hlog2sq).2 ?_
    nlinarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- Helper for Theorem 5.30: the shifted dyadic block variance sums inherit summability from the
shifted log-square weighted series. -/
private lemma summable_shiftedDyadicBlocks_of_shiftedLogSqSummable
    (N0 : ℕ) {v : ℕ → ℝ} (hv_nonneg : ∀ n, 0 ≤ v n)
    (hsummable : Summable (fun n : ℕ ↦ ((Real.log (n + N0 + 1)) ^ 2) * v n)) :
    Summable (fun m : ℕ ↦
      ((m + 2 : ℝ) ^ 2) * ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), v i) := by
  let c : ℝ := 4 / (Real.log 2) ^ 2
  let g : ℕ → ℝ := fun n ↦ c * ((Real.log (n + N0 + 1)) ^ 2) * v n
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    -- Proof comment: every scalar factor in the comparison series is nonnegative.
    have hlog2 : 0 < Real.log 2 := by exact Real.log_pos (by norm_num)
    have hlog_nonneg : 0 ≤ Real.log (n + N0 + 1) := by
      have harg_one : 1 ≤ (n + N0 + 1 : ℝ) := by
        exact_mod_cast (show 1 ≤ n + N0 + 1 by omega)
      exact Real.log_nonneg harg_one
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      positivity
    dsimp [g]
    exact mul_nonneg (mul_nonneg hc_nonneg (sq_nonneg _)) (hv_nonneg n)
  have hg_summable : Summable g := by
    -- Proof comment: the comparison series is just a constant multiple of the given one.
    simpa [g, c, mul_assoc, mul_left_comm, mul_comm] using hsummable.mul_left c
  have hblock_summable :
      Summable (fun m : ℕ ↦ ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), g i) := by
    -- Proof comment: regroup the nonnegative comparison series into shifted dyadic blocks.
    have hbase :
        Summable (fun m : ℕ ↦ ∑ i ∈ Finset.Icc (2 ^ m) (2 ^ (m + 1) - 1), g i) := by
      exact summable_dyadicBlockSums_of_summable_nonneg hg_nonneg hg_summable
    simpa [Nat.add_assoc] using ((summable_nat_add_iff 1).2 hbase)
  refine Summable.of_nonneg_of_le ?_ ?_ hblock_summable
  · intro m
    have hblock_nonneg :
        0 ≤ ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), v i := by
      exact Finset.sum_nonneg fun i _ ↦ hv_nonneg i
    exact mul_nonneg (sq_nonneg _) hblock_nonneg
  · intro m
    -- Proof comment: compare each dyadic block weight termwise with the logarithmic block weight.
    calc
      ((m + 2 : ℝ) ^ 2) * ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), v i
        = ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), ((m + 2 : ℝ) ^ 2) * v i := by
            rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), g i := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hi' : 2 ^ (m + 1) ≤ i + 1 := by
              exact le_trans (Finset.mem_Icc.mp hi).1 (Nat.le_succ i)
            have hweight := shiftedDyadicWeight_le_logSqWeight N0 m i hi'
            have hvi : 0 ≤ v i := hv_nonneg i
            dsimp [g, c]
            nlinarith

/-- Helper for Theorem 5.30: the normalized-tail variances have summable shifted dyadic block
weights, which is the bookkeeping input needed before the orthogonal maximal estimate. -/
private lemma normalizedTail_shiftedDyadicVarianceSummable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ)
    (hseries :
      Summable (fun n : ℕ ↦
        ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹) * Var[X n; P])) :
    Summable (fun m : ℕ ↦
      ((m + 2 : ℝ) ^ 2) *
        ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1),
          Var[normalizedTail X a N0 i; P]) := by
  -- Proof comment: this is the dyadic regrouping of the already-proved shifted log-square
  -- variance summability for the normalized tail.
  refine summable_shiftedDyadicBlocks_of_shiftedLogSqSummable N0
    (fun n ↦ variance_nonneg (normalizedTail X a N0 n) P) ?_
  exact normalizedTail_weighted_variance_summable P X a N0 hseries

/-- Helper for Theorem 5.30: the variance of a generic orthogonal partial sum is the sum of the
term variances. -/
private lemma partialSum_variance_eq_sum_of_pairwise_uncorrelated
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (n : ℕ)
    (hY_memLp : ∀ k, MemLp (Y k) 2 P)
    (hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0) :
    Var[partialSum Y n; P] =
      ∑ i ∈ Finset.range n, Var[Y i; P] := by
  let Z : Fin n → Ω → ℝ := fun i ↦ Y i
  have hZ_memLp : ∀ i, MemLp (Z i) 2 P := by
    intro i
    simpa [Z] using hY_memLp i
  have hZ_uncorrelated : Pairwise fun i j ↦ cov[Z i, Z j; P] = 0 := by
    intro i j hij
    have hval : (i : ℕ) ≠ j := by
      intro hEq
      exact hij (Fin.ext hEq)
    simpa [Z] using hY_uncorrelated hval
  calc
    Var[partialSum Y n; P]
      = Var[∑ i, Z i; P] := by
          rw [partialSum_eq_sum_univ Y n]
    _ = ∑ i, Var[Z i; P] := by
          simpa using variance_sum_eq_sum_variance_of_pairwise_uncorrelated hZ_memLp hZ_uncorrelated
    _ = ∑ i ∈ Finset.range n, Var[Y i; P] := by
          simpa [Z] using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ Var[Y i; P]) n)

/-- Helper for Theorem 5.30: square-integrable summands give square-integrable finite partial
sums. -/
private lemma partialSum_memLp_two_of_memLp_two
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P) :
    ∀ n, MemLp (partialSum Y n) 2 P := by
  intro n
  -- Proof comment: expand the chapter partial sum as a finite sum and use stability of `MemLp`
  -- under finite addition.
  simpa [partialSum] using
    (memLp_finset_sum (Finset.range n) fun i _ ↦ hY_memLp i)

/-- Helper for Theorem 5.30: centered summands give centered finite partial sums. -/
private lemma partialSum_mean_zero_of_mean_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P)
    (hY_centered : ∀ n, P[Y n] = 0) :
    ∀ n, P[partialSum Y n] = 0 := by
  intro n
  -- Proof comment: integrate the finite-sum presentation termwise and use the centeredness of
  -- each summand.
  change ∫ ω, ∑ i ∈ Finset.range n, Y i ω ∂P = 0
  rw [integral_finset_sum]
  · exact Finset.sum_eq_zero fun i _ ↦ hY_centered i
  · intro i _
    exact (hY_memLp i).integrable (by norm_num)

/-- Helper for Theorem 5.30: the increment of `partialSum Y` across the finite interval
`[start, start + len)`. -/
private def blockIncrement (Y : ℕ → Ω → ℝ) (start len : ℕ) : Ω → ℝ :=
  fun ω ↦ partialSum Y (start + len) ω - partialSum Y start ω

/-- Helper for Theorem 5.30: finite block increments inherit square-integrability from the
summands. -/
private lemma blockIncrement_memLp_two_of_memLp_two
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P) (start len : ℕ) :
    MemLp (blockIncrement Y start len) 2 P := by
  -- Proof comment: a block increment is the difference of two square-integrable partial sums.
  simpa [blockIncrement] using
    ((partialSum_memLp_two_of_memLp_two P Y hY_memLp (start + len)).sub
      (partialSum_memLp_two_of_memLp_two P Y hY_memLp start))

/-- Helper for Theorem 5.30: centered summands give centered finite block increments. -/
private lemma blockIncrement_mean_zero_of_mean_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P)
    (hY_centered : ∀ n, P[Y n] = 0) (start len : ℕ) :
    P[blockIncrement Y start len] = 0 := by
  -- Proof comment: subtract the two centered partial sums at the block endpoints.
  change P[fun ω ↦ partialSum Y (start + len) ω - partialSum Y start ω] = 0
  rw [integral_sub
    ((partialSum_memLp_two_of_memLp_two P Y hY_memLp (start + len)).integrable (by norm_num))
    ((partialSum_memLp_two_of_memLp_two P Y hY_memLp start).integrable (by norm_num))]
  rw [partialSum_mean_zero_of_mean_zero P Y hY_memLp hY_centered,
    partialSum_mean_zero_of_mean_zero P Y hY_memLp hY_centered]
  ring

/-- Helper for Theorem 5.30: the variance of a finite block increment is the sum of the term
variances over that block for pairwise-uncorrelated centered summands. -/
private lemma variance_blockIncrement_eq_sum_of_pairwise_uncorrelated
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (start len : ℕ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P)
    (hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0) :
    Var[blockIncrement Y start len; P] =
      ∑ i ∈ Finset.Ico start (start + len), Var[Y i; P] := by
  let Z : ℕ → Ω → ℝ := fun i ↦ Y (i + start)
  have hshift : blockIncrement Y start len = partialSum Z len := by
    -- Proof comment: rewrite the shifted block as a partial sum of the translated sequence.
    ext ω
    rw [blockIncrement, partialSum_sub_eq_sum_Ico Y (Nat.le_add_right start len) ω, partialSum]
    have hsum := Finset.sum_Ico_eq_sum_range (fun i : ℕ ↦ Y i ω) start (start + len)
    simpa [Z, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum
  have hZ_memLp : ∀ n, MemLp (Z n) 2 P := by
    intro n
    simpa [Z] using hY_memLp (n + start)
  have hZ_uncorrelated : Pairwise fun i j ↦ cov[Z i, Z j; P] = 0 := by
    intro i j hij
    have hshift_ne : i + start ≠ j + start := by
      exact fun hEq ↦ hij (Nat.add_right_cancel hEq)
    simpa [Z] using hY_uncorrelated hshift_ne
  calc
    Var[blockIncrement Y start len; P]
      = Var[partialSum Z len; P] := by
          rw [hshift]
    _ = ∑ i ∈ Finset.range len, Var[Z i; P] := by
          exact partialSum_variance_eq_sum_of_pairwise_uncorrelated P Z len hZ_memLp hZ_uncorrelated
    _ = ∑ i ∈ Finset.Ico start (start + len), Var[Y i; P] := by
          have hsum :=
            (Finset.sum_Ico_eq_sum_range (fun i : ℕ ↦ Var[Y i; P]) start (start + len)).symm
          simpa [Z, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum

/-- Helper for Theorem 5.30: a nonempty half-open interval of naturals is the corresponding
closed interval ending at the predecessor of the right endpoint. -/
private lemma Ico_eq_Icc_pred_of_lt {a b : ℕ} (hab : a < b) :
    Finset.Ico a b = Finset.Icc a (b - 1) := by
  -- Proof comment: membership in a nonempty half-open interval is equivalent to membership in the
  -- closed interval whose top endpoint is the predecessor of the right endpoint.
  ext i
  constructor
  · intro hi
    rcases Finset.mem_Ico.mp hi with ⟨hlo, hhi⟩
    exact Finset.mem_Icc.mpr ⟨hlo, Nat.le_pred_of_lt hhi⟩
  · intro hi
    rcases Finset.mem_Icc.mp hi with ⟨hlo, hhi⟩
    have hb_pos : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
    have htop : b - 1 + 1 = b := Nat.sub_add_cancel (Nat.succ_le_of_lt hb_pos)
    exact Finset.mem_Ico.mpr ⟨hlo, by
      have hsuc : i + 1 ≤ b := by
        simpa [htop] using Nat.succ_le_succ hhi
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hsuc⟩

/-- Helper for Theorem 5.30: summing over a consecutive family of equal-length half-open blocks
reconstructs the sum over the full concatenated interval. -/
private lemma sum_range_sum_Ico_eq_sum_Ico {β : Type*} [AddCommMonoid β]
    (f : ℕ → β) (start len blocks : ℕ) :
    ∑ q ∈ Finset.range blocks,
      ∑ i ∈ Finset.Ico (start + q * len) (start + (q + 1) * len), f i =
        ∑ i ∈ Finset.Ico start (start + blocks * len), f i := by
  induction blocks with
  | zero =>
      -- Proof comment: with no blocks, both sides are empty sums.
      simp
  | succ blocks ih =>
      -- Proof comment: append the last interval and collapse the two consecutive `Ico` sums.
      rw [Finset.sum_range_succ, ih]
      simpa [Nat.succ_mul, add_assoc, add_left_comm, add_comm] using
        (Finset.sum_Ico_consecutive f
          (show start ≤ start + blocks * len by omega)
          (show start + blocks * len ≤ start + (blocks + 1) * len by
            exact Nat.add_le_add_left
              (Nat.mul_le_mul_right len (Nat.le_succ blocks)) start))

/-- Helper for Theorem 5.30: the scale-`j` dyadic energy inside the dyadic block
`[2^(m+1), 2^(m+2))` is the sum of the squared aligned block increments of length `2^j`. -/
private def dyadicScaleEnergy (Y : ℕ → Ω → ℝ) (m j : ℕ) : Ω → ℝ :=
  fun ω ↦
    ∑ q ∈ Finset.range (2 ^ (m + 1 - j)),
      (blockIncrement Y (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j) ω) ^ 2

/-- Helper for Theorem 5.30: aggregate the dyadic energies over every scale in one ambient dyadic
block. -/
private def totalDyadicScaleEnergy (Y : ℕ → Ω → ℝ) (m : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ j ∈ Finset.range (m + 2), dyadicScaleEnergy Y m j ω

/-- Helper for Theorem 5.30: a longer block increment splits into the first piece plus the shifted
remainder block. -/
private lemma blockIncrement_add
    {α : Type u} (Y : ℕ → α → ℝ) (start len₁ len₂ : ℕ) (ω : α) :
    blockIncrement Y start (len₁ + len₂) ω =
      blockIncrement Y start len₁ ω + blockIncrement Y (start + len₁) len₂ ω := by
  -- Proof comment: expand both block increments and telescope the intermediate partial sum.
  dsimp [blockIncrement]
  ring

/-- Helper for Theorem 5.30: recursively record the dyadic pieces chosen from a descending list of
binary exponents. -/
private def pieceIncrements
    (Y : ℕ → Ω → ℝ) (ω : Ω) (start : ℕ) : List ℕ → List ℝ
  | [] => []
  | j :: L =>
      blockIncrement Y start (2 ^ j) ω :: pieceIncrements Y ω (start + 2 ^ j) L

/-- Helper for Theorem 5.30: summing the recursively chosen dyadic pieces reconstructs the full
block increment whose length is the sum of their dyadic lengths. -/
private lemma pieceIncrements_sum_eq_blockIncrement
    {α : Type u} (Y : ℕ → α → ℝ) (ω : α) :
    ∀ (L : List ℕ) (start : ℕ),
      (pieceIncrements Y ω start L).sum =
        blockIncrement Y start ((L.map fun j ↦ 2 ^ j).sum) ω
  | [], start => by
      -- Proof comment: with no dyadic pieces, both the recorded sum and the total block length
      -- are zero.
      simp [pieceIncrements, blockIncrement]
  | j :: L, start => by
      -- Proof comment: peel off the first dyadic piece and use the block-increment splitting
      -- identity on the remaining tail length.
      rw [pieceIncrements, List.map_cons, List.sum_cons, pieceIncrements_sum_eq_blockIncrement]
      simpa using (blockIncrement_add Y start (2 ^ j) ((L.map fun j ↦ 2 ^ j).sum) ω).symm

/-- Helper for Theorem 5.30: the dyadic-piece recorder stores exactly one real increment for each
input binary exponent. -/
private lemma pieceIncrements_length
    {α : Type u} (Y : ℕ → α → ℝ) (ω : α) :
    ∀ (L : List ℕ) (start : ℕ), (pieceIncrements Y ω start L).length = L.length
  | [], start => by
      -- Proof comment: the empty dyadic decomposition contributes no recorded increments.
      simp [pieceIncrements]
  | j :: L, start => by
      -- Proof comment: each recursion step adds exactly one new block increment to the recorded
      -- list.
      simp [pieceIncrements, pieceIncrements_length]

/-- Helper for Theorem 5.30: one aligned dyadic block increment contributes a single summand to
the scale-`j` energy. -/
private lemma blockIncrement_sq_le_dyadicScaleEnergy
    {α : Type u} (Y : ℕ → α → ℝ) (m j q : ℕ) (ω : α)
    (hq : q ∈ Finset.range (2 ^ (m + 1 - j))) :
    (blockIncrement Y (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j) ω) ^ 2 ≤
      dyadicScaleEnergy Y m j ω := by
  -- Proof comment: the chosen aligned block is one nonnegative summand in the scale energy.
  let f : ℕ → ℝ := fun q' ↦ (blockIncrement Y (2 ^ (m + 1) + q' * 2 ^ j) (2 ^ j) ω) ^ 2
  change f q ≤ ∑ q' ∈ Finset.range (2 ^ (m + 1 - j)), f q'
  exact Finset.single_le_sum
    (f := f) (s := Finset.range (2 ^ (m + 1 - j))) (fun q' hq' ↦ by
      dsimp [f]
      exact sq_nonneg _) hq

/-- Helper for Theorem 5.30: for a descending list of binary exponents, the sum of the recorded
piece energies is bounded by the sum of the corresponding dyadic scale energies. -/
private lemma pieceSquares_sum_le_selectedScaleEnergy
    {α : Type u} (Y : ℕ → α → ℝ) (m : ℕ) (ω : α) :
    ∀ (L : List ℕ) (offset : ℕ),
      L.SortedGT →
      (∀ j ∈ L, j ∈ Finset.range (m + 2)) →
      (∀ j ∈ L, 2 ^ j ∣ offset) →
      offset + (L.map fun j ↦ 2 ^ j).sum ≤ 2 ^ (m + 1) →
      (List.map (fun x : ℝ ↦ x ^ 2)
          (pieceIncrements Y ω (2 ^ (m + 1) + offset) L)).sum ≤
        ∑ j ∈ L.toFinset, dyadicScaleEnergy Y m j ω := by
  intro L
  induction L with
  | nil =>
      intro offset hsorted hrange hdiv hbound
      -- Proof comment: the empty dyadic decomposition contributes no piece energy.
      simp [pieceIncrements]
  | cons j L ih =>
      intro offset hsorted hrange hdiv hbound
      have hpair : List.Pairwise (fun x y : ℕ ↦ x > y) (j :: L) :=
        (List.sortedGT_iff_pairwise).mp hsorted
      obtain ⟨hj_tail, hL_pair⟩ := List.pairwise_cons.mp hpair
      have hL_sorted : L.SortedGT := List.Pairwise.sortedGT hL_pair
      have hj_range : j ∈ Finset.range (m + 2) := hrange j (by simp)
      have hj_le : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj_range)
      rcases hdiv j (by simp) with ⟨q, rfl⟩
      have hj_not_mem : j ∉ L := by
        intro hj_mem
        exact lt_irrefl j (hj_tail j hj_mem)
      have hj_not_mem_finset : j ∉ L.toFinset := by
        simpa [List.mem_toFinset] using hj_not_mem
      have hq_mem : q ∈ Finset.range (2 ^ (m + 1 - j)) := by
        refine Finset.mem_range.mpr ?_
        have hfirst_bound : (q + 1) * 2 ^ j ≤ 2 ^ (m + 1) := by
          have hprefix :
              2 ^ j * q + 2 ^ j ≤ 2 ^ j * q + (2 ^ j + (L.map fun l ↦ 2 ^ l).sum) := by
            omega
          have hle := le_trans hprefix hbound
          simpa [Nat.succ_mul, add_assoc, add_left_comm, add_comm, Nat.mul_comm] using hle
        have hpow : 2 ^ (m + 1 - j) * 2 ^ j = 2 ^ (m + 1) := by
          rw [← pow_add, Nat.sub_add_cancel hj_le]
        have hq_succ_le : q + 1 ≤ 2 ^ (m + 1 - j) := by
          refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (by decide : 0 < 2) j)
          simpa [hpow] using hfirst_bound
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self q) hq_succ_le
      have hrange_tail : ∀ l ∈ L, l ∈ Finset.range (m + 2) := by
        intro l hl
        exact hrange l (by simp [hl])
      have hdiv_tail : ∀ l ∈ L, 2 ^ l ∣ q * 2 ^ j + 2 ^ j := by
        intro l hl
        have hl_lt : l < j := hj_tail l hl
        have hpow_dvd : 2 ^ l ∣ 2 ^ j := pow_dvd_pow 2 (Nat.le_of_lt hl_lt)
        exact dvd_add (by simpa [Nat.mul_comm] using hdiv l (by simp [hl])) hpow_dvd
      have hbound_tail :
          (q * 2 ^ j + 2 ^ j) + (L.map fun l ↦ 2 ^ l).sum ≤ 2 ^ (m + 1) := by
        simpa [List.map_cons, add_assoc, add_left_comm, add_comm, Nat.mul_comm] using hbound
      have htail :
          (List.map (fun x : ℝ ↦ x ^ 2)
              (pieceIncrements Y ω (2 ^ (m + 1) + (q * 2 ^ j + 2 ^ j)) L)).sum ≤
            ∑ l ∈ L.toFinset, dyadicScaleEnergy Y m l ω := by
        exact ih (q * 2 ^ j + 2 ^ j) hL_sorted hrange_tail hdiv_tail hbound_tail
      -- Proof comment: the head piece lands in its scale energy, and the tail reuses the same
      -- aligned-divisibility argument at the shifted offset.
      calc
        (List.map (fun x : ℝ ↦ x ^ 2)
            (pieceIncrements Y ω (2 ^ (m + 1) + 2 ^ j * q) (j :: L))).sum
          =
            (blockIncrement Y (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j) ω) ^ 2 +
              (List.map (fun x : ℝ ↦ x ^ 2)
                (pieceIncrements Y ω (2 ^ (m + 1) + (q * 2 ^ j + 2 ^ j)) L)).sum := by
              simp [pieceIncrements, add_assoc, Nat.mul_comm]
        _ ≤ dyadicScaleEnergy Y m j ω + ∑ l ∈ L.toFinset, dyadicScaleEnergy Y m l ω := by
              exact add_le_add
                (by simpa [Nat.mul_comm] using
                  (blockIncrement_sq_le_dyadicScaleEnergy Y m j q ω hq_mem)) htail
        _ = ∑ l ∈ insert j L.toFinset, dyadicScaleEnergy Y m l ω := by
              rw [Finset.sum_insert hj_not_mem_finset]
        _ = ∑ l ∈ (j :: L).toFinset, dyadicScaleEnergy Y m l ω := by
              simp

/-- Helper for Theorem 5.30: if a block increment has mean zero, then its squared integral is its
variance. -/
private lemma integral_blockIncrement_sq_eq_variance
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P)
    (hY_centered : ∀ n, P[Y n] = 0)
    (start len : ℕ) :
    ∫ ω, (blockIncrement Y start len ω) ^ 2 ∂P = Var[blockIncrement Y start len; P] := by
  have hBlock_memLp : MemLp (blockIncrement Y start len) 2 P :=
    blockIncrement_memLp_two_of_memLp_two P Y hY_memLp start len
  have hBlock_mean : P[blockIncrement Y start len] = 0 :=
    blockIncrement_mean_zero_of_mean_zero P Y hY_memLp hY_centered start len
  -- Proof comment: the centered block increment has variance equal to its second moment.
  simpa [hBlock_mean] using
    (ProbabilityTheory.variance_of_integral_eq_zero hBlock_memLp.aemeasurable hBlock_mean).symm

/-- Helper for Theorem 5.30: at each fixed dyadic scale, the total expected squared aligned
increment energy is exactly the variance mass of the whole dyadic block. -/
private lemma integral_dyadicScaleEnergy_eq_blockVarianceMass
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (m j : ℕ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P)
    (hY_centered : ∀ n, P[Y n] = 0)
    (hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0)
    (hj : j ∈ Finset.range (m + 2)) :
    ∫ ω, dyadicScaleEnergy Y m j ω ∂P =
      ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P] := by
  have hj_le : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpow :
      2 ^ (m + 1 - j) * 2 ^ j = 2 ^ (m + 1) := by
    rw [← pow_add, Nat.sub_add_cancel hj_le]
  have hend : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by
    rw [pow_succ]
    omega
  have hlt :
      2 ^ (m + 1) < 2 ^ (m + 2) := by
    have hpow_pos : 0 < 2 ^ (m + 1) := pow_pos (by decide : 0 < 2) _
    rw [hend]
    exact Nat.lt_add_of_pos_right hpow_pos
  calc
    ∫ ω, dyadicScaleEnergy Y m j ω ∂P
      = ∑ q ∈ Finset.range (2 ^ (m + 1 - j)),
          ∫ ω, (blockIncrement Y (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j) ω) ^ 2 ∂P := by
            change
              ∫ ω,
                ∑ q ∈ Finset.range (2 ^ (m + 1 - j)),
                  (blockIncrement Y (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j) ω) ^ 2 ∂P = _
            rw [integral_finset_sum]
            intro q hq
            exact
              (blockIncrement_memLp_two_of_memLp_two P Y hY_memLp
                (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j)).integrable_sq
    _ = ∑ q ∈ Finset.range (2 ^ (m + 1 - j)),
          Var[blockIncrement Y (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j); P] := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            rw [integral_blockIncrement_sq_eq_variance P Y hY_memLp hY_centered]
    _ = ∑ q ∈ Finset.range (2 ^ (m + 1 - j)),
          ∑ i ∈ Finset.Ico (2 ^ (m + 1) + q * 2 ^ j)
            (2 ^ (m + 1) + (q + 1) * 2 ^ j), Var[Y i; P] := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            have hstep :
                2 ^ (m + 1) + q * 2 ^ j + 2 ^ j =
                  2 ^ (m + 1) + (q + 1) * 2 ^ j := by
              rw [Nat.succ_mul, add_assoc]
            simpa [hstep] using
              variance_blockIncrement_eq_sum_of_pairwise_uncorrelated
                P Y (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j) hY_memLp hY_uncorrelated
    _ = ∑ i ∈ Finset.Ico (2 ^ (m + 1))
          (2 ^ (m + 1) + 2 ^ (m + 1 - j) * 2 ^ j), Var[Y i; P] := by
            simpa using
              sum_range_sum_Ico_eq_sum_Ico
                (fun i ↦ Var[Y i; P]) (2 ^ (m + 1)) (2 ^ j) (2 ^ (m + 1 - j))
    _ = ∑ i ∈ Finset.Ico (2 ^ (m + 1)) (2 ^ (m + 2)), Var[Y i; P] := by
            rw [hpow, hend]
    _ = ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P] := by
            rw [Ico_eq_Icc_pred_of_lt hlt]

/-- Helper for Theorem 5.30: integrating the total dyadic energy over all scales multiplies the
block variance mass by the number of available scales. -/
private lemma integral_totalDyadicScaleEnergy_eq_scaleCount_mul_blockVarianceMass
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (m : ℕ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P)
    (hY_centered : ∀ n, P[Y n] = 0)
    (hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0) :
    ∫ ω, totalDyadicScaleEnergy Y m ω ∂P =
      (m + 2 : ℝ) *
        ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P] := by
  -- Proof comment: every scale has the same expected energy, so summing over the `m + 2`
  -- admissible scales contributes a scalar factor of `m + 2`.
  dsimp [totalDyadicScaleEnergy]
  rw [integral_finset_sum]
  · calc
      ∑ j ∈ Finset.range (m + 2), ∫ ω, dyadicScaleEnergy Y m j ω ∂P
        =
          ∑ j ∈ Finset.range (m + 2),
            ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P] := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [integral_dyadicScaleEnergy_eq_blockVarianceMass P Y m j hY_memLp hY_centered
                hY_uncorrelated hj]
      _ = (m + 2 : ℝ) *
            ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P] := by
            simp
  · intro j hj
    simpa [dyadicScaleEnergy] using
      (show Integrable
          (fun ω ↦
            ∑ q ∈ Finset.range (2 ^ (m + 1 - j)),
              (blockIncrement Y (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j) ω) ^ 2) P from by
        refine integrable_finset_sum _ ?_
        intro q hq
        exact
          (blockIncrement_memLp_two_of_memLp_two P Y hY_memLp
            (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j)).integrable_sq)

/-- Helper for Theorem 5.30: every within-block prefix increment is controlled by `(m + 2)` times
the total dyadic energy of the ambient block. -/
private lemma blockIncrement_sq_le_totalDyadicScaleEnergy
    {α : Type u} (Y : ℕ → α → ℝ) (m d : ℕ) (ω : α) (hd : d ≤ 2 ^ (m + 1)) :
    (blockIncrement Y (2 ^ (m + 1)) d ω) ^ 2 ≤
      (m + 2 : ℝ) * totalDyadicScaleEnergy Y m ω := by
  let L := d.bitIndices.reverse
  let pieces := pieceIncrements Y ω (2 ^ (m + 1)) L
  have hsorted : L.SortedGT := by
    change d.bitIndices.reverse.SortedGT
    exact (Nat.bitIndices_sorted (n := d)).reverse
  have hrange : ∀ j ∈ L, j ∈ Finset.range (m + 2) := by
    intro j hj
    have hj_rev : j ∈ d.bitIndices.reverse := by
      simpa [L] using hj
    have hj_bit : j ∈ d.bitIndices := List.mem_reverse.mp hj_rev
    have hpow_le : 2 ^ j ≤ d := Nat.two_pow_le_of_mem_bitIndices hj_bit
    have hlt_top : d < 2 ^ (m + 2) := by
      have hpow_pos : 0 < 2 ^ (m + 1) := pow_pos (by decide : 0 < 2) _
      have hend : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by
        rw [pow_succ]
        omega
      rw [hend]
      exact lt_of_le_of_lt hd (Nat.lt_add_of_pos_right hpow_pos)
    have hj_lt : j < m + 2 := by
      have hj_size : j < d.size := (Nat.lt_size).2 hpow_le
      exact lt_of_lt_of_le hj_size ((Nat.size_le).2 hlt_top)
    exact Finset.mem_range.mpr hj_lt
  have hcover_sum : (L.map fun j ↦ 2 ^ j).sum = d := by
    change ((d.bitIndices.reverse).map fun j ↦ 2 ^ j).sum = d
    rw [List.map_reverse, List.sum_reverse]
    exact Nat.twoPowSum_bitIndices d
  have hpieces_sum : pieces.sum = blockIncrement Y (2 ^ (m + 1)) d ω := by
    simpa [pieces, hcover_sum] using
      (pieceIncrements_sum_eq_blockIncrement Y ω L (2 ^ (m + 1)))
  have hpieces_sq :
      (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum ≤
        ∑ j ∈ L.toFinset, dyadicScaleEnergy Y m j ω := by
    -- Proof comment: the binary expansion of `d` chooses distinct dyadic scales whose piece
    -- energies inject into the matching scale energies.
    unfold pieces
    exact pieceSquares_sum_le_selectedScaleEnergy Y m ω L 0 hsorted hrange
      (by intro j hj; simp)
      (by simpa [hcover_sum] using hd)
  have hsubset : L.toFinset ⊆ Finset.range (m + 2) := by
    intro j hj
    exact hrange j ((List.mem_toFinset).mp hj)
  have hselected_le_total :
      ∑ j ∈ L.toFinset, dyadicScaleEnergy Y m j ω ≤ totalDyadicScaleEnergy Y m ω := by
    -- Proof comment: summing over the selected scales is bounded by summing over every admissible
    -- scale in the ambient dyadic block.
    dsimp [totalDyadicScaleEnergy]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun j hj hjnot ↦ by
      dsimp [dyadicScaleEnergy]
      exact Finset.sum_nonneg fun q hq ↦ sq_nonneg _)
  have hL_nodup : L.Nodup := by
    change d.bitIndices.reverse.Nodup
    exact List.nodup_reverse.mpr (Nat.bitIndices_nodup (n := d))
  have hL_length_le : L.length ≤ m + 2 := by
    have hcard_le : L.toFinset.card ≤ (Finset.range (m + 2)).card := Finset.card_le_card hsubset
    rw [List.toFinset_card_of_nodup hL_nodup, Finset.card_range] at hcard_le
    exact hcard_le
  have hpieces_length : pieces.length = L.length := by
    simpa [pieces] using (pieceIncrements_length Y ω L (2 ^ (m + 1)))
  have hpieces_length_le : pieces.length ≤ m + 2 := by
    rw [hpieces_length]
    exact hL_length_le
  have hsq :
      pieces.sum ^ 2 ≤ (pieces.length : ℝ) * (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum := by
    have hsq' :
        pieces.sum ^ 2 ≤ (pieces.length : ℝ) * ∑ i : Fin pieces.length, pieces[i] ^ 2 := by
      simpa [Fin.sum_univ_getElem] using
        (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin pieces.length)))
          (f := fun i : Fin pieces.length => pieces[i]))
    have hsum_sq :
        (∑ i : Fin pieces.length, pieces[i] ^ 2) =
          (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum := by
      simpa using (Fin.sum_univ_fun_getElem pieces (fun x : ℝ ↦ x ^ 2))
    calc
      pieces.sum ^ 2 ≤ (pieces.length : ℝ) * ∑ i : Fin pieces.length, pieces[i] ^ 2 := hsq'
      _ = (pieces.length : ℝ) * (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum := by
            rw [hsum_sq]
  have htotal_nonneg : 0 ≤ totalDyadicScaleEnergy Y m ω := by
    dsimp [totalDyadicScaleEnergy, dyadicScaleEnergy]
    exact Finset.sum_nonneg fun j hj ↦ Finset.sum_nonneg fun q hq ↦ sq_nonneg _
  have hsquares_le_total :
      (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum ≤ totalDyadicScaleEnergy Y m ω :=
    le_trans hpieces_sq hselected_le_total
  have hsquares_nonneg : 0 ≤ (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum := by
    refine List.sum_nonneg ?_
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact sq_nonneg x
  have hmul :
      (pieces.length : ℝ) * (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum ≤
        (m + 2 : ℝ) * totalDyadicScaleEnergy Y m ω := by
    have hlen_mul :
        (pieces.length : ℝ) * (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum ≤
          (m + 2 : ℝ) * (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hpieces_length_le) hsquares_nonneg
    have henergy_mul :
        (m + 2 : ℝ) * (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum ≤
          (m + 2 : ℝ) * totalDyadicScaleEnergy Y m ω := by
      exact mul_le_mul_of_nonneg_left hsquares_le_total (by positivity)
    exact le_trans hlen_mul henergy_mul
  -- Proof comment: the block increment is the sum of the selected dyadic pieces, so Cauchy-Schwarz
  -- reduces it to the total selected energy and then to the total block energy.
  calc
    (blockIncrement Y (2 ^ (m + 1)) d ω) ^ 2 = pieces.sum ^ 2 := by
      rw [hpieces_sum]
    _ ≤ (pieces.length : ℝ) * (List.map (fun x : ℝ ↦ x ^ 2) pieces).sum := hsq
    _ ≤ (m + 2 : ℝ) * totalDyadicScaleEnergy Y m ω := hmul

/-- Helper for Theorem 5.30: the dyadic anchor increment between two consecutive
dyadic endpoints. -/
private def dyadicAnchorIncrement (Y : ℕ → Ω → ℝ) (m : ℕ) : Ω → ℝ :=
  fun ω ↦ partialSum Y (2 ^ (m + 2)) ω - partialSum Y (2 ^ (m + 1)) ω

/-- Helper for Theorem 5.30: a dyadic anchor increment is the block increment on the
corresponding dyadic block. -/
private lemma dyadicAnchorIncrement_eq_blockIncrement
    {α : Type u} (Y : ℕ → α → ℝ) (m : ℕ) :
    dyadicAnchorIncrement Y m = blockIncrement Y (2 ^ (m + 1)) (2 ^ (m + 1)) := by
  -- Proof comment: the right dyadic endpoint is exactly one block width beyond the left endpoint.
  ext ω
  have hpow : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by
    rw [pow_succ]
    omega
  rw [dyadicAnchorIncrement, blockIncrement, hpow]

/-- Helper for Theorem 5.30: the variance of a dyadic anchor increment is exactly the variance
mass of its dyadic block. -/
private lemma variance_dyadicAnchorIncrement_eq
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (m : ℕ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P)
    (hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0) :
    Var[dyadicAnchorIncrement Y m; P] =
      ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P] := by
  have hend : 2 ^ (m + 1) + 2 ^ (m + 1) = 2 ^ (m + 2) := by
    rw [pow_succ, pow_succ]
    ring
  have hIcc :
      Finset.Ico (2 ^ (m + 1)) (2 ^ (m + 2)) =
        Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_Ico.mp hi with ⟨hlo, hhi⟩
      exact Finset.mem_Icc.mpr ⟨hlo, Nat.le_pred_of_lt hhi⟩
    · intro hi
      rcases Finset.mem_Icc.mp hi with ⟨hlo, hhi⟩
      have htop : 2 ^ (m + 2) - 1 + 1 = 2 ^ (m + 2) := by
        exact Nat.sub_add_cancel (Nat.one_le_two_pow)
      exact Finset.mem_Ico.mpr ⟨hlo, by
        have hsuc : i + 1 ≤ 2 ^ (m + 2) := by
          simpa [htop] using Nat.succ_le_succ hhi
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hsuc⟩
  calc
    Var[dyadicAnchorIncrement Y m; P]
      = Var[blockIncrement Y (2 ^ (m + 1)) (2 ^ (m + 1)); P] := by
          rw [dyadicAnchorIncrement_eq_blockIncrement]
    _ = ∑ i ∈ Finset.Ico (2 ^ (m + 1)) (2 ^ (m + 2)), Var[Y i; P] := by
          simpa [hend] using
            variance_blockIncrement_eq_sum_of_pairwise_uncorrelated
              P Y (2 ^ (m + 1)) (2 ^ (m + 1)) hY_memLp hY_uncorrelated
    _ = ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P] := by
          rw [hIcc]

/-- Helper for Theorem 5.30: on a probability space, the `L¹` norm of a centered square-integrable
real random variable is bounded by the square root of its variance. -/
private lemma integralAbs_le_sqrt_variance_of_meanZero
    (P : Measure Ω) [IsProbabilityMeasure P] {B : Ω → ℝ}
    (hB_memLp : MemLp B 2 P) (hB_mean : P[B] = 0) :
    ∫ ω, |B ω| ∂P ≤ Real.sqrt (Var[B; P]) := by
  have hcompare : eLpNorm B 1 P ≤ eLpNorm B 2 P :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num) hB_memLp.aestronglyMeasurable
  -- Proof comment: rewrite the `p = 1` and `p = 2` seminorms as the textbook `L¹` integral and
  -- the centered second-moment square root.
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
    ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm
      (hB_memLp.integrable (by norm_num))] at hcompare
  have htwo :
      eLpNorm B 2 P = ENNReal.ofReal (Real.sqrt (∫ ω, (B ω) ^ 2 ∂P)) := by
    simpa [Real.sqrt_eq_rpow, one_div, sq_abs] using
      (MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hB_memLp)
  rw [htwo] at hcompare
  have hvar :
      Var[B; P] = ∫ ω, (B ω) ^ 2 ∂P := by
    simpa [hB_mean] using
      (ProbabilityTheory.variance_of_integral_eq_zero hB_memLp.aemeasurable hB_mean)
  have hcompare' : ∫ ω, |B ω| ∂P ≤ Real.sqrt (∫ ω, (B ω) ^ 2 ∂P) := by
    rw [← ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)]
    simpa [Real.norm_eq_abs] using hcompare
  simpa [hvar] using hcompare'

/-- Helper for Theorem 5.30: if the weighted square profile `((m + 2)^2) * v m` is summable, then
the square-root profile `sqrt (v m)` is summable as well. -/
private lemma summable_sqrt_of_weightedSqSummable
    {v : ℕ → ℝ} (hv_nonneg : ∀ m, 0 ≤ v m)
    (hweighted : Summable (fun m : ℕ ↦ ((m + 2 : ℝ) ^ 2) * v m)) :
    Summable (fun m : ℕ ↦ Real.sqrt (v m)) := by
  have hrecip : Summable (fun m : ℕ ↦ (((m + 2 : ℝ) ^ 2)⁻¹)) := by
    refine ((Real.summable_one_div_nat_add_rpow 2 2).2 (by norm_num)).congr ?_
    intro m
    have hm_nonneg : 0 ≤ (m : ℝ) + 2 := by positivity
    simp [abs_of_nonneg hm_nonneg, one_div]
  have hmajorant :
      Summable (fun m : ℕ ↦
        ((((m + 2 : ℝ) ^ 2) * v m) + (((m + 2 : ℝ) ^ 2)⁻¹)) / 2) := by
    -- Proof comment: the AM-GM majorant is a fixed scalar multiple of the sum of the weighted
    -- variance profile and the reciprocal-square comparison series.
    simpa [div_eq_mul_inv, mul_add, mul_assoc, mul_left_comm, mul_comm] using
      (hweighted.add hrecip).mul_left (1 / 2 : ℝ)
  refine Summable.of_nonneg_of_le ?_ ?_ hmajorant
  · intro m
    exact Real.sqrt_nonneg _
  · intro m
    have hv : 0 ≤ v m := hv_nonneg m
    have hm_ne : (m + 2 : ℝ) ≠ 0 := by positivity
    have hsq_left :
        (((m + 2 : ℝ) * Real.sqrt (v m)) ^ 2) = ((m + 2 : ℝ) ^ 2) * v m := by
      calc
        (((m + 2 : ℝ) * Real.sqrt (v m)) ^ 2)
          = ((m + 2 : ℝ) ^ 2) * (Real.sqrt (v m) ^ 2) := by ring
        _ = ((m + 2 : ℝ) ^ 2) * v m := by rw [Real.sq_sqrt hv]
    have hsq_right :
        (((m + 2 : ℝ)⁻¹) ^ 2) = (((m + 2 : ℝ) ^ 2)⁻¹) := by
      rw [inv_pow]
    have hbound :
        2 * Real.sqrt (v m) ≤ ((m + 2 : ℝ) ^ 2) * v m + (((m + 2 : ℝ) ^ 2)⁻¹) := by
      -- Proof comment: apply the binary AM-GM inequality to
      -- `(m + 2) * sqrt (v m)` and `(m + 2)⁻¹`, then simplify the two squares.
      calc
        2 * Real.sqrt (v m)
          = 2 * ((m + 2 : ℝ) * Real.sqrt (v m)) * ((m + 2 : ℝ)⁻¹) := by
              field_simp [hm_ne]
        _ ≤ (((m + 2 : ℝ) * Real.sqrt (v m)) ^ 2) + (((m + 2 : ℝ)⁻¹) ^ 2) := by
              exact two_mul_le_add_sq (((m + 2 : ℝ) * Real.sqrt (v m))) (((m + 2 : ℝ)⁻¹))
        _ = ((m + 2 : ℝ) ^ 2) * v m + (((m + 2 : ℝ) ^ 2)⁻¹) := by
              rw [hsq_left, hsq_right]
    linarith

/-- Helper for Theorem 5.30: the dyadic anchor increments are absolutely summable in `L¹` once
the shifted dyadic variance profile is summable. -/
private lemma summable_integralAbs_dyadicAnchors
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P)
    (hY_centered : ∀ n, P[Y n] = 0)
    (hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0)
    (hdyadicVariance :
      Summable (fun m : ℕ ↦
        ((m + 2 : ℝ) ^ 2) *
          ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P])) :
    Summable (fun m : ℕ ↦ ∫ ω, |dyadicAnchorIncrement Y m ω| ∂P) := by
  have hpartial_memLp : ∀ n, MemLp (partialSum Y n) 2 P :=
    partialSum_memLp_two_of_memLp_two P Y hY_memLp
  have hpartial_centered : ∀ n, P[partialSum Y n] = 0 :=
    partialSum_mean_zero_of_mean_zero P Y hY_memLp hY_centered
  have hsqrt :
      Summable (fun m : ℕ ↦
        Real.sqrt (∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P])) := by
    refine summable_sqrt_of_weightedSqSummable ?_ hdyadicVariance
    intro m
    exact Finset.sum_nonneg fun i _ ↦ variance_nonneg (Y i) P
  refine Summable.of_nonneg_of_le ?_ ?_ hsqrt
  · intro m
    exact integral_nonneg fun ω ↦ abs_nonneg _
  · intro m
    have hanchor_memLp : MemLp (dyadicAnchorIncrement Y m) 2 P := by
      -- Proof comment: each dyadic anchor increment is a difference of two square-integrable
      -- partial sums.
      simpa [dyadicAnchorIncrement] using
        (hpartial_memLp (2 ^ (m + 2))).sub (hpartial_memLp (2 ^ (m + 1)))
    have hanchor_centered : P[dyadicAnchorIncrement Y m] = 0 := by
      -- Proof comment: the anchor increment is the difference of two centered dyadic anchors.
      change
        P[fun ω ↦ partialSum Y (2 ^ (m + 2)) ω - partialSum Y (2 ^ (m + 1)) ω] = 0
      rw [integral_sub
        ((hpartial_memLp (2 ^ (m + 2))).integrable (by norm_num))
        ((hpartial_memLp (2 ^ (m + 1))).integrable (by norm_num))]
      rw [hpartial_centered, hpartial_centered]
      ring
    calc
      ∫ ω, |dyadicAnchorIncrement Y m ω| ∂P
        ≤ Real.sqrt (Var[dyadicAnchorIncrement Y m; P]) := by
            exact integralAbs_le_sqrt_variance_of_meanZero P hanchor_memLp hanchor_centered
      _ = Real.sqrt
            (∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P]) := by
            rw [variance_dyadicAnchorIncrement_eq P Y m hY_memLp hY_uncorrelated]

/-- Helper for Theorem 5.30: the dyadic anchor increments are absolutely summable almost surely
once their `L¹` norms form a summable series. -/
private lemma ae_summable_abs_dyadicAnchors
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P)
    (hY_centered : ∀ n, P[Y n] = 0)
    (hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0)
    (hdyadicVariance :
      Summable (fun m : ℕ ↦
        ((m + 2 : ℝ) ^ 2) *
          ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P])) :
    ∀ᵐ ω ∂P, Summable (fun m : ℕ ↦ |dyadicAnchorIncrement Y m ω|) := by
  have hAnchorIntegrable :
      ∀ m : ℕ, Integrable (fun ω ↦ |dyadicAnchorIncrement Y m ω|) P := by
    intro m
    -- Proof comment: each anchor increment is the difference of two `L²` partial sums, hence its
    -- absolute value is integrable.
    have hpartial_memLp : ∀ n, MemLp (partialSum Y n) 2 P :=
      partialSum_memLp_two_of_memLp_two P Y hY_memLp
    have hanchor_int : Integrable (dyadicAnchorIncrement Y m) P := by
      simpa [dyadicAnchorIncrement] using
        ((hpartial_memLp (2 ^ (m + 2))).sub (hpartial_memLp (2 ^ (m + 1)))).integrable
          (by norm_num)
    simpa [Real.norm_eq_abs] using hanchor_int.norm
  have hAnchorSummable :
      Summable (fun m : ℕ ↦ ∫ ω, |dyadicAnchorIncrement Y m ω| ∂P) :=
    summable_integralAbs_dyadicAnchors P Y hY_memLp hY_centered hY_uncorrelated hdyadicVariance
  have hMeas :
      ∀ m : ℕ, AEMeasurable (fun ω ↦ ENNReal.ofReal |dyadicAnchorIncrement Y m ω|) P := by
    intro m
    -- Proof comment: the nonnegative summands in the Tonelli step inherit measurability from the
    -- integrability of each absolute anchor increment.
    simpa [abs_abs] using
      (((hAnchorIntegrable m).aestronglyMeasurable.aemeasurable.abs).ennreal_ofReal)
  have hSeriesLintegral_ne_top :
      (∫⁻ ω, ∑' m : ℕ, ENNReal.ofReal |dyadicAnchorIncrement Y m ω| ∂P) ≠ ⊤ := by
    -- Proof comment: Tonelli identifies the total `lintegral` with the sum of the `L¹` norms,
    -- and that sum is finite by the already-closed anchor estimate.
    rw [MeasureTheory.lintegral_tsum hMeas]
    have hOfReal :
        (∑' m : ℕ, ∫⁻ ω, ENNReal.ofReal |dyadicAnchorIncrement Y m ω| ∂P) =
          ∑' m : ℕ, ENNReal.ofReal (∫ ω, |dyadicAnchorIncrement Y m ω| ∂P) := by
      refine tsum_congr fun m ↦ ?_
      symm
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hAnchorIntegrable m) (Filter.Eventually.of_forall fun ω ↦ abs_nonneg _)
    rw [hOfReal]
    exact hAnchorSummable.tsum_ofReal_ne_top
  refine
    (MeasureTheory.ae_lt_top'
      (AEMeasurable.ennreal_tsum hMeas) hSeriesLintegral_ne_top).mono ?_
  intro ω hω
  have hω_ne_top :
      (∑' m : ℕ, ENNReal.ofReal |dyadicAnchorIncrement Y m ω|) ≠ ⊤ := hω.ne
  have hsum :
      Summable (fun m : ℕ ↦ (ENNReal.ofReal |dyadicAnchorIncrement Y m ω|).toReal) :=
    ENNReal.summable_toReal hω_ne_top
  simpa using hsum

/-- Helper for Theorem 5.30: summable real-valued event probabilities imply almost-sure eventual
avoidance of those events by Borel-Cantelli. -/
private lemma ae_eventually_notMem_of_summable_measureReal
    (P : Measure Ω) [IsProbabilityMeasure P] {s : ℕ → Set Ω}
    (hs : Summable (fun n : ℕ ↦ (P (s n)).toReal)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ s n := by
  have htsum : (∑' n, P (s n)) ≠ ∞ := by
    -- Proof comment: summability of the real-valued probabilities lifts back to a finite
    -- `ENNReal` total mass because a probability measure never assigns `∞` to a set.
    simpa [ENNReal.ofReal_toReal, measure_ne_top] using hs.tsum_ofReal_ne_top
  exact MeasureTheory.ae_eventually_notMem htsum

/-- Helper for Theorem 5.30: the bad event that a partial sum in the dyadic block
`[2^(m+1), 2^(m+2)]` oscillates away from the left dyadic anchor by at least the reciprocal
threshold `1 / (r + 1)`. -/
private def dyadicBlockBadEvent (Y : ℕ → Ω → ℝ) (r m : ℕ) : Set Ω :=
  {ω |
    ∃ k ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2)),
      (1 / ((r : ℝ) + 1)) ≤ |partialSum Y k ω - partialSum Y (2 ^ (m + 1)) ω|}

/-- Helper for Theorem 5.30: the real-valued probability of a dyadic oscillation event is bounded
by the weighted variance mass of its ambient dyadic block. -/
private lemma measureReal_dyadicBlockBadEvent_le_weightedBlockVariance
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (r m : ℕ)
    (hY_memLp : ∀ n, MemLp (Y n) 2 P)
    (hY_centered : ∀ n, P[Y n] = 0)
    (hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0) :
    (P (dyadicBlockBadEvent Y r m)).toReal ≤
      (((r : ℝ) + 1) ^ 2) *
        (((m + 2 : ℝ) ^ 2) *
          ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P]) := by
  -- Route correction: the old raw-prefix-square route is false. The right proof writes each
  -- within-block prefix as a sum of at most `m + 2` aligned dyadic increments, bounds its square
  -- by the total scale energy, integrates that energy using
  -- `integral_dyadicScaleEnergy_eq_blockVarianceMass`, and then applies Markov's inequality.
  let ε : ℝ := (1 / ((r : ℝ) + 1)) ^ 2
  let F : Ω → ℝ := fun ω ↦ (m + 2 : ℝ) * totalDyadicScaleEnergy Y m ω
  have hEnergyInt : Integrable (totalDyadicScaleEnergy Y m) P := by
    dsimp [totalDyadicScaleEnergy]
    refine integrable_finset_sum _ ?_
    intro j hj
    simpa [dyadicScaleEnergy] using
      (show Integrable
          (fun ω ↦
            ∑ q ∈ Finset.range (2 ^ (m + 1 - j)),
              (blockIncrement Y (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j) ω) ^ 2) P from by
        refine integrable_finset_sum _ ?_
        intro q hq
        exact
          (blockIncrement_memLp_two_of_memLp_two P Y hY_memLp
            (2 ^ (m + 1) + q * 2 ^ j) (2 ^ j)).integrable_sq)
  have hF_int : Integrable F P := hEnergyInt.const_mul (m + 2 : ℝ)
  have hF_nonneg : 0 ≤ᵐ[P] F := Filter.Eventually.of_forall fun ω ↦ by
    refine mul_nonneg ?_ ?_
    · positivity
    · dsimp [F, totalDyadicScaleEnergy, dyadicScaleEnergy]
      exact Finset.sum_nonneg fun j hj ↦ Finset.sum_nonneg fun q hq ↦ sq_nonneg _
  have hsubset : dyadicBlockBadEvent Y r m ⊆ {ω | ε ≤ F ω} := by
    intro ω hω
    rcases hω with ⟨k, hk, hthr⟩
    let d : ℕ := k - 2 ^ (m + 1)
    have hk_left : 2 ^ (m + 1) ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_right : k ≤ 2 ^ (m + 2) := (Finset.mem_Icc.mp hk).2
    have hend : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by
      rw [pow_succ]
      omega
    have hd : d ≤ 2 ^ (m + 1) := by
      dsimp [d]
      rw [hend] at hk_right
      omega
    have hinc_eq :
        partialSum Y k ω - partialSum Y (2 ^ (m + 1)) ω =
          blockIncrement Y (2 ^ (m + 1)) d ω := by
      dsimp [d, blockIncrement]
      rw [Nat.add_sub_of_le hk_left]
    have hthr_block :
        1 / ((r : ℝ) + 1) ≤ |blockIncrement Y (2 ^ (m + 1)) d ω| := by
      simpa [hinc_eq] using hthr
    have hdet :
        (blockIncrement Y (2 ^ (m + 1)) d ω) ^ 2 ≤ F ω := by
      simpa [F] using blockIncrement_sq_le_totalDyadicScaleEnergy Y m d ω hd
    have hthr_sq :
        (1 / ((r : ℝ) + 1)) ^ 2 ≤ (blockIncrement Y (2 ^ (m + 1)) d ω) ^ 2 := by
      have hinv_pos : 0 < ((r : ℝ) + 1)⁻¹ := by positivity
      have hthr_abs : |((r : ℝ) + 1)⁻¹| ≤ |blockIncrement Y (2 ^ (m + 1)) d ω| := by
        simpa [abs_of_pos hinv_pos] using hthr_block
      simpa [one_div] using (sq_le_sq).2 hthr_abs
    -- Proof comment: a bad-event witness gives one large within-block prefix, and the deterministic
    -- dyadic inequality pushes its square below the total block energy.
    calc
      ε = (1 / ((r : ℝ) + 1)) ^ 2 := rfl
      _ ≤ (blockIncrement Y (2 ^ (m + 1)) d ω) ^ 2 := hthr_sq
      _ ≤ F ω := hdet
  have hbad_le :
      (P (dyadicBlockBadEvent Y r m)).toReal ≤ P.real {ω | ε ≤ F ω} := by
    simpa [MeasureTheory.measureReal_def] using
      (MeasureTheory.measureReal_mono hsubset :
        P.real (dyadicBlockBadEvent Y r m) ≤ P.real {ω | ε ≤ F ω})
  have hmarkov :
      ε * P.real {ω | ε ≤ F ω} ≤ ∫ ω, F ω ∂P :=
    MeasureTheory.mul_meas_ge_le_integral_of_nonneg (μ := P) hF_nonneg hF_int ε
  have hε_pos : 0 < ε := by
    positivity
  have hdiv :
      P.real {ω | ε ≤ F ω} ≤ (∫ ω, F ω ∂P) / ε := by
    exact (le_div_iff₀ hε_pos).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmarkov
  have hF_integral :
      ∫ ω, F ω ∂P =
        ((m + 2 : ℝ) ^ 2) *
          ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P] := by
    calc
      ∫ ω, F ω ∂P = (m + 2 : ℝ) * ∫ ω, totalDyadicScaleEnergy Y m ω ∂P := by
            rw [integral_const_mul]
      _ = (m + 2 : ℝ) *
            ((m + 2 : ℝ) *
              ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P]) := by
            rw [integral_totalDyadicScaleEnergy_eq_scaleCount_mul_blockVarianceMass
              P Y m hY_memLp hY_centered hY_uncorrelated]
      _ = ((m + 2 : ℝ) ^ 2) *
            ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P] := by
            ring
  have hr1_ne : ((r : ℝ) + 1) ≠ 0 := by positivity
  calc
    (P (dyadicBlockBadEvent Y r m)).toReal ≤ P.real {ω | ε ≤ F ω} := hbad_le
    _ ≤ (∫ ω, F ω ∂P) / ε := hdiv
    _ = (((r : ℝ) + 1) ^ 2) *
          (((m + 2 : ℝ) ^ 2) *
            ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1), Var[Y i; P]) := by
          rw [hF_integral, show ε = (1 / ((r : ℝ) + 1)) ^ 2 by rfl]
          field_simp [hr1_ne]

/-- Helper for Theorem 5.30: if the dyadic anchors have absolutely summable increments and every
reciprocal-threshold dyadic oscillation event is eventually absent on a sample path, then the
full partial-sum sequence is pathwise Cauchy. -/
private lemma cauchySeq_partialSum_of_dyadicControl
    {α : Type u} (Y : ℕ → α → ℝ) (ω : α)
    (hAnchor : Summable (fun m : ℕ ↦ |dyadicAnchorIncrement Y m ω|))
    (hBlock : ∀ r : ℕ, ∀ᶠ m in atTop, ω ∉ dyadicBlockBadEvent Y r m) :
    CauchySeq (fun n ↦ partialSum Y n ω) := by
  let anchor : ℕ → ℝ := fun m ↦ partialSum Y (2 ^ (m + 1)) ω
  have hAnchorCauchy : CauchySeq anchor := by
    -- Proof comment: the dyadic anchor sequence has summable successive distances because those
    -- distances are exactly the absolute anchor increments.
    refine cauchySeq_of_dist_le_of_summable _ ?_ hAnchor
    intro m
    simp [anchor, dyadicAnchorIncrement, Real.dist_eq, abs_sub_comm]
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε_third : 0 < ε / 3 := by positivity
  have hrecip_tendsto :
      Tendsto (fun r : ℕ ↦ 1 / ((r : ℝ) + 1)) atTop (𝓝 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
  rcases (Metric.tendsto_atTop.1 hrecip_tendsto) (ε / 3) hε_third with ⟨r, hr⟩
  have hδ : 1 / ((r : ℝ) + 1) < ε / 3 := by
    have hpos : 0 < (r : ℝ) + 1 := by positivity
    simpa [Real.dist_eq, abs_of_pos hpos] using hr r le_rfl
  rcases Filter.eventually_atTop.1 (hBlock r) with ⟨Mbad, hMbad⟩
  rcases (Metric.cauchySeq_iff.1 hAnchorCauchy) (ε / 3) hε_third with
    ⟨Manchor, hAnchorClose⟩
  let M : ℕ := max Mbad Manchor
  refine ⟨2 ^ (M + 1), ?_⟩
  intro m hm n hn
  let qm : ℕ := Nat.log2 m
  let qn : ℕ := Nat.log2 n
  have hm_pos : 0 < m := lt_of_lt_of_le (pow_pos (by decide : 0 < 2) (M + 1)) hm
  have hn_pos : 0 < n := lt_of_lt_of_le (pow_pos (by decide : 0 < 2) (M + 1)) hn
  have hqm_ge : M + 1 ≤ qm := by
    apply (Nat.le_log2 (Nat.ne_of_gt hm_pos)).2
    exact hm
  have hqn_ge : M + 1 ≤ qn := by
    apply (Nat.le_log2 (Nat.ne_of_gt hn_pos)).2
    exact hn
  have hqm_pos : 1 ≤ qm := by omega
  have hqn_pos : 1 ≤ qn := by omega
  have hm_lower : 2 ^ qm ≤ m := Nat.log2_self_le (Nat.ne_of_gt hm_pos)
  have hn_lower : 2 ^ qn ≤ n := Nat.log2_self_le (Nat.ne_of_gt hn_pos)
  have hm_upper : m ≤ 2 ^ (qm + 1) := by
    simpa [qm] using (Nat.lt_log2_self : m < 2 ^ (Nat.log2 m + 1)).le
  have hn_upper : n ≤ 2 ^ (qn + 1) := by
    simpa [qn] using (Nat.lt_log2_self : n < 2 ^ (Nat.log2 n + 1)).le
  have hm_not_bad : ω ∉ dyadicBlockBadEvent Y r (qm - 1) := by
    apply hMbad (qm - 1)
    omega
  have hn_not_bad : ω ∉ dyadicBlockBadEvent Y r (qn - 1) := by
    apply hMbad (qn - 1)
    omega
  have hm_osc :
      dist (partialSum Y m ω) (anchor (qm - 1)) < ε / 3 := by
    have hbound : |partialSum Y m ω - partialSum Y (2 ^ qm) ω| < 1 / ((r : ℝ) + 1) := by
      -- Proof comment: if the within-block oscillation at `m` were at least the reciprocal
      -- threshold, then `m` itself would witness membership in the bad dyadic block event.
      apply lt_of_not_ge
      intro hge
      apply hm_not_bad
      refine ⟨m, ?_, ?_⟩
      · refine Finset.mem_Icc.mpr ?_
        constructor
        · simpa [Nat.sub_add_cancel hqm_pos] using hm_lower
        · have hstep : (qm - 1) + 2 = qm + 1 := by omega
          simpa [hstep] using hm_upper
      · simpa [dyadicBlockBadEvent, Nat.sub_add_cancel hqm_pos] using hge
    calc
      dist (partialSum Y m ω) (anchor (qm - 1))
        = |partialSum Y m ω - partialSum Y (2 ^ qm) ω| := by
            rw [Real.dist_eq]
            congr 2
            dsimp [anchor]
            rw [Nat.sub_add_cancel hqm_pos]
      _ < 1 / ((r : ℝ) + 1) := hbound
      _ < ε / 3 := hδ
  have hn_osc :
      dist (partialSum Y n ω) (anchor (qn - 1)) < ε / 3 := by
    have hbound : |partialSum Y n ω - partialSum Y (2 ^ qn) ω| < 1 / ((r : ℝ) + 1) := by
      -- Proof comment: the same block-membership argument controls the within-block oscillation
      -- at `n`.
      apply lt_of_not_ge
      intro hge
      apply hn_not_bad
      refine ⟨n, ?_, ?_⟩
      · refine Finset.mem_Icc.mpr ?_
        constructor
        · simpa [Nat.sub_add_cancel hqn_pos] using hn_lower
        · have hstep : (qn - 1) + 2 = qn + 1 := by omega
          simpa [hstep] using hn_upper
      · simpa [dyadicBlockBadEvent, Nat.sub_add_cancel hqn_pos] using hge
    calc
      dist (partialSum Y n ω) (anchor (qn - 1))
        = |partialSum Y n ω - partialSum Y (2 ^ qn) ω| := by
            rw [Real.dist_eq]
            congr 2
            dsimp [anchor]
            rw [Nat.sub_add_cancel hqn_pos]
      _ < 1 / ((r : ℝ) + 1) := hbound
      _ < ε / 3 := hδ
  have hanchor_close :
      dist (anchor (qm - 1)) (anchor (qn - 1)) < ε / 3 := by
    -- Proof comment: once the two dyadic block indices are large, the anchor sequence itself is
    -- already Cauchy.
    exact hAnchorClose (qm - 1) (by omega) (qn - 1) (by omega)
  have htri :
      dist (partialSum Y m ω) (partialSum Y n ω) ≤
        dist (partialSum Y m ω) (anchor (qm - 1)) +
          dist (anchor (qm - 1)) (anchor (qn - 1)) +
            dist (anchor (qn - 1)) (partialSum Y n ω) := by
    -- Proof comment: compare each large partial sum to its dyadic anchor, then bridge the two
    -- anchors by their own Cauchy control.
    calc
      dist (partialSum Y m ω) (partialSum Y n ω)
        ≤ dist (partialSum Y m ω) (anchor (qm - 1)) +
            dist (anchor (qm - 1)) (partialSum Y n ω) := dist_triangle _ _ _
      _ ≤ dist (partialSum Y m ω) (anchor (qm - 1)) +
            (dist (anchor (qm - 1)) (anchor (qn - 1)) +
              dist (anchor (qn - 1)) (partialSum Y n ω)) := by
            gcongr
            exact dist_triangle _ _ _
      _ = dist (partialSum Y m ω) (anchor (qm - 1)) +
            dist (anchor (qm - 1)) (anchor (qn - 1)) +
            dist (anchor (qn - 1)) (partialSum Y n ω) := by ring
  have hn_osc' :
      dist (anchor (qn - 1)) (partialSum Y n ω) < ε / 3 := by
    simpa [dist_comm] using hn_osc
  have hsum_lt :
      dist (partialSum Y m ω) (anchor (qm - 1)) +
          dist (anchor (qm - 1)) (anchor (qn - 1)) +
          dist (anchor (qn - 1)) (partialSum Y n ω) < ε := by
    nlinarith
  exact lt_of_le_of_lt htri hsum_lt

/-- Helper for Theorem 5.30: almost-sure Cauchy convergence of the partial sums already gives an
almost-sure limit because `ℝ` is complete. -/
private lemma ae_exists_tendsto_of_ae_cauchy_partialSum
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hCauchy : ∀ᵐ ω ∂P, CauchySeq (fun n ↦ partialSum Y n ω)) :
    ∀ᵐ ω ∂P, ∃ l : ℝ, Tendsto (fun n ↦ partialSum Y n ω) atTop (𝓝 l) := by
  filter_upwards [hCauchy] with ω hω
  -- Proof comment: once the pathwise partial sums are Cauchy, completeness of `ℝ` produces the
  -- limiting value on that sample path.
  exact cauchySeq_tendsto_of_complete hω

/-- Helper for Theorem 5.30: the normalized tail series converges almost surely once the
Rademacher--Menshov dyadic convergence package is available for its log-square variance profile. -/
private lemma aeExistsLimit_partialSum_normalizedTail
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_centered : ∀ n, P[X n] = 0)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0)
    (hseries :
      Summable (fun n : ℕ ↦
        ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹) * Var[X n; P])) :
    ∀ᵐ ω ∂P, ∃ l : ℝ, Tendsto (fun n ↦ partialSum (normalizedTail X a N0) n ω) atTop (𝓝 l) := by
  -- Route correction: the main theorem now isolates the Kronecker endgame, so the only missing
  -- ingredient is the orthogonal-series convergence package for the normalized tail itself.
  have hdyadicVariance :
      Summable (fun m : ℕ ↦
        ((m + 2 : ℝ) ^ 2) *
          ∑ i ∈ Finset.Icc (2 ^ (m + 1)) (2 ^ (m + 2) - 1),
            Var[normalizedTail X a N0 i; P]) := by
    -- Proof comment: the scalar dyadic regrouping phase is complete, so the normalized tail now
    -- satisfies the exact shifted block summability profile needed by the probabilistic step.
    exact normalizedTail_shiftedDyadicVarianceSummable P X a N0 hseries
  have hAnchorAE :
      ∀ᵐ ω ∂P, Summable (fun m : ℕ ↦ |dyadicAnchorIncrement (normalizedTail X a N0) m ω|) := by
    -- Proof comment: the dyadic anchor subsequence already has almost-sure absolutely summable
    -- increments, so its pathwise convergence is no longer part of the blocker.
    exact ae_summable_abs_dyadicAnchors P (normalizedTail X a N0)
      (normalizedTail_memLp P X a N0 hX_memLp)
      (normalizedTail_mean_zero P X a N0 hX_centered)
      (normalizedTail_pairwise_uncorrelated P X a N0 hX_uncorrelated)
      hdyadicVariance
  have hBlockAE :
      ∀ r : ℕ, ∀ᵐ ω ∂P,
        ∀ᶠ m in atTop, ω ∉ dyadicBlockBadEvent (normalizedTail X a N0) r m := by
    intro r
    have hbadSummable :
        Summable (fun m : ℕ ↦
          (P (dyadicBlockBadEvent (normalizedTail X a N0) r m)).toReal) := by
      -- Proof comment: once the dyadic bad-event probability is controlled by the weighted block
      -- variance mass, the already-closed dyadic summability hypothesis gives the needed series.
      refine Summable.of_nonneg_of_le ?_ ?_ (hdyadicVariance.mul_left (((r : ℝ) + 1) ^ 2))
      · intro m
        exact ENNReal.toReal_nonneg
      · intro m
        simpa [mul_assoc] using
          measureReal_dyadicBlockBadEvent_le_weightedBlockVariance P
            (normalizedTail X a N0) r m
            (normalizedTail_memLp P X a N0 hX_memLp)
            (normalizedTail_mean_zero P X a N0 hX_centered)
            (normalizedTail_pairwise_uncorrelated P X a N0 hX_uncorrelated)
    -- Proof comment: Borel-Cantelli now gives almost-sure eventual avoidance for the fixed
    -- reciprocal threshold `r`.
    exact ae_eventually_notMem_of_summable_measureReal P hbadSummable
  have hBlockAll :
      ∀ᵐ ω ∂P, ∀ r : ℕ,
        ∀ᶠ m in atTop, ω ∉ dyadicBlockBadEvent (normalizedTail X a N0) r m := by
    -- Proof comment: intersect the fixed-threshold eventual-avoidance statements over the
    -- countable family of reciprocal thresholds.
    exact MeasureTheory.ae_all_iff.2 hBlockAE
  have hCauchy :
      ∀ᵐ ω ∂P, CauchySeq (fun n ↦ partialSum (normalizedTail X a N0) n ω) := by
    -- Proof comment: combine the already-closed anchor summability with the new pathwise dyadic
    -- Cauchy criterion.
    filter_upwards [hAnchorAE, hBlockAll] with ω hω_anchor hω_block
    exact cauchySeq_partialSum_of_dyadicControl (normalizedTail X a N0) ω hω_anchor hω_block
  exact ae_exists_tendsto_of_ae_cauchy_partialSum P (normalizedTail X a N0) hCauchy

/-- Helper for Theorem 5.30: once the normalized tail series converges almost surely, Kronecker's
lemma turns that convergence into almost-sure vanishing of the normalized absolute partial sums. -/
lemma ae_tendsto_abs_weighted_partial_sums_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal)
    (ha_mono : Monotone a)
    (ha_tendsto : Tendsto a atTop atTop)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_centered : ∀ n, P[X n] = 0)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0)
    (hseries :
      Summable (fun n : ℕ ↦
        ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹) * Var[X n; P])) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ ↦ abs (partialSum X (n + 1) ω) / (a n : ℝ))
        atTop (𝓝 0) := by
  obtain ⟨N0, hN0_pos_tail⟩ := eventually_pos_of_tendsto_atTop_nnreal a ha_tendsto
  have hLimitAE :
      ∀ᵐ ω ∂P, ∃ l : ℝ, Tendsto (fun n ↦ partialSum (normalizedTail X a N0) n ω) atTop (𝓝 l) :=
    aeExistsLimit_partialSum_normalizedTail P X a N0 hX_memLp hX_centered hX_uncorrelated hseries
  filter_upwards [hLimitAE] with ω hω
  rcases hω with ⟨l, hl⟩
  have hN0_pos : ∀ k, 0 < a (k + N0) := by
    intro k
    exact hN0_pos_tail (k + N0) (Nat.le_add_left N0 k)
  have ha_shift_tendsto : Tendsto (fun n : ℕ ↦ a (n + N0)) atTop atTop :=
    (Filter.tendsto_add_atTop_iff_nat N0).2 ha_tendsto
  have ha_shift_real_tendsto :
      Tendsto (fun n : ℕ ↦ (a (n + N0) : ℝ)) atTop atTop := by
    exact (NNReal.tendsto_coe_atTop).2 ha_shift_tendsto
  have hweighted_tail :
      Tendsto
        (fun n : ℕ ↦
          ((a (n + N0) : ℝ)⁻¹) *
            ∑ i ∈ Finset.range n, (a (i + N0) : ℝ) * normalizedTail X a N0 i ω)
        atTop (𝓝 0) := by
    -- Proof comment: apply the deterministic Kronecker lemma to the convergent normalized tail.
    exact weightedPartialSumDiv_tendstoZero_of_monotone
      (fun n ↦ a (n + N0))
      (fun i j hij ↦ ha_mono (Nat.add_le_add_right hij N0))
      ha_shift_tendsto
      (fun n ↦ normalizedTail X a N0 n ω)
      hl
  have htail_increment :
      Tendsto
        (fun n : ℕ ↦
          ((a (n + N0) : ℝ)⁻¹) *
            (partialSum X (n + N0) ω - partialSum X N0 ω))
        atTop (𝓝 0) := by
    -- Proof comment: rewrite the weighted normalized-tail partial sums as the corresponding tail
    -- increments of the original sequence.
    refine hweighted_tail.congr' ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      dsimp
      rw [weighted_normalizedTail_partialSum_eq_tail_increment X a N0 n ω hN0_pos]
  have hanchor_div :
      Tendsto
        (fun n : ℕ ↦ ((a (n + N0) : ℝ)⁻¹) * partialSum X N0 ω)
        atTop (𝓝 0) := by
    -- Proof comment: the fixed anchor is killed by the divergence of the weight sequence.
    simpa [mul_comm] using
      (Filter.Tendsto.inv_tendsto_atTop ha_shift_real_tendsto).const_mul (partialSum X N0 ω)
  have hpartial_div_shift :
      Tendsto
        (fun n : ℕ ↦ ((a (n + N0) : ℝ)⁻¹) * partialSum X (n + N0) ω)
        atTop (𝓝 0) := by
    -- Proof comment: add back the fixed anchor contribution after the Kronecker tail estimate.
    have hsum :
        Tendsto
          (fun n : ℕ ↦
            ((a (n + N0) : ℝ)⁻¹) *
                (partialSum X (n + N0) ω - partialSum X N0 ω) +
              ((a (n + N0) : ℝ)⁻¹) * partialSum X N0 ω)
          atTop (𝓝 0) := by
      simpa using htail_increment.add hanchor_div
    refine hsum.congr' ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      ring
  have hpartial_div :
      Tendsto (fun n : ℕ ↦ ((a n : ℝ)⁻¹) * partialSum X n ω) atTop (𝓝 0) := by
    -- Proof comment: remove the finite index shift from the tail estimate.
    exact (Filter.tendsto_add_atTop_iff_nat N0).1 <| by
      simpa using hpartial_div_shift
  have hnormalized_term_shift :
      Tendsto (fun n : ℕ ↦ normalizedTail X a N0 n ω) atTop (𝓝 0) := by
    have hpartial_shift :
        Tendsto
          (fun n : ℕ ↦ partialSum (normalizedTail X a N0) (n + 1) ω)
          atTop (𝓝 l) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2 hl
    have hdiff :
        Tendsto
          (fun n : ℕ ↦
            partialSum (normalizedTail X a N0) (n + 1) ω -
              partialSum (normalizedTail X a N0) n ω)
          atTop (𝓝 0) := by
      simpa using hpartial_shift.sub hl
    -- Proof comment: the terms of a convergent real series tend to zero.
    refine hdiff.congr' ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      simpa using
        (partialSum_sub_eq_sum_Ico (normalizedTail X a N0) (show n ≤ n + 1 by omega) ω)
  have hnormalized_term :
      Tendsto (fun n : ℕ ↦ ((a n : ℝ)⁻¹) * X n ω) atTop (𝓝 0) := by
    -- Proof comment: identify the normalized tail terms with the shifted original terms.
    exact (Filter.tendsto_add_atTop_iff_nat N0).1 <| by
      simpa [normalizedTail] using hnormalized_term_shift
  have hsum_tendsto :
      Tendsto
        (fun n : ℕ ↦
          ((a n : ℝ)⁻¹) * partialSum X n ω + ((a n : ℝ)⁻¹) * X n ω)
        atTop (𝓝 0) := by
    -- Proof comment: the next normalized partial sum is the sum of the previous normalized
    -- partial sum and the normalized next term.
    simpa using hpartial_div.add hnormalized_term
  have htarget :
      Tendsto
        (fun n : ℕ ↦ abs ((((a n : ℝ)⁻¹) * partialSum X n ω) + (((a n : ℝ)⁻¹) * X n ω)))
        atTop (𝓝 0) := by
    simpa using continuous_abs.continuousAt.tendsto.comp hsum_tendsto
  refine htarget.congr' ?_
  exact Filter.Eventually.of_forall fun n ↦ by
    dsimp
    have hnonneg : 0 ≤ ((a n : ℝ)⁻¹) := by positivity
    have hpartial_succ : partialSum X (n + 1) ω = partialSum X n ω + X n ω := by
      rw [partialSum, partialSum, Finset.sum_range_succ]
    rw [hpartial_succ, div_eq_mul_inv]
    have hfactor :
        ((a n : ℝ)⁻¹) * partialSum X n ω + ((a n : ℝ)⁻¹) * X n ω =
          (partialSum X n ω + X n ω) * ((a n : ℝ)⁻¹) := by
      ring
    rw [hfactor, abs_mul, abs_of_nonneg hnonneg]

-- Proof sketch: apply Chebyshev's inequality to the normalized partial sums, use the
-- covariance-zero hypotheses to expand the variance of each `partialSum` into the sum of the
-- individual variances, and then invoke Borel-Cantelli from the summability assumption.
-- Lean implementation note: the public theorem keeps the textbook surface of increasing
-- nonnegative weights and makes the asymptotically necessary divergence hypothesis explicit; the
-- `0`-based encoding still allows finitely many initial zero weights because the conclusion is a
-- limsup statement and the `n = 0` logarithmic weight vanishes.
-- Semantic recall note: `lean_leansearch` only surfaced generic limsup/Borel-Cantelli
-- infrastructure, not an existing owner for this source-facing Rademacher-Menshov statement, so
-- the chapter theorem remains the public surface.
/-- Theorem 5.30 [Rademacher--Menshov]: in the canonical `0`-based Lean indexing, the textbook
sequences `X₁, X₂, …` and `a₁, a₂, …` are represented directly by `X 0, X 1, …` and
`a 0, a 1, …`. If these real random variables are centered, pairwise uncorrelated, and
square-integrable, and if `a` is an increasing sequence of nonnegative numbers tending to `∞`,
then summability of the logarithmically weighted inverse-square variance series implies that the
limsup of the normalized absolute partial sums is `0` almost surely. Only when a user has inserted
a dummy `0`th term
should this statement be applied to shifted sequences such as `fun n ↦ X (n + 1)` and
`fun n ↦ a (n + 1)`. -/
theorem rademacher_menshov_ae_limsup_weighted_partial_sums_eq_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal)
    (ha_mono : Monotone a)
    (ha_tendsto : Tendsto a atTop atTop)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_centered : ∀ n, P[X n] = 0)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0)
    (hseries :
      Summable (fun n : ℕ ↦
        ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹) * Var[X n; P])) :
    ∀ᵐ ω ∂P,
      limsup
        (fun n : ℕ ↦ abs (partialSum X (n + 1) ω) / (a n : ℝ))
        atTop = 0 := by
  have hTendsto :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n : ℕ ↦ abs (partialSum X (n + 1) ω) / (a n : ℝ))
          atTop (𝓝 0) :=
    ae_tendsto_abs_weighted_partial_sums_zero P X a ha_mono ha_tendsto
      hX_memLp hX_centered hX_uncorrelated hseries
  filter_upwards [hTendsto] with ω hω
  -- Proof comment: for a real sequence converging to `0`, the limsup is exactly `0`.
  exact hω.limsup_eq
