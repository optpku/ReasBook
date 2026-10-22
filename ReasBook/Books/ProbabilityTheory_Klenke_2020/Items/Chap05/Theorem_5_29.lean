/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 5.29: each finite partial sum has variance bounded by the variance supremum
times the number of summands. -/
private lemma partialSum_variance_le_sSup_mul
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_var_bdd : BddAbove (Set.range fun n ↦ Var[X n; P]))
    (N : ℕ) :
    Var[partialSum X N; P] ≤ sSup (Set.range fun n ↦ Var[X n; P]) * (N : ℝ) := by
  -- Proof comment: restrict the independent sequence to the first `N` coordinates, rewrite the
  -- partial sum as a `Fin N`-indexed sum, and then use additivity of variance for finite
  -- independent sums.
  let Y : Fin N → Ω → ℝ := fun i ↦ X i.1
  have hY_memLp : ∀ i, MemLp (Y i) 2 P := by
    intro i
    exact hX_memLp i.1
  have hY_pairwise :
      ((Finset.univ : Finset (Fin N)) : Set (Fin N)).Pairwise fun i j ↦ IndepFun (Y i) (Y j) P :=
    by
      intro i _ j _ hij
      exact (hX_indep.precomp Fin.val_injective).indepFun hij
  have hpartial_eq : partialSum X N = fun ω ↦ ∑ i : Fin N, Y i ω := by
    -- Proof comment: the chapter's `partialSum` is exactly the sum over `Fin.range N`.
    ext ω
    simpa [partialSum, Y] using (Fin.sum_univ_eq_sum_range (fun i ↦ X i ω) N).symm
  have hsum_fun_eq : (∑ i : Fin N, Y i) = fun ω ↦ ∑ i : Fin N, Y i ω := by
    -- Proof comment: rewrite the sum of functions in explicit pointwise form.
    funext ω
    simp [Finset.sum_apply]
  have hsum_var : Var[partialSum X N; P] = ∑ i : Fin N, Var[Y i; P] := by
    -- Proof comment: variance additivity is available once the finite family is pairwise
    -- independent and square-integrable.
    rw [hpartial_eq, ← hsum_fun_eq]
    simpa using IndepFun.variance_sum (fun i _ ↦ hY_memLp i) hY_pairwise
  have hvar_le : ∀ i : Fin N, Var[Y i; P] ≤ sSup (Set.range fun n ↦ Var[X n; P]) := by
    intro i
    exact le_csSup hX_var_bdd (Set.mem_range_self i.1)
  have hsum_le :
      ∑ i : Fin N, Var[Y i; P] ≤ N * sSup (Set.range fun n ↦ Var[X n; P]) := by
    -- Proof comment: each summand is bounded by the common variance supremum.
    simpa [Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_card_nsmul Finset.univ (fun i : Fin N ↦ Var[Y i; P])
        (sSup (Set.range fun n ↦ Var[X n; P])) (fun i _ ↦ hvar_le i)
  rw [hsum_var]
  simpa [mul_comm] using hsum_le

/-- Helper for Theorem 5.29: logarithms of dyadic powers linearize exactly. -/
private lemma dyadic_log_pow_eq
    (k : ℕ) :
    Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
  -- Proof comment: `Real.log_pow` applies directly once the dyadic natural power is cast to `ℝ`.
  rw [Nat.cast_pow]
  exact Real.log_pow (2 : ℝ) k

/-- Helper for Theorem 5.29: the shifted dyadic logarithm is the `k = m + 1` case of the general
dyadic logarithm identity. -/
private lemma dyadic_log_eq
    (m : ℕ) :
    Real.log ((2 ^ (m + 1) : ℕ) : ℝ) = (m + 1 : ℝ) * Real.log 2 := by
  -- Proof comment: specialize the general dyadic logarithm identity to the shifted block index.
  rw [dyadic_log_pow_eq]
  norm_num

/-- Helper for Theorem 5.29: the dyadic normalization square expands into the exact p-series
denominator used in the Kolmogorov bound. -/
private lemma dyadic_normalization_sq
    {ε δ : ℝ} (m : ℕ) :
    (δ *
      (Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) *
        Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε))) ^ 2 =
      δ ^ 2 * ((((2 ^ (m + 1) : ℕ) : ℝ)) *
        (((m + 1 : ℝ) ^ (1 + 2 * ε)) * Real.rpow (Real.log 2) (1 + 2 * ε))) := by
  have hlog_nonneg : 0 ≤ Real.log (((2 ^ (m + 1) : ℕ) : ℝ)) := by
    -- Proof comment: on a shifted dyadic block the logarithm is positive, hence nonnegative.
    rw [dyadic_log_eq]
    positivity
  have hrpow_sq :
      (Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε)) ^ 2 =
        Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 + 2 * ε) := by
    -- Proof comment: multiply the exponent `1 / 2 + ε` by `2` to recover `1 + 2 * ε`.
    calc
      (Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε)) ^ 2 =
          (Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε)) ^ (2 : ℝ) := by
        rw [← Real.rpow_natCast]
        norm_num
      _ = Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) ((1 / 2 + ε) * 2) := by
        symm
        exact Real.rpow_mul hlog_nonneg (1 / 2 + ε) (2 : ℝ)
      _ = Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 + 2 * ε) := by
        congr 1
        ring
  have hscale_sq :
      (Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) *
          Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε)) ^ 2 =
        (((2 ^ (m + 1) : ℕ) : ℝ)) *
          (((m + 1 : ℝ) ^ (1 + 2 * ε)) * Real.rpow (Real.log 2) (1 + 2 * ε)) := by
    -- Proof comment: square the `sqrt` and `rpow` factors separately and then linearize the
    -- dyadic logarithm.
    rw [mul_pow, Real.sq_sqrt (by positivity), hrpow_sq, dyadic_log_eq]
    have hmul :
        (((m + 1 : ℝ) * Real.log 2) ^ (1 + 2 * ε)) =
          (m + 1 : ℝ) ^ (1 + 2 * ε) * (Real.log 2) ^ (1 + 2 * ε) := by
      simpa using (Real.mul_rpow (by positivity) (by positivity) :
        (((m + 1 : ℝ) * Real.log 2) ^ (1 + 2 * ε)) =
          (m + 1 : ℝ) ^ (1 + 2 * ε) * (Real.log 2) ^ (1 + 2 * ε))
    exact congrArg (fun t : ℝ ↦ (((2 ^ (m + 1) : ℕ) : ℝ)) * t) hmul
  -- Proof comment: the threshold factor `δ` now contributes only the scalar square `δ ^ 2`.
  rw [mul_pow, hscale_sq]

/-- Helper for Theorem 5.29: the shifted p-series coming from the dyadic maximal inequality is
summable as soon as `ε > 0`. -/
private lemma shifted_p_series_summable
    {ε C : ℝ} (hε : 0 < ε) :
    Summable (fun m : ℕ ↦ C / ((m + 1 : ℝ) ^ (1 + 2 * ε))) := by
  have hs :
      Summable (fun m : ℕ ↦ 1 / ((m + 1 : ℝ) ^ (1 + 2 * ε))) := by
    -- Proof comment: this is the textbook `p`-series with exponent `1 + 2 * ε > 1`.
    refine
      ((Real.summable_one_div_nat_add_rpow 1 (1 + 2 * ε)).2 (by linarith)).congr ?_
    intro m
    rw [abs_of_nonneg]
    positivity
  -- Proof comment: multiplying a summable series by the constant prefactor preserves summability.
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs.mul_left C

/-- Helper for Theorem 5.29: on each dyadic block, the dyadic normalization is controlled by the
normalization at any interior index up to an explicit `ε`-dependent constant. -/
private lemma dyadic_scale_le_block_scale
    {ε : ℝ} (hε : 0 < ε) {m n : ℕ}
    (hm : 1 ≤ m) (h_lower : 2 ^ m ≤ n + 1) (h_upper : n + 1 ≤ 2 ^ (m + 1)) :
    Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) *
        Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) ≤
      (Real.sqrt 2 * 2 ^ (1 / 2 + ε)) *
        (Real.sqrt (n + 1) * Real.rpow (Real.log (n + 1)) (1 / 2 + ε)) := by
  have hp_pos : 0 < (1 / 2 + ε : ℝ) := by
    linarith
  have hsqrt :
      Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) ≤ Real.sqrt 2 * Real.sqrt (n + 1) := by
    have h_cast : (((2 ^ (m + 1) : ℕ) : ℝ)) ≤ 2 * (n + 1 : ℝ) := by
      -- Proof comment: the upper dyadic endpoint is at most twice any index in the same dyadic
      -- block.
      calc
        (((2 ^ (m + 1) : ℕ) : ℝ)) = 2 * ((2 ^ m : ℕ) : ℝ) := by
          rw [pow_succ, Nat.cast_mul]
          ring
        _ ≤ 2 * (n + 1 : ℝ) := by
          gcongr
          exact_mod_cast h_lower
    calc
      Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) ≤ Real.sqrt (2 * (n + 1 : ℝ)) := Real.sqrt_le_sqrt h_cast
      _ = Real.sqrt 2 * Real.sqrt (n + 1) := by
        rw [Real.sqrt_mul (by positivity)]
  have hlog_nonneg : 0 ≤ Real.log (n + 1 : ℝ) := by
    have hpow_two : (2 : ℕ) ≤ 2 ^ m := by
      rcases Nat.exists_eq_add_of_le hm with ⟨k, rfl⟩
      have hk : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) k)
      calc
        2 = 2 * 1 := by ring
        _ ≤ 2 * 2 ^ k := by gcongr
        _ = 2 ^ (1 + k) := by simp [pow_succ, Nat.mul_comm, Nat.add_comm]
    have h_lower_two : (2 : ℕ) ≤ n + 1 := le_trans hpow_two h_lower
    -- Proof comment: every index in a shifted dyadic block is at least `2`, so its logarithm is
    -- nonnegative.
    exact le_of_lt (Real.log_pos (by exact_mod_cast h_lower_two))
  have hlog_upper_bound :
      Real.log (((2 ^ (m + 1) : ℕ) : ℝ)) ≤ 2 * Real.log (n + 1 : ℝ) := by
    have hm_cast : (1 : ℝ) ≤ m := by
      exact_mod_cast hm
    have hm_succ_le : (m + 1 : ℝ) ≤ 2 * m := by
      linarith
    have hlog_lower : (m : ℝ) * Real.log 2 ≤ Real.log (n + 1 : ℝ) := by
      -- Proof comment: the lower dyadic endpoint lies below `n + 1`, so its logarithm does too.
      rw [← dyadic_log_pow_eq m]
      exact Real.log_le_log (by positivity) (by exact_mod_cast h_lower)
    rw [dyadic_log_eq]
    calc
      (m + 1 : ℝ) * Real.log 2 ≤ (2 * m : ℝ) * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right hm_succ_le (le_of_lt (Real.log_pos one_lt_two))
      _ = 2 * ((m : ℝ) * Real.log 2) := by
        ring
      _ ≤ 2 * Real.log (n + 1 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlog_lower (by positivity)
  have hrpow :
      Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) ≤
        2 ^ (1 / 2 + ε) * Real.rpow (Real.log (n + 1 : ℝ)) (1 / 2 + ε) := by
    -- Proof comment: monotonicity of `x ↦ x^(1 / 2 + ε)` on `[0, ∞)` upgrades the logarithmic
    -- block comparison to the normalization factor.
    calc
      Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) ≤
          Real.rpow (2 * Real.log (n + 1 : ℝ)) (1 / 2 + ε) := by
        exact Real.rpow_le_rpow (by positivity) hlog_upper_bound hp_pos.le
      _ = 2 ^ (1 / 2 + ε) * Real.rpow (Real.log (n + 1 : ℝ)) (1 / 2 + ε) := by
        have hmul :
            ((2 * Real.log (n + 1 : ℝ)) ^ (1 / 2 + ε)) =
              2 ^ (1 / 2 + ε) * (Real.log (n + 1 : ℝ)) ^ (1 / 2 + ε) := by
          simpa using (Real.mul_rpow (by positivity) hlog_nonneg :
            ((2 * Real.log (n + 1 : ℝ)) ^ (1 / 2 + ε)) =
              2 ^ (1 / 2 + ε) * (Real.log (n + 1 : ℝ)) ^ (1 / 2 + ε))
        exact hmul
  have hdyadic_log_nonneg : 0 ≤ Real.log (((2 ^ (m + 1) : ℕ) : ℝ)) := by
    rw [dyadic_log_eq]
    positivity
  have hdyadic_rpow_nonneg :
      0 ≤ Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) := by
    exact Real.rpow_nonneg hdyadic_log_nonneg _
  have hblock_nonneg : 0 ≤ Real.sqrt 2 * Real.sqrt (n + 1) := by
    positivity
  -- Proof comment: combine the square-root control and the logarithmic control, then regroup the
  -- scalar constants.
  calc
    Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) *
        Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) ≤
      (Real.sqrt 2 * Real.sqrt (n + 1)) *
        Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) := by
      exact mul_le_mul_of_nonneg_right hsqrt hdyadic_rpow_nonneg
    _ ≤ (Real.sqrt 2 * Real.sqrt (n + 1)) *
        (2 ^ (1 / 2 + ε) * Real.rpow (Real.log (n + 1 : ℝ)) (1 / 2 + ε)) := by
      exact mul_le_mul_of_nonneg_left hrpow hblock_nonneg
    _ = (Real.sqrt 2 * 2 ^ (1 / 2 + ε)) *
          (Real.sqrt (n + 1) * Real.rpow (Real.log (n + 1)) (1 / 2 + ε)) := by
      ring

-- Proof sketch: pass to the dyadic subsequence `2^k`, apply Kolmogorov's maximal inequality to
-- the centered partial sums using the uniform variance bound, show the resulting probabilities are
-- summable, and conclude from Borel--Cantelli. A comparison between arbitrary `n` and the
-- neighboring dyadic block then gives the full limsup statement.
/-- Theorem 5.29: if the real random variables `X₀, X₁, …` are independent, have mean `0`, and
have uniformly bounded variances, then for every `ε > 0` the normalized partial sums
`Sₙ = X₀ + ⋯ + Xₙ₋₁` satisfy
`limsup |Sₙ| / (sqrt n * (log n)^(1 / 2 + ε)) = 0` almost surely. For the textbook indexing
`X₁, X₂, …`, apply this statement to `fun k ↦ X (k + 1)`. -/
theorem ae_limsup_partial_sum_div_sqrt_log_rpow_eq_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_mean_zero : ∀ n, P[X n] = 0)
    (hX_var_bdd : BddAbove (Set.range fun n ↦ Var[X n; P]))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P,
      limsup
        (fun n ↦
          |partialSum X (n + 1) ω| /
            (Real.sqrt (n + 1) *
              Real.rpow (Real.log (n + 1)) (1 / 2 + ε))) atTop = 0 := by
  let V : ℝ := sSup (Set.range fun n ↦ Var[X n; P])
  let L : ℕ → ℝ := fun n ↦ Real.sqrt n * Real.rpow (Real.log n) (1 / 2 + ε)
  have hvariance : ∀ N, Var[partialSum X N; P] ≤ V * (N : ℝ) := by
    intro N
    simpa [V] using partialSum_variance_le_sSup_mul P X hX_indep hX_memLp hX_var_bdd N
  have hp_pos : 0 < (1 / 2 + ε : ℝ) := by
    linarith
  let Cε : ℝ := Real.sqrt 2 * 2 ^ (1 / 2 + ε)
  let Ldyadic : ℕ → ℝ := fun n ↦ Real.sqrt n * Real.rpow (Real.log n) (1 / 2 + ε)
  let u : ℕ → Ω → ℝ := fun n ω ↦ |partialSum X (n + 1) ω| / Ldyadic (n + 1)
  let A : ℝ → ℕ → Set Ω := fun δ m ↦
    absHitEvent X (2 ^ (m + 1)) (δ * Ldyadic (2 ^ (m + 1)))
  have hV_nonneg : 0 ≤ V := by
    have hvar0_nonneg : 0 ≤ Var[X 0; P] := by
      simpa using variance_nonneg (X 0) P
    exact hvar0_nonneg.trans <| by
      simpa [V] using
        (le_csSup hX_var_bdd (Set.mem_range_self 0) : Var[X 0; P] ≤
          sSup (Set.range fun n ↦ Var[X n; P]))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2rpow_pos : 0 < Real.rpow (Real.log 2) (1 + 2 * ε) := by
    exact Real.rpow_pos_of_pos hlog2_pos _
  have hboundδ :
      ∀ {δ : ℝ}, 0 < δ → ∀ᵐ ω ∂P, ∀ᶠ n in atTop, u n ω ≤ Cε * δ := by
    intro δ hδ
    let g : ℕ → ℝ := fun m ↦
      (V / (δ ^ 2 * Real.rpow (Real.log 2) (1 + 2 * ε))) /
        ((m + 1 : ℝ) ^ (1 + 2 * ε))
    have hg_nonneg : ∀ m, 0 ≤ g m := by
      intro m
      dsimp [g]
      positivity
    have hg_summable : Summable g := by
      -- Proof comment: the dyadic maximal-inequality majorant is exactly a shifted p-series.
      simpa [g] using
        shifted_p_series_summable
          (ε := ε)
          (C := V / (δ ^ 2 * Real.rpow (Real.log 2) (1 + 2 * ε)))
          hε
    have hprob : ∀ m, P (A δ m) ≤ ENNReal.ofReal (g m) := by
      intro m
      have hLdyadic_pos : 0 < Ldyadic (2 ^ (m + 1)) := by
        -- Proof comment: the dyadic normalization is strictly positive because the block index is
        -- at least `2`, so both the square-root and logarithmic factors are positive.
        dsimp [Ldyadic]
        have hlog_pos : 0 < Real.log (((2 ^ (m + 1) : ℕ) : ℝ)) := by
          rw [dyadic_log_eq]
          positivity
        positivity
      have hkolmogorov :
          P (A δ m) ≤
            ENNReal.ofReal
              (Var[partialSum X (2 ^ (m + 1)); P] /
                (δ * Ldyadic (2 ^ (m + 1))) ^ 2) := by
        -- Proof comment: apply Kolmogorov's maximal inequality on the dyadic prefix.
        simpa [A] using
          kolmogorov_inequality_abs_partial_sums
            P X (2 ^ (m + 1))
            (hX_indep.precomp Fin.val_injective)
            (fun k hk ↦ hX_mean_zero k)
            (fun k hk ↦ hX_memLp k)
            (show 0 < δ * Ldyadic (2 ^ (m + 1)) by positivity)
      calc
        P (A δ m) ≤
            ENNReal.ofReal
              (Var[partialSum X (2 ^ (m + 1)); P] /
                (δ * Ldyadic (2 ^ (m + 1))) ^ 2) := hkolmogorov
        _ ≤ ENNReal.ofReal
              ((V * (((2 ^ (m + 1) : ℕ) : ℝ))) /
                (δ * Ldyadic (2 ^ (m + 1))) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          exact div_le_div_of_nonneg_right
            (hvariance (2 ^ (m + 1)))
            (sq_nonneg _)
        _ = ENNReal.ofReal (g m) := by
          -- Proof comment: expand the dyadic normalization square and cancel the dyadic block
          -- size, leaving the textbook p-series denominator.
          rw [dyadic_normalization_sq (ε := ε) (δ := δ) m]
          have hpow_pos : 0 < (((2 ^ (m + 1) : ℕ) : ℝ)) := by
            positivity
          have hm_pow_pos : 0 < (m + 1 : ℝ) ^ (1 + 2 * ε) := by
            positivity
          dsimp [g]
          congr 1
          field_simp [hpow_pos.ne', hδ.ne', hm_pow_pos.ne', hlog2rpow_pos.ne']
    have htsum_lt_top : (∑' m, P (A δ m)) < ⊤ := by
      -- Proof comment: compare the finite partial sums of the event probabilities with the
      -- convergent p-series majorant, then pass to the limit.
      have hpartial :
          ∀ N, ∑ m ∈ Finset.range N, P (A δ m) ≤ ENNReal.ofReal (∑' m, g m) := by
        intro N
        calc
          ∑ m ∈ Finset.range N, P (A δ m) ≤
              ∑ m ∈ Finset.range N, ENNReal.ofReal (g m) := by
            gcongr with m hm
            exact hprob m
          _ = ENNReal.ofReal (∑ m ∈ Finset.range N, g m) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun m hm ↦ hg_nonneg m]
          _ ≤ ENNReal.ofReal (∑' m, g m) := by
            apply ENNReal.ofReal_le_ofReal
            exact sum_le_hasSum (Finset.range N) (fun m hm ↦ hg_nonneg m) hg_summable.hasSum
      exact
        (le_of_tendsto_of_tendsto'
          (ENNReal.tendsto_nat_tsum (fun m ↦ P (A δ m)))
          tendsto_const_nhds hpartial).trans_lt ENNReal.ofReal_lt_top
    have hae_not_mem : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∉ A δ m :=
      MeasureTheory.ae_eventually_notMem htsum_lt_top.ne
    filter_upwards [hae_not_mem] with ω hω
    rcases Filter.eventually_atTop.1 hω with ⟨M, hM⟩
    refine Filter.eventually_atTop.2 ?_
    refine ⟨2 ^ M, fun n hn ↦ ?_⟩
    let m : ℕ := Nat.log2 (n + 1)
    have hm_ge_M : M ≤ m := by
      -- Proof comment: once `n` lies past the dyadic threshold `2^M`, its dyadic block index is
      -- at least `M`.
      apply (Nat.le_log2 (Nat.succ_ne_zero n)).2
      exact le_trans hn (Nat.le_succ n)
    have hm_one : 1 ≤ m := by
      -- Proof comment: the eventual lower cutoff also removes the exceptional index `n = 0`.
      apply (Nat.le_log2 (Nat.succ_ne_zero n)).2
      have hpow_one : 1 ≤ 2 ^ M := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) M)
      have hn_one : 1 ≤ n := le_trans hpow_one hn
      simpa using Nat.succ_le_succ hn_one
    have h_lower : 2 ^ m ≤ n + 1 := Nat.log2_self_le (Nat.succ_ne_zero n)
    have h_upper : n + 1 ≤ 2 ^ (m + 1) := (Nat.lt_log2_self (n := n + 1)).le
    have hk_mem : n + 1 ∈ Finset.Icc 1 (2 ^ (m + 1)) := by
      refine Finset.mem_Icc.mpr ⟨?_, h_upper⟩
      have hpow_one : 1 ≤ 2 ^ m := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) m)
      exact le_trans hpow_one h_lower
    have hthreshold_lt : |partialSum X (n + 1) ω| < δ * Ldyadic (2 ^ (m + 1)) := by
      apply lt_of_not_ge
      intro hge
      exact hM m hm_ge_M ⟨n + 1, hk_mem, hge⟩
    have hLn_pos : 0 < Ldyadic (n + 1) := by
      -- Proof comment: every sufficiently large interior block index has strictly positive
      -- normalization.
      dsimp [Ldyadic]
      have hpow_two : (2 : ℕ) ≤ 2 ^ m := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm_one
        rw [hk]
        have hk : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) k)
        calc
          2 = 2 * 1 := by ring
          _ ≤ 2 * 2 ^ k := by gcongr
          _ = 2 ^ (1 + k) := by simp [pow_succ, Nat.mul_comm, Nat.add_comm]
      have htwo : (2 : ℕ) ≤ n + 1 := le_trans hpow_two h_lower
      have hlog_pos : 0 < Real.log (((n + 1 : ℕ) : ℝ)) := by
        exact Real.log_pos (by exact_mod_cast htwo)
      have hsqrt_pos : 0 < Real.sqrt (((n + 1 : ℕ) : ℝ)) := by
        exact Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos n)
      have hrpow_pos :
          0 < Real.rpow (Real.log (((n + 1 : ℕ) : ℝ))) (1 / 2 + ε) := by
        exact Real.rpow_pos_of_pos hlog_pos _
      exact mul_pos hsqrt_pos hrpow_pos
    have hscale :
        Ldyadic (2 ^ (m + 1)) ≤ Cε * Ldyadic (n + 1) := by
      -- Proof comment: compare the dyadic normalization with the normalization at an interior
      -- point of the same dyadic block.
      simpa [Ldyadic, Cε] using
        dyadic_scale_le_block_scale (ε := ε) hε hm_one h_lower h_upper
    calc
      u n ω = |partialSum X (n + 1) ω| / Ldyadic (n + 1) := by
        rfl
      _ ≤ (δ * Ldyadic (2 ^ (m + 1))) / Ldyadic (n + 1) := by
        exact div_le_div_of_nonneg_right hthreshold_lt.le hLn_pos.le
      _ ≤ (δ * (Cε * Ldyadic (n + 1))) / Ldyadic (n + 1) := by
        gcongr
      _ = Cε * δ := by
        field_simp [hLn_pos.ne']
  have hrecip :
      ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop, u n ω ≤ Cε / (((j + 1 : ℕ) : ℝ)) := by
    intro j
    -- Proof comment: specialize the fixed-threshold bound to the reciprocal thresholds
    -- `δⱼ = (j + 1)⁻¹`.
    simpa [div_eq_mul_inv, Cε, mul_assoc, mul_left_comm, mul_comm] using
      (hboundδ
        (δ := ((j + 1 : ℕ) : ℝ)⁻¹)
        (show 0 < (((j + 1 : ℕ) : ℝ)⁻¹) by positivity))
  have hall :
      ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ᶠ n in atTop, u n ω ≤ Cε / (((j + 1 : ℕ) : ℝ)) := by
    -- Proof comment: intersect the reciprocal-threshold estimates over the countable family `j`.
    exact MeasureTheory.ae_all_iff.2 hrecip
  have hCzero : Tendsto (fun j : ℕ ↦ Cε / (((j + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    -- Proof comment: the reciprocal thresholds tend to `0`, so pathwise eventual control at each
    -- reciprocal threshold is enough to prove convergence.
    convert (tendsto_const_div_atTop_nhds_zero_nat Cε).comp (tendsto_add_atTop_nat 1) using 1
  filter_upwards [hall] with ω hω
  have hω_tendsto : Tendsto (fun n : ℕ ↦ u n ω) atTop (𝓝 0) := by
    -- Proof comment: use the reciprocal-threshold eventual bounds as the neighborhood basis at
    -- `0` and combine them with the nonnegativity of the normalized sequence.
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro z hz
      exact Filter.Eventually.of_forall fun n ↦ by
        have hu_nonneg : 0 ≤ u n ω := by
          dsimp [u, Ldyadic]
          positivity
        exact lt_of_lt_of_le hz hu_nonneg
    · intro z hz
      rcases Filter.eventually_atTop.1 (hCzero.eventually (Iio_mem_nhds hz)) with ⟨j, hj⟩
      exact (hω j).mono fun n hn ↦ lt_of_le_of_lt hn (hj j le_rfl)
  -- Route correction: the previous attempt confirmed the correct dyadic skeleton and isolated the
  -- exact algebraic bottleneck in Lean. The file now contains the closed normalization identity
  -- `dyadic_normalization_sq`, the p-series helper `shifted_p_series_summable`, and the
  -- deterministic block comparison `dyadic_scale_le_block_scale`.
  -- Proof comment: after upgrading the dyadic control to pathwise convergence of the normalized
  -- sequence, the `limsup` identity is immediate.
  simpa [u, Ldyadic] using hω_tendsto.limsup_eq
