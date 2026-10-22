/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Lemma_3_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators

-- Proof sketch: use the product formula for the probability generating functions coming from the
-- independent Bernoulli summands, compare `∑' l, log (1 + p n l * (z - 1))` with
-- `(z - 1) * ∑' l, p n l` via the bound `|log (1 + x) - x| ≤ x^2`, deduce convergence of pgfs to
-- `z ↦ exp (λ * (z - 1))`, and then invoke the equivalence between pgf convergence and weak
-- convergence on `ℕ`.
/-- Helper for Theorem 3.7: the Poisson probability generating series is the exponential
`exp (λ * (z - 1))`. -/
private theorem poissonPMF_pgf_eq_exp (lam : NNReal) (z : ℝ) :
    (∑' m : ℕ, (poissonPMF lam m).toReal * z ^ m) = Real.exp (lam * (z - 1)) := by
  -- Route correction: localize the Poisson pgf computation here so the theorem no longer depends
  -- on the broken `Example_3_4` item file.
  have hseries :
      HasSum (fun n : ℕ ↦ Real.exp (-((lam : ℝ))) * (((lam : ℝ) * z) ^ n / ↑n.factorial))
        (Real.exp (-((lam : ℝ))) * Real.exp ((lam : ℝ) * z)) := by
    -- This is the exponential power series, scaled by the constant factor `exp (-λ)`.
    simpa [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * z)).mul_left (Real.exp (-((lam : ℝ))))
  -- Rewrite the Poisson coefficients into the exponential-series normal form.
  calc
    ∑' n : ℕ, (poissonPMF lam n).toReal * z ^ n
      = ∑' n : ℕ, Real.exp (-((lam : ℝ))) * (((lam : ℝ) * z) ^ n / ↑n.factorial) := by
          refine tsum_congr fun n ↦ ?_
          rw [← ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF]
          rw [ENNReal.toReal_ofReal ProbabilityTheory.poissonPMFReal_nonneg]
          rw [ProbabilityTheory.poissonPMFReal]
          have hfac : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
          field_simp [hfac]
          ring
    _ = Real.exp (-((lam : ℝ))) * Real.exp ((lam : ℝ) * z) := hseries.tsum_eq
    _ = Real.exp (lam * (z - 1)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- Helper for Theorem 3.7: the source-proof bound `(∑ p_{n,l}) * sup_l p_{n,l}` tends to zero. -/
private theorem row_sum_mul_iSup_tendsto_zero
    (p : ℕ → ℕ → NNReal) (lam : NNReal)
    (hsum : Tendsto (fun n ↦ ∑' l : ℕ, p n l) atTop (𝓝 lam))
    (hmax : Tendsto (fun n ↦ ⨆ l : ℕ, p n l) atTop (𝓝 0)) :
    Tendsto
      (fun n ↦ (((∑' l : ℕ, p n l : NNReal) : ℝ) * (((⨆ l : ℕ, p n l : NNReal) : ℝ))))
      atTop (𝓝 0) := by
  have hsum_real :
      Tendsto (fun n ↦ ((∑' l : ℕ, p n l : NNReal) : ℝ)) atTop (𝓝 (lam : ℝ)) :=
    (NNReal.continuous_coe.tendsto lam).comp hsum
  have hmax_real : Tendsto (fun n ↦ ((⨆ l : ℕ, p n l : NNReal) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    (NNReal.continuous_coe.tendsto 0).comp hmax
  simpa using hsum_real.mul hmax_real

/-- Helper for Theorem 3.7: if `|x| ≤ 1 / 2`, then the logarithm is linear up to a quadratic
remainder. -/
private theorem real_log_one_add_sub_self_le_sq {x : ℝ} (hx0 : 0 < 1 + x) (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ x ^ 2 := by
  -- Transfer the standard complex logarithm estimate to the real line.
  have hxlt : |x| < 1 := lt_of_le_of_lt hx (by norm_num)
  have hcomplex :=
    Complex.norm_log_one_add_sub_self_le (z := (x : ℂ))
      (by simpa [Complex.norm_real, Real.norm_eq_abs] using hxlt)
  have hlog :
      Complex.log (1 + (x : ℂ)) = ((Real.log (1 + x) : ℝ) : ℂ) := by
    rw [show (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) by norm_num]
    exact (Complex.ofReal_log (show 0 ≤ 1 + x by linarith)).symm
  have hnorm :
      ‖((Real.log (1 + x) : ℝ) : ℂ) - (x : ℂ)‖ ≤ ‖(x : ℂ)‖ ^ 2 * (1 - ‖(x : ℂ)‖)⁻¹ / 2 := by
    simpa [hlog] using hcomplex
  have haux : |Real.log (1 + x) - x| ≤ x ^ 2 * (1 - |x|)⁻¹ / 2 := by
    -- Rewrite the complex norm back to an absolute value on `ℝ`.
    rw [← show ‖((Real.log (1 + x) : ℝ) : ℂ) - (x : ℂ)‖ = |Real.log (1 + x) - x| by
      rw [← Complex.ofReal_sub]
      simpa [Real.norm_eq_abs] using (Complex.norm_real (Real.log (1 + x) - x))]
    simpa [Complex.norm_real, Real.norm_eq_abs] using hnorm
  have hinv : (1 - |x|)⁻¹ ≤ (2 : ℝ) := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - |x| := by
      nlinarith
    simpa [one_div] using
      (one_div_le (by nlinarith) (by norm_num : (0 : ℝ) < 2)).2 hhalf
  have hfactor : (1 - |x|)⁻¹ / 2 ≤ (1 : ℝ) := by
    exact (div_le_one (by norm_num : (0 : ℝ) < 2)).2 hinv
  calc
    |Real.log (1 + x) - x| ≤ x ^ 2 * (1 - |x|)⁻¹ / 2 := haux
    _ = x ^ 2 * ((1 - |x|)⁻¹ / 2) := by ring
    _ ≤ x ^ 2 * 1 := by
      exact mul_le_mul_of_nonneg_left hfactor (sq_nonneg x)
    _ = x ^ 2 := by ring

/-- Helper for Theorem 3.7: once a row is summable and the factors stay positive, its product can
be rewritten as the exponential of the logarithmic series. -/
private theorem row_product_eq_exp_tsum_log
    (p : ℕ → NNReal) (a : ℝ)
    (hpSummable : Summable fun l : ℕ ↦ (p l : ℝ))
    (hpos : ∀ l : ℕ, 0 < 1 + (p l : ℝ) * a) :
    ∏' l : ℕ, (1 + (p l : ℝ) * a) = Real.exp (∑' l : ℕ, Real.log (1 + (p l : ℝ) * a)) := by
  -- Use the standard real infinite-product identity for a convergent logarithmic series.
  symm
  exact
    Real.rexp_tsum_eq_tprod hpos
      (Real.summable_log_one_add_of_summable (hpSummable.mul_right a))

/-- Helper for Theorem 3.7: each Bernoulli factor rewrites into the logarithm-friendly form
`1 + p (z - 1)`. -/
private theorem bernoulli_factor_eq_one_add (p : NNReal) (z : ℝ) :
    (p : ℝ) * z + (1 - (p : ℝ)) = 1 + (p : ℝ) * (z - 1) := by
  ring

/-- Helper for Theorem 3.7: every probability mass function has a strictly positive generating
series at each point of `(0,1)`. -/
private theorem pmf_series_pos_on_Ioo (μ : PMF ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    0 < ∑' m : ℕ, (μ m).toReal * z ^ m := by
  have hsummable : Summable (fun m : ℕ ↦ (μ m).toReal * z ^ m) :=
    pgf_series_summable μ (le_of_lt hz0) hz1
  have hmass_exists : ∃ k : ℕ, (μ k).toReal ≠ 0 := by
    by_contra hmass
    have hzero : ∀ k : ℕ, (μ k).toReal = 0 := by
      simpa using hmass
    have htsum_zero : ∑' k : ℕ, (μ k).toReal = 0 := by
      simp [hzero]
    linarith [pmf_toReal_tsum_eq_one μ]
  rcases hmass_exists with ⟨k, hk_nonzero⟩
  have hk_mass_pos : 0 < (μ k).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hk_nonzero)
  have hk_term_pos : 0 < (μ k).toReal * z ^ k := by
    exact mul_pos hk_mass_pos (pow_pos hz0 _)
  have hterm_nonneg : ∀ m : ℕ, 0 ≤ (μ m).toReal * z ^ m := by
    intro m
    exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz0.le _)
  have hterm_le_tsum :
      (μ k).toReal * z ^ k ≤ ∑' m : ℕ, (μ m).toReal * z ^ m := by
    simpa using
      (hsummable.sum_le_tsum ({k} : Finset ℕ) (by
        intro i hi
        exact hterm_nonneg i))
  exact lt_of_lt_of_le hk_term_pos hterm_le_tsum

/-- Helper for Theorem 3.7: every probability mass function has a strictly positive generating
series at `z = 1 / 2`. -/
private theorem pmf_series_pos_at_half (μ : PMF ℕ) :
    0 < ∑' m : ℕ, (μ m).toReal * (1 / 2 : ℝ) ^ m := by
  -- Specialize the interior positivity statement to the fixed point `z = 1 / 2`.
  simpa using pmf_series_pos_on_Ioo (μ := μ) (z := (1 / 2 : ℝ)) (by norm_num) (by norm_num)

/-- Helper for Theorem 3.7: the pgf factorization forces each Bernoulli parameter to lie in
`[0,1]`. -/
private theorem row_entry_le_one_of_hpgf
    (μ : PMF ℕ) (p : ℕ → NNReal)
    (hpgf :
      ∀ z : Set.Icc (0 : ℝ) 1,
        (∑' m : ℕ, (μ m).toReal * (z : ℝ) ^ m) =
          ∏' l : ℕ, ((p l : ℝ) * (z : ℝ) + (1 - (p l : ℝ)))) :
    ∀ l : ℕ, (p l : ℝ) ≤ 1 := by
  intro l
  by_contra hp
  have hp_one_lt : 1 < (p l : ℝ) := lt_of_not_ge hp
  have hp_pos : 0 < (p l : ℝ) := by linarith
  let z : ℝ := 1 - (p l : ℝ)⁻¹
  have hz_mem : z ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · dsimp [z]
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp_one_lt.le)
    · dsimp [z]
      linarith [inv_pos.mpr hp_pos]
  have hz_pos : 0 < z := by
    dsimp [z]
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp_one_lt)
  have hz_lt : z < 1 := by
    dsimp [z]
    linarith [inv_pos.mpr hp_pos]
  have hfactor_zero : (p l : ℝ) * z + (1 - (p l : ℝ)) = 0 := by
    dsimp [z]
    field_simp [show (p l : ℝ) ≠ 0 by linarith]
    ring
  have hproduct_zero :
      ∏' j : ℕ, ((p j : ℝ) * z + (1 - (p j : ℝ))) = 0 := by
    exact
      (hasProd_zero_of_exists_eq_zero
        (f := fun j : ℕ ↦ ((p j : ℝ) * z + (1 - (p j : ℝ))))
        ⟨l, hfactor_zero⟩).tprod_eq
  have hseries_zero : ∑' m : ℕ, (μ m).toReal * z ^ m = 0 := by
    rw [hpgf ⟨z, hz_mem⟩, hproduct_zero]
  have hseries_pos : 0 < ∑' m : ℕ, (μ m).toReal * z ^ m := pmf_series_pos_on_Ioo μ hz_pos hz_lt
  rw [hseries_zero] at hseries_pos
  linarith

/-- Helper for Theorem 3.7: if a row is not summable but stays below `1`, then its half-point
Bernoulli product converges to `0`. -/
private theorem rowHalfPrefixProductLeExpNegHalfSum
    (p : ℕ → NNReal)
    (hbound : ∀ l : ℕ, (p l : ℝ) ≤ 1)
    (N : ℕ) :
    ∏ l ∈ Finset.range N, (1 - (p l : ℝ) / 2) ≤
      Real.exp (-(1 / 2 : ℝ) * ∑ l ∈ Finset.range N, (p l : ℝ)) := by
  -- Compare each Bernoulli half-factor with the corresponding exponential term.
  have hterm :
      ∀ l : ℕ, 1 - (p l : ℝ) / 2 ≤ Real.exp (-(p l : ℝ) / 2) := by
    intro l
    have hpos : 0 < 1 - (p l : ℝ) / 2 := by
      have hp_lt_two : (p l : ℝ) < 2 := lt_of_le_of_lt (hbound l) (by norm_num)
      nlinarith
    have hlog : Real.log (1 - (p l : ℝ) / 2) ≤ -(p l : ℝ) / 2 := by
      have hlog_aux : Real.log (1 - (p l : ℝ) / 2) ≤ (1 - (p l : ℝ) / 2) - 1 :=
        Real.log_le_sub_one_of_pos hpos
      linarith
    have hexp :
        Real.exp (Real.log (1 - (p l : ℝ) / 2)) ≤ Real.exp (-(p l : ℝ) / 2) :=
      Real.exp_le_exp.mpr hlog
    simpa [Real.exp_log hpos] using hexp
  have hfactor_nonneg :
      ∀ l : ℕ, 0 ≤ 1 - (p l : ℝ) / 2 := by
    intro l
    have hp_nonneg : 0 ≤ (p l : ℝ) := NNReal.coe_nonneg _
    nlinarith [hbound l]
  have hexp_prod :
      ∀ n : ℕ,
        ∏ l ∈ Finset.range n, Real.exp (-(p l : ℝ) / 2) =
          Real.exp (∑ l ∈ Finset.range n, (-(p l : ℝ) / 2)) := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Finset.prod_range_succ, Finset.sum_range_succ, ih, ← Real.exp_add]
  calc
    ∏ l ∈ Finset.range N, (1 - (p l : ℝ) / 2) ≤
        ∏ l ∈ Finset.range N, Real.exp (-(p l : ℝ) / 2) := by
          induction N with
          | zero =>
              simp
          | succ n ih =>
              rw [Finset.prod_range_succ, Finset.prod_range_succ]
              have hprefix_nonneg :
                  0 ≤ ∏ l ∈ Finset.range n, (1 - (p l : ℝ) / 2) := by
                refine Finset.prod_nonneg ?_
                intro l hl
                exact hfactor_nonneg l
              calc
                (∏ l ∈ Finset.range n, (1 - (p l : ℝ) / 2)) * (1 - (p n : ℝ) / 2) ≤
                    (∏ l ∈ Finset.range n, (1 - (p l : ℝ) / 2)) *
                      Real.exp (-(p n : ℝ) / 2) := by
                        exact mul_le_mul_of_nonneg_left (hterm n) hprefix_nonneg
                _ ≤ (∏ l ∈ Finset.range n, Real.exp (-(p l : ℝ) / 2)) *
                      Real.exp (-(p n : ℝ) / 2) := by
                        exact mul_le_mul_of_nonneg_right ih (le_of_lt (Real.exp_pos _))
    _ = Real.exp (∑ l ∈ Finset.range N, (-(p l : ℝ) / 2)) := hexp_prod N
    _ = Real.exp (-(1 / 2 : ℝ) * ∑ l ∈ Finset.range N, (p l : ℝ)) := by
      congr 1
      calc
        ∑ l ∈ Finset.range N, (-(p l : ℝ) / 2)
            = ∑ l ∈ Finset.range N, (-(1 / 2 : ℝ)) * (p l : ℝ) := by
                refine Finset.sum_congr rfl ?_
                intro l hl
                ring
        _ = (-(1 / 2 : ℝ)) * ∑ l ∈ Finset.range N, (p l : ℝ) := by
              rw [← Finset.mul_sum]
        _ = -(1 / 2 : ℝ) * ∑ l ∈ Finset.range N, (p l : ℝ) := rfl

/-- Helper for Theorem 3.7: if a row is not summable but stays below `1`, then its half-point
Bernoulli product converges to `0`. -/
private theorem row_half_product_hasProd_zero_of_not_summable
    (p : ℕ → NNReal)
    (hbound : ∀ l : ℕ, (p l : ℝ) ≤ 1)
    (hnot : ¬ Summable fun l : ℕ ↦ (p l : ℝ)) :
    HasProd (fun l : ℕ ↦ (1 - (p l : ℝ) / 2)) 0 := by
  let factor : ℕ → ℝ := fun l ↦ 1 - (p l : ℝ) / 2
  let factorNN : ℕ → NNReal := fun l ↦ (factor l).toNNReal
  have hfactor_nonneg : ∀ l : ℕ, 0 ≤ factor l := by
    intro l
    have hp_nonneg : 0 ≤ (p l : ℝ) := NNReal.coe_nonneg _
    dsimp [factor]
    nlinarith [hbound l]
  have hfactor_le_one : ∀ l : ℕ, factor l ≤ 1 := by
    intro l
    have hp_nonneg : 0 ≤ (p l : ℝ) := NNReal.coe_nonneg _
    dsimp [factor]
    nlinarith
  have hnotNN : ¬ Summable p := by
    simpa [NNReal.summable_coe] using hnot
  have hsum_atTopNN :
      Tendsto (fun N : ℕ ↦ ∑ l ∈ Finset.range N, p l) atTop atTop :=
    (NNReal.not_summable_iff_tendsto_nat_atTop).1 hnotNN
  have hsum_atTop :
      Tendsto (fun N : ℕ ↦ ∑ l ∈ Finset.range N, (p l : ℝ)) atTop atTop := by
    -- The non-summable row has divergent prefix sums.
    simpa [NNReal.coe_sum] using (NNReal.tendsto_coe_atTop).2 hsum_atTopNN
  have hscaled_atTop :
      Tendsto (fun N : ℕ ↦ (1 / 2 : ℝ) * ∑ l ∈ Finset.range N, (p l : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop' (by norm_num) hsum_atTop
  have hexp_tendsto :
      Tendsto
        (fun N : ℕ ↦ Real.exp (-(1 / 2 : ℝ) * ∑ l ∈ Finset.range N, (p l : ℝ)))
        atTop (𝓝 0) := by
    -- The exponential comparison from the source proof therefore vanishes.
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled_atTop using 1
    ext N
    congr 1
    ring
  have hprefix_nonneg :
      ∀ N : ℕ, 0 ≤ ∏ l ∈ Finset.range N, factor l := by
    intro N
    refine Finset.prod_nonneg ?_
    intro l hl
    exact hfactor_nonneg l
  have hprefix_tendsto_real :
      Tendsto (fun N : ℕ ↦ ∏ l ∈ Finset.range N, factor l) atTop (𝓝 0) := by
    -- Squeeze the partial products between `0` and the vanishing exponential bound.
    refine squeeze_zero'
      (Eventually.of_forall hprefix_nonneg)
      ?_ hexp_tendsto
    exact Eventually.of_forall (rowHalfPrefixProductLeExpNegHalfSum p hbound)
  have hfactorNN_coe : ∀ l : ℕ, ((factorNN l : NNReal) : ℝ) = factor l := by
    intro l
    simp [factorNN, factor, Real.toNNReal_of_nonneg, hfactor_nonneg l]
  have hprefix_tendsto_nnreal :
      Tendsto (fun N : ℕ ↦ ∏ l ∈ Finset.range N, factorNN l) atTop (𝓝 (0 : NNReal)) := by
    -- Move the vanishing prefix products into `NNReal`, where `HasProd` can be reconstructed
    -- from the infimum of finite products.
    refine (NNReal.tendsto_coe).1 ?_
    simpa [factorNN, factor, hfactorNN_coe] using hprefix_tendsto_real
  have hfactorNN_le_one : ∀ l : ℕ, factorNN l ≤ 1 := by
    intro l
    rw [← NNReal.coe_le_coe]
    simpa [hfactorNN_coe l] using hfactor_le_one l
  have hanti_full : Antitone fun s : Finset ℕ ↦ ∏ l ∈ s, factorNN l :=
    Finset.prod_anti_set_of_le_one' hfactorNN_le_one
  have hanti_range : Antitone fun N : ℕ ↦ ∏ l ∈ Finset.range N, factorNN l := by
    intro m n hmn
    exact hanti_full (Finset.range_mono hmn)
  have hglb_range :
      IsGLB (Set.range fun N : ℕ ↦ ∏ l ∈ Finset.range N, factorNN l) 0 :=
    isGLB_of_tendsto_atTop hanti_range hprefix_tendsto_nnreal
  have hlowerBounds :
      lowerBounds (Set.range fun N : ℕ ↦ ∏ l ∈ Finset.range N, factorNN l) =
        lowerBounds (Set.range fun s : Finset ℕ ↦ ∏ l ∈ s, factorNN l) := by
    simpa [Function.comp] using
      hanti_full.lowerBounds_range_comp_tendsto_atTop Filter.tendsto_finset_range
  have hglb_full :
      IsGLB (Set.range fun s : Finset ℕ ↦ ∏ l ∈ s, factorNN l) 0 := by
    refine ⟨?_, ?_⟩
    · rw [← hlowerBounds]
      exact hglb_range.1
    · intro b hb
      exact hglb_range.2 (by rw [hlowerBounds]; exact hb)
  have hhasProdNN : HasProd factorNN 0 :=
    hasProd_of_isGLB_of_le_one 0 hfactorNN_le_one hglb_full
  have hhasProdReal : HasProd (fun l : ℕ ↦ ((factorNN l : NNReal) : ℝ)) 0 :=
    hhasProdNN.map NNReal.toRealHom NNReal.continuous_coe
  -- Finally identify the `NNReal` factors with the original real factors.
  exact hhasProdReal.congr_fun (fun l ↦ (hfactorNN_coe l).symm)

/-- Helper for Theorem 3.7: the original `hpgf` and `hmax` hypotheses already force eventual
rowwise summability. -/
private theorem eventually_row_summable_of_hpgf_and_hmax
    (μ : ℕ → PMF ℕ) (p : ℕ → ℕ → NNReal)
    (hpgf :
      ∀ n (z : Set.Icc (0 : ℝ) 1),
        (∑' m : ℕ, (μ n m).toReal * (z : ℝ) ^ m) =
          ∏' l : ℕ, ((p n l : ℝ) * (z : ℝ) + (1 - (p n l : ℝ))))
    (_hmax : Tendsto (fun n ↦ ⨆ l : ℕ, p n l) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, Summable fun l : ℕ ↦ (p n l : ℝ) := by
  let hentry_le_one : ∀ n l : ℕ, (p n l : ℝ) ≤ 1 := fun n l ↦
    row_entry_le_one_of_hpgf (μ := μ n) (p := p n) (hpgf := hpgf n) l
  -- Any non-summable row would make the half-point product vanish, contradicting positivity of the
  -- pmf generating series.
  refine Eventually.of_forall fun n ↦ ?_
  by_contra hnot
  have hbound_one : ∀ l : ℕ, (p n l : ℝ) ≤ 1 := hentry_le_one n
  have hhalfProdZero :
      HasProd (fun l : ℕ ↦ (1 - (p n l : ℝ) / 2)) 0 :=
    row_half_product_hasProd_zero_of_not_summable (p := p n) hbound_one hnot
  have hsource_zero :
      (∑' m : ℕ, (μ n m).toReal * (1 / 2 : ℝ) ^ m) = 0 := by
    calc
      ∑' m : ℕ, (μ n m).toReal * (1 / 2 : ℝ) ^ m =
          ∏' l : ℕ, ((p n l : ℝ) * (1 / 2 : ℝ) + (1 - (p n l : ℝ))) := by
            exact hpgf n ⟨1 / 2, by norm_num⟩
      _ = ∏' l : ℕ, (1 - (p n l : ℝ) / 2) := by
            refine tprod_congr ?_
            intro l
            ring
      _ = 0 := hhalfProdZero.tprod_eq
  -- But every pmf has a strictly positive generating series at `z = 1 / 2`.
  have hpositive : 0 < ∑' m : ℕ, (μ n m).toReal * (1 / 2 : ℝ) ^ m := pmf_series_pos_at_half (μ n)
  rw [hsource_zero] at hpositive
  linarith

/-- Helper for Theorem 3.7: if a row is bounded by a small real number, then every logarithmic
factor stays strictly positive on `[0,1]`. -/
private theorem row_factor_pos_of_row_bound
    (p : ℕ → NNReal) (z : Set.Icc (0 : ℝ) 1) (rowSup : ℝ)
    (hbound : ∀ l : ℕ, (p l : ℝ) ≤ rowSup)
    (hsmall : rowSup ≤ 1 / 2) :
    ∀ l : ℕ, 0 < 1 + (p l : ℝ) * ((z : ℝ) - 1) := by
  intro l
  -- The explicit row bound keeps every factor above `1 - rowSup`.
  have hp_nonneg : 0 ≤ (p l : ℝ) := NNReal.coe_nonneg _
  have hp_le_half : (p l : ℝ) ≤ 1 / 2 := (hbound l).trans hsmall
  have hz_lower : (-1 : ℝ) ≤ (z : ℝ) - 1 := by
    linarith [z.2.1]
  have hz_upper : (z : ℝ) - 1 ≤ 0 := by
    linarith [z.2.2]
  nlinarith

/-- Helper for Theorem 3.7: under an explicit row bound, the logarithmic series differs from its
linear part by at most `(row sum) * rowSup`. -/
private theorem row_log_linearization_error_le
    (p : ℕ → NNReal) (z : Set.Icc (0 : ℝ) 1) (rowSup : ℝ)
    (hpSummable : Summable fun l : ℕ ↦ (p l : ℝ))
    (hbound : ∀ l : ℕ, (p l : ℝ) ≤ rowSup)
    (hsmall : rowSup ≤ 1 / 2) :
    |(∑' l : ℕ, Real.log (1 + (p l : ℝ) * ((z : ℝ) - 1))) -
        (((z : ℝ) - 1) * ∑' l : ℕ, (p l : ℝ))| ≤
      (((∑' l : ℕ, p l : NNReal) : ℝ) * rowSup) := by
  let a : ℝ := (z : ℝ) - 1
  have ha_nonpos : a ≤ 0 := by
    dsimp [a]
    linarith [z.2.2]
  have ha_abs_le_one : |a| ≤ 1 := by
    -- On `[0,1]`, the shift `z - 1` lies in `[-1,0]`.
    rw [abs_of_nonpos ha_nonpos]
    dsimp [a]
    linarith [z.2.1]
  have hpSummableNN : Summable p := NNReal.summable_coe.1 hpSummable
  have hlinearSummable : Summable fun l : ℕ ↦ (p l : ℝ) * a := hpSummable.mul_right a
  have hlogSummable :
      Summable fun l : ℕ ↦ Real.log (1 + (p l : ℝ) * a) := by
    exact Real.summable_log_one_add_of_summable hlinearSummable
  have hboundSummable : Summable fun l : ℕ ↦ (p l : ℝ) * rowSup := hpSummable.mul_right rowSup
  have hterm_bound :
      ∀ l : ℕ, |Real.log (1 + (p l : ℝ) * a) - (p l : ℝ) * a| ≤ (p l : ℝ) * rowSup := by
    intro l
    have hp_nonneg : 0 ≤ (p l : ℝ) := NNReal.coe_nonneg _
    have hp_le_sup : (p l : ℝ) ≤ rowSup := hbound l
    have hx_abs :
        |(p l : ℝ) * a| ≤ 1 / 2 := by
      calc
        |(p l : ℝ) * a| = (p l : ℝ) * |a| := by
          rw [abs_mul, abs_of_nonneg hp_nonneg]
        _ ≤ (p l : ℝ) * 1 := by
          exact mul_le_mul_of_nonneg_left ha_abs_le_one hp_nonneg
        _ = (p l : ℝ) := by ring
        _ ≤ rowSup := hp_le_sup
        _ ≤ 1 / 2 := hsmall
    have hlog_bound :
        |Real.log (1 + (p l : ℝ) * a) - (p l : ℝ) * a| ≤ ((p l : ℝ) * a) ^ 2 :=
      real_log_one_add_sub_self_le_sq
        (row_factor_pos_of_row_bound p z rowSup hbound hsmall l) hx_abs
    have ha_sq_le_one : a ^ 2 ≤ 1 := by
      calc
        a ^ 2 = |a| ^ 2 := by rw [sq_abs]
        _ ≤ 1 ^ 2 := by
          gcongr
        _ = 1 := by norm_num
    calc
      |Real.log (1 + (p l : ℝ) * a) - (p l : ℝ) * a| ≤ ((p l : ℝ) * a) ^ 2 := hlog_bound
      _ = ((p l : ℝ) ^ 2) * (a ^ 2) := by ring
      _ ≤ ((p l : ℝ) ^ 2) * 1 := by
        exact mul_le_mul_of_nonneg_left ha_sq_le_one (sq_nonneg (p l : ℝ))
      _ = (p l : ℝ) * (p l : ℝ) := by ring
      _ ≤ (p l : ℝ) * rowSup := by
        exact mul_le_mul_of_nonneg_left hp_le_sup hp_nonneg
  have habsSummable :
      Summable fun l : ℕ ↦ |Real.log (1 + (p l : ℝ) * a) - (p l : ℝ) * a| :=
    Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) hterm_bound hboundSummable
  have htsum_bound :
      |∑' l : ℕ, (Real.log (1 + (p l : ℝ) * a) - (p l : ℝ) * a)| ≤
        ∑' l : ℕ, (p l : ℝ) * rowSup := by
    calc
      |∑' l : ℕ, (Real.log (1 + (p l : ℝ) * a) - (p l : ℝ) * a)| ≤
          ∑' l : ℕ, |Real.log (1 + (p l : ℝ) * a) - (p l : ℝ) * a| := by
            simpa [Real.norm_eq_abs] using
              (norm_tsum_le_tsum_norm
                (f := fun l : ℕ ↦ Real.log (1 + (p l : ℝ) * a) - (p l : ℝ) * a)
                (by simpa [Real.norm_eq_abs] using habsSummable))
      _ ≤ ∑' l : ℕ, (p l : ℝ) * rowSup :=
        habsSummable.tsum_le_tsum hterm_bound hboundSummable
  have hsumReal :
      ((∑' l : ℕ, p l : NNReal) : ℝ) = ∑' l : ℕ, (p l : ℝ) := by
    rw [NNReal.coe_tsum]
  -- Rewrite both sides into the exact source-proof shape.
  rw [hlogSummable.tsum_sub hlinearSummable, tsum_mul_right, mul_comm] at htsum_bound
  have hright :
      (∑' l : ℕ, (p l : ℝ) * rowSup) = ((∑' l : ℕ, p l : NNReal) : ℝ) * rowSup := by
    rw [tsum_mul_right, ← hsumReal]
  have hfinal :
      |(∑' l : ℕ, Real.log (1 + (p l : ℝ) * a)) - (a * ∑' l : ℕ, (p l : ℝ))| ≤
        ((∑' l : ℕ, p l : NNReal) : ℝ) * rowSup := by
    calc
      |(∑' l : ℕ, Real.log (1 + (p l : ℝ) * a)) - (a * ∑' l : ℕ, (p l : ℝ))| ≤
          ∑' l : ℕ, (p l : ℝ) * rowSup := htsum_bound
      _ = ((∑' l : ℕ, p l : NNReal) : ℝ) * rowSup := hright
  simpa [a] using hfinal

/-- Helper for Theorem 3.7: if the real row bounds tend to `0`, then the source-proof error term
also tends to `0`. -/
private theorem row_sum_mul_bound_tendsto_zero
    (p : ℕ → ℕ → NNReal) (rowSup : ℕ → ℝ) (lam : NNReal)
    (hsum : Tendsto (fun n ↦ ∑' l : ℕ, p n l) atTop (𝓝 lam))
    (hrowSup : Tendsto rowSup atTop (𝓝 0)) :
    Tendsto (fun n ↦ (((∑' l : ℕ, p n l : NNReal) : ℝ) * rowSup n)) atTop (𝓝 0) := by
  have hsum_real :
      Tendsto (fun n ↦ ((∑' l : ℕ, p n l : NNReal) : ℝ)) atTop (𝓝 (lam : ℝ)) :=
    (NNReal.continuous_coe.tendsto lam).comp hsum
  simpa using hsum_real.mul hrowSup

/-- Helper for Theorem 3.7: under rowwise summability and an explicit vanishing row bound, the
logarithmic exponents converge to the Poisson exponent. -/
private theorem row_log_exponent_tendsto
    (p : ℕ → ℕ → NNReal) (rowSup : ℕ → ℝ) (lam : NNReal) (z : Set.Icc (0 : ℝ) 1)
    (hsummable : ∀ᶠ n in atTop, Summable fun l : ℕ ↦ (p n l : ℝ))
    (hbound : ∀ᶠ n in atTop, ∀ l : ℕ, (p n l : ℝ) ≤ rowSup n)
    (hsum : Tendsto (fun n ↦ ∑' l : ℕ, p n l) atTop (𝓝 lam))
    (hrowSup : Tendsto rowSup atTop (𝓝 0)) :
    Tendsto
      (fun n ↦ ∑' l : ℕ, Real.log (1 + (p n l : ℝ) * ((z : ℝ) - 1)))
      atTop (𝓝 ((lam : ℝ) * ((z : ℝ) - 1))) := by
  let a : ℝ := (z : ℝ) - 1
  let exponent : ℕ → ℝ := fun n ↦ ∑' l : ℕ, Real.log (1 + (p n l : ℝ) * a)
  let linear : ℕ → ℝ := fun n ↦ a * ∑' l : ℕ, (p n l : ℝ)
  have hsum_real :
      Tendsto (fun n ↦ ∑' l : ℕ, (p n l : ℝ)) atTop (𝓝 (lam : ℝ)) := by
    have hsum_real_coe :
        Tendsto (fun n ↦ ((∑' l : ℕ, p n l : NNReal) : ℝ)) atTop (𝓝 (lam : ℝ)) :=
      (NNReal.continuous_coe.tendsto lam).comp hsum
    refine Tendsto.congr' ?_ hsum_real_coe
    filter_upwards with n
    symm
    rw [NNReal.coe_tsum]
  have hlinear :
      Tendsto linear atTop (𝓝 (a * (lam : ℝ))) := by
    simpa [linear] using hsum_real.const_mul a
  have hhalf : ∀ᶠ n in atTop, rowSup n < 1 / 2 :=
    hrowSup.eventually (Iio_mem_nhds (by norm_num))
  have herror_abs :
      Tendsto (fun n ↦ |exponent n - linear n|) atTop (𝓝 0) := by
    -- The rowwise logarithmic error is squeezed by `(row sum) * rowSup`.
    refine squeeze_zero'
      (Eventually.of_forall fun n ↦ abs_nonneg (exponent n - linear n)) ?_
      (row_sum_mul_bound_tendsto_zero p rowSup lam hsum hrowSup)
    filter_upwards [hhalf, hsummable, hbound] with n hn hsummable_n hbound_n
    simpa [exponent, linear, a] using
      row_log_linearization_error_le (p := p n) (z := z) (rowSup := rowSup n)
        hsummable_n hbound_n (le_of_lt hn)
  have herror :
      Tendsto (fun n ↦ exponent n - linear n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using herror_abs
  -- Add back the linear term, whose limit is controlled by the row sums.
  simpa [exponent, linear, a, sub_add_cancel, mul_comm, mul_left_comm, mul_assoc] using
    herror.add hlinear

/-- Helper for Theorem 3.7: the textbook logarithm-linearization proof closes once each row of
Bernoulli parameters is summable and dominated by a real row bound tending to `0`. -/
private theorem pgf_converges_on_unit_interval_to_poisson_of_row_summable
    (μ : ℕ → PMF ℕ) (p : ℕ → ℕ → NNReal) (rowSup : ℕ → ℝ) (lam : NNReal)
    (hpgf :
      ∀ n (z : Set.Icc (0 : ℝ) 1),
        (∑' m : ℕ, (μ n m).toReal * (z : ℝ) ^ m) =
          ∏' l : ℕ, ((p n l : ℝ) * (z : ℝ) + (1 - (p n l : ℝ))))
    (hsummable : ∀ᶠ n in atTop, Summable fun l : ℕ ↦ (p n l : ℝ))
    (hbound : ∀ᶠ n in atTop, ∀ l : ℕ, (p n l : ℝ) ≤ rowSup n)
    (hsum : Tendsto (fun n ↦ ∑' l : ℕ, p n l) atTop (𝓝 lam))
    (hrowSup : Tendsto rowSup atTop (𝓝 0)) :
    probabilityGeneratingFunctionsConvergeOnUnitInterval μ (poissonPMF lam) := by
  rw [probabilityGeneratingFunctionsConvergeOnUnitInterval_iff]
  intro z hz
  by_cases hzEq : z = 1
  · subst hzEq
    -- At `z = 1`, both pgfs are identically `1`.
    have hsource_const :
        (fun n : ℕ ↦ ∑' m : ℕ, (μ n m).toReal * (1 : ℝ) ^ m) = fun _ ↦ (1 : ℝ) := by
      funext n
      calc
        ∑' m : ℕ, (μ n m).toReal * (1 : ℝ) ^ m =
            ∏' l : ℕ, ((p n l : ℝ) * (1 : ℝ) + (1 - (p n l : ℝ))) := hpgf n ⟨1, by norm_num⟩
        _ = 1 := by simp
    rw [hsource_const]
    have htarget_one : ∑' m : ℕ, (poissonPMF lam m).toReal * (1 : ℝ) ^ m = 1 := by
      simpa using pmf_toReal_tsum_eq_one (poissonPMF lam)
    rw [htarget_one]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 (1 : ℝ)))
  · let zI : Set.Icc (0 : ℝ) 1 := ⟨z, hz⟩
    have hhalf : ∀ᶠ n in atTop, rowSup n < 1 / 2 :=
      hrowSup.eventually (Iio_mem_nhds (by norm_num))
    have hsource_eq :
        (fun n : ℕ ↦ ∑' m : ℕ, (μ n m).toReal * z ^ m) =ᶠ[atTop]
          (fun n ↦ Real.exp (∑' l : ℕ, Real.log (1 + (p n l : ℝ) * (z - 1)))) := by
      filter_upwards [hhalf, hsummable, hbound] with n hn hsummable_n hbound_n
      calc
        ∑' m : ℕ, (μ n m).toReal * z ^ m =
            ∏' l : ℕ, ((p n l : ℝ) * z + (1 - (p n l : ℝ))) := hpgf n zI
        _ = ∏' l : ℕ, (1 + (p n l : ℝ) * (z - 1)) := by
          refine tprod_congr ?_
          intro l
          simpa using bernoulli_factor_eq_one_add (p := p n l) z
        _ = Real.exp (∑' l : ℕ, Real.log (1 + (p n l : ℝ) * (z - 1))) :=
          row_product_eq_exp_tsum_log (p := p n) (a := z - 1) hsummable_n
            (row_factor_pos_of_row_bound (p := p n) (z := zI) (rowSup := rowSup n) hbound_n
              (le_of_lt hn))
    have hexp :
        Tendsto
          (fun n ↦ Real.exp (∑' l : ℕ, Real.log (1 + (p n l : ℝ) * (z - 1))))
          atTop (𝓝 (Real.exp ((lam : ℝ) * (z - 1)))) := by
      exact
        (Real.continuous_exp.tendsto ((lam : ℝ) * (z - 1))).comp
          (row_log_exponent_tendsto (p := p) (rowSup := rowSup) (lam := lam) (z := zI)
            hsummable hbound hsum hrowSup)
    -- Rewrite the source series into the exponential form and then use continuity of `exp`.
    refine Tendsto.congr' hsource_eq.symm ?_
    simpa [poissonPMF_pgf_eq_exp] using hexp

/-- Helper for Theorem 3.7: the original hypotheses should supply an eventually summable row family
and a real row bound tending to `0`, which is exactly the interface needed by the logarithmic
argument. -/
private theorem row_summable_and_bound_bridge
    (μ : ℕ → PMF ℕ) (p : ℕ → ℕ → NNReal) (lam : NNReal)
    (hpgf :
      ∀ n (z : Set.Icc (0 : ℝ) 1),
        (∑' m : ℕ, (μ n m).toReal * (z : ℝ) ^ m) =
          ∏' l : ℕ, ((p n l : ℝ) * (z : ℝ) + (1 - (p n l : ℝ))))
    (_hsum : Tendsto (fun n ↦ ∑' l : ℕ, p n l) atTop (𝓝 lam))
    (hmax : Tendsto (fun n ↦ ⨆ l : ℕ, p n l) atTop (𝓝 0)) :
    ∃ rowSup : ℕ → ℝ,
      (∀ᶠ n in atTop, Summable fun l : ℕ ↦ (p n l : ℝ)) ∧
        (∀ᶠ n in atTop, ∀ l : ℕ, (p n l : ℝ) ≤ rowSup n) ∧
          Tendsto rowSup atTop (𝓝 0) := by
  let rowSup : ℕ → ℝ := fun n ↦ ((⨆ l : ℕ, p n l : NNReal) : ℝ)
  let hentry_le_one : ∀ n l : ℕ, (p n l : ℝ) ≤ 1 := fun n l ↦
    row_entry_le_one_of_hpgf (μ := μ n) (p := p n) (hpgf := hpgf n) l
  have hrow_bdd : ∀ n : ℕ, BddAbove (Set.range fun l : ℕ ↦ p n l) := by
    intro n
    refine ⟨1, ?_⟩
    rintro _ ⟨l, rfl⟩
    rw [← NNReal.coe_le_coe]
    simpa using hentry_le_one n l
  -- Choose the real row bound to be the coercion of the rowwise `NNReal` supremum.
  refine ⟨rowSup, ?_, ?_, ?_⟩
  · exact eventually_row_summable_of_hpgf_and_hmax μ p hpgf hmax
  · exact Eventually.of_forall fun n l ↦ by
      dsimp [rowSup]
      exact_mod_cast (le_ciSup (hrow_bdd n) l)
  · -- The chosen row bound tends to `0` because the original `NNReal` supremum does.
    dsimp [rowSup]
    exact (NNReal.continuous_coe.tendsto 0).comp hmax

/-- Helper for Theorem 3.7: once the product representation is linearized in the exponent, the pgfs
converge pointwise on `[0,1]` to the Poisson pgf. -/
private theorem pgf_converges_on_unit_interval_to_poisson
    (μ : ℕ → PMF ℕ) (p : ℕ → ℕ → NNReal) (lam : NNReal)
    (hpgf :
      ∀ n (z : Set.Icc (0 : ℝ) 1),
        (∑' m : ℕ, (μ n m).toReal * (z : ℝ) ^ m) =
          ∏' l : ℕ, ((p n l : ℝ) * (z : ℝ) + (1 - (p n l : ℝ))))
    (hsum : Tendsto (fun n ↦ ∑' l : ℕ, p n l) atTop (𝓝 lam))
    (hmax : Tendsto (fun n ↦ ⨆ l : ℕ, p n l) atTop (𝓝 0)) :
    probabilityGeneratingFunctionsConvergeOnUnitInterval μ (poissonPMF lam) := by
  -- Route correction: the logarithm-linearization route is stable, but it needs rowwise
  -- summability together with an explicit real row bound tending to `0`.
  have hconv_of_summable_and_bound :
      ∀ rowSup : ℕ → ℝ,
        (∀ᶠ n in atTop, Summable fun l : ℕ ↦ (p n l : ℝ)) →
        (∀ᶠ n in atTop, ∀ l : ℕ, (p n l : ℝ) ≤ rowSup n) →
        Tendsto rowSup atTop (𝓝 0) →
        probabilityGeneratingFunctionsConvergeOnUnitInterval μ (poissonPMF lam) := by
    intro rowSup hsummable hbound hrowSup
    -- Once rowwise summability and a vanishing real row bound are available, the source proof goes
    -- through exactly as planned.
    exact
      pgf_converges_on_unit_interval_to_poisson_of_row_summable
        μ p rowSup lam hpgf hsummable hbound hsum hrowSup
  rcases row_summable_and_bound_bridge μ p lam hpgf hsum hmax with
    ⟨rowSup, hsummable, hbound, hrowSup⟩
  exact hconv_of_summable_and_bound rowSup hsummable hbound hrowSup

/-- Theorem 3.7: if the laws `μ n = P_{S^n}` have the Poisson-binomial generating functions
coming from Bernoulli success probabilities `p n l`, the row sums `∑' l, p n l` converge to `λ`,
and the maximal success probability in each row tends to `0`, then the laws converge weakly to the
Poisson distribution `Poi_λ`. On `ℕ`, this is the chapter's canonical notion
`natLawWeaklyConvergesTo`. -/
theorem poissonApproximation_tendsto_poissonPMF
    (μ : ℕ → PMF ℕ) (p : ℕ → ℕ → NNReal) (lam : NNReal)
    (hpgf :
      ∀ n (z : Set.Icc (0 : ℝ) 1),
        (∑' m : ℕ, (μ n m).toReal * (z : ℝ) ^ m) =
          ∏' l : ℕ, ((p n l : ℝ) * (z : ℝ) + (1 - (p n l : ℝ))))
    (hsum : Tendsto (fun n ↦ ∑' l : ℕ, p n l) atTop (𝓝 lam))
    (hmax : Tendsto (fun n ↦ ⨆ l : ℕ, p n l) atTop (𝓝 0)) :
    natLawWeaklyConvergesTo μ (poissonPMF lam) := by
  -- First package the source-proof argument at the level of probability generating functions.
  have hpgfConv : probabilityGeneratingFunctionsConvergeOnUnitInterval μ (poissonPMF lam) :=
    pgf_converges_on_unit_interval_to_poisson μ p lam hpgf hsum hmax
  -- Then invoke the earlier chapter equivalence between pgf convergence and weak convergence on
  -- `ℕ`.
  exact ((natLawWeakConvergence_tfae μ (poissonPMF lam)).out 2 0).mp hpgfConv

/-- Companion to Theorem 3.7: weak convergence to `poissonPMF lam` yields pointwise convergence of
the `ENNReal` pmf coefficients. -/
theorem poissonApproximation_tendsto_poissonPMF_apply
    (μ : ℕ → PMF ℕ) (p : ℕ → ℕ → NNReal) (lam : NNReal)
    (hpgf :
      ∀ n (z : Set.Icc (0 : ℝ) 1),
        (∑' m : ℕ, (μ n m).toReal * (z : ℝ) ^ m) =
          ∏' l : ℕ, ((p n l : ℝ) * (z : ℝ) + (1 - (p n l : ℝ))))
    (hsum : Tendsto (fun n ↦ ∑' l : ℕ, p n l) atTop (𝓝 lam))
    (hmax : Tendsto (fun n ↦ ⨆ l : ℕ, p n l) atTop (𝓝 0)) :
    ∀ k : ℕ, Tendsto (fun n ↦ μ n k) atTop (𝓝 (poissonPMF lam k)) := by
  have hweak : natLawWeaklyConvergesTo μ (poissonPMF lam) :=
    poissonApproximation_tendsto_poissonPMF μ p lam hpgf hsum hmax
  intro k
  have htoReal :
      Tendsto (fun n ↦ ((μ n) k).toReal) atTop (𝓝 ((poissonPMF lam k).toReal)) :=
    hweak k
  -- Finally move back from real masses to the original `ENNReal`-valued pmf coefficients.
  have hofReal :
      Tendsto (fun n ↦ ENNReal.ofReal ((μ n k).toReal)) atTop
        (𝓝 (ENNReal.ofReal ((poissonPMF lam k).toReal))) :=
    (ENNReal.continuous_ofReal.tendsto ((poissonPMF lam k).toReal)).comp htoReal
  simpa [ENNReal.ofReal_toReal, PMF.apply_ne_top] using hofReal
