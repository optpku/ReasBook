/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Helper for Example 2.10: rewrite the shifted threshold event through the Poisson law. -/
lemma measure_preimage_ge_eq_poisson_tail (rates : ℕ → NNReal) (X : ℕ → Ω → ℕ)
    (hX : ∀ n, HasLaw (X n) (poissonMeasure (rates n)) μ) (n : ℕ) :
    μ (X (n + 1) ⁻¹' Set.Ici (n + 1))
      = (poissonMeasure (rates (n + 1))) (Set.Ici (n + 1)) := by
  -- Rewrite the event measure as the pushforward measure of `X (n + 1)`.
  rw [← Measure.map_apply_of_aemeasurable (hX (n + 1)).aemeasurable measurableSet_Ici]
  -- The pushforward is exactly the Poisson law registered by `HasLaw`.
  rw [(hX (n + 1)).map_eq]

/-- Helper for Example 2.10: expand a Poisson tail as a discrete `tsum`. -/
lemma poisson_tail_eq_tsum (r : NNReal) (k : ℕ) :
    (poissonMeasure r) (Set.Ici k) = ∑' m : ℕ, (Set.Ici k).indicator (poissonPMF r) m := by
  -- `poissonMeasure` is the measure associated to the Poisson PMF.
  rw [poissonMeasure, PMF.toMeasure_apply_eq_tsum]

/-- Helper for Example 2.10: the uniform envelope used to dominate shifted Poisson tails. -/
noncomputable abbrev poisson_tail_envelope (Λ : NNReal) (n m : ℕ) : ENNReal :=
  if n + 1 ≤ m then ENNReal.ofReal ((Λ : ℝ) ^ m / m.factorial) else 0

/-- Helper for Example 2.10: each Poisson mass is bounded by the uniform `Λ`-envelope. -/
lemma poisson_term_le_uniform (Λ r : NNReal) (hr : r ≤ Λ) (m : ℕ) :
    poissonPMFReal r m ≤ (Λ : ℝ) ^ m / m.factorial := by
  have hpow : (r : ℝ) ^ m ≤ (Λ : ℝ) ^ m := by
    exact_mod_cast pow_le_pow_left' hr m
  have hexp : Real.exp (-(r : ℝ)) ≤ 1 := by
    rw [Real.exp_neg]
    exact (inv_le_one₀ (Real.exp_pos _)).2
      (Real.one_le_exp (show 0 ≤ (r : ℝ) by exact_mod_cast r.2))
  have hmul : Real.exp (-(r : ℝ)) * (r : ℝ) ^ m ≤ (Λ : ℝ) ^ m := by
    calc
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ m ≤ (r : ℝ) ^ m := by
        exact mul_le_of_le_one_left (by positivity) hexp
      _ ≤ (Λ : ℝ) ^ m := hpow
  -- The exponential factor is at most `1`, so only the power term matters.
  rw [poissonPMFReal]
  exact div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ (m.factorial : ℝ))

/-- Helper for Example 2.10: the numeric comparison series from the textbook is summable. -/
lemma nat_mul_pow_div_factorial_summable (Λ : NNReal) :
    Summable (fun m : ℕ ↦ (m : ℝ) * (Λ : ℝ) ^ m / m.factorial) := by
  have hpow : Summable (fun m : ℕ ↦ (Λ : ℝ) ^ m / m.factorial) :=
    Real.summable_pow_div_factorial (Λ : ℝ)
  have hbase : Summable (fun m : ℕ ↦ (Λ : ℝ) * ((Λ : ℝ) ^ m / m.factorial)) :=
    hpow.mul_left (Λ : ℝ)
  have hterm : ∀ m : ℕ,
      ((m + 1 : ℕ) : ℝ) * (Λ : ℝ) ^ (m + 1) / (m + 1).factorial
        = (Λ : ℝ) * ((Λ : ℝ) ^ m / m.factorial) := by
    intro m
    rw [Nat.factorial_succ, pow_succ]
    have hm : (((m + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hm' : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    -- Cancel the common factor `(m + 1)` after rewriting `(m + 1)!`.
    field_simp [hm, hm', hf]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hshift :
      Summable
        (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ) * (Λ : ℝ) ^ (m + 1) / (m + 1).factorial) :=
    hbase.congr (fun m => (hterm m).symm)
  -- Shift back from the `m + 1` series to the original index.
  exact
    (summable_nat_add_iff
      (f := fun m : ℕ ↦ (m : ℝ) * (Λ : ℝ) ^ m / m.factorial) 1).1 hshift

/-- Helper for Example 2.10: for fixed `m`, exactly `m` shifted indices satisfy `n + 1 ≤ m`. -/
lemma finite_ge_count_tsum (m : ℕ) (c : ENNReal) :
    (∑' n : ℕ, if n + 1 ≤ m then c else 0) = (m : ENNReal) * c := by
  calc
    (∑' n : ℕ, if n + 1 ≤ m then c else 0)
        = Finset.sum (Finset.range m) (fun n ↦ if n + 1 ≤ m then c else 0) := by
            refine tsum_eq_sum (α := ENNReal) (L := SummationFilter.unconditional ℕ)
              (f := fun n : ℕ ↦ if n + 1 ≤ m then c else 0) (s := Finset.range m) ?_
            intro n hn
            simp only [Finset.mem_range, not_lt] at hn
            have hnm : m ≤ n := hn
            simp [hnm]
    _ = Finset.sum (Finset.range m) (fun _ ↦ c) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp only [Finset.mem_range] at hn
            simp [hn]
    _ = (m : ENNReal) * c := by
            simp [Finset.card_range]

/-- Helper for Example 2.10: the shifted Poisson tail probabilities form a finite series. -/
lemma shifted_poisson_tail_series_ne_top (Λ : NNReal) (rates : ℕ → NNReal)
    (hΛ : ∀ n, rates n ≤ Λ) :
    (∑' n : ℕ, (poissonMeasure (rates (n + 1))) (Set.Ici (n + 1))) ≠ ⊤ := by
  have htail_le : ∀ n : ℕ,
      (poissonMeasure (rates (n + 1))) (Set.Ici (n + 1))
        ≤ ∑' m : ℕ, poisson_tail_envelope Λ n m := by
    intro n
    rw [poisson_tail_eq_tsum]
    -- Compare each Poisson tail term with the uniform envelope termwise.
    refine ENNReal.tsum_le_tsum ?_
    intro m
    by_cases hnm : n + 1 ≤ m
    · calc
        (Set.Ici (n + 1)).indicator (poissonPMF (rates (n + 1))) m
            = ENNReal.ofReal (poissonPMFReal (rates (n + 1)) m) := by
                simp [Set.mem_Ici, hnm, poissonPMFReal_ofReal_eq_poissonPMF]
        _ ≤ ENNReal.ofReal ((Λ : ℝ) ^ m / m.factorial) := by
                exact ENNReal.ofReal_le_ofReal
                  (poisson_term_le_uniform Λ (rates (n + 1)) (hΛ (n + 1)) m)
        _ = poisson_tail_envelope Λ n m := by
                simp [poisson_tail_envelope, hnm]
    · have hnotmem : m ∉ Set.Ici (n + 1) := hnm
      simp [poisson_tail_envelope, Set.indicator_of_notMem, hnotmem]
  have hseries_le :
      (∑' n : ℕ, (poissonMeasure (rates (n + 1))) (Set.Ici (n + 1)))
        ≤ ∑' n : ℕ, ∑' m : ℕ, poisson_tail_envelope Λ n m := by
    exact ENNReal.tsum_le_tsum htail_le
  have hcount : ∀ m : ℕ,
      (∑' n : ℕ, poisson_tail_envelope Λ n m)
        = (m : ENNReal) * ENNReal.ofReal ((Λ : ℝ) ^ m / m.factorial) := by
    intro m
    simpa [poisson_tail_envelope] using
      finite_ge_count_tsum m (ENNReal.ofReal ((Λ : ℝ) ^ m / m.factorial))
  have hnum :
      (∑' m : ℕ, (m : ENNReal) * ENNReal.ofReal ((Λ : ℝ) ^ m / m.factorial)) ≠ ⊤ := by
    have hsum := nat_mul_pow_div_factorial_summable Λ
    have hnonneg : ∀ m : ℕ, 0 ≤ (m : ℝ) * (Λ : ℝ) ^ m / m.factorial := by
      intro m
      positivity
    have hterm : ∀ m : ℕ,
        (m : ENNReal) * ENNReal.ofReal ((Λ : ℝ) ^ m / m.factorial)
          = ENNReal.ofReal ((m : ℝ) * (Λ : ℝ) ^ m / m.factorial) := by
      intro m
      have hm : 0 ≤ (m : ℝ) := by positivity
      calc
        (m : ENNReal) * ENNReal.ofReal ((Λ : ℝ) ^ m / m.factorial)
            = ENNReal.ofReal (m : ℝ) * ENNReal.ofReal ((Λ : ℝ) ^ m / m.factorial) := by
                simp [ENNReal.ofReal_natCast]
        _ = ENNReal.ofReal ((m : ℝ) * ((Λ : ℝ) ^ m / m.factorial)) := by
                symm
                exact ENNReal.ofReal_mul hm
        _ = ENNReal.ofReal ((m : ℝ) * (Λ : ℝ) ^ m / m.factorial) := by
                ring_nf
    -- Convert the ENNReal series to the corresponding real series.
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum]
    exact ENNReal.ofReal_ne_top
  have hbound_ne_top :
      (∑' n : ℕ, ∑' m : ℕ, poisson_tail_envelope Λ n m) ≠ ⊤ := by
    rw [ENNReal.tsum_comm]
    simpa [hcount] using hnum
  -- The dominated double series is finite, so the original shifted tail series is finite as well.
  exact ne_top_of_le_ne_top hbound_ne_top hseries_le

-- Proof sketch: For `A n := X n ⁻¹' Set.Ici n`, use `HasLaw.measure_mem_eq` to rewrite
-- `μ (A n)` as the Poisson tail probability `poissonMeasure (λ n) (Set.Ici n)`. The uniform bound
-- `λ n ≤ Λ` gives a summable comparison, for instance by the textbook double-sum estimate
-- `∑ n μ (A n) ≤ Λ * exp Λ < ∞`. Then apply the first Borel-Cantelli lemma
-- `MeasureTheory.measure_limsup_atTop_eq_zero`.
/-- Example 2.10: If `X n` has Poisson law with parameter `rates n`, and the parameters are uniformly
bounded by `Λ`, then the event `{ω | X n ω ≥ n for infinitely many n}` has probability zero. -/
theorem measure_limsup_poisson_ge_index_eq_zero (Λ : NNReal) (rates : ℕ → NNReal)
    (hΛ : ∀ n, rates n ≤ Λ) (X : ℕ → Ω → ℕ)
    (hX : ∀ n, HasLaw (X n) (poissonMeasure (rates n)) μ) :
    μ (limsup (fun n ↦ X n ⁻¹' Set.Ici n) atTop) = 0 := by
  -- Shift away the finite `n = 0` prefix so the textbook counting starts at `1`.
  rw [← limsup_nat_add (fun n ↦ X n ⁻¹' Set.Ici n) 1]
  apply MeasureTheory.measure_limsup_atTop_eq_zero
  have hseries :
      (∑' n : ℕ, μ (X (n + 1) ⁻¹' Set.Ici (n + 1))) ≠ ⊤ := by
    calc
      (∑' n : ℕ, μ (X (n + 1) ⁻¹' Set.Ici (n + 1)))
          = ∑' n : ℕ, (poissonMeasure (rates (n + 1))) (Set.Ici (n + 1)) := by
              congr with n
              exact measure_preimage_ge_eq_poisson_tail rates X hX n
      _ ≠ ⊤ := shifted_poisson_tail_series_ne_top Λ rates hΛ
  -- The first Borel-Cantelli lemma now gives measure zero for the limsup event.
  exact hseries
