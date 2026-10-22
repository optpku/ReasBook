/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

/- The one-trial binomial PMF is the Bernoulli PMF. -/
recall PMF.binomial_one_eq_bernoulli

/- The expectation of the Bernoulli PMF on `Bool`, pushed forward by `true ↦ 1`, `false ↦ 0`,
is `PMF.bernoulli_expectation`. -/
recall PMF.bernoulli_expectation

/-- Helper for Example 5.9: the one-point initial segment `Set.Iio 1` is `{0}`. -/
lemma setIioOne_eq_singleton : (Set.Iio 1 : Set ℕ) = {0} := by
  -- On `ℕ`, the only element strictly below `1` is `0`.
  ext x
  simp [Set.mem_Iio]

/-- Helper for Example 5.9: the natural-number cast `ℕ → ℝ` is measurable. -/
lemma measurableNatCastReal : Measurable (Nat.cast : ℕ → ℝ) := by
  -- This is the standard measurability fact for casts into `ℝ`.
  exact measurable_of_countable _

/-- Helper for Example 5.9: the subsets of `Set.Iio n` with cardinality `k` are exactly the
coercions of `((Finset.range n).powersetCard k)`. -/
lemma cardinalityEvent_eq_image_powersetCardRange (n k : ℕ) :
    {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k} =
      ((((Finset.range n).powersetCard k).image ((↑) : Finset ℕ → Set ℕ)) : Set (Set ℕ)) := by
  classical
  -- Convert finite subsets of `Set.Iio n` to `Finset`s and back.
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hsub, hcard⟩
    let hsfin : s.Finite := (Set.finite_Iio n).subset hsub
    refine Finset.mem_coe.2 <| Finset.mem_image.2 ?_
    refine ⟨hsfin.toFinset, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        simpa [Set.mem_Iio, hsfin.coe_toFinset] using hsub (by simpa [hsfin.coe_toFinset] using hx)
      · rw [← Set.ncard_coe_finset, hsfin.coe_toFinset, hcard]
    · simp [hsfin.coe_toFinset]
  · intro hs
    rcases Finset.mem_coe.1 hs with hs
    rcases Finset.mem_image.1 hs with ⟨t, ht, rfl⟩
    rw [Finset.mem_powersetCard] at ht
    refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_range.mp (ht.1 (by simpa using hx))
    · simpa using ht.2

/-- Helper for Example 5.9: the `setBernoulli` law on `Set.Iio n` assigns the usual binomial mass
to the event that the chosen subset has cardinality `k`, viewed in `ℝ`. -/
lemma setBernoulliIio_apply_card_toReal (n k : ℕ) (p : I) :
    (setBer(Set.Iio n, p) {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k}).toReal =
      (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
  classical
  -- Rewrite the cardinality event as a finite image of `powersetCard`.
  change (setBer(Set.Iio n, p)).real {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k} = _
  rw [cardinalityEvent_eq_image_powersetCardRange]
  let A : Finset (Set ℕ) := (((Finset.range n).powersetCard k).image ((↑) : Finset ℕ → Set ℕ))
  rw [← MeasureTheory.sum_measureReal_singleton (μ := setBer(Set.Iio n, p)) A]
  have hterm :
      ∀ s ∈ A,
        (setBer(Set.Iio n, p)).real {s} = (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
    intro s hs
    have hs' : ∃ t, t ∈ (Finset.range n).powersetCard k ∧ ((↑t : Set ℕ) = s) := by
      simpa [A] using hs
    rcases hs' with ⟨t, ht, rfl⟩
    rw [Finset.mem_powersetCard] at ht
    have hsubset : (↑t : Set ℕ) ⊆ Set.Iio n := by
      intro x hx
      exact Finset.mem_range.mp (ht.1 (by simpa using hx))
    have hsingle :
        (setBer(Set.Iio n, p)).real {(↑t : Set ℕ)} =
          (p : ℝ) ^ (↑t : Set ℕ).ncard * (1 - (p : ℝ)) ^ ((Set.Iio n \ (↑t : Set ℕ)).ncard) := by
      -- Evaluate each singleton mass with `setBernoulli_singleton`.
      rw [measureReal_def,
        ProbabilityTheory.setBernoulli_singleton (s := (↑t : Set ℕ)) (u := Set.Iio n)
          (p := p) hsubset (Set.finite_Iio n), ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_pow]
      · simp
    simpa [Set.ncard_coe_finset, Set.ncard_diff hsubset, Set.ncard_Iio_nat, ht.2] using hsingle
  have hcardA : A.card = Nat.choose n k := by
    -- Count the cardinality-`k` subsets of `range n`.
    unfold A
    rw [Finset.card_image_of_injective _ Finset.coe_injective]
    simpa using (Finset.card_powersetCard k (Finset.range n))
  calc
    ∑ s ∈ A, (setBer(Set.Iio n, p)).real {s}
      = ∑ s ∈ A, (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          exact hterm s hs
    _ = (A.card : ℝ) * ((p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
          rw [hcardA]
          ring

/-- Helper for Example 5.9: the singleton masses of the binomial law are given by the standard
choose formula, viewed in `ℝ`. -/
lemma binomial_apply_singleton_toReal (n k : ℕ) (p : I) :
    (Bin(n, p) ({k} : Set ℕ)).toReal =
      (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
  -- Rewrite the `Bin(n, p)` singleton as the cardinality event under `setBer(Set.Iio n, p)`.
  rw [ProbabilityTheory.binomial, Measure.map_apply measurable_ncard (measurableSet_singleton k)]
  have hpreimage :
      Set.ncard ⁻¹' ({k} : Set ℕ) = {s : Set ℕ | s.ncard = k} := by
    ext s
    simp
  rw [hpreimage]
  have hμ :
      setBer(Set.Iio n, p) {s : Set ℕ | s.ncard = k} =
        setBer(Set.Iio n, p) {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k} := by
    -- Outside `Set.Iio n`, the `setBernoulli` law has zero mass.
    refine measure_congr ?_
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := Set.Iio n) (p := p)] with s hs
    apply propext
    constructor
    · intro hk
      exact ⟨hs, hk⟩
    · intro hk
      exact hk.2
  rw [hμ]
  exact setBernoulliIio_apply_card_toReal n k p

/-- Helper for Example 5.9: the real-valued binomial law is almost surely bounded by `n` in
absolute value. -/
lemma binomialRealAeAbsLe (n : ℕ) (p : I) :
    ∀ᵐ x : ℝ ∂Bin(ℝ, n, p), |x| ≤ n := by
  have hNat : ∀ᵐ k : ℕ ∂Bin(n, p), k ≤ n := by
    -- The nat-valued binomial law is supported on `[0, n]`.
    simpa using
      (ProbabilityTheory.ae_le_of_hasLaw_binomial (n := n) (p := p)
        (X := id) (P := Bin(n, p)) (ProbabilityTheory.HasLaw.id (μ := Bin(n, p))))
  -- Transport the support bound through the defining cast map of `Bin(ℝ, n, p)`.
  rw [show Bin(ℝ, n, p) = Measure.map (Nat.cast : ℕ → ℝ) (Bin(n, p)) by rfl]
  rw [ae_map_iff measurableNatCastReal.aemeasurable (measurableSet_setOf.2 (by fun_prop))]
  filter_upwards [hNat] with k hk
  simpa [abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by exact_mod_cast Nat.zero_le k)] using
    (show (k : ℝ) ≤ (n : ℝ) by exact_mod_cast hk)

/-- Helper for Example 5.9: the identity random variable belongs to `L²` under `Bin(ℝ, n, p)`. -/
lemma memLpTwoIdBinomialReal (n : ℕ) (p : I) :
    MemLp id 2 (Bin(ℝ, n, p)) := by
  -- The almost sure bound by `n` gives every finite `L^p` norm on this probability space.
  exact MemLp.of_bound aestronglyMeasurable_id n (binomialRealAeAbsLe n p)

/-- Helper for Example 5.9: the first moment of `Bin(ℝ, n, p)` is `p * n`. -/
lemma binomialRealIntegralId_eq (n : ℕ) (p : I) :
    (∫ x, x ∂Bin(ℝ, n, p)) = p * n := by
  cases n with
  | zero =>
      have hNat : ∀ᵐ k : ℕ ∂Bin(0, p), k ≤ 0 := by
        -- The nat-valued zero-trial law is supported at `0`.
        simpa using
          (ProbabilityTheory.ae_le_of_hasLaw_binomial (n := 0) (p := p)
            (X := id) (P := Bin(0, p)) (ProbabilityTheory.HasLaw.id (μ := Bin(0, p))))
      have hInt : Integrable (fun k : ℕ ↦ (k : ℝ)) (Bin(0, p)) := by
        -- The support bound gives an absolute bound by `0`.
        refine Integrable.of_bound (by fun_prop) 0 ?_
        filter_upwards [hNat] with k hk
        simpa [Real.norm_eq_abs,
          abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by exact_mod_cast Nat.zero_le k)] using
          (show (k : ℝ) ≤ (0 : ℝ) by exact_mod_cast hk)
      -- Expand the integral as a discrete sum and collapse it to the single `k = 0` term.
      rw [show Bin(ℝ, 0, p) = Measure.map (Nat.cast : ℕ → ℝ) (Bin(0, p)) by rfl]
      rw [integral_map measurableNatCastReal.aemeasurable (by fun_prop)]
      rw [integral_countable hInt]
      simp_rw [smul_eq_mul, Measure.real, binomial_apply_singleton_toReal]
      have htail :
          ∀ k ∉ Finset.range 1,
            ((Nat.choose 0 k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (0 - k)) * k = 0 := by
        intro k hk
        have hk' : 0 < k := by
          exact Nat.pos_of_ne_zero (by simpa [Finset.mem_range] using hk)
        simp [Nat.choose_eq_zero_of_lt hk']
      rw [tsum_eq_sum htail]
      simp
  | succ m =>
      have hNat : ∀ᵐ k : ℕ ∂Bin(m + 1, p), k ≤ m + 1 := by
        -- The nat-valued binomial law is supported on `[0, m + 1]`.
        simpa using
          (ProbabilityTheory.ae_le_of_hasLaw_binomial (n := m + 1) (p := p)
            (X := id) (P := Bin(m + 1, p)) (ProbabilityTheory.HasLaw.id (μ := Bin(m + 1, p))))
      have hInt : Integrable (fun k : ℕ ↦ (k : ℝ)) (Bin(m + 1, p)) := by
        -- The support bound gives an absolute bound by `m + 1`.
        refine Integrable.of_bound (by fun_prop) (m + 1) ?_
        filter_upwards [hNat] with k hk
        simpa [Real.norm_eq_abs,
          abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by exact_mod_cast Nat.zero_le k)] using
          (show (k : ℝ) ≤ (m + 1 : ℝ) by exact_mod_cast hk)
      -- Push the real-valued integral back to the nat-valued law and expand it as a discrete sum.
      rw [show Bin(ℝ, m + 1, p) = Measure.map (Nat.cast : ℕ → ℝ) (Bin(m + 1, p)) by rfl]
      rw [integral_map measurableNatCastReal.aemeasurable (by fun_prop)]
      rw [integral_countable hInt]
      simp_rw [smul_eq_mul, Measure.real, binomial_apply_singleton_toReal]
      let f : ℕ → ℝ := fun k ↦
        ((Nat.choose (m + 1) k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m + 1 - k)) * k
      have hf :
          (∑' x : ℕ,
              ((Nat.choose (m + 1) x : ℝ) * (p : ℝ) ^ x * (1 - (p : ℝ)) ^ (m + 1 - x)) * x) =
            ∑' k : ℕ, f k := by
        rfl
      rw [hf]
      have htail : ∀ k ∉ Finset.range (m + 2), f k = 0 := by
        intro k hk
        have hk' : m + 1 < k := by
          exact Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hk)
        simp [f, Nat.choose_eq_zero_of_lt hk']
      rw [tsum_eq_sum htail, Finset.sum_range_succ' f (m + 1)]
      have hshift :
          ∑ k ∈ Finset.range (m + 1), f (k + 1) =
            (p * (m + 1)) *
              ∑ k ∈ Finset.range (m + 1),
                (Nat.choose m k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m - k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hchoose : ((Nat.choose (m + 1) (k + 1) : ℝ) * (k + 1 : ℝ)) =
            (m + 1 : ℝ) * (Nat.choose m k : ℝ) := by
          exact_mod_cast (Nat.add_one_mul_choose_eq m k).symm
        have hpow : (p : ℝ) ^ (k + 1) = (p : ℝ) * (p : ℝ) ^ k := by
          rw [pow_succ', mul_comm]
        have hsub : m + 1 - (k + 1) = m - k := by
          omega
        calc
          f (k + 1)
            = (((Nat.choose (m + 1) (k + 1) : ℝ) * (k + 1 : ℝ)) *
                ((p : ℝ) ^ (k + 1) * (1 - (p : ℝ)) ^ (m + 1 - (k + 1)))) := by
                  simp [f]
                  ring
          _ = (((m + 1 : ℝ) * (Nat.choose m k : ℝ)) *
                (((p : ℝ) * (p : ℝ) ^ k) * (1 - (p : ℝ)) ^ (m - k))) := by
                  rw [hchoose, hpow, hsub]
          _ = (p * (m + 1)) *
                ((Nat.choose m k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m - k)) := by
                  ring
      have hsum :
          ∑ k ∈ Finset.range (m + 1),
              (Nat.choose m k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m - k) = 1 := by
        -- This is the binomial theorem at `p + (1 - p) = 1`.
        have hpow := add_pow (p : ℝ) (1 - (p : ℝ)) m
        rw [show (p : ℝ) + (1 - (p : ℝ)) = 1 by ring, one_pow] at hpow
        simpa [mul_comm, mul_left_comm, mul_assoc] using hpow.symm
      have hf0 : f 0 = 0 := by
        simp [f]
      rw [hshift, hsum, hf0]
      simpa [Nat.cast_add, Nat.cast_one, mul_add, add_mul, mul_assoc] using
        (show (p : ℝ) * ((m : ℝ) + 1) = (p : ℝ) + (p : ℝ) * m by ring)

/-- Helper for Example 5.9: after shifting the factorial-second-moment sum by two, each binomial
summand factors through the corresponding `m`-trial binomial term. -/
lemma binomialFactorialTwoSummand_shift (m k : ℕ) (p : I) (hk : k ≤ m) :
    (((Nat.choose (m + 2) (k + 2) : ℝ) * (p : ℝ) ^ (k + 2) *
        (1 - (p : ℝ)) ^ ((m + 2) - (k + 2))) *
      ((k + 2 : ℝ) * ((k + 2 : ℝ) - 1))) =
      (((m + 2 : ℝ) * (m + 1 : ℝ) * (p : ℝ) ^ 2) *
        ((Nat.choose m k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m - k))) := by
  have hchoose1 :
      ((Nat.choose (m + 2) (k + 2) : ℝ) * (k + 2 : ℝ)) =
        (m + 2 : ℝ) * (Nat.choose (m + 1) (k + 1) : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq (m + 1) (k + 1)).symm
  have hchoose2 :
      ((Nat.choose (m + 1) (k + 1) : ℝ) * (k + 1 : ℝ)) =
        (m + 1 : ℝ) * (Nat.choose m k : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq m k).symm
  have hpow : (p : ℝ) ^ (k + 2) = (p : ℝ) ^ 2 * (p : ℝ) ^ k := by
    rw [show k + 2 = 2 + k by omega, pow_add]
  have hsub : (m + 2) - (k + 2) = m - k := by
    omega
  -- Normalize the shifted summand before applying the two choose recurrences.
  rw [hsub, hpow]
  calc
    (((Nat.choose (m + 2) (k + 2) : ℝ) * ((p : ℝ) ^ 2 * (p : ℝ) ^ k) *
          (1 - (p : ℝ)) ^ (m - k)) *
        ((k + 2 : ℝ) * ((k + 2 : ℝ) - 1)))
      = ((((Nat.choose (m + 2) (k + 2) : ℝ) * (k + 2 : ℝ)) * (k + 1 : ℝ)) *
          (((p : ℝ) ^ 2 * (p : ℝ) ^ k) * (1 - (p : ℝ)) ^ (m - k))) := by
            ring
    _ = ((((m + 2 : ℝ) * (Nat.choose (m + 1) (k + 1) : ℝ)) * (k + 1 : ℝ)) *
          (((p : ℝ) ^ 2 * (p : ℝ) ^ k) * (1 - (p : ℝ)) ^ (m - k))) := by
            rw [hchoose1]
    _ = (((m + 2 : ℝ) * ((m + 1 : ℝ) * (Nat.choose m k : ℝ))) *
          (((p : ℝ) ^ 2 * (p : ℝ) ^ k) * (1 - (p : ℝ)) ^ (m - k))) := by
            have hchoose2' :
                ((m + 2 : ℝ) * (Nat.choose (m + 1) (k + 1) : ℝ) * (k + 1 : ℝ)) =
                  (m + 2 : ℝ) * ((m + 1 : ℝ) * (Nat.choose m k : ℝ)) := by
              calc
                ((m + 2 : ℝ) * (Nat.choose (m + 1) (k + 1) : ℝ) * (k + 1 : ℝ))
                  = (m + 2 : ℝ) * ((Nat.choose (m + 1) (k + 1) : ℝ) * (k + 1 : ℝ)) := by
                      ring
                _ = (m + 2 : ℝ) * ((m + 1 : ℝ) * (Nat.choose m k : ℝ)) := by
                      rw [hchoose2]
            exact congrArg
              (fun z : ℝ ↦ z * (((p : ℝ) ^ 2 * (p : ℝ) ^ k) * (1 - (p : ℝ)) ^ (m - k)))
              hchoose2'
    _ = (((m + 2 : ℝ) * (m + 1 : ℝ) * (p : ℝ) ^ 2) *
          ((Nat.choose m k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m - k))) := by
            simpa [mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Example 5.9: the factorial second moment of `Bin(ℝ, n, p)` is
`n * (n - 1) * p²`. -/
lemma binomialRealIntegralFactorialTwo_eq (n : ℕ) (p : I) :
    (∫ x, x * (x - 1) ∂Bin(ℝ, n, p)) = n * (n - 1) * (p : ℝ) ^ 2 := by
  have hNat : ∀ᵐ k : ℕ ∂Bin(n, p), k ≤ n := by
    -- The nat-valued binomial law is supported on `[0, n]`.
    simpa using
      (ProbabilityTheory.ae_le_of_hasLaw_binomial (n := n) (p := p)
        (X := id) (P := Bin(n, p)) (ProbabilityTheory.HasLaw.id (μ := Bin(n, p))))
  have hInt : Integrable (fun k : ℕ ↦ (k : ℝ) * ((k : ℝ) - 1)) (Bin(n, p)) := by
    -- The support bound gives a uniform absolute bound on the factorial integrand.
    refine Integrable.of_bound (by fun_prop) ((n : ℝ) * ((n : ℝ) + 1)) ?_
    filter_upwards [hNat] with k hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.zero_le k
    have hkAbs : |(k : ℝ)| ≤ (n : ℝ) := by
      simpa [abs_of_nonneg hk0] using (show (k : ℝ) ≤ (n : ℝ) by exact_mod_cast hk)
    have hsub : |(k : ℝ) - 1| ≤ |(k : ℝ)| + 1 := by
      simpa using (abs_sub (k : ℝ) 1)
    calc
      ‖(k : ℝ) * ((k : ℝ) - 1)‖ = |(k : ℝ)| * |(k : ℝ) - 1| := by
        rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |(k : ℝ)| * (|(k : ℝ)| + 1) := by
        exact mul_le_mul_of_nonneg_left hsub (abs_nonneg _)
      _ ≤ (n : ℝ) * ((n : ℝ) + 1) := by
        nlinarith [abs_nonneg (k : ℝ), hkAbs]
  -- Push the real-valued integral back to the nat-valued law and expand it as a finite sum.
  rw [show Bin(ℝ, n, p) = Measure.map (Nat.cast : ℕ → ℝ) (Bin(n, p)) by rfl]
  rw [integral_map measurableNatCastReal.aemeasurable (by fun_prop)]
  rw [integral_countable hInt]
  simp_rw [smul_eq_mul, Measure.real, binomial_apply_singleton_toReal]
  cases n with
  | zero =>
      have htail :
          ∀ k ∉ Finset.range 1,
            ((Nat.choose 0 k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (0 - k)) *
              ((k : ℝ) * ((k : ℝ) - 1)) = 0 := by
        intro k hk
        have hk' : 0 < k := by
          exact Nat.pos_of_ne_zero (by simpa [Finset.mem_range] using hk)
        simp [Nat.choose_eq_zero_of_lt hk']
      rw [tsum_eq_sum htail]
      simp
  | succ n =>
      cases n with
      | zero =>
          have htail :
              ∀ k ∉ Finset.range 2,
                ((Nat.choose 1 k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (1 - k)) *
                  ((k : ℝ) * ((k : ℝ) - 1)) = 0 := by
            intro k hk
            by_cases hk1 : k ≤ 1
            · have hkCases : k = 0 ∨ k = 1 := by omega
              rcases hkCases with rfl | rfl <;> simp
            · have hk' : 1 < k := Nat.lt_of_not_ge hk1
              simp [Nat.choose_eq_zero_of_lt hk']
          rw [tsum_eq_sum htail]
          -- Only the `k = 0, 1` summands remain, and both vanish directly.
          rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
          norm_num
      | succ m =>
          let f : ℕ → ℝ := fun k ↦
            ((Nat.choose (m + 2) k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m + 2 - k)) *
              ((k : ℝ) * ((k : ℝ) - 1))
          have hf :
              (∑' x : ℕ,
                  ((Nat.choose (m + 2) x : ℝ) * (p : ℝ) ^ x * (1 - (p : ℝ)) ^ (m + 2 - x)) *
                    ((x : ℝ) * ((x : ℝ) - 1))) =
                ∑' k : ℕ, f k := by
            rfl
          rw [hf]
          have htail : ∀ k ∉ Finset.range (m + 3), f k = 0 := by
            intro k hk
            have hk' : m + 2 < k := by
              exact Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hk)
            simp [f, Nat.choose_eq_zero_of_lt hk']
          rw [tsum_eq_sum htail]
          rw [show m + 3 = 2 + (m + 1) by omega, Finset.sum_range_add f 2 (m + 1)]
          have hfirst : ∑ k ∈ Finset.range 2, f k = 0 := by
            -- The first two factorial summands vanish before the index shift starts.
            rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
            norm_num [f]
          have hshift :
              ∑ k ∈ Finset.range (m + 1), f (2 + k) =
                (((m + 2 : ℝ) * (m + 1 : ℝ) * (p : ℝ) ^ 2) *
                  ∑ k ∈ Finset.range (m + 1),
                    (Nat.choose m k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m - k)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk' : k ≤ m := by
              exact Nat.le_of_lt_succ (by simpa [Finset.mem_range] using hk)
            -- Rewrite the shifted `k + 2` summand once and factor out the constant term.
            simpa [f, show 2 + k = k + 2 by omega] using
              binomialFactorialTwoSummand_shift m k p hk'
          have hsum :
              ∑ k ∈ Finset.range (m + 1),
                  (Nat.choose m k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m - k) = 1 := by
            -- This is the binomial theorem at `p + (1 - p) = 1`.
            have hpow := add_pow (p : ℝ) (1 - (p : ℝ)) m
            rw [show (p : ℝ) + (1 - (p : ℝ)) = 1 by ring, one_pow] at hpow
            simpa [mul_comm, mul_left_comm, mul_assoc] using hpow.symm
          rw [hfirst, zero_add, hshift, hsum]
          have hcast : (↑(m + 1 + 1) : ℝ) = (m + 2 : ℝ) := by
            exact_mod_cast (show m + 1 + 1 = m + 2 by omega)
          have hsucc : ((m + 2 : ℝ) - 1) = (m + 1 : ℝ) := by
            ring
          rw [hcast, hsucc]
          ring

/-- Helper for Example 5.9: the second moment of `Bin(ℝ, n, p)` is
`(pn)² + p(1-p)n`. -/
lemma binomialRealIntegralSq_eq (n : ℕ) (p : I) :
    (∫ x, x ^ 2 ∂Bin(ℝ, n, p)) = (p * n) ^ 2 + p * (1 - p) * n := by
  have hIntSq : Integrable (fun x : ℝ ↦ x ^ 2) (Bin(ℝ, n, p)) := by
    -- The `L²` bound upgrades the square to an integrable function.
    exact MeasureTheory.MemLp.integrable_sq (memLpTwoIdBinomialReal n p)
  have hIntId : Integrable (fun x : ℝ ↦ x) (Bin(ℝ, n, p)) := by
    -- The almost sure bound by `n` gives integrability of the identity.
    exact Integrable.of_bound aestronglyMeasurable_id n (binomialRealAeAbsLe n p)
  have hDecomp :
      (∫ x, x * (x - 1) ∂Bin(ℝ, n, p)) =
        (∫ x, x ^ 2 ∂Bin(ℝ, n, p)) - (∫ x, x ∂Bin(ℝ, n, p)) := by
    -- Rewrite the factorial moment as `E[X²] - E[X]`.
    rw [show (fun x : ℝ ↦ x * (x - 1)) = fun x ↦ x ^ 2 - x by
      funext x
      ring]
    rw [integral_sub hIntSq hIntId]
  -- Solve for `E[X²]` using the factorial-second-moment and mean formulas.
  calc
    (∫ x, x ^ 2 ∂Bin(ℝ, n, p))
      = (∫ x, x * (x - 1) ∂Bin(ℝ, n, p)) + (∫ x, x ∂Bin(ℝ, n, p)) := by
          linarith
    _ = n * (n - 1) * (p : ℝ) ^ 2 + p * n := by
          rw [binomialRealIntegralFactorialTwo_eq, binomialRealIntegralId_eq]
    _ = (p * n) ^ 2 + p * (1 - p) * n := by
          ring

-- Proof sketch: push `Bin(ℝ, n, p)` back to the nat-valued binomial law, compute the first and
-- second moments from finite binomial sums, and conclude with `variance_eq_sub`.
/-- Example 5.9 (2): Item (ii). The binomial law with parameters `n` and `p` has mean `pn` and
variance `p(1-p)n`. -/
theorem binomial_mean_variance (n : ℕ) (p : I) :
    (∫ x, x ∂Bin(ℝ, n, p)) = p * n ∧
      Var[id; Bin(ℝ, n, p)] = p * (1 - p) * n := by
  letI : IsProbabilityMeasure (Bin(ℝ, n, p)) :=
    Measure.isProbabilityMeasure_map measurableNatCastReal.aemeasurable
  refine ⟨binomialRealIntegralId_eq n p, ?_⟩
  -- Route correction: the proof now stays in the discrete singleton-mass expansion instead of the
  -- abandoned convolution route, so the variance step is just `variance_eq_sub` plus the moment
  -- formulas already established above.
  have hVariance :
      Var[id; Bin(ℝ, n, p)] =
        (∫ x, x ^ 2 ∂Bin(ℝ, n, p)) - (∫ x, x ∂Bin(ℝ, n, p)) ^ 2 := by
    simpa [Pi.pow_apply] using
      (variance_eq_sub (μ := Bin(ℝ, n, p)) (X := id) (memLpTwoIdBinomialReal n p))
  -- Substitute the computed moments and close the remaining polynomial identity.
  rw [hVariance, binomialRealIntegralSq_eq n p, binomialRealIntegralId_eq n p]
  ring

-- Proof sketch: compute the mean from the two-point Bernoulli law on `ℝ`, then evaluate the
-- variance either from the centered-square formula or from the identity `Var[X] = E[X²] - E[X]²`.
/-- Example 5.9 (1): Item (i). The Bernoulli law `Ber_p`, viewed as a probability measure on
`ℝ` via the canonical one-trial binomial law `Bin(ℝ, 1, p)`, has mean `p` and variance
`p(1-p)`. -/
theorem bernoulliReal_mean_variance (p : I) :
    (∫ x, x ∂Bin(ℝ, 1, p)) = p ∧
      Var[id; Bin(ℝ, 1, p)] = p * (1 - p) := by
  simpa using binomial_mean_variance 1 p

/- The Gaussian mean formula is `integral_id_gaussianReal`. -/
recall integral_id_gaussianReal

/- The Gaussian variance formula is `variance_id_gaussianReal`. -/
recall variance_id_gaussianReal

-- Proof sketch: this is exactly the pair of canonical Gaussian moment formulas
-- `integral_id_gaussianReal` and `variance_id_gaussianReal`.
/-- Example 5.9 (3): Item (iii). The Gaussian distribution `N_{μ,σ²}` has mean `μ` and variance
`σ²`. -/
theorem gaussianReal_mean_variance (μ σ2 : ℝ) (hσ2 : 0 < σ2) :
    (∫ x, x ∂gaussianReal μ ⟨σ2, hσ2.le⟩) = μ ∧
      Var[id; gaussianReal μ ⟨σ2, hσ2.le⟩] = σ2 := by
  exact ⟨integral_id_gaussianReal, variance_id_gaussianReal⟩

-- Proof sketch: integrate `x` and `(x - 1 / θ)^2` against the exponential density
-- `θ * exp (-θx)` on `[0, ∞)`, or equivalently reduce to the corresponding gamma-moment formulas
-- for shape `1`.
/-- Helper for Example 5.9: rewrite integration against `expMeasure θ` as integration against its
real-valued density. -/
lemma integral_expMeasure_eq_integral_density {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ} :
    ∫ x, f x ∂expMeasure θ = ∫ x, exponentialPDFReal θ x * f x := by
  -- Expand the exponential law as a `withDensity` measure and simplify the density to a real
  -- scalar multiplier.
  rw [expMeasure, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul (μ := volume) (f := gammaPDF 1 θ)
      (measurable_gammaPDFReal 1 θ).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp [gammaPDF, exponentialPDFReal, gammaPDFReal_nonneg zero_lt_one hθ x, smul_eq_mul]

/-- Helper for Example 5.9: the first moment of `expMeasure θ` is `1 / θ`. -/
lemma integral_id_expMeasure_eq_inv {θ : ℝ} (hθ : 0 < θ) :
    (∫ x, x ∂expMeasure θ) = 1 / θ := by
  have hGammaTwo : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num : (1 : ℝ) ≠ 0),
      Real.Gamma_one]
    norm_num
  -- Rewrite the expectation as a density integral supported on `[0, ∞)`.
  rw [integral_expMeasure_eq_integral_density hθ]
  have h_indicator :
      (fun x ↦ exponentialPDFReal θ x * x) =
        Set.indicator (Set.Ici 0) (fun x ↦ (θ * Real.exp (-(θ * x))) * x) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [exponentialPDFReal, gammaPDFReal, hx]
    · simp [exponentialPDFReal, gammaPDFReal, hx]
  rw [h_indicator, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    show (fun x ↦ (θ * Real.exp (-(θ * x))) * x) =
      fun x ↦ θ * (x ^ ((2 : ℝ) - 1) * Real.exp (-(θ * x))) by
        funext x
        rw [show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one]
        ring_nf,
    integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := θ)
      (by norm_num) hθ]
  rw [hGammaTwo]
  field_simp [hθ.ne']
  simp [one_div, inv_pow, hθ.ne']

/-- Helper for Example 5.9: the second moment of `expMeasure θ` is `2 / θ ^ 2`. -/
lemma integral_sq_expMeasure_eq_two_div_sq {θ : ℝ} (hθ : 0 < θ) :
    (∫ x, x ^ 2 ∂expMeasure θ) = 2 / θ ^ 2 := by
  have hGammaThree : Real.Gamma (3 : ℝ) = 2 := by
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num : (2 : ℝ) ≠ 0),
      show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num : (1 : ℝ) ≠ 0),
      Real.Gamma_one]
    norm_num
  -- The second moment is the same gamma integral with exponent parameter `3`.
  rw [integral_expMeasure_eq_integral_density hθ]
  have h_indicator :
      (fun x ↦ exponentialPDFReal θ x * x ^ 2) =
        Set.indicator (Set.Ici 0) (fun x ↦ (θ * Real.exp (-(θ * x))) * x ^ 2) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [exponentialPDFReal, gammaPDFReal, hx]
    · simp [exponentialPDFReal, gammaPDFReal, hx]
  rw [h_indicator, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    show (fun x ↦ (θ * Real.exp (-(θ * x))) * x ^ 2) =
      fun x ↦ θ * (x ^ ((3 : ℝ) - 1) * Real.exp (-(θ * x))) by
        funext x
        rw [show ((3 : ℝ) - 1) = 2 by norm_num]
        simp [mul_left_comm, mul_comm],
    integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := θ)
      (by norm_num) hθ]
  rw [hGammaThree]
  field_simp [hθ.ne']
  simp [one_div, inv_pow, hθ.ne']

/-- Helper for Example 5.9: `expMeasure θ` has a finite second moment. -/
lemma memLp_two_id_expMeasure {θ : ℝ} (hθ : 0 < θ) :
    MemLp id 2 (expMeasure θ) := by
  -- A nonzero second moment is enough to upgrade `x ↦ x^2` to an integrable function.
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 <| Integrable.of_integral_ne_zero ?_
  simpa [Pi.pow_apply] using show (∫ x, x ^ 2 ∂expMeasure θ) ≠ 0 by
    rw [integral_sq_expMeasure_eq_two_div_sq hθ]
    positivity

/-- Example 5.9 (4): Item (iv). The exponential distribution with rate `θ > 0` has mean `1 / θ`
and variance `1 / θ²`. -/
theorem expMeasure_mean_variance (θ : ℝ) (hθ : 0 < θ) :
    (∫ x, x ∂expMeasure θ) = 1 / θ ∧
      Var[id; expMeasure θ] = 1 / θ ^ 2 := by
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  refine ⟨integral_id_expMeasure_eq_inv hθ, ?_⟩
  -- Rewrite the variance through the first two moments and substitute the computed values.
  have hVariance :
      Var[id; expMeasure θ] =
        (∫ x, x ^ 2 ∂expMeasure θ) - (∫ x, x ∂expMeasure θ) ^ 2 := by
    simpa [Pi.pow_apply] using
      (variance_eq_sub (μ := expMeasure θ) (X := id) (memLp_two_id_expMeasure hθ))
  rw [hVariance, integral_sq_expMeasure_eq_two_div_sq hθ, integral_id_expMeasure_eq_inv hθ]
  field_simp [hθ.ne']
  ring
