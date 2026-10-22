/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_105
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Exercise_1_5_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Example_2_33

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory unitInterval
open scoped BigOperators ProbabilityTheory unitInterval NNReal

/-- The probability generating series of a measure on `ℕ`, evaluated at a real point `z`. -/
noncomputable def probabilityGeneratingSeries (μ : Measure ℕ) (z : ℝ) : ℝ :=
  ∑' n : ℕ, (μ {n}).toReal * z ^ n

/-- The positive convolution powers of a measure on `ℕ`, indexed so that `1` is the original
measure. -/
noncomputable def measureConvolutionPower (μ : Measure ℕ) (n : ℕ+) : Measure ℕ :=
  (fun ν : Measure ℕ ↦ ν ∗ μ)^[n.natPred] μ

/-- Helper for Example 3.4: the singleton mass of a convolution on `ℕ` is the finite antidiagonal
sum of the singleton masses of the two factors. -/
private lemma convolutionApplySingletonEqSumAntidiagonal
    {μ ν : Measure ℕ} [SFinite μ] [SFinite ν] (n : ℕ) :
    (μ ∗ ν) ({n} : Set ℕ) =
      ∑ p ∈ Finset.antidiagonal n, μ ({p.1} : Set ℕ) * ν ({p.2} : Set ℕ) := by
  -- Rewrite convolution as the pushforward along addition and identify the addition fiber.
  rw [Measure.conv, Measure.map_apply measurable_add (measurableSet_singleton n)]
  have hpreimage :
      (fun z : ℕ × ℕ ↦ z.1 + z.2) ⁻¹' ({n} : Set ℕ) = ↑(Finset.antidiagonal n) := by
    ext z
    simp [Finset.mem_antidiagonal]
  rw [hpreimage, ← MeasureTheory.sum_measure_singleton (μ := μ.prod ν)
    (s := Finset.antidiagonal n)]
  -- Each atom of the product measure splits as the product of the singleton masses.
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hsingleton :
      ({p} : Set (ℕ × ℕ)) = ({p.1} : Set ℕ) ×ˢ ({p.2} : Set ℕ) := by
    ext z
    rcases z with ⟨a, b⟩
    cases p
    simp
  rw [hsingleton]
  exact Measure.prod_prod (μ := μ) (ν := ν) ({p.1} : Set ℕ) ({p.2} : Set ℕ)

/-- Helper for Example 3.4: the successor step of the positive convolution powers is one more
convolution by the original measure. -/
private lemma measureConvolutionPower_succ (μ : Measure ℕ) (n : ℕ+) :
    measureConvolutionPower μ (n + 1) = measureConvolutionPower μ n ∗ μ := by
  -- Normalize the successor index on `ℕ+` so one more iterate becomes explicit.
  rw [PNat.add_one, measureConvolutionPower, Nat.natPred_succPNat, ← PNat.natPred_add_one n,
    measureConvolutionPower]
  simpa using (Function.iterate_succ_apply' (f := fun ν : Measure ℕ ↦ ν ∗ μ) n.natPred μ)

/-- Helper for Example 3.4: the subsets of `Set.Iio n` with cardinality `k` are exactly the
coercions of `((Finset.range n).powersetCard k)`. -/
private lemma cardinalityEvent_eq_image_powersetCardRange (n k : ℕ) :
    {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k} =
      ((((Finset.range n).powersetCard k).image ((↑) : Finset ℕ → Set ℕ)) : Set (Set ℕ)) := by
  classical
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

/-- Helper for Example 3.4: the `setBernoulli` law on `Set.Iio n` assigns the usual binomial mass
to one concrete `k`-subset of `Set.Iio n`, in the native `ℝ≥0∞` normal form. -/
private lemma setBernoulliIioSingletonMass (n k : ℕ) (p : I) {t : Finset ℕ}
    (ht : t ∈ (Finset.range n).powersetCard k) :
    setBer(Set.Iio n, p) ({(t : Set ℕ)} : Set (Set ℕ)) =
      ((toNNReal p : ENNReal) ^ k) * ((toNNReal (σ p) : ENNReal) ^ (n - k)) := by
  classical
  rw [Finset.mem_powersetCard] at ht
  have hsub : (t : Set ℕ) ⊆ Set.Iio n := by
    intro x hx
    exact Finset.mem_range.mp (ht.1 (by simpa using hx))
  -- Route correction: normalize the Bernoulli singleton mass before any `ofReal` transport.
  rw [ProbabilityTheory.setBernoulli_singleton (u := Set.Iio n) (p := p) (s := (t : Set ℕ))
    hsub (Set.toFinite _)]
  -- The complement cardinality is the ambient size minus the chosen subset size.
  rw [Set.ncard_diff hsub, Set.ncard_Iio_nat]
  simp [ht.2]

/-- Helper for Example 3.4: the `setBernoulli` law on `Set.Iio n` assigns the usual binomial mass
to the event that the chosen subset has cardinality `k`, viewed in native `ℝ≥0∞` form. -/
private lemma setBernoulliIio_apply_card_native (n k : ℕ) (p : I) :
    setBer(Set.Iio n, p) {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k} =
      (Nat.choose n k : ENNReal) * ((toNNReal p : ENNReal) ^ k) *
        ((toNNReal (σ p) : ENNReal) ^ (n - k)) := by
  classical
  -- Rewrite the cardinality event as a finite image so the measure becomes a finite singleton sum.
  rw [cardinalityEvent_eq_image_powersetCardRange]
  rw [← MeasureTheory.sum_measure_singleton (μ := setBer(Set.Iio n, p))
    (s := ((Finset.range n).powersetCard k).image ((↑) : Finset ℕ → Set ℕ))]
  rw [Finset.sum_image]
  · -- Each singleton mass is the same native Bernoulli weight from the previous lemma.
    calc
      ∑ t ∈ (Finset.range n).powersetCard k,
          setBer(Set.Iio n, p) ({(t : Set ℕ)} : Set (Set ℕ))
        = ∑ t ∈ (Finset.range n).powersetCard k,
            ((toNNReal p : ENNReal) ^ k) * ((toNNReal (σ p) : ENNReal) ^ (n - k)) := by
              refine Finset.sum_congr rfl fun t ht ↦ ?_
              rw [setBernoulliIioSingletonMass n k p ht]
      _ = (Nat.choose n k : ENNReal) * ((toNNReal p : ENNReal) ^ k) *
            ((toNNReal (σ p) : ENNReal) ^ (n - k)) := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_range]
              rw [mul_assoc]
  · intro s _ t _ hst
    simpa using hst

/-- Helper for Example 3.4: taking `toReal` of the native `ℝ≥0∞` Bernoulli cardinality mass
recovers the usual real-valued binomial weight. -/
private lemma setBernoulliIio_apply_card_native_toReal (n k : ℕ) (p : I) :
    (setBer(Set.Iio n, p) {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k}).toReal =
      (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
  have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
  have hq_nonneg : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  rw [setBernoulliIio_apply_card_native, ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp

/-- Helper for Example 3.4: the `setBernoulli` law on `Set.Iio n` assigns the usual binomial mass
to the event that the chosen subset has cardinality `k`, viewed in `ℝ≥0∞`. -/
private lemma setBernoulliIio_apply_card (n k : ℕ) (p : I) :
    setBer(Set.Iio n, p) {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k} =
      ENNReal.ofReal ((Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) := by
  have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
  have hq_nonneg : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  have hnonneg :
      0 ≤ (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
    exact
      mul_nonneg
        (mul_nonneg (by positivity) (pow_nonneg hp_nonneg _))
        (pow_nonneg hq_nonneg _)
  -- Compare the two finite `ℝ≥0∞` masses through their real values.
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hnonneg]
  exact setBernoulliIio_apply_card_native_toReal n k p

/-- Helper for Example 3.4: the `setBernoulli` law on `Set.Iio n` assigns the usual binomial mass
to the event that the chosen subset has cardinality `k`. -/
private lemma setBernoulliIio_apply_card_toReal (n k : ℕ) (p : I) :
    (setBer(Set.Iio n, p) {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k}).toReal =
      (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
  exact setBernoulliIio_apply_card_native_toReal n k p

/-- Helper for Example 3.4: the singleton masses of the binomial law are given by the standard
choose formula, viewed in `ℝ`. -/
private lemma binomial_apply_singleton_toReal (n k : ℕ) (p : I) :
    (binomial n p ({k} : Set ℕ)).toReal =
      (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
  -- Rewrite the singleton event under the `ncard` pushforward, then add the missing subset
  -- condition using the almost-sure support of `setBer(Set.Iio n, p)`.
  rw [ProbabilityTheory.binomial, Measure.map_apply measurable_ncard (measurableSet_singleton k)]
  change (setBer(Set.Iio n, p) {s : Set ℕ | s.ncard = k}).toReal =
    (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)
  have hEvent :
      setBer(Set.Iio n, p) {s : Set ℕ | s.ncard = k} =
        setBer(Set.Iio n, p) {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k} := by
    refine measure_congr ?_
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := Set.Iio n) (p := p)] with s hs
    apply propext
    constructor
    · intro hk
      exact ⟨hs, hk⟩
    · intro hk
      exact hk.2
  rw [hEvent]
  exact setBernoulliIio_apply_card_toReal n k p

/-- Helper for Example 3.4: the singleton masses of the binomial law are given by the standard
choose formula, viewed as an `ENNReal` mass. -/
private lemma binomial_apply_singleton (n k : ℕ) (p : I) :
    binomial n p ({k} : Set ℕ) =
      ENNReal.ofReal ((Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) := by
  -- Recover the `ENNReal` mass from its `toReal` value; singleton masses of a probability law are
  -- finite.
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), binomial_apply_singleton_toReal]

/-- Helper for Example 3.4: the singleton mass of `poissonMeasure r` is the explicit Poisson
weight `poissonPMFReal r n`. -/
private lemma poissonMeasure_apply_singleton (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Rewrite the Poisson measure as the measure attached to its canonical `PMF`.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Example 3.4: the singleton mass of `geometricMeasure hp hp_le_one` is the explicit
geometric weight `geometricPMFReal p n`. -/
private lemma geometricMeasure_apply_singleton {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1) (n : ℕ) :
    geometricMeasure hp hp_le_one ({n} : Set ℕ) = ENNReal.ofReal (geometricPMFReal p n) := by
  -- Rewrite the geometric measure as the measure attached to its canonical `PMF`.
  simpa [geometricMeasure, geometricPMF] using
    (PMF.toMeasure_apply_singleton (geometricPMF hp hp_le_one) n (measurableSet_singleton n))

/-- Helper for Example 3.4: integer-shape negative-binomial masses are nonnegative for admissible
success parameter `p`. -/
private lemma negativeBinomialMass_natShape_nonneg {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1)
    (n : ℕ+) (k : ℕ) :
    0 ≤ negativeBinomialMass ((n : ℕ) : ℝ) p k := by
  rw [negativeBinomialMass_eq_waitingTimeMass n.pos p]
  positivity [sub_nonneg.mpr hp_le_one]

/-- Helper for Example 3.4: the hockey-stick identity in the casted range-sum normal form used by
the geometric convolution proof. -/
private lemma sumRangeAddChooseCast (d k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (Nat.choose (i + d) d : ℝ)) =
      (Nat.choose (k + d + 1) (d + 1) : ℝ) := by
  -- Cast the natural-number hockey-stick identity once so later proofs can stay in `ℝ`.
  exact_mod_cast (Nat.sum_range_add_choose k d)

/-- Helper for Example 3.4: convolving an integer-shape negative-binomial mass with one geometric
step collapses to the next integer shape. -/
private lemma sumAntidiagonalNegativeBinomialNatShapeGeometric {p : ℝ} (_hp : 0 < p)
    (n : ℕ+) (k : ℕ) :
    ∑ ij ∈ Finset.antidiagonal k,
        negativeBinomialMass ((n : ℕ) : ℝ) p ij.1 * geometricPMFReal p ij.2 =
      negativeBinomialMass ((((n + 1 : ℕ+) : ℕ) : ℝ)) p k := by
  have hpred : ((n : ℕ) - 1) + 1 = (n : ℕ) := Nat.sub_add_cancel (Nat.succ_le_of_lt n.pos)
  have hterm :
      ∀ m ∈ Finset.range (k + 1),
        negativeBinomialMass ((n : ℕ) : ℝ) p m * geometricPMFReal p (k - m) =
          (Nat.choose (m + ((n : ℕ) - 1)) ((n : ℕ) - 1) : ℝ) *
            (p ^ ((n : ℕ) + 1) * (1 - p) ^ k) := by
    intro m hm
    have hm_le : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hchooseNat :
        Nat.choose ((n : ℕ) + m - 1) m = Nat.choose (m + ((n : ℕ) - 1)) ((n : ℕ) - 1) := by
      calc
        Nat.choose ((n : ℕ) + m - 1) m = Nat.choose (m + ((n : ℕ) - 1)) m := by
          congr 1
          omega
        _ = Nat.choose (m + ((n : ℕ) - 1)) ((n : ℕ) - 1) := by
          simpa [Nat.add_comm] using
            (Nat.choose_symm_add (a := m) (b := (n : ℕ) - 1))
    have hchoose :
        (Nat.choose ((n : ℕ) + m - 1) m : ℝ) =
          (Nat.choose (m + ((n : ℕ) - 1)) ((n : ℕ) - 1) : ℝ) := by
      exact_mod_cast hchooseNat
    -- Route correction: normalize the antidiagonal summand completely in `ℝ` before summing.
    calc
      negativeBinomialMass ((n : ℕ) : ℝ) p m * geometricPMFReal p (k - m)
        = ((Nat.choose ((n : ℕ) + m - 1) m : ℝ) * p ^ (n : ℕ) * (1 - p) ^ m) *
            ((1 - p) ^ (k - m) * p) := by
              rw [negativeBinomialMass_eq_waitingTimeMass (n := (n : ℕ)) (k := m) n.pos p,
                geometricPMFReal]
      _ = (Nat.choose ((n : ℕ) + m - 1) m : ℝ) *
            ((p ^ (n : ℕ) * p) * ((1 - p) ^ m * (1 - p) ^ (k - m))) := by
              ring
      _ = (Nat.choose ((n : ℕ) + m - 1) m : ℝ) *
            (p ^ ((n : ℕ) + 1) * (1 - p) ^ k) := by
              rw [← pow_succ, ← pow_add, Nat.add_sub_of_le hm_le]
      _ = (Nat.choose (m + ((n : ℕ) - 1)) ((n : ℕ) - 1) : ℝ) *
            (p ^ ((n : ℕ) + 1) * (1 - p) ^ k) := by
              rw [hchoose]
  -- Rewrite the antidiagonal as a range sum, then collapse the remaining choose sum once.
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    ∑ m ∈ Finset.range (k + 1),
        negativeBinomialMass ((n : ℕ) : ℝ) p m * geometricPMFReal p (k - m)
      = ∑ m ∈ Finset.range (k + 1),
          (Nat.choose (m + ((n : ℕ) - 1)) ((n : ℕ) - 1) : ℝ) *
            (p ^ ((n : ℕ) + 1) * (1 - p) ^ k) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [hterm m hm]
    _ = (∑ m ∈ Finset.range (k + 1),
          (Nat.choose (m + ((n : ℕ) - 1)) ((n : ℕ) - 1) : ℝ)) *
            (p ^ ((n : ℕ) + 1) * (1 - p) ^ k) := by
              rw [Finset.sum_mul]
    _ = (Nat.choose (k + ((n : ℕ) - 1) + 1) (((n : ℕ) - 1) + 1) : ℝ) *
          (p ^ ((n : ℕ) + 1) * (1 - p) ^ k) := by
            rw [sumRangeAddChooseCast]
    _ = (Nat.choose (k + (n : ℕ)) (n : ℕ) : ℝ) * (p ^ ((n : ℕ) + 1) * (1 - p) ^ k) := by
          simp [hpred, Nat.add_assoc]
    _ = (Nat.choose (k + (n : ℕ)) k : ℝ) * (p ^ ((n : ℕ) + 1) * (1 - p) ^ k) := by
          rw [Nat.choose_symm_add]
    _ = negativeBinomialMass ((((n + 1 : ℕ+) : ℕ) : ℝ)) p k := by
          -- Finish by rewriting the next integer shape back to the waiting-time mass.
          have hsucc : (((n + 1 : ℕ+) : ℕ)) = (n : ℕ) + 1 := by
            rw [PNat.add_one, Nat.succPNat_coe]
          rw [hsucc]
          rw [show (Nat.choose (k + (n : ℕ)) k : ℝ) * (p ^ ((n : ℕ) + 1) * (1 - p) ^ k) =
              (Nat.choose (k + (n : ℕ)) k : ℝ) * p ^ ((n : ℕ) + 1) * (1 - p) ^ k by ring]
          have hchoose :
              (Nat.choose (k + (n : ℕ)) k : ℝ) =
                (Nat.choose (k + ((n : ℕ) + 1) - 1) k : ℝ) := by
            simp
          rw [hchoose]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            using
              (negativeBinomialMass_eq_waitingTimeMass (n := ((n : ℕ) + 1)) (k := k)
                (Nat.succ_pos _) p).symm

/-- The probability generating function of the binomial law is `(p z + (1 - p))^n`. -/
theorem example_3_4_binomial_pgf (n : ℕ) (p : I) (z : ℝ) :
    probabilityGeneratingSeries (binomial n p) z = (p * z + (1 - p)) ^ n := by
  -- Rewrite the generating series as a finite sum because all singleton masses vanish above `n`.
  rw [probabilityGeneratingSeries]
  calc
    ∑' m : ℕ, (binomial n p {m}).toReal * z ^ m
      = ∑ m ∈ Finset.range (n + 1), (binomial n p {m}).toReal * z ^ m := by
          refine tsum_eq_sum fun m hm ↦ ?_
          have hmn : n < m := Nat.lt_of_not_ge fun hle ↦
            hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
          rw [binomial_apply_singleton_toReal, Nat.choose_eq_zero_of_lt hmn]
          simp
    _ = ∑ m ∈ Finset.range (n + 1),
          (Nat.choose n m : ℝ) * ((p : ℝ) ^ m * z ^ m) * (1 - (p : ℝ)) ^ (n - m) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [binomial_apply_singleton_toReal]
          ring
    _ = ∑ m ∈ Finset.range (n + 1),
          (Nat.choose n m : ℝ) * (((p : ℝ) * z) ^ m) * (1 - (p : ℝ)) ^ (n - m) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [← mul_pow]
    _ = (p * z + (1 - p)) ^ n := by
          simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using
            (add_pow ((p : ℝ) * z) (1 - (p : ℝ)) n).symm

/-- Helper for Example 3.4: one antidiagonal summand in the binomial convolution already carries
the common `k`-power and `(m + n - k)`-power once the indices add to `k`. -/
private lemma binomialConvolutionSummand {p : ℝ} (m n k i j : ℕ) (hk : i + j = k) :
    (((Nat.choose m i : ℝ) * p ^ i * (1 - p) ^ (m - i)) *
      ((Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j))) =
      (((Nat.choose m i : ℝ) * (Nat.choose n j : ℝ)) * p ^ k * (1 - p) ^ (m + n - k)) := by
  by_cases hi : i ≤ m
  · by_cases hj : j ≤ n
    · have hsub : (m - i) + (n - j) = m + n - k := by
        omega
      calc
        (((Nat.choose m i : ℝ) * p ^ i * (1 - p) ^ (m - i)) *
            ((Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j)))
          = (((Nat.choose m i : ℝ) * (Nat.choose n j : ℝ)) * (p ^ i * p ^ j) *
              ((1 - p) ^ (m - i) * (1 - p) ^ (n - j))) := by
                ring
        _ = (((Nat.choose m i : ℝ) * (Nat.choose n j : ℝ)) * p ^ (i + j) *
              (1 - p) ^ ((m - i) + (n - j))) := by
                rw [← pow_add, ← pow_add]
        _ = (((Nat.choose m i : ℝ) * (Nat.choose n j : ℝ)) * p ^ k *
              (1 - p) ^ (m + n - k)) := by
                rw [hk, hsub]
    · have hj' : n < j := Nat.lt_of_not_ge hj
      rw [Nat.choose_eq_zero_of_lt hj']
      ring
  · have hi' : m < i := Nat.lt_of_not_ge hi
    rw [Nat.choose_eq_zero_of_lt hi']
    ring

/-- Helper for Example 3.4: once each summand has been normalized, the remaining real
antidiagonal sum is exactly Vandermonde's identity times the common weight. -/
private lemma binomialConvolutionAntidiagonalReal (m n k : ℕ) (p : ℝ) :
    ∑ ij ∈ Finset.antidiagonal k,
        (((Nat.choose m ij.1 : ℝ) * (Nat.choose n ij.2 : ℝ)) *
          p ^ k * (1 - p) ^ (m + n - k)) =
      (Nat.choose (m + n) k : ℝ) * p ^ k * (1 - p) ^ (m + n - k) := by
  have hchoose :
      ∑ ij ∈ Finset.antidiagonal k,
          ((Nat.choose m ij.1 : ℝ) * (Nat.choose n ij.2 : ℝ)) =
        (Nat.choose (m + n) k : ℝ) := by
    exact_mod_cast (Nat.add_choose_eq m n k).symm
  -- Factor out the common real weight so only Vandermonde remains.
  calc
    ∑ ij ∈ Finset.antidiagonal k,
        (((Nat.choose m ij.1 : ℝ) * (Nat.choose n ij.2 : ℝ)) *
          p ^ k * (1 - p) ^ (m + n - k))
      = ∑ ij ∈ Finset.antidiagonal k,
          ((Nat.choose m ij.1 : ℝ) * (Nat.choose n ij.2 : ℝ)) *
            (p ^ k * (1 - p) ^ (m + n - k)) := by
              refine Finset.sum_congr rfl ?_
              intro ij hij
              ring
    _ = (∑ ij ∈ Finset.antidiagonal k,
          ((Nat.choose m ij.1 : ℝ) * (Nat.choose n ij.2 : ℝ))) *
            (p ^ k * (1 - p) ^ (m + n - k)) := by
              rw [Finset.sum_mul]
    _ = (Nat.choose (m + n) k : ℝ) * (p ^ k * (1 - p) ^ (m + n - k)) := by
          rw [hchoose]
    _ = (Nat.choose (m + n) k : ℝ) * p ^ k * (1 - p) ^ (m + n - k) := by
          ring

/-- Binomial laws with a common success probability are stable under convolution. -/
theorem example_3_4_binomial_conv (m n : ℕ) (p : I) :
    binomial m p ∗ binomial n p = binomial (m + n) p := by
  have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
  have hq_nonneg : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  -- Compare singleton masses on the discrete space `ℕ`.
  refine Measure.ext_of_singleton fun k ↦ ?_
  rw [convolutionApplySingletonEqSumAntidiagonal]
  calc
    ∑ ij ∈ Finset.antidiagonal k,
        binomial m p ({ij.1} : Set ℕ) * binomial n p ({ij.2} : Set ℕ)
      = ∑ ij ∈ Finset.antidiagonal k,
          ENNReal.ofReal
            ((((Nat.choose m ij.1 : ℝ) * (Nat.choose n ij.2 : ℝ)) *
              (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m + n - k))) := by
              refine Finset.sum_congr rfl ?_
              intro ij hij
              have hk : ij.1 + ij.2 = k := by
                simpa [Finset.mem_antidiagonal] using hij
              have hm_nonneg :
                  0 ≤ (Nat.choose m ij.1 : ℝ) * (p : ℝ) ^ ij.1 *
                    (1 - (p : ℝ)) ^ (m - ij.1) := by
                positivity [sub_nonneg.mpr p.2.2]
              -- Normalize each singleton product to the common real antidiagonal summand.
              rw [binomial_apply_singleton, binomial_apply_singleton]
              calc
                ENNReal.ofReal
                    ((Nat.choose m ij.1 : ℝ) * (p : ℝ) ^ ij.1 * (1 - (p : ℝ)) ^ (m - ij.1)) *
                    ENNReal.ofReal
                      ((Nat.choose n ij.2 : ℝ) * (p : ℝ) ^ ij.2 *
                        (1 - (p : ℝ)) ^ (n - ij.2))
                  = ENNReal.ofReal
                      (((Nat.choose m ij.1 : ℝ) * (p : ℝ) ^ ij.1 *
                        (1 - (p : ℝ)) ^ (m - ij.1)) *
                        ((Nat.choose n ij.2 : ℝ) * (p : ℝ) ^ ij.2 *
                          (1 - (p : ℝ)) ^ (n - ij.2))) := by
                            simpa using (ENNReal.ofReal_mul hm_nonneg).symm
                _ = ENNReal.ofReal
                      ((((Nat.choose m ij.1 : ℝ) * (Nat.choose n ij.2 : ℝ)) *
                        (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m + n - k))) := by
                          congr 1
                          exact
                            binomialConvolutionSummand (m := m) (n := n) (k := k) (i := ij.1)
                              (j := ij.2) hk
    _ = ENNReal.ofReal
          (∑ ij ∈ Finset.antidiagonal k,
            (((Nat.choose m ij.1 : ℝ) * (Nat.choose n ij.2 : ℝ)) *
              (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m + n - k))) := by
            symm
            exact ENNReal.ofReal_sum_of_nonneg fun ij hij ↦
              mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp_nonneg _))
                (pow_nonneg hq_nonneg _)
    _ = ENNReal.ofReal
          ((Nat.choose (m + n) k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (m + n - k)) := by
            rw [binomialConvolutionAntidiagonalReal]
    _ = binomial (m + n) p ({k} : Set ℕ) := by
          rw [binomial_apply_singleton]

/-- The probability generating function of the Poisson law with rate `lam` is
`exp (lam * (z - 1))`. -/
theorem example_3_4_poisson_pgf (lam : ℝ≥0) (z : ℝ) :
    probabilityGeneratingSeries (poissonMeasure lam) z = Real.exp (lam * (z - 1)) := by
  have hseries :
      HasSum (fun n : ℕ ↦ Real.exp (-((lam : ℝ))) * (((lam : ℝ) * z) ^ n / ↑n.factorial))
        (Real.exp (-((lam : ℝ))) * Real.exp ((lam : ℝ) * z)) :=
    by
      simpa [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * z)).mul_left (Real.exp (-((lam : ℝ))))
  -- Rewrite the Poisson generating series into the exponential power series.
  rw [probabilityGeneratingSeries]
  calc
    ∑' n : ℕ, (poissonMeasure lam {n}).toReal * z ^ n
      = ∑' n : ℕ, Real.exp (-((lam : ℝ))) * (((lam : ℝ) * z) ^ n / ↑n.factorial) := by
          refine tsum_congr fun n ↦ ?_
          rw [poissonMeasure_apply_singleton, ENNReal.toReal_ofReal poissonPMFReal_nonneg]
          rw [poissonPMFReal]
          have hfac : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
          field_simp [hfac]
          ring
    _ = Real.exp (-((lam : ℝ))) * Real.exp ((lam : ℝ) * z) := hseries.tsum_eq
    _ = Real.exp ((lam : ℝ) * (z - 1)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- Poisson laws are stable under convolution, with rates adding. -/
theorem example_3_4_poisson_conv (lam mu : ℝ≥0) :
    poissonMeasure lam ∗ poissonMeasure mu = poissonMeasure (lam + mu) := by
  -- Reuse the earlier Poisson convolution theorem directly.
  simpa using poissonMeasure_conv_poissonMeasure lam mu

/-- The probability generating function of the geometric law is `p / (1 - (1 - p) * z)` on
`[0,1]`. -/
theorem example_3_4_geometric_pgf {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingSeries (geometricMeasure hp hp_le_one) z = p / (1 - (1 - p) * z) := by
  have hz_nonneg : 0 ≤ z := hz.1
  have hz_le_one : z ≤ 1 := hz.2
  have hr_nonneg : 0 ≤ (1 - p) * z := mul_nonneg (sub_nonneg.mpr hp_le_one) hz_nonneg
  have hr_lt_one : (1 - p) * z < 1 := by
    have hmul_le : (1 - p) * z ≤ (1 - p) * 1 := by
      exact mul_le_mul_of_nonneg_left hz_le_one (sub_nonneg.mpr hp_le_one)
    have hsub_lt : 1 - p < 1 := sub_lt_self 1 hp
    simpa using lt_of_le_of_lt hmul_le (by simpa using hsub_lt)
  have hseries :
      HasSum (fun n : ℕ ↦ p * (((1 - p) * z) ^ n)) (p * (1 / (1 - (1 - p) * z))) :=
    by
      simpa [one_div] using (hasSum_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left p
  -- Rewrite the geometric generating series into the geometric power series.
  rw [probabilityGeneratingSeries]
  calc
    ∑' n : ℕ, (geometricMeasure hp hp_le_one {n}).toReal * z ^ n
      = ∑' n : ℕ, p * (((1 - p) * z) ^ n) := by
          refine tsum_congr fun n ↦ ?_
          rw [geometricMeasure_apply_singleton hp hp_le_one, ENNReal.toReal_ofReal]
          · rw [geometricPMFReal]
            calc
              ((1 - p) ^ n * p) * z ^ n = p * (((1 - p) ^ n) * z ^ n) := by ring
              _ = p * (((1 - p) * z) ^ n) := by rw [← mul_pow]
          · exact geometricPMFReal_nonneg hp hp_le_one
    _ = p * (1 / (1 - (1 - p) * z)) := hseries.tsum_eq
    _ = p / (1 - (1 - p) * z) := by ring

/-- The `n`th positive convolution power of the geometric law has the negative binomial point
masses from the example. -/
theorem example_3_4_geometric_conv_power_apply {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1)
    (n : ℕ+) (k : ℕ) :
    measureConvolutionPower (geometricMeasure hp hp_le_one) n {k} =
      ENNReal.ofReal (negativeBinomialMass ((n : ℕ) : ℝ) p k) := by
  -- Prove the singleton formula by induction on the positive convolution exponent.
  refine PNat.recOn n ?_ ?_ k
  · intro k
    -- The first positive convolution power is the geometric law itself.
    calc
      measureConvolutionPower (geometricMeasure hp hp_le_one) 1 {k}
        = geometricMeasure hp hp_le_one {k} := by
            rw [measureConvolutionPower]
            rfl
      _ = ENNReal.ofReal (geometricPMFReal p k) := geometricMeasure_apply_singleton hp hp_le_one k
      _ = ENNReal.ofReal (negativeBinomialMass (((1 : ℕ+) : ℕ) : ℝ) p k) := by
            -- Route correction: rewrite the shape-`1` negative-binomial mass to the waiting-time
            -- form so it matches the geometric singleton mass exactly.
            congr 1
            simpa [geometricPMFReal, mul_comm] using
              (negativeBinomialMass_eq_waitingTimeMass (n := 1) (k := k) (by decide) p).symm
  · intro n ih k
    -- Unfold one more convolution step and compare the resulting singleton masses.
    rw [measureConvolutionPower_succ, convolutionApplySingletonEqSumAntidiagonal]
    calc
      ∑ ij ∈ Finset.antidiagonal k,
          measureConvolutionPower (geometricMeasure hp hp_le_one) n ({ij.1} : Set ℕ) *
            geometricMeasure hp hp_le_one ({ij.2} : Set ℕ)
        = ∑ ij ∈ Finset.antidiagonal k,
            ENNReal.ofReal
              (negativeBinomialMass ((n : ℕ) : ℝ) p ij.1 * geometricPMFReal p ij.2) := by
                refine Finset.sum_congr rfl ?_
                intro ij hij
                -- Rewrite both singleton masses through their real-valued formulas.
                rw [ih ij.1, geometricMeasure_apply_singleton hp hp_le_one ij.2,
                  ENNReal.ofReal_mul (negativeBinomialMass_natShape_nonneg hp hp_le_one n ij.1)]
      _ = ENNReal.ofReal
            (∑ ij ∈ Finset.antidiagonal k,
              negativeBinomialMass ((n : ℕ) : ℝ) p ij.1 * geometricPMFReal p ij.2) := by
              symm
              exact ENNReal.ofReal_sum_of_nonneg fun ij hij ↦
                mul_nonneg (negativeBinomialMass_natShape_nonneg hp hp_le_one n ij.1)
                  (geometricPMFReal_nonneg hp hp_le_one)
      _ = ENNReal.ofReal (negativeBinomialMass ((((n + 1 : ℕ+) : ℕ) : ℝ)) p k) := by
            rw [sumAntidiagonalNegativeBinomialNatShapeGeometric hp n k]

-- Proof sketch: apply the closed formulas for the singleton masses of the binomial, Poisson,
-- and geometric laws, compute the corresponding generating series, and use the convolution law
-- for sums of independent `ℕ`-valued random variables.
/-- Example 3.4: Binomial, Poisson, and geometric laws have the generating functions and
convolution identities displayed in the example, with geometric convolution powers given by the
negative binomial mass formula. -/
theorem example_3_4 :
    (∀ (n : ℕ) (p : I) (z : ℝ),
      probabilityGeneratingSeries (binomial n p) z = (p * z + (1 - p)) ^ n) ∧
      (∀ (m n : ℕ) (p : I),
        binomial m p ∗ binomial n p = binomial (m + n) p) ∧
      (∀ (lam : ℝ≥0) (z : ℝ),
        probabilityGeneratingSeries (poissonMeasure lam) z = Real.exp (lam * (z - 1))) ∧
      (∀ lam mu : ℝ≥0,
        poissonMeasure lam ∗ poissonMeasure mu = poissonMeasure (lam + mu)) ∧
      (∀ {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1) {z : ℝ},
        z ∈ Set.Icc (0 : ℝ) 1 →
          probabilityGeneratingSeries (geometricMeasure hp hp_le_one) z =
            p / (1 - (1 - p) * z)) ∧
      (∀ {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1) (n : ℕ+) (k : ℕ),
        measureConvolutionPower (geometricMeasure hp hp_le_one) n {k} =
          ENNReal.ofReal (negativeBinomialMass ((n : ℕ) : ℝ) p k)) := by
  refine ⟨example_3_4_binomial_pgf, example_3_4_binomial_conv, example_3_4_poisson_pgf,
    example_3_4_poisson_conv, ?_, example_3_4_geometric_conv_power_apply⟩
  intro p hp hp_le_one z hz
  exact example_3_4_geometric_pgf hp hp_le_one hz
