/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

section BernsteinChernoff

variable (P : Measure Ω) [IsProbabilityMeasure P]
variable {n : ℕ} (p : Fin n → I) (X : Fin n → Ω → ℝ)
variable (hX_indep : iIndepFun X P) (hX_law : ∀ i, HasLaw (X i) (Bin(ℝ, 1, p i)) P)

local notation "m" => ∑ i, (p i : ℝ)

omit [IsProbabilityMeasure P] in
/-- Helper for Exercise 5.2.1: a random variable with law `Bin(ℝ, 1, p)` is almost surely
`0` or `1`. -/
lemma ae_eq_zero_or_one_of_hasLaw_binomialOne {Y : Ω → ℝ} {q : I}
    (hY : HasLaw Y (Bin(ℝ, 1, q)) P) :
    ∀ᵐ ω ∂P, Y ω = 0 ∨ Y ω = 1 := by
  have hMeasZeroOrOne : Measurable fun x : ℝ ↦ x = 0 ∨ x = 1 := by
    fun_prop
  have htarget : ∀ᵐ x ∂(Bin(ℝ, 1, q)), x = 0 ∨ x = 1 := by
    have hNat : HasLaw (fun n : ℕ ↦ (n : ℝ)) (Bin(ℝ, 1, q)) (Bin(1, q)) := by
      refine ⟨?_, rfl⟩
      have hmeas : Measurable (fun n : ℕ ↦ (n : ℝ)) := by fun_prop
      exact hmeas.aemeasurable
    -- The one-trial binomial law on `ℕ` only charges `0` and `1`.
    have hModel : ∀ᵐ x : ℕ ∂(Bin(1, q)), (x : ℝ) = 0 ∨ (x : ℝ) = 1 := by
      have hle :
          ∀ᵐ x ∂(Bin(1, q)), x ≤ 1 :=
        ProbabilityTheory.ae_le_of_hasLaw_binomial (P := Bin(1, q)) (X := id)
          (p := q) (n := 1) HasLaw.id
      filter_upwards [hle] with x hx
      interval_cases x <;> simp
    exact (ProbabilityTheory.HasLaw.ae_iff (X := fun n : ℕ ↦ (n : ℝ))
      (μ := Bin(ℝ, 1, q)) (P := Bin(1, q)) hNat
      (p := fun x => x = 0 ∨ x = 1) hMeasZeroOrOne).1 hModel
  -- Transfer the `{0,1}`-valued statement from the model law to `Y`.
  exact (ProbabilityTheory.HasLaw.ae_iff (X := Y) (μ := Bin(ℝ, 1, q)) (P := P) hY
    (p := fun x => x = 0 ∨ x = 1) hMeasZeroOrOne).2 htarget

/-- Helper for Exercise 5.2.1: a `Bin(ℝ, 1, q)`-distributed variable is integrable because it is
almost surely bounded by `1`. -/
lemma integrable_of_hasLaw_binomialOne {Y : Ω → ℝ} {q : I}
    (hY : HasLaw Y (Bin(ℝ, 1, q)) P) :
    Integrable Y P := by
  -- The a.s. `{0,1}`-valued description gives the uniform `‖Y‖ ≤ 1` bound.
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
    hY.aemeasurable.aestronglyMeasurable ?_
  filter_upwards [ae_eq_zero_or_one_of_hasLaw_binomialOne (P := P) hY] with ω hω
  rcases hω with h0 | h1
  · simp [h0]
  · simp [h1]

/-- Helper for Exercise 5.2.1: on `{0,1}`, the exponential kernel is affine. -/
lemma exp_mul_eq_one_add_mul_of_zero_one {t x : ℝ} (hx : x = 0 ∨ x = 1) :
    Real.exp (t * x) = 1 + (Real.exp t - 1) * x := by
  rcases hx with rfl | rfl <;> simp [sub_eq_add_neg]

/-- Helper for Exercise 5.2.1: a subset of `Set.Iio 1` is either empty or `{0}`. -/
lemma eq_empty_or_singleton_zero_of_subset_Iio_one {s : Set ℕ} (hs : s ⊆ Set.Iio 1) :
    s = ∅ ∨ s = ({0} : Set ℕ) := by
  -- A subset of `{n | n < 1}` can only contain the unique natural number `0`.
  have hs0 : s ⊆ ({0} : Set ℕ) := by
    intro k hk
    have hk0 : k = 0 := by
      have hk1 : k < 1 := hs hk
      omega
    simp [hk0]
  by_cases h0 : 0 ∈ s
  · right
    ext k
    constructor
    · intro hk
      exact hs0 hk
    · intro hk
      simpa using hk ▸ h0
  · left
    ext k
    constructor
    · intro hk
      have hk1 : k < 1 := hs hk
      have hk0 : k = 0 := by omega
      exact (h0 <| hk0 ▸ hk).elim
    · intro hk
      simp at hk

/-- Helper for Exercise 5.2.1: the natural-valued one-trial binomial law assigns mass `q` to
`{1}`. -/
lemma binomialOne_apply_singleton_one (q : I) :
    Bin(1, q) ({1} : Set ℕ) = ENNReal.ofReal (q : ℝ) := by
  -- Unfold the one-trial binomial law to the `setBer (Set.Iio 1, q)` model.
  rw [ProbabilityTheory.binomial, Measure.map_apply measurable_ncard (measurableSet_singleton 1)]
  have hsingleton_zero_subset_Iio_one : ({0} : Set ℕ) ⊆ Set.Iio 1 := by
    simp
  have hEvent :
      Set.ncard ⁻¹' ({1} : Set ℕ) =ᵐ[setBer(Set.Iio 1, q)]
        ({({0} : Set ℕ)} : Set (Set ℕ)) := by
    -- Inside `Set.Iio 1`, cardinality `1` forces the unique singleton `{0}`.
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := Set.Iio 1) (p := q)] with s hs
    rcases eq_empty_or_singleton_zero_of_subset_Iio_one hs with rfl | rfl
    · apply propext
      constructor
      · intro h
        change Set.ncard (∅ : Set ℕ) = 1 at h
        simp at h
      · intro h
        change (∅ : Set ℕ) = ({0} : Set ℕ) at h
        simp at h
    · apply propext
      constructor
      · intro h
        trivial
      · intro h
        change Set.ncard ({0} : Set ℕ) = 1
        simp
  rw [measure_congr hEvent]
  calc
    setBer(Set.Iio 1, q) ({({0} : Set ℕ)} : Set (Set ℕ))
        = unitInterval.toNNReal q ^ ({0} : Set ℕ).ncard
            * unitInterval.toNNReal (σ q) ^ (Set.Iio 1 \ ({0} : Set ℕ)).ncard := by
              rw [ProbabilityTheory.setBernoulli_singleton (u := Set.Iio 1)
                (p := q) (s := ({0} : Set ℕ)) hsingleton_zero_subset_Iio_one (Set.toFinite _)]
    _ = (unitInterval.toNNReal q : ENNReal) := by
      simp
    _ = ENNReal.ofReal (q : ℝ) := by
      simpa using (ENNReal.ofReal_eq_coe_nnreal q.2.1).symm

omit [IsProbabilityMeasure P] in
/-- Helper for Exercise 5.2.1: the success event of a one-trial binomial random variable has
probability `q`. -/
lemma measure_preimage_one_of_hasLaw_binomialOne {Y : Ω → ℝ} {q : I}
    (hY : HasLaw Y (Bin(ℝ, 1, q)) P) :
    P {ω | Y ω = 1} = ENNReal.ofReal (q : ℝ) := by
  have hBin : Bin(ℝ, 1, q) ({1} : Set ℝ) = ENNReal.ofReal (q : ℝ) := by
    rw [ProbabilityTheory.binomial]
    rw [Measure.map_apply measurable_from_nat (measurableSet_singleton 1)]
    have hPreimage : (fun k : ℕ ↦ (k : ℝ)) ⁻¹' ({1} : Set ℝ) = ({1} : Set ℕ) := by
      ext k
      simp
    rw [hPreimage]
    exact binomialOne_apply_singleton_one q
  -- Rewrite the success event as the singleton mass of the pushforward law.
  calc
    P {ω | Y ω = 1} = P.map Y ({1} : Set ℝ) := by
      simpa [Set.preimage, Set.mem_setOf_eq] using
        (Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton 1)).symm
    _ = Bin(ℝ, 1, q) ({1} : Set ℝ) := by
      rw [hY.map_eq]
    _ = ENNReal.ofReal (q : ℝ) := hBin

omit [IsProbabilityMeasure P] in
/-- Helper for Exercise 5.2.1: a `Bin(ℝ, 1, q)`-distributed variable has expectation `q`. -/
lemma integral_of_hasLaw_binomialOne {Y : Ω → ℝ} {q : I}
    (hY : HasLaw Y (Bin(ℝ, 1, q)) P) :
    P[Y] = (q : ℝ) := by
  have hEventNull : NullMeasurableSet {ω | Y ω = 1} P :=
    hY.aemeasurable.nullMeasurableSet_preimage (measurableSet_singleton 1)
  have hIndicator :
      (fun ω ↦ Y ω) =ᵐ[P] Set.indicator {ω | Y ω = 1} (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [ae_eq_zero_or_one_of_hasLaw_binomialOne (P := P) hY] with ω hω
    rcases hω with h0 | h1
    · simp [Set.indicator, h0]
    · simp [Set.indicator, h1]
  -- On `{0,1}`, the variable is the indicator of its success event.
  calc
    P[Y] = ∫ ω, Set.indicator {ω | Y ω = 1} (fun _ ↦ (1 : ℝ)) ω ∂P := by
      exact integral_congr_ae hIndicator
    _ = P.real {ω | Y ω = 1} := by
      rw [MeasureTheory.integral_indicator₀ hEventNull, MeasureTheory.setIntegral_const]
      simp
    _ = (P {ω | Y ω = 1}).toReal := by
      rw [MeasureTheory.Measure.real_def]
    _ = (ENNReal.ofReal (q : ℝ)).toReal := by
      rw [measure_preimage_one_of_hasLaw_binomialOne (P := P) hY]
    _ = (q : ℝ) := by
      exact ENNReal.toReal_ofReal q.2.1

/-- Helper for Exercise 5.2.1: the Bernoulli moment generating function is the affine textbook
formula `1 + q (e^t - 1)`. -/
lemma mgf_of_hasLaw_binomialOne {Y : Ω → ℝ} {q : I} (t : ℝ)
    (hY : HasLaw Y (Bin(ℝ, 1, q)) P) :
    mgf Y P t = 1 + (q : ℝ) * (Real.exp t - 1) := by
  have hY_int : Integrable Y P := integrable_of_hasLaw_binomialOne (P := P) hY
  -- Replace `exp (t * Y)` by its affine `{0,1}`-valued form and integrate termwise.
  rw [ProbabilityTheory.mgf]
  calc
    P[fun ω ↦ Real.exp (t * Y ω)] = P[fun ω ↦ 1 + (Real.exp t - 1) * Y ω] := by
      refine integral_congr_ae ?_
      filter_upwards [ae_eq_zero_or_one_of_hasLaw_binomialOne (P := P) hY] with ω hω
      simp [exp_mul_eq_one_add_mul_of_zero_one hω]
    _ = P[fun _ ↦ (1 : ℝ)] + (Real.exp t - 1) * P[Y] := by
      rw [integral_add (integrable_const _) (hY_int.const_mul _), integral_const_mul]
    _ = 1 + (Real.exp t - 1) * P[Y] := by
      simp
    _ = 1 + (q : ℝ) * (Real.exp t - 1) := by
      rw [integral_of_hasLaw_binomialOne (P := P) hY]
      ring

include hX_law
/-- Helper for Exercise 5.2.1: each coordinate has the exact Bernoulli moment generating
function. -/
lemma coordinateMgf_eq (i : Fin n) (t : ℝ) :
    mgf (X i) P t = 1 + (p i : ℝ) * (Real.exp t - 1) := by
  -- This is the one-coordinate mgf formula transported along `hX_law i`.
  exact mgf_of_hasLaw_binomialOne (P := P) t (hX_law i)

include hX_indep
/-- Helper for Exercise 5.2.1: the lower-tail mgf of the Bernoulli sum is bounded by the
textbook exponential envelope at parameter `-δ`. -/
lemma sumMgfNegDelta_le {δ : ℝ} :
    mgf (∑ i, X i) P (-δ) ≤ Real.exp ((Real.exp (-δ) - 1) * m) := by
  have hmgf_prod :
      mgf (∑ i, X i) P (-δ) = ∏ i, mgf (X i) P (-δ) := by
    -- Independence turns the mgf of the sum into the product of the coordinate mgfs.
    exact iIndepFun.mgf_sum₀ (μ := P) (X := X) (t := -δ) hX_indep
      (fun i => (hX_law i).aemeasurable) Finset.univ
  calc
    mgf (∑ i, X i) P (-δ) = ∏ i, (1 + (p i : ℝ) * (Real.exp (-δ) - 1)) := by
      -- Rewrite each factor by the exact Bernoulli mgf formula.
      rw [hmgf_prod]
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [coordinateMgf_eq (P := P) (p := p) (X := X) hX_law i (-δ)]
    _ ≤ ∏ i, Real.exp ((Real.exp (-δ) - 1) * (p i : ℝ)) := by
      -- Bound each affine Bernoulli factor by the corresponding exponential.
      refine Finset.prod_le_prod ?_ ?_
      · intro i hi
        have hp0 : 0 ≤ (p i : ℝ) := (p i).2.1
        have hp1 : (p i : ℝ) ≤ 1 := (p i).2.2
        have hleft : 0 ≤ 1 - (p i : ℝ) := sub_nonneg.mpr hp1
        have hright : 0 ≤ (p i : ℝ) * Real.exp (-δ) :=
          mul_nonneg hp0 (le_of_lt (Real.exp_pos _))
        have hnonneg : 0 ≤ (1 - (p i : ℝ)) + (p i : ℝ) * Real.exp (-δ) :=
          add_nonneg hleft hright
        have hrewrite :
            1 + (p i : ℝ) * (Real.exp (-δ) - 1) =
              (1 - (p i : ℝ)) + (p i : ℝ) * Real.exp (-δ) := by
          ring
        rw [hrewrite]
        exact hnonneg
      · intro i hi
        simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
          sub_eq_add_neg] using
          (Real.add_one_le_exp ((Real.exp (-δ) - 1) * (p i : ℝ)))
    _ = Real.exp ((Real.exp (-δ) - 1) * m) := by
      -- Collapse the product of exponentials into one exponential of a sum.
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.mul_sum]
omit hX_indep

omit P p X hX_law in
/-- Helper for Exercise 5.2.1: the elementary exponential remainder gives the quadratic upper
bound on `exp (-δ)`. -/
lemma expNeg_le_one_sub_add_sq_half {δ : ℝ} (hδ : 0 ≤ δ) :
    Real.exp (-δ) ≤ 1 - δ + δ ^ 2 / 2 := by
  have hquad : 1 + δ + δ ^ 2 / 2 ≤ Real.exp δ :=
    Real.quadratic_le_exp_of_nonneg hδ
  have hpoly_pos : 0 < 1 + δ + δ ^ 2 / 2 := by
    nlinarith [hδ, sq_nonneg δ]
  have hinv : Real.exp (-δ) ≤ (1 + δ + δ ^ 2 / 2)⁻¹ := by
    rw [Real.exp_neg]
    simpa [one_div] using (one_div_le_one_div_of_le hpoly_pos hquad)
  have hrecip : (1 + δ + δ ^ 2 / 2)⁻¹ ≤ 1 - δ + δ ^ 2 / 2 := by
    refine (inv_le_iff_one_le_mul₀ hpoly_pos).2 ?_
    have hone : 1 ≤ (1 - δ + δ ^ 2 / 2) * (1 + δ + δ ^ 2 / 2) := by
      ring_nf
      nlinarith [sq_nonneg (δ ^ 2)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hone
  -- Compare `exp (-δ)` to the reciprocal quadratic lower bound for `exp δ`.
  exact le_trans hinv hrecip

omit P p X hX_law in
/-- Helper for Exercise 5.2.1: the negative-parameter Chernoff exponent is bounded by the
standard quadratic lower-tail exponent. -/
lemma lowerTailExponentNegDelta_le_halfSq {δ : ℝ} (hδ : 0 ≤ δ) :
    δ * (1 - δ) + (Real.exp (-δ) - 1) ≤ -(δ ^ 2) / 2 := by
  -- Replace `exp (-δ)` by its quadratic upper bound and simplify the scalar exponent.
  have hquad : Real.exp (-δ) - 1 ≤ -δ + δ ^ 2 / 2 := by
    linarith [expNeg_le_one_sub_add_sq_half (δ := δ) hδ]
  linarith

omit [IsProbabilityMeasure P] in
/-- Helper for Exercise 5.2.1: every finite Bernoulli partial sum stays in `[0, #s]` almost
surely. -/
lemma ae_finset_sum_mem_Icc (s : Finset (Fin n)) :
    ∀ᵐ ω ∂P, (∑ i ∈ s, X i ω) ∈ Set.Icc (0 : ℝ) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi hs =>
      -- Extend the interval bound by one Bernoulli coordinate.
      have hs_card_le_succ : (s.card : ℝ) ≤ s.card + 1 := by
        exact_mod_cast Nat.le_succ s.card
      filter_upwards
        [ae_eq_zero_or_one_of_hasLaw_binomialOne (P := P) (hX_law i), hs] with
        ω hiω hsω
      rcases hsω with ⟨hs_nonneg, hs_le⟩
      rcases hiω with h0 | h1
      · constructor
        · simpa [Finset.sum_insert, hi, h0] using hs_nonneg
        · simpa [Finset.sum_insert, hi, h0] using le_trans hs_le hs_card_le_succ
      · constructor
        · simpa [Finset.sum_insert, hi, h1] using add_nonneg zero_le_one hs_nonneg
        · simpa [Finset.sum_insert, hi, h1, add_comm, add_left_comm, add_assoc] using
            add_le_add_right hs_le 1

omit [IsProbabilityMeasure P] in
/-- Helper for Exercise 5.2.1: the total Bernoulli sum is almost everywhere measurable. -/
lemma totalBernoulliSumAEMeasurable :
    AEMeasurable (fun ω ↦ ∑ i, X i ω) P := by
  -- Measurability is preserved under finite sums of the coordinate random variables.
  simpa using Finset.aemeasurable_fun_sum Finset.univ fun i _ => (hX_law i).aemeasurable

omit [IsProbabilityMeasure P] in
/-- Helper for Exercise 5.2.1: the full Bernoulli sum stays in `[0, n]` almost surely. -/
lemma ae_totalBernoulliSum_mem_Icc :
    ∀ᵐ ω ∂P, (∑ i, X i ω) ∈ Set.Icc (0 : ℝ) n := by
  -- Specialize the finite partial-sum interval bound to the full index set.
  simpa using
    (ae_finset_sum_mem_Icc (P := P) (p := p) (X := X) hX_law (s := Finset.univ))

-- Proof sketch: apply the Chernoff bound `measure_ge_le_exp_mul_mgf` to the finite sum
-- `ω ↦ ∑ i, X i ω`, use independence to factor its moment generating function into a product of
-- Bernoulli moment generating functions, bound each factor by the textbook expression, and then
-- optimize over the exponential parameter `λ > 0`.
include hX_indep hX_law
/-- Exercise 5.2.1, upper-tail estimate: independent Bernoulli random variables
`X₁, …, Xₙ` with success
parameters `p₁, …, pₙ`, the upper tail of the partial sum is bounded by the Bernstein--Chernoff
estimate `P[Sₙ ≥ (1 + δ)m] ≤ (exp δ / (1 + δ)^(1 + δ))^m`, where
`Sₙ = ∑ᵢ Xᵢ` and `m = ∑ᵢ pᵢ = 𝔼[Sₙ]`. -/
theorem bernoulli_sum_upper_tail_le_bernstein_chernoff
    {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | (1 + δ) * m ≤ ∑ i, X i ω} ≤
      Real.rpow (Real.exp δ / Real.rpow (1 + δ) (1 + δ)) m := by
  classical
  let S : Ω → ℝ := ∑ i, X i
  have hS_eq : S = fun ω ↦ ∑ i, X i ω := by
    funext ω
    simp [S]
  have hOneAddDelta : 0 < 1 + δ := by linarith
  have ht : 0 ≤ Real.log (1 + δ) := by
    refine Real.log_nonneg ?_
    linarith
  have hS_meas : AEMeasurable S P := by
    -- Rewrite the local alias `S` back to the canonical finite sum.
    rw [hS_eq]
    exact totalBernoulliSumAEMeasurable (P := P) (p := p) (X := X) hX_law
  have hsum_mem_Icc : ∀ᵐ ω ∂P, (∑ i, X i ω) ∈ Set.Icc (0 : ℝ) n := by
    -- The dedicated full-sum interval lemma keeps the upper-tail side conditions flat.
    exact ae_totalBernoulliSum_mem_Icc (P := P) (p := p) (X := X) hX_law
  have hS_le : ∀ᵐ ω ∂P, S ω ≤ n := by
    filter_upwards [hsum_mem_Icc] with ω hω
    simpa [S] using hω.2
  have hS_int :
      Integrable (fun ω ↦ Real.exp (Real.log (1 + δ) * S ω)) P := by
    -- The sum is a.s. bounded by `n`, so the exponential kernel is integrable at the positive
    -- optimizer `log (1 + δ)`.
    exact ProbabilityTheory.integrable_exp_mul_of_le (μ := P) (X := S)
      (t := Real.log (1 + δ)) (b := n) ht hS_meas hS_le
  have hmgf_prod :
      mgf S P (Real.log (1 + δ)) = ∏ i, mgf (X i) P (Real.log (1 + δ)) := by
    simpa [S] using
      (iIndepFun.mgf_sum₀ (μ := P) (X := X) (t := Real.log (1 + δ)) hX_indep
        (fun i => (hX_law i).aemeasurable) Finset.univ)
  have hmgf_le : mgf S P (Real.log (1 + δ)) ≤ Real.exp (δ * m) := by
    -- Rewrite the sum mgf as a product and bound each Bernoulli factor by `exp (δ pᵢ)`.
    calc
      mgf S P (Real.log (1 + δ)) = ∏ i, (1 + (p i : ℝ) * δ) := by
        rw [hmgf_prod]
        refine Finset.prod_congr rfl ?_
        intro i hi
        rw [coordinateMgf_eq (P := P) (p := p) (X := X) hX_law i (Real.log (1 + δ))]
        simp [Real.exp_log hOneAddDelta, sub_eq_add_neg, mul_comm]
      _ ≤ ∏ i, Real.exp (δ * (p i : ℝ)) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i hi
          have hterm : 0 ≤ 1 + (p i : ℝ) * δ := by
            have hp : 0 ≤ (p i : ℝ) := (p i).2.1
            nlinarith
          exact hterm
        · intro i hi
          simpa [add_comm, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using
            (Real.add_one_le_exp (δ * (p i : ℝ)))
      _ = Real.exp (δ * m) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.mul_sum]
  have hbase : 0 < Real.exp δ / Real.rpow (1 + δ) (1 + δ) := by
    exact div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hOneAddDelta _)
  -- Apply Chernoff at the optimizer `log (1 + δ)` and rewrite the resulting exponential.
  calc
    P.real {ω | (1 + δ) * m ≤ ∑ i, X i ω} = P.real {ω | (1 + δ) * m ≤ S ω} := by
      simp [S]
    _ ≤ Real.exp (-Real.log (1 + δ) * ((1 + δ) * m)) * mgf S P (Real.log (1 + δ)) := by
      exact ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := P) (X := S) ((1 + δ) * m) ht hS_int
    _ ≤ Real.exp (-Real.log (1 + δ) * ((1 + δ) * m)) * Real.exp (δ * m) := by
      gcongr
    _ = Real.exp ((δ - (1 + δ) * Real.log (1 + δ)) * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.rpow (Real.exp δ / Real.rpow (1 + δ) (1 + δ)) m := by
      have hlogbase :
          Real.log (Real.exp δ / Real.rpow (1 + δ) (1 + δ)) =
            δ - (1 + δ) * Real.log (1 + δ) := by
        calc
          Real.log (Real.exp δ / Real.rpow (1 + δ) (1 + δ)) =
              Real.log (Real.exp δ) - Real.log (Real.rpow (1 + δ) (1 + δ)) := by
                exact Real.log_div (Real.exp_ne_zero δ)
                  (ne_of_gt (Real.rpow_pos_of_pos hOneAddDelta _))
          _ = δ - Real.log (Real.rpow (1 + δ) (1 + δ)) := by
            rw [Real.log_exp]
          _ = δ - (1 + δ) * Real.log (1 + δ) := by
            have hlogrpow :
                Real.log (Real.rpow (1 + δ) (1 + δ)) = (1 + δ) * Real.log (1 + δ) :=
              Real.log_rpow hOneAddDelta (1 + δ)
            simpa [sub_eq_add_neg] using congrArg (fun x => δ - x) hlogrpow
      calc
        Real.exp ((δ - (1 + δ) * Real.log (1 + δ)) * m)
            = Real.exp (Real.log (Real.exp δ / Real.rpow (1 + δ) (1 + δ)) * m) := by
                rw [hlogbase]
        _ = Real.rpow (Real.exp δ / Real.rpow (1 + δ) (1 + δ)) m := by
            symm
            exact Real.rpow_def_of_pos hbase m

-- Proof sketch: apply the lower-tail Chernoff bound `measure_le_le_exp_mul_mgf` to the same sum,
-- equivalently to the upper tail of its negative, factor the moment generating function using
-- independence and the Bernoulli laws, then optimize the resulting exponential estimate to obtain
-- the standard quadratic bound `exp (-δ² m / 2)`.
/-- Lower-tail estimate for Exercise 5.2.1: independent Bernoulli random variables
`X₁, …, Xₙ` with success
parameters `p₁, …, pₙ`, the lower tail of the partial sum satisfies
`P[Sₙ ≤ (1 - δ)m] ≤ exp (-δ² m / 2)`, where `Sₙ = ∑ᵢ Xᵢ` and
`m = ∑ᵢ pᵢ = 𝔼[Sₙ]`. -/
theorem bernoulli_sum_lower_tail_le_bernstein_chernoff
    {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | (∑ i, X i ω) ≤ (1 - δ) * m} ≤
      Real.exp (-(δ ^ 2) * m / 2) := by
  classical
  have hδ_nonneg : 0 ≤ δ := hδ.le
  have hnegδ : -δ ≤ 0 := by
    linarith
  let S : Ω → ℝ := ∑ i, X i
  have hS_eq : S = fun ω ↦ ∑ i, X i ω := by
    funext ω
    simp [S]
  have hS_meas : AEMeasurable S P := by
    -- Rewrite the local alias `S` back to the canonical finite sum.
    rw [hS_eq]
    exact totalBernoulliSumAEMeasurable (P := P) (p := p) (X := X) hX_law
  have hsum_mem_Icc : ∀ᵐ ω ∂P, (∑ i, X i ω) ∈ Set.Icc (0 : ℝ) n := by
    -- The same interval control feeds the lower-tail integrability argument.
    exact ae_totalBernoulliSum_mem_Icc (P := P) (p := p) (X := X) hX_law
  have hS_mem_Icc : ∀ᵐ ω ∂P, S ω ∈ Set.Icc (0 : ℝ) n := by
    -- The sum stays between `0` and `n` almost surely because each coordinate is `{0,1}`-valued.
    filter_upwards [hsum_mem_Icc] with ω hω
    simpa [S] using hω
  have hS_int : Integrable (fun ω ↦ Real.exp (-δ * S ω)) P := by
    -- The a.s. interval bound makes the negative exponential integrable.
    exact ProbabilityTheory.integrable_exp_mul_of_mem_Icc (μ := P) (X := S)
      (a := 0) (b := n) (t := -δ) hS_meas hS_mem_Icc
  have hm_nonneg : 0 ≤ m := by
    -- The mean parameter `m` is a sum of nonnegative Bernoulli parameters.
    exact Finset.sum_nonneg fun i hi => (p i).2.1
  -- Route correction: replace the earlier log-based scalar close by the equivalent
  -- `exp (-δ)` quadratic bound, so the probabilistic assembly stays flat.
  calc
    P.real {ω | (∑ i, X i ω) ≤ (1 - δ) * m} = P.real {ω | S ω ≤ (1 - δ) * m} := by
      simp [S]
    _ ≤ Real.exp (-(-δ) * ((1 - δ) * m)) * mgf S P (-δ) := by
      exact ProbabilityTheory.measure_le_le_exp_mul_mgf (μ := P) (X := S) ((1 - δ) * m)
        hnegδ hS_int
    _ ≤ Real.exp (-(-δ) * ((1 - δ) * m)) *
        Real.exp ((Real.exp (-δ) - 1) * m) := by
      gcongr
      simpa [S] using sumMgfNegDelta_le (P := P) (p := p) (X := X) hX_indep hX_law
    _ = Real.exp ((δ * (1 - δ) + (Real.exp (-δ) - 1)) * m) := by
      -- Combine the Chernoff prefactor and the mgf estimate into one exponent.
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(δ ^ 2) * m / 2) := by
      apply Real.exp_le_exp.mpr
      have hscalar :
          δ * (1 - δ) + (Real.exp (-δ) - 1) ≤ -(δ ^ 2) / 2 :=
        lowerTailExponentNegDelta_le_halfSq (δ := δ) hδ.le
      have hmul :
          (δ * (1 - δ) + (Real.exp (-δ) - 1)) * m ≤ (-(δ ^ 2) / 2) * m :=
        mul_le_mul_of_nonneg_right hscalar hm_nonneg
      calc
        (δ * (1 - δ) + (Real.exp (-δ) - 1)) * m ≤ (-(δ ^ 2) / 2) * m := hmul
        _ = -(δ ^ 2) * m / 2 := by ring

/-- The Bernstein--Chernoff upper and lower tail bounds for
the Bernoulli sum
`Sₙ = ∑ᵢ Xᵢ` hold simultaneously. -/
theorem bernoulli_sum_tail_bounds_bernstein_chernoff
    {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | (1 + δ) * m ≤ ∑ i, X i ω} ≤
      Real.rpow (Real.exp δ / Real.rpow (1 + δ) (1 + δ)) m ∧
    P.real {ω | (∑ i, X i ω) ≤ (1 - δ) * m} ≤
      Real.exp (-(δ ^ 2) * m / 2) := by
  constructor
  · simpa using
      (bernoulli_sum_upper_tail_le_bernstein_chernoff
        (P := P) (p := p) (X := X) (hX_indep := hX_indep) (hX_law := hX_law) (δ := δ) hδ)
  · simpa using
      (bernoulli_sum_lower_tail_le_bernstein_chernoff
        (P := P) (p := p) (X := X) (hX_indep := hX_indep) (hX_law := hX_law) (δ := δ) hδ)

end BernsteinChernoff
