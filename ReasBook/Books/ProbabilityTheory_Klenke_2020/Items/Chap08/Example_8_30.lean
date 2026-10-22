/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Example_2_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 8.30: the split parameter `lam1 / (lam1 + lam2)` is admissible for the
binomial law. -/
private theorem poisson_split_parameter_le_one (lam1 lam2 : ℝ≥0) :
    lam1 / (lam1 + lam2) ≤ 1 := by
  -- Proof comment: compare `lam1` with the total rate `lam1 + lam2` and divide by the
  -- nonnegative denominator.
  by_cases hsum : lam1 + lam2 = 0
  · simp [hsum]
  · have hpos : 0 < lam1 + lam2 := pos_iff_ne_zero.mpr hsum
    have hle : lam1 ≤ lam1 + lam2 := le_add_of_nonneg_right (zero_le lam2)
    exact (div_le_iff₀ hpos).2 (by simp [one_mul, hle])

section PoissonSplit

variable (P : Measure Ω) [IsProbabilityMeasure P]
variable {Z1 Z2 : Ω → ℕ} {lam1 lam2 : ℝ≥0}

/-- Helper for Example 8.30: the singleton mass of `poissonMeasure r` is the explicit Poisson
weight `poissonPMFReal r n`. -/
private theorem poissonMeasure_apply_singleton (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Proof comment: rewrite `poissonMeasure` as the measure of the corresponding Poisson `PMF`.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Example 8.30: the sum of two independent Poisson variables is Poisson with the sum
of the rates. -/
private theorem hasLawPoissonSum
    (hZ1 : HasLaw Z1 (poissonMeasure lam1) P)
    (hZ2 : HasLaw Z2 (poissonMeasure lam2) P)
    (hindep : IndepFun Z1 Z2 P) :
    HasLaw (fun ω ↦ Z1 ω + Z2 ω) (poissonMeasure (lam1 + lam2)) P := by
  -- Proof comment: combine the additive-convolution law from independence with the earlier
  -- Poisson convolution theorem.
  let _ : IsProbabilityMeasure P := inferInstance
  simpa [poissonMeasure_conv_poissonMeasure] using hindep.hasLaw_fun_add hZ1 hZ2

/-- Helper for Example 8.30: the joint law of the independent Poisson pair is the product of the
two Poisson laws. -/
private theorem jointPoissonPairLaw
    (hZ1 : HasLaw Z1 (poissonMeasure lam1) P)
    (hZ2 : HasLaw Z2 (poissonMeasure lam2) P)
    (hindep : IndepFun Z1 Z2 P) :
    P.map (fun ω ↦ (Z1 ω, Z2 ω)) = (poissonMeasure lam1).prod (poissonMeasure lam2) := by
  -- Proof comment: independence is equivalent to factorization of the pushed-forward pair law.
  simpa [hZ1.map_eq, hZ2.map_eq] using
    (indepFun_iff_map_prod_eq_prod_map_map hZ1.aemeasurable hZ2.aemeasurable).mp hindep

/-- Helper for Example 8.30: the singleton fiber of `(a, b) ↦ (a + b, a)` is either the singleton
`{(k, n - k)}` or empty, according to whether `k ≤ n`. -/
private theorem sumLeftSingletonPreimage (n k : ℕ) :
    (fun z : ℕ × ℕ ↦ (z.1 + z.2, z.1)) ⁻¹' ({(n, k)} : Set (ℕ × ℕ)) =
      if k ≤ n then ({(k, n - k)} : Set (ℕ × ℕ)) else ∅ := by
  -- Proof comment: identify the unique fiber point in the feasible branch, and rule out the
  -- infeasible branch by the inequality `k ≤ n` forced by any witness.
  ext z
  rcases z with ⟨a, b⟩
  by_cases hk : k ≤ n
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, hk]
    constructor
    · intro hz
      rcases Prod.mk.inj hz with ⟨hab, ha⟩
      subst a
      have hb : b = n - k := by
        calc
          b = (k + b) - k := by rw [Nat.add_sub_cancel_left]
          _ = n - k := by rw [hab]
      simp [hb]
    · intro hz
      rcases Prod.mk.inj hz with ⟨ha, hb⟩
      subst a
      subst b
      simp [Nat.add_sub_of_le hk]
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, hk]
    constructor
    · intro hz
      rcases Prod.mk.inj hz with ⟨hab, ha⟩
      have : k ≤ n := by
        subst a
        calc
          k ≤ k + b := Nat.le_add_right _ _
          _ = n := hab
      exact (hk this).elim
    · intro hz
      exact False.elim hz

/-- Helper for Example 8.30: under the map `(a,b) ↦ (a+b,a)`, the rectangle `{n} × {k}` pulls
back either to `{k} × {n-k}` or to the empty set. -/
private theorem sumLeftRectangleMass
    (hZ1 : HasLaw Z1 (poissonMeasure lam1) P)
    (hZ2 : HasLaw Z2 (poissonMeasure lam2) P)
    (hindep : IndepFun Z1 Z2 P)
    (n k : ℕ) :
    P.map (fun ω ↦ (Z1 ω + Z2 ω, Z1 ω)) ({n} ×ˢ ({k} : Set ℕ)) =
      if k ≤ n then
        poissonMeasure lam1 ({k} : Set ℕ) * poissonMeasure lam2 ({n - k} : Set ℕ)
      else 0 := by
  -- Route correction: rewrite the target rectangle as a singleton pair before applying
  -- `Measure.map_apply`, so the preimage normalization matches the actual map normal form.
  have hpair :
      AEMeasurable (fun ω ↦ (Z1 ω, Z2 ω)) P := hZ1.aemeasurable.prodMk hZ2.aemeasurable
  have hsumLeft :
      Measurable (fun z : ℕ × ℕ ↦ (z.1 + z.2, z.1)) := by
    fun_prop
  have hmap :
      (P.map (fun ω ↦ (Z1 ω, Z2 ω))).map (fun z : ℕ × ℕ ↦ (z.1 + z.2, z.1)) =
        P.map (fun ω ↦ (Z1 ω + Z2 ω, Z1 ω)) := by
    simpa [Function.comp_def] using
      AEMeasurable.map_map_of_aemeasurable (μ := P) (f := fun ω ↦ (Z1 ω, Z2 ω))
        (g := fun z : ℕ × ℕ ↦ (z.1 + z.2, z.1)) hsumLeft.aemeasurable hpair
  rw [← hmap, jointPoissonPairLaw (P := P) hZ1 hZ2 hindep, Set.singleton_prod_singleton]
  rw [Measure.map_apply hsumLeft (measurableSet_singleton (n, k))]
  rw [sumLeftSingletonPreimage]
  by_cases hk : k ≤ n
  · -- Proof comment: in the feasible branch the preimage is a singleton pair, so the product
    -- measure splits into the product of the singleton masses.
    simpa [hk, Set.singleton_prod_singleton] using
      (Measure.prod_prod (μ := poissonMeasure lam1) (ν := poissonMeasure lam2) ({k} : Set ℕ)
        ({n - k} : Set ℕ))
  · -- Proof comment: in the infeasible branch the preimage is empty, so the pushed-forward mass
    -- vanishes.
    simp [hk]

/-- Helper for Example 8.30: the feasible joint singleton mass of the Poisson split equals the
Poisson singleton mass at the sum times the corresponding binomial mass. -/
private theorem poissonSplitSingletonMass_eq_binomial
    (lam1 lam2 : ℝ≥0) {n k : ℕ} (hk : k ≤ n) :
    poissonMeasure lam1 ({k} : Set ℕ) * poissonMeasure lam2 ({n - k} : Set ℕ) =
      poissonMeasure (lam1 + lam2) ({n} : Set ℕ) *
        PMF.binomial (lam1 / (lam1 + lam2)) (poisson_split_parameter_le_one lam1 lam2) n
          (Fin.ofNat (n + 1) k) := by
  let q : ℝ≥0 := lam1 / (lam1 + lam2)
  have hq : q ≤ 1 := poisson_split_parameter_le_one lam1 lam2
  let p : PMF (Fin 2) := PMF.binomial q hq 1
  let counts : Fin 2 → ℕ := ![n - k, k]
  have hmass := poissonMultinomialMass_eq_prodPoissonMass (α := lam1 + lam2) p counts
  have hsum_counts : ∑ i, counts i = n := by
    -- Proof comment: the two-cell count vector records `n - k` failures and `k` successes.
    simp [counts, hk]
  have hmulti : Nat.multinomial Finset.univ counts = n.choose k := by
    -- Proof comment: the two-cell multinomial coefficient is the usual binomial coefficient.
    calc
      Nat.multinomial Finset.univ counts = Nat.multinomial Finset.univ ![n - k, k] := by
        rfl
      _ = n.choose k := by
        rw [Nat.multinomial_univ_two]
        simpa [Nat.add_sub_of_le hk, hk, Nat.mul_comm] using
          (Nat.choose_eq_factorial_div_factorial hk).symm
  have hqmul : (lam1 + lam2) * q = lam1 := by
    -- Proof comment: the total rate times the split parameter recovers the left Poisson rate.
    dsimp [q]
    by_cases hsum : lam1 + lam2 = 0
    · have hlam1 : lam1 = 0 := by
        apply le_antisymm
        · calc
            lam1 ≤ lam1 + lam2 := le_add_of_nonneg_right (zero_le lam2)
            _ = 0 := hsum
        · exact bot_le
      simp [hlam1]
    · rw [mul_div_cancel₀ _ hsum]
  have hcomul : (lam1 + lam2) * (1 - q) = lam2 := by
    -- Proof comment: the complementary cell parameter recovers the right Poisson rate.
    dsimp [q]
    by_cases hsum : lam1 + lam2 = 0
    · have hlam1 : lam1 = 0 := by
        apply le_antisymm
        · calc
            lam1 ≤ lam1 + lam2 := le_add_of_nonneg_right (zero_le lam2)
            _ = 0 := hsum
        · exact bot_le
      have hlam2 : lam2 = 0 := by
        apply le_antisymm
        · calc
            lam2 ≤ lam1 + lam2 := le_add_of_nonneg_left (zero_le lam1)
            _ = 0 := hsum
        · exact bot_le
      simp [hlam1, hlam2]
    · have hcomp : 1 - lam1 / (lam1 + lam2) = lam2 / (lam1 + lam2) := by
        have htotal : lam1 / (lam1 + lam2) + lam2 / (lam1 + lam2) = 1 := by
          rw [← add_div]
          simpa [add_comm] using (div_self hsum : (lam1 + lam2) / (lam1 + lam2) = (1 : ℝ≥0))
        rw [tsub_eq_iff_eq_add_of_le (poisson_split_parameter_le_one lam1 lam2)]
        simpa [add_comm] using htotal.symm
      rw [hcomp, mul_div_cancel₀ _ hsum]
  have hp0 : p 0 = 1 - q := by
    -- Proof comment: the first binomial atom for one trial is the failure mass `1 - q`.
    simp [p]
  have hp1 : p 1 = q := by
    -- Proof comment: the second binomial atom for one trial is the success mass `q`.
    simpa [p] using (PMF.binomial_apply_last q hq 1)
  have hp0nn : (p 0).toNNReal = 1 - q := by
    rw [hp0]
    simp
  have hp1nn : (p 1).toNNReal = q := by
    rw [hp1]
    simp
  have hbin :
      PMF.binomial q hq n (Fin.ofNat (n + 1) k) =
        (n.choose k : ENNReal) * q ^ k * ENNReal.ofReal ((1 - q : ℝ) ^ (n - k)) := by
    -- Proof comment: rewrite the `n`-trial binomial singleton mass into the explicit formula.
    simpa [mul_assoc, mul_comm] using (PMF.binomial_apply_of_le hk hq).symm
  have hpowcomp : (1 - (q : ENNReal)) ^ (n - k) = ENNReal.ofReal ((1 - q : ℝ) ^ (n - k)) := by
    -- Proof comment: convert the complementary `ENNReal` power into the real power used by
    -- `PMF.binomial_apply_of_le`.
    have hqreal : (q : ℝ) ≤ 1 := by exact_mod_cast hq
    have hnonneg : 0 ≤ (1 - q : ℝ) := sub_nonneg.mpr hqreal
    rw [show (1 - (q : ENNReal)) = ENNReal.ofReal (1 - q : ℝ) by norm_cast]
    simpa using (ENNReal.ofReal_pow hnonneg (n - k)).symm
  have hmass' :
      poissonMeasure lam1 ({k} : Set ℕ) * poissonMeasure lam2 ({n - k} : Set ℕ) =
        (q : ENNReal) ^ k *
          ((n.choose k : ENNReal) * ((1 - (q : ENNReal)) ^ (n - k) *
            poissonMeasure (lam1 + lam2) ({n} : Set ℕ))) := by
    -- Proof comment: specialize the Chapter 5 multinomial Poisson product law to the two-cell
    -- count vector `(n - k, k)`.
    simpa [counts, hp0, hp1, hp0nn, hp1nn, hsum_counts, hmulti, hqmul, hcomul,
      Fin.prod_univ_two, Fin.sum_univ_two, mul_assoc, mul_left_comm, mul_comm] using hmass.symm
  calc
    poissonMeasure lam1 ({k} : Set ℕ) * poissonMeasure lam2 ({n - k} : Set ℕ)
      = (q : ENNReal) ^ k *
          ((n.choose k : ENNReal) * ((1 - (q : ENNReal)) ^ (n - k) *
            poissonMeasure (lam1 + lam2) ({n} : Set ℕ))) := hmass'
    _ = poissonMeasure (lam1 + lam2) ({n} : Set ℕ) *
          PMF.binomial q hq n (Fin.ofNat (n + 1) k) := by
          -- Proof comment: finish by rewriting the explicit binomial factor and commuting the
          -- scalar factors into the target order.
          rw [hbin, hpowcomp]
          simp [mul_assoc, mul_comm]

/-- Helper for Example 8.30: the conditional singleton mass of `Z₁` given `Z₁ + Z₂ = n` is the
corresponding binomial mass on `ℕ`, with the impossible branch `k > n` equal to `0`. -/
private theorem condDistribPoissonLeftGivenSumSingletonMass
    (hZ1 : HasLaw Z1 (poissonMeasure lam1) P)
    (hZ2 : HasLaw Z2 (poissonMeasure lam2) P)
    (hindep : IndepFun Z1 Z2 P)
    (n k : ℕ)
    (hn : P.map (fun ω ↦ Z1 ω + Z2 ω) {n} ≠ 0) :
    condDistrib Z1 (fun ω ↦ Z1 ω + Z2 ω) P n ({k} : Set ℕ) =
      if k ≤ n then
        PMF.binomial (lam1 / (lam1 + lam2)) (poisson_split_parameter_le_one lam1 lam2) n
          (Fin.ofNat (n + 1) k)
      else 0 := by
  let Z1m : Ω → ℕ := hZ1.aemeasurable.mk Z1
  let Xm : Ω → ℕ := fun ω ↦ Z1m ω + Z2 ω
  have hZ1_ae : Z1 =ᵐ[P] Z1m := hZ1.aemeasurable.ae_eq_mk
  have hXm_ae : (fun ω ↦ Z1 ω + Z2 ω) =ᵐ[P] Xm := by
    -- Proof comment: the measurable representative for `Z₁` induces the corresponding
    -- measurable representative for the sum variable.
    filter_upwards [hZ1_ae] with ω hω
    simp [Xm, Z1m, hω]
  have hZ1m : HasLaw Z1m (poissonMeasure lam1) P := hZ1.congr hZ1_ae.symm
  have hindep_m : IndepFun Z1m Z2 P := hindep.congr hZ1_ae Filter.EventuallyEq.rfl
  have hn_m : P.map Xm {n} ≠ 0 := by
    -- Proof comment: transport the nonzero denominator to the measurable representative of
    -- the sum variable.
    have hmap : P.map (fun ω ↦ Z1 ω + Z2 ω) = P.map Xm := Measure.map_congr hXm_ae
    simpa [hmap] using hn
  rw [condDistrib_congr_left hZ1_ae, condDistrib_congr_right hXm_ae]
  by_cases hk : k ≤ n
  · -- Route correction: use the earlier Poisson-multinomial factorization instead of the stalled
    -- direct real-ratio proof, then cancel the denominator from `condDistrib_apply_of_ne_zero`.
    rw [ProbabilityTheory.condDistrib_apply_of_ne_zero hZ1.aemeasurable.measurable_mk _ hn_m]
    rw [sumLeftRectangleMass (P := P) hZ1m hZ2 hindep_m n k]
    rw [if_pos hk, if_pos hk]
    rw [poissonSplitSingletonMass_eq_binomial lam1 lam2 hk]
    have hsumlaw : HasLaw Xm (poissonMeasure (lam1 + lam2)) P :=
      hasLawPoissonSum (P := P) hZ1m hZ2 hindep_m
    have hden :
        P.map Xm ({n} : Set ℕ) = poissonMeasure (lam1 + lam2) ({n} : Set ℕ) := by
      -- Proof comment: identify the denominator with the singleton mass of the Poisson sum law.
      simpa [Xm] using congrArg (fun μ => μ ({n} : Set ℕ)) hsumlaw.map_eq
    have hden_ne : poissonMeasure (lam1 + lam2) ({n} : Set ℕ) ≠ 0 := by
      simpa [hden] using hn_m
    rw [hden, ← mul_assoc, ENNReal.inv_mul_cancel hden_ne (measure_ne_top _ _), one_mul]
  · -- Proof comment: the infeasible singleton event `Z₁ = k` inside `Z₁ + Z₂ = n` has zero mass.
    rw [ProbabilityTheory.condDistrib_apply_of_ne_zero hZ1.aemeasurable.measurable_mk _ hn_m]
    rw [sumLeftRectangleMass (P := P) hZ1m hZ2 hindep_m n k]
    simp [hk]

/-- Helper for Example 8.30: the singleton preimage of `Fin.val` is feasible exactly when
the target singleton lies in `{0, …, n}`. -/
private theorem finVal_singletonPreimage (n k : ℕ) :
    Fin.val ⁻¹' ({k} : Set ℕ) =
      if k ≤ n then ({Fin.ofNat (n + 1) k} : Set (Fin (n + 1))) else ∅ := by
  -- Proof comment: `Fin.val` hits `k` at exactly one point when `k ≤ n`, and misses it otherwise.
  ext i
  by_cases hk : k ≤ n
  · simp [hk, Fin.ext_iff, Fin.ofNat_eq_cast, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hk)]
  · constructor
    · intro hi
      have : (i : ℕ) = k := by simpa using hi
      exact (hk (by simpa [this] using Nat.lt_succ_iff.mp i.isLt)).elim
    · intro hi
      simp [hk] at hi

-- Proof sketch: combine the Poisson laws of `Z₁` and `Z₂` with independence to identify the law
-- of `Z₁ + Z₂`, then compute the conditional point masses given `Z₁ + Z₂ = n`. These point masses
-- agree with the canonical binomial `PMF`, so the conditional law itself is the corresponding
-- measure on `ℕ`.
/-- Example 8.30: if `Z₁` and `Z₂` are independent Poisson random variables with parameters `λ₁`
and `λ₂`, then, whenever `P[Z₁ + Z₂ = n] > 0`, the conditional law of `Z₁` given `Z₁ + Z₂ = n`
is the binomial distribution with parameters `n` and `λ₁ / (λ₁ + λ₂)`, viewed as a measure on
`ℕ` via the canonical inclusion `Fin (n + 1) → ℕ`. -/
theorem condDistrib_poisson_left_given_sum_eq_binomial
    (hZ1 : HasLaw Z1 (poissonMeasure lam1) P)
    (hZ2 : HasLaw Z2 (poissonMeasure lam2) P)
    (hindep : IndepFun Z1 Z2 P)
    (n : ℕ)
    (hn : P.map (fun ω ↦ Z1 ω + Z2 ω) {n} ≠ 0) :
    condDistrib Z1 (fun ω ↦ Z1 ω + Z2 ω) P n =
      ((PMF.binomial (lam1 / (lam1 + lam2)) (poisson_split_parameter_le_one lam1 lam2) n).map
        Fin.val).toMeasure :=
  by
  refine Measure.ext_of_singleton fun k ↦ ?_
  rw [condDistribPoissonLeftGivenSumSingletonMass (P := P) hZ1 hZ2 hindep n k hn]
  rw [PMF.toMeasure_map_apply (p := PMF.binomial (lam1 / (lam1 + lam2))
    (poisson_split_parameter_le_one lam1 lam2) n) (f := Fin.val)
    (hf := measurable_of_countable Fin.val) (hs := measurableSet_singleton k)]
  rw [finVal_singletonPreimage]
  by_cases hk : k ≤ n
  · rw [if_pos hk, if_pos hk]
    exact
      (PMF.toMeasure_apply_singleton
        (PMF.binomial (lam1 / (lam1 + lam2)) (poisson_split_parameter_le_one lam1 lam2) n)
        (Fin.ofNat (n + 1) k) (measurableSet_singleton _)).symm
  · simp [hk]

/-- The singleton-mass view of `condDistrib_poisson_left_given_sum_eq_binomial`. -/
theorem condDistrib_poisson_left_given_sum_apply_singleton
    (hZ1 : HasLaw Z1 (poissonMeasure lam1) P)
    (hZ2 : HasLaw Z2 (poissonMeasure lam2) P)
    (hindep : IndepFun Z1 Z2 P)
    (n k : ℕ) (hk : k ≤ n)
    (hn : P.map (fun ω ↦ Z1 ω + Z2 ω) {n} ≠ 0) :
    condDistrib Z1 (fun ω ↦ Z1 ω + Z2 ω) P n {k} =
      PMF.binomial (lam1 / (lam1 + lam2)) (poisson_split_parameter_le_one lam1 lam2) n
        (Fin.ofNat (n + 1) k) :=
  by
  -- Proof comment: specialize the private singleton-mass computation to the feasible branch.
  simpa [hk, if_pos hk] using
    condDistribPoissonLeftGivenSumSingletonMass (P := P) hZ1 hZ2 hindep n k hn

end PoissonSplit
