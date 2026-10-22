/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_60
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

namespace ProbabilityTheory

/-- Helper for Exercise 17.7.3: the singleton mass of `poissonMeasure λ` is the explicit Poisson
weight `poissonPMFReal λ k`. -/
private lemma poissonMeasure_apply_singleton (lam : NNReal) (k : ℕ) :
    poissonMeasure lam ({k} : Set ℕ) = ENNReal.ofReal (poissonPMFReal lam k) := by
  -- Proof comment: rewrite `poissonMeasure` as the measure attached to the Poisson PMF.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF lam) k (measurableSet_singleton k))

/-- Helper for Exercise 17.7.3: taking `toReal` on a Poisson singleton atom recovers the textbook
Poisson mass formula. -/
private lemma poissonMeasure_apply_singleton_toReal (lam : NNReal) (k : ℕ) :
    ((poissonMeasure lam) ({k} : Set ℕ)).toReal = poissonPMFReal lam k := by
  -- Proof comment: remove the `ENNReal.ofReal` wrapper from the singleton mass formula.
  rw [poissonMeasure_apply_singleton, ENNReal.toReal_ofReal poissonPMFReal_nonneg]

/-- Helper for Exercise 17.7.3: the zero-atom of `Bin(n, p)` equals `(1 - p)^n`. -/
private lemma binomial_apply_zero_toReal (n : ℕ) (p : I) :
    (Bin(n, p) ({0} : Set ℕ)).toReal = (1 - (p : ℝ)) ^ n := by
  -- Proof comment: specialize the standard singleton formula at `0`.
  simpa using binomial_apply_singleton_toReal n 0 p

/-- Helper for Exercise 17.7.3: the zero-atom of `poissonMeasure λ` is `exp (-λ)`. -/
private lemma poissonMeasure_apply_zero_toReal (lam : NNReal) :
    ((poissonMeasure lam) ({0} : Set ℕ)).toReal = Real.exp (-(lam : ℝ)) := by
  -- Proof comment: specialize the Poisson singleton formula at `0`.
  simpa [poissonPMFReal] using poissonMeasure_apply_singleton_toReal lam 0

/-- Helper for Exercise 17.7.3: for any probability measure on `ℕ`, the upper tail `μ([k, ∞))`
is the complement of the finite prefix `{0, ..., k - 1}`. -/
private lemma natMeasure_tail_Ici_toReal (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    (μ (Set.Ici k)).toReal = 1 - ∑ i ∈ Finset.range k, (μ ({i} : Set ℕ)).toReal := by
  have hcompl : ((Set.Ici k : Set ℕ)ᶜ) = (((Finset.range k : Finset ℕ) : Set ℕ)) := by
    -- Proof comment: on `ℕ`, being outside `Ici k` means belonging to the first `k` values.
    ext i
    simp
  have hsplit :
      μ.real (Set.Ici k) + ∑ i ∈ Finset.range k, μ.real ({i} : Set ℕ) = 1 := by
    -- Proof comment: split the probability mass into the tail and its finite complement.
    calc
      μ.real (Set.Ici k) + ∑ i ∈ Finset.range k, μ.real ({i} : Set ℕ)
          = μ.real (Set.Ici k) + μ.real (((Finset.range k : Finset ℕ) : Set ℕ)) := by
              rw [← MeasureTheory.sum_measureReal_singleton (μ := μ) (s := Finset.range k)]
      _ = μ.real (Set.Ici k) + μ.real ((Set.Ici k : Set ℕ)ᶜ) := by rw [hcompl]
      _ = μ.real Set.univ := by
            simpa using
              (MeasureTheory.measureReal_add_measureReal_compl
                (μ := μ) (s := (Set.Ici k : Set ℕ)) measurableSet_Ici)
      _ = 1 := by simp [Measure.real_def]
  have htail : μ.real (Set.Ici k) = 1 - ∑ i ∈ Finset.range k, μ.real ({i} : Set ℕ) := by
    -- Proof comment: isolate the tail term from the partition identity.
    linarith
  simpa [Measure.real_def] using htail

/-- Helper for Exercise 17.7.3: the approximation parameter matching the Poisson zero-mass
condition is `1 - exp (-λ / m)`. -/
private def poissonApproxSuccessProb (lam : NNReal) (m : ℕ) : ℝ :=
  1 - Real.exp (-(lam : ℝ) / m)

/-- Helper for Exercise 17.7.3: the Poisson approximation success probability is nonnegative. -/
private lemma poissonApproxSuccessProb_nonneg (lam : NNReal) (m : ℕ) :
    0 ≤ poissonApproxSuccessProb lam m := by
  -- Proof comment: `exp x ≤ 1` for `x ≤ 0`, and here `x = -λ / m`.
  have hnonneg : 0 ≤ (lam : ℝ) / m := by
    exact div_nonneg lam.2 (by positivity)
  have hnonpos' : -((lam : ℝ) / m) ≤ 0 := neg_nonpos.mpr hnonneg
  have hnonpos : -(lam : ℝ) / m ≤ 0 := by
    rw [show -(lam : ℝ) / m = -((lam : ℝ) / m) by ring]
    exact hnonpos'
  have hexp : Real.exp (-(lam : ℝ) / m) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr hnonpos
  exact sub_nonneg.mpr hexp

/-- Helper for Exercise 17.7.3: the Poisson approximation success probability is at most `1`. -/
private lemma poissonApproxSuccessProb_le_one (lam : NNReal) (m : ℕ) :
    poissonApproxSuccessProb lam m ≤ 1 := by
  -- Proof comment: subtracting a nonnegative exponential term can only decrease `1`.
  dsimp [poissonApproxSuccessProb]
  have hexp_nonneg : 0 ≤ Real.exp (-(lam : ℝ) / m) := by positivity
  linarith

/-- Helper for Exercise 17.7.3: coercing the approximation parameter back to `ℝ` removes the
`Real.toNNReal` wrapper. -/
private lemma poissonApproxSuccessProb_toNNReal_coe (lam : NNReal) (m : ℕ) :
    (((Real.toNNReal (poissonApproxSuccessProb lam m)) : NNReal) : ℝ) =
      poissonApproxSuccessProb lam m := by
  -- Proof comment: the approximation probability already lies in `[0, ∞)`.
  simp [Real.toNNReal, max_eq_left (poissonApproxSuccessProb_nonneg lam m)]

/-- Helper for Exercise 17.7.3: the approximation probability packaged as an `NNReal` lies in the
unit interval `I`. -/
private lemma poissonApproxParameter_mem_unitInterval (lam : NNReal) (m : ℕ) :
    Set.Icc (0 : NNReal) 1 (Real.toNNReal (poissonApproxSuccessProb lam m)) := by
  constructor
  · positivity
  · rw [← NNReal.coe_le_coe, poissonApproxSuccessProb_toNNReal_coe]
    exact poissonApproxSuccessProb_le_one lam m

/-- Helper for Exercise 17.7.3: at every positive trial count `m`, the approximation parameter
has the exact zero-mass identity `(1 - q_m)^m = exp (-λ)`. -/
private lemma poissonApproxSuccessProb_pow (lam : NNReal) {m : ℕ} (hm : 1 ≤ m) :
    (1 - (((Real.toNNReal (poissonApproxSuccessProb lam m)) : NNReal) : ℝ)) ^ m =
      Real.exp (-(lam : ℝ)) := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  -- Proof comment: `1 - q_m = exp (-λ / m)`, and raising to the `m`-th power collapses the
  -- exponent back to `-λ`.
  rw [poissonApproxSuccessProb_toNNReal_coe, poissonApproxSuccessProb]
  rw [show 1 - (1 - Real.exp (-(lam : ℝ) / m)) = Real.exp (-(lam : ℝ) / m) by ring]
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [hm_pos.ne']

/-- Helper for Exercise 17.7.3: once `m` dominates `λ`, the scaled approximation error is bounded
by `λ^2 / m`. -/
private lemma poissonApproxScaledProb_error_le (lam : NNReal) {m : ℕ}
    (hm : 1 ≤ m) (hlamm : (lam : ℝ) ≤ m) :
    |(m : ℝ) * poissonApproxSuccessProb lam m - (lam : ℝ)| ≤ (lam : ℝ) ^ 2 / m := by
  let x : ℝ := -((lam : ℝ) / m)
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiv_nonneg : 0 ≤ (lam : ℝ) / m := by positivity
  have hdiv_le_one : (lam : ℝ) / m ≤ 1 := by
    field_simp [hm_pos.ne']
    simpa using hlamm
  have hx_abs : |x| ≤ 1 := by
    -- Proof comment: the choice `m ≥ λ` keeps the exponential linearization inside the unit ball.
    simpa [x, abs_of_nonneg hdiv_nonneg] using hdiv_le_one
  have hlin : |Real.exp x - 1 - x| ≤ x ^ 2 := Real.abs_exp_sub_one_sub_id_le hx_abs
  have hrewrite :
      (m : ℝ) * poissonApproxSuccessProb lam m - (lam : ℝ) =
        -(m : ℝ) * (Real.exp x - 1 - x) := by
    -- Proof comment: rewrite the deviation from `λ` into the standard `exp x - 1 - x`
    -- linearization error with `x = -λ / m`.
    dsimp [poissonApproxSuccessProb, x]
    field_simp [hm_pos.ne']
    ring
  calc
    |(m : ℝ) * poissonApproxSuccessProb lam m - (lam : ℝ)|
        = |-(m : ℝ) * (Real.exp x - 1 - x)| := by rw [hrewrite]
    _ = (m : ℝ) * |Real.exp x - 1 - x| := by
          rw [abs_mul, abs_neg, abs_of_nonneg hm_nonneg]
    _ ≤ (m : ℝ) * x ^ 2 := by
          gcongr
    _ = (lam : ℝ) ^ 2 / m := by
          dsimp [x]
          field_simp [hm_pos.ne']

/-- Helper for Exercise 17.7.3: the scaled approximation probabilities satisfy
`m * q_m → λ`. -/
private lemma poissonApproxScaledProb_tendsto (lam : NNReal) :
    Tendsto (fun m : ℕ => (m : ℝ) * poissonApproxSuccessProb lam m) atTop (𝓝 (lam : ℝ)) := by
  let N : ℕ := Nat.ceil (lam : ℝ) + 1
  have hN_pos : 1 ≤ N := by
    -- Proof comment: the extra `+ 1` keeps the comparison away from the degenerate index `0`.
    dsimp [N]
    omega
  have hlamN : (lam : ℝ) ≤ N := by
    -- Proof comment: `Nat.ceil λ + 1` is strictly above `λ`.
    have hceil : (lam : ℝ) ≤ Nat.ceil (lam : ℝ) := Nat.le_ceil (lam : ℝ)
    exact le_trans hceil (by exact_mod_cast Nat.le_succ (Nat.ceil (lam : ℝ)))
  have hbound :
      ∀ᶠ m : ℕ in atTop,
        |(m : ℝ) * poissonApproxSuccessProb lam m - (lam : ℝ)| ≤ (lam : ℝ) ^ 2 / m := by
    refine (eventually_ge_atTop N).mono ?_
    intro m hm
    exact poissonApproxScaledProb_error_le lam (le_trans hN_pos hm)
      (le_trans hlamN (by exact_mod_cast hm))
  have hdiv :
      Tendsto (fun m : ℕ => (lam : ℝ) ^ 2 / m) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat ((lam : ℝ) ^ 2)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using
    (squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound hdiv)

/-- Helper for Exercise 17.7.3: the singleton masses of the binomial approximants with parameters
`q_m = 1 - exp (-λ / m)` converge to the Poisson masses. -/
private lemma poissonApproxSingletonTendsto (lam : NNReal) (k : ℕ) :
    Tendsto
      (fun m : ℕ ↦
        let q : I := ⟨Real.toNNReal (poissonApproxSuccessProb lam m),
          poissonApproxParameter_mem_unitInterval lam m⟩
        ((Bin(m, q)) ({k} : Set ℕ)).toReal)
      atTop
      (𝓝 (poissonPMFReal lam k)) := by
  have hchoose :
      Tendsto
        (fun m : ℕ ↦
          (m.choose k : ℝ) * (poissonApproxSuccessProb lam m) ^ k *
            (1 - poissonApproxSuccessProb lam m) ^ (m - k))
        atTop
        (𝓝 (poissonPMFReal lam k)) := by
    -- Proof comment: this is the textbook Poisson limit theorem specialized to the exact
    -- zero-mass-matching probabilities `q_m`.
    simpa [poissonPMFReal] using
      (tendsto_choose_mul_pow_of_tendsto_mul_atTop
        (k := k) (p := poissonApproxSuccessProb lam) (r := (lam : ℝ))
        (poissonApproxScaledProb_tendsto lam))
  refine Tendsto.congr' ?_ hchoose
  filter_upwards with m
  dsimp
  rw [binomial_apply_singleton_toReal]
  simp [max_eq_left (poissonApproxSuccessProb_nonneg lam m)]

/-- Helper for Exercise 17.7.3: the upper tails of the binomial approximants with parameters
`q_m = 1 - exp (-λ / m)` converge to the upper tails of `Poi_λ`. -/
private lemma poissonApproxTailTendsto (lam : NNReal) (k : ℕ) :
    Tendsto
      (fun m : ℕ ↦
        let q : I := ⟨Real.toNNReal (poissonApproxSuccessProb lam m),
          poissonApproxParameter_mem_unitInterval lam m⟩
        ((Bin(m, q)) (Set.Ici k)).toReal)
      atTop
      (𝓝 (((poissonMeasure lam) (Set.Ici k)).toReal)) := by
  have hprefix :
      Tendsto
        (fun m : ℕ ↦
          ∑ i ∈ Finset.range k,
            let q : I := ⟨Real.toNNReal (poissonApproxSuccessProb lam m),
              poissonApproxParameter_mem_unitInterval lam m⟩
            ((Bin(m, q)) ({i} : Set ℕ)).toReal)
        atTop
        (𝓝 (∑ i ∈ Finset.range k, poissonPMFReal lam i)) := by
    -- Proof comment: finite prefix masses converge termwise, hence their sum converges.
    refine tendsto_finset_sum (Finset.range k) ?_
    intro i hi
    simpa using poissonApproxSingletonTendsto lam i
  have htail :
      Tendsto
        (fun m : ℕ ↦
          1 - ∑ i ∈ Finset.range k,
            let q : I := ⟨Real.toNNReal (poissonApproxSuccessProb lam m),
              poissonApproxParameter_mem_unitInterval lam m⟩
            ((Bin(m, q)) ({i} : Set ℕ)).toReal)
        atTop
        (𝓝 (1 - ∑ i ∈ Finset.range k, poissonPMFReal lam i)) := by
    -- Proof comment: tail probabilities are complements of those finite prefixes.
    exact tendsto_const_nhds.sub hprefix
  have hleft :
      (fun m : ℕ ↦
        let q : I := ⟨Real.toNNReal (poissonApproxSuccessProb lam m),
          poissonApproxParameter_mem_unitInterval lam m⟩
        ((Bin(m, q)) (Set.Ici k)).toReal) =ᶠ[atTop]
        (fun m : ℕ ↦
          1 - ∑ i ∈ Finset.range k,
            let q : I := ⟨Real.toNNReal (poissonApproxSuccessProb lam m),
              poissonApproxParameter_mem_unitInterval lam m⟩
            ((Bin(m, q)) ({i} : Set ℕ)).toReal) := by
    filter_upwards with m
    dsimp
    rw [natMeasure_tail_Ici_toReal]
  have hpoisson :
      1 - ∑ i ∈ Finset.range k, poissonPMFReal lam i =
        ((poissonMeasure lam) (Set.Ici k)).toReal := by
    -- Proof comment: the limiting Poisson tail has the same finite-prefix decomposition.
    rw [natMeasure_tail_Ici_toReal]
    refine congrArg (fun t : ℝ => 1 - t) ?_
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact (poissonMeasure_apply_singleton_toReal lam i).symm
  have htail' :
      Tendsto
        (fun m : ℕ ↦
          let q : I := ⟨Real.toNNReal (poissonApproxSuccessProb lam m),
            poissonApproxParameter_mem_unitInterval lam m⟩
          ((Bin(m, q)) (Set.Ici k)).toReal)
        atTop
        (𝓝 (1 - ∑ i ∈ Finset.range k, poissonPMFReal lam i)) :=
    htail.congr' hleft.symm
  simpa [hpoisson] using htail'

/-- Helper for Exercise 17.7.3: the power condition already forces every binomial upper tail to be
bounded by the corresponding Poisson upper tail. -/
private lemma upperTail_le_poisson_of_powCondition
    (n : ℕ) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (lam : NNReal)
    (hpow : (1 - (p : ℝ)) ^ n ≥ Real.exp (-(lam : ℝ))) :
    ∀ k : ℕ, (Bin(n, p)) (Set.Ici k) ≤ (poissonMeasure lam) (Set.Ici k) := by
  let N : ℕ := max n (Nat.ceil (lam : ℝ) + 1)
  have hN_n : n ≤ N := by
    dsimp [N]
    exact le_max_left _ _
  have hN_pos : 1 ≤ N := by
    dsimp [N]
    have : 1 ≤ Nat.ceil (lam : ℝ) + 1 := by omega
    exact le_trans this (le_max_right _ _)
  intro k
  have htail_real :
      ((Bin(n, p)) (Set.Ici k)).toReal ≤ ((poissonMeasure lam) (Set.Ici k)).toReal := by
    by_contra hlt
    have hgap :
        0 < ((Bin(n, p)) (Set.Ici k)).toReal - ((poissonMeasure lam) (Set.Ici k)).toReal := by
      linarith
    have hconv_base := (poissonApproxTailTendsto lam k).comp (tendsto_add_atTop_nat N)
    have hconv :
        Tendsto
          (fun j : ℕ ↦
            let m := N + j
            let q : I := ⟨Real.toNNReal (poissonApproxSuccessProb lam m),
              poissonApproxParameter_mem_unitInterval lam m⟩
            ((Bin(m, q)) (Set.Ici k)).toReal)
          atTop
          (𝓝 (((poissonMeasure lam) (Set.Ici k)).toReal)) := by
      -- Proof comment: the Poisson-approximation tails converge along every cofinal tail.
      refine Tendsto.congr' ?_ hconv_base
      filter_upwards with j
      simp [Function.comp, N, Nat.add_comm]
    have hconv_atTop := Metric.tendsto_atTop.1 hconv
    rcases hconv_atTop
        ((((Bin(n, p)) (Set.Ici k)).toReal - ((poissonMeasure lam) (Set.Ici k)).toReal) / 2)
        (by linarith) with ⟨J, hJ⟩
    specialize hJ J le_rfl
    have hclose :
        |((let m := N + J
            let q : I := ⟨Real.toNNReal (poissonApproxSuccessProb lam m),
              poissonApproxParameter_mem_unitInterval lam m⟩
            ((Bin(m, q)) (Set.Ici k)).toReal)) -
            ((poissonMeasure lam) (Set.Ici k)).toReal|
          < (((Bin(n, p)) (Set.Ici k)).toReal - ((poissonMeasure lam) (Set.Ici k)).toReal) / 2 := by
      simpa [Real.dist_eq] using hJ
    let m := N + J
    let q : I := ⟨Real.toNNReal (poissonApproxSuccessProb lam m),
      poissonApproxParameter_mem_unitInterval lam m⟩
    have hm_ge_n : n ≤ m := by
      dsimp [m]
      exact le_trans hN_n (Nat.le_add_right N J)
    have hm_pos : 1 ≤ m := by
      dsimp [m]
      exact le_trans hN_pos (Nat.le_add_right N J)
    have hpow_m :
        (1 - (p : ℝ)) ^ n ≥ (1 - (q : ℝ)) ^ m := by
      -- Proof comment: the chosen approximation matches the Poisson zero atom exactly.
      calc
        (1 - (p : ℝ)) ^ n ≥ Real.exp (-(lam : ℝ)) := hpow
        _ = (1 - (q : ℝ)) ^ m := by
              simpa [q, poissonApproxSuccessProb_toNNReal_coe] using
                (poissonApproxSuccessProb_pow lam hm_pos).symm
    have hst :
        StochasticLE
          (ProbabilityMeasure.toFin1Real (⟨Bin(n, p), inferInstance⟩ : ProbabilityMeasure ℕ))
          (ProbabilityMeasure.toFin1Real (⟨Bin(m, q), inferInstance⟩ : ProbabilityMeasure ℕ)) :=
      (binomial_stochasticLE_iff n m p q hp0 hp1).2 ⟨hpow_m, hm_ge_n⟩
    have hmono :
        ((Bin(n, p)) (Set.Ici k)).toReal ≤ ((Bin(m, q)) (Set.Ici k)).toReal := by
      -- Proof comment: Theorem 17.60 transfers the power condition into upper-tail dominance.
      exact ENNReal.toReal_mono (measure_ne_top (Bin(m, q)) _)
        (ProbabilityTheory.StochasticLE.upper_tail_nat
          (μ₁ := (⟨Bin(n, p), inferInstance⟩ : ProbabilityMeasure ℕ))
          (μ₂ := (⟨Bin(m, q), inferInstance⟩ : ProbabilityMeasure ℕ))
          hst k)
    have hupper :
        ((Bin(m, q)) (Set.Ici k)).toReal < ((Bin(n, p)) (Set.Ici k)).toReal := by
      have hhalf :
          ((poissonMeasure lam) (Set.Ici k)).toReal +
            (((Bin(n, p)) (Set.Ici k)).toReal - ((poissonMeasure lam) (Set.Ici k)).toReal) / 2
            < ((Bin(n, p)) (Set.Ici k)).toReal := by
        linarith
      have hclose' :
          ((Bin(m, q)) (Set.Ici k)).toReal <
            ((poissonMeasure lam) (Set.Ici k)).toReal +
              ((((Bin(n, p)) (Set.Ici k)).toReal -
                  ((poissonMeasure lam) (Set.Ici k)).toReal) / 2) := by
        have := abs_lt.mp hclose
        linarith
      linarith
    linarith
  exact (ENNReal.toReal_le_toReal
    (measure_ne_top (Bin(n, p)) (Set.Ici k))
    (measure_ne_top (poissonMeasure lam) (Set.Ici k))).mp htail_real

-- Proof sketch: the forward implication is detected at the first upper tail `Set.Ici 1`, where
-- both laws reduce to the complements of their zero atoms. For the reverse implication, compare
-- `Bin(n, p)` with the exact zero-mass-matching binomial approximants
-- `Bin(m, 1 - exp (-λ / m))`, use Theorem 17.60 at each large `m`, and then pass to the Poisson
-- limit on every upper tail.
/-- Exercise 17.7.3: for `p ∈ (0,1)`, the binomial law `Bin(n, p)` is below `Poi_λ` in the
discrete stochastic order on `ℕ` if and only if their zero-mass comparison
`(1 - p)^n ≥ exp (-λ)` holds. -/
theorem binomial_stochasticLE_poissonMeasure_iff
    (n : ℕ) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (lam : NNReal) :
    StochasticLE
      (ProbabilityMeasure.toFin1Real
        (⟨Bin(n, p), inferInstance⟩ : ProbabilityMeasure ℕ))
      (ProbabilityMeasure.toFin1Real
        (⟨poissonMeasure lam, inferInstance⟩ : ProbabilityMeasure ℕ)) ↔
      (1 - (p : ℝ)) ^ n ≥ Real.exp (-(lam : ℝ)) := by
  constructor
  · intro hst
    -- Proof comment: test the stochastic order at `Set.Ici 1`, so only the atom at `0` remains.
    have htail :
        (Bin(n, p)) (Set.Ici 1) ≤ (poissonMeasure lam) (Set.Ici 1) :=
      ProbabilityTheory.StochasticLE.upper_tail_nat
        (μ₁ := (⟨Bin(n, p), inferInstance⟩ : ProbabilityMeasure ℕ))
        (μ₂ := (⟨poissonMeasure lam, inferInstance⟩ : ProbabilityMeasure ℕ))
        hst 1
    have htail_real :
        ((Bin(n, p)) (Set.Ici 1)).toReal ≤ ((poissonMeasure lam) (Set.Ici 1)).toReal := by
      exact ENNReal.toReal_mono (measure_ne_top (poissonMeasure lam) _) htail
    rw [natMeasure_tail_Ici_toReal, natMeasure_tail_Ici_toReal] at htail_real
    simp [binomial_apply_zero_toReal, poissonMeasure_apply_zero_toReal] at htail_real
    linarith
  · intro hpow
    -- Proof comment: compare `Bin(n, p)` with the exact zero-mass-matching binomial
    -- approximants and pass to the Poisson limit on every upper tail.
    refine
      (ProbabilityTheory.stochasticLE_toFin1Real_iff_upper_tail
        (⟨Bin(n, p), inferInstance⟩ : ProbabilityMeasure ℕ)
        (⟨poissonMeasure lam, inferInstance⟩ : ProbabilityMeasure ℕ)).2 ?_
    exact upperTail_le_poisson_of_powCondition n p hp0 hp1 lam hpow

end ProbabilityTheory
