/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Exercise_6_1_4
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.HasLawExists

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: reuse the Chapter 6 `L²` convergence theorem, then replace its almost-sure limit
-- by the canonical measurable representative of the underlying `MemLp` function.
/-- For Exercise 7.1.1, part (i): if `X₁, X₂, …` is an independent sequence of
centered square-integrable real random variables and `∑ Var[X_i] < ∞`, then the
partial sums converge almost surely to a
measurable real-valued limit. In Lean's `0`-based indexing, the partial sums are `partialSum X n
= X₀ + ⋯ + Xₙ₋₁`. -/
theorem hasAETendstoPartialSums_of_iIndepFun_summable_variance
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_centered : ∀ n, P[X n] = 0)
    (h_var_summable : Summable fun n ↦ Var[X n; P]) :
    ∃ Y : Ω → ℝ, Measurable Y ∧
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ partialSum X n ω) atTop (𝓝 (Y ω)) := by
  obtain ⟨Y, hY_memLp, hY_lim⟩ :=
    exists_memLp_two_ae_tendsto_partial_sums_of_iIndepFun_summable_variance
      P X hX_indep hX_memLp hX_centered h_var_summable
  let hY_meas := hY_memLp.aestronglyMeasurable
  refine ⟨hY_meas.mk Y, hY_meas.measurable_mk, ?_⟩
  filter_upwards [hY_lim, hY_meas.ae_eq_mk] with ω hω hY_eq
  simpa [hY_eq] using hω

/-- Helper for Exercise 7.1.1: the rare-jump marginal probability of seeing a nonzero value in the
`n`th coordinate is `1 / (n + 1)^2`. -/
private noncomputable def rareJumpProbReal (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ (2 : ℕ))⁻¹

/-- Helper for Exercise 7.1.1: the `n`th marginal law puts mass `1 - 1 / (n + 1)^2` at `0` and
mass `1 / (2 (n + 1)^2)` at each of `± (n + 1)`. -/
private noncomputable def rareJumpMarginal (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - rareJumpProbReal n) • Measure.dirac 0 +
    ENNReal.ofReal (rareJumpProbReal n / 2) • Measure.dirac (n + 1 : ℝ) +
      ENNReal.ofReal (rareJumpProbReal n / 2) • Measure.dirac (-(n + 1 : ℝ))

/-- Helper for Exercise 7.1.1: the rare-jump probability `1 / (n + 1)^2` is nonnegative. -/
private lemma rareJumpProbReal_nonneg (n : ℕ) :
    0 ≤ rareJumpProbReal n := by
  -- Proof comment: the rare-jump probability is a reciprocal square.
  simpa [rareJumpProbReal] using
    (inv_nonneg.mpr (show 0 ≤ ((n + 1 : ℝ) ^ (2 : ℕ)) by positivity))

/-- Helper for Exercise 7.1.1: the rare-jump probability never exceeds `1`. -/
private lemma rareJumpProbReal_le_one (n : ℕ) :
    rareJumpProbReal n ≤ 1 := by
  -- Proof comment: `(n + 1)^2 ≥ 1`, so its reciprocal is at most `1`.
  have hsq_pos : 0 < ((n + 1 : ℝ) ^ (2 : ℕ)) := by
    positivity
  have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hsq_ge_one : (1 : ℝ) ≤ (n + 1 : ℝ) ^ (2 : ℕ) := by
    nlinarith
  have hdiv : 1 / ((n + 1 : ℝ) ^ (2 : ℕ)) ≤ 1 := by
    have hsq_ne : ((n + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 := by
      positivity
    field_simp [hsq_ne]
    nlinarith
  simpa [rareJumpProbReal, one_div] using hdiv

/-- Helper for Exercise 7.1.1: the mass at `0` in the rare-jump marginal is nonnegative. -/
private lemma rareJumpZeroWeight_nonneg (n : ℕ) :
    0 ≤ 1 - rareJumpProbReal n := by
  -- Proof comment: the zero mass is the complement of the rare-jump probability.
  exact sub_nonneg.mpr (rareJumpProbReal_le_one n)

/-- Helper for Exercise 7.1.1: the three-point rare-jump marginal is a probability measure. -/
private lemma rareJumpMarginalIsProbability (n : ℕ) :
    IsProbabilityMeasure (rareJumpMarginal n) := by
  -- Proof comment: the three weights add up to `1`.
  refine ⟨?_⟩
  have hzero_nonneg : 0 ≤ 1 - rareJumpProbReal n := rareJumpZeroWeight_nonneg n
  have hside_nonneg : 0 ≤ rareJumpProbReal n / 2 := by
    exact div_nonneg (rareJumpProbReal_nonneg n) (by norm_num)
  have hside_sum_nonneg : 0 ≤ rareJumpProbReal n / 2 + rareJumpProbReal n / 2 := by
    nlinarith
  have hside_add :
      ENNReal.ofReal (rareJumpProbReal n / 2) + ENNReal.ofReal (rareJumpProbReal n / 2) =
        ENNReal.ofReal (rareJumpProbReal n / 2 + rareJumpProbReal n / 2) := by
    exact (ENNReal.ofReal_add hside_nonneg hside_nonneg).symm
  calc
    rareJumpMarginal n Set.univ
        = ENNReal.ofReal (1 - rareJumpProbReal n) +
            ENNReal.ofReal (rareJumpProbReal n / 2) +
              ENNReal.ofReal (rareJumpProbReal n / 2) := by
            simp [rareJumpMarginal, add_assoc]
    _ = ENNReal.ofReal (1 - rareJumpProbReal n) +
          ENNReal.ofReal (rareJumpProbReal n / 2 + rareJumpProbReal n / 2) := by
          rw [add_assoc, hside_add]
    _ = ENNReal.ofReal
          ((1 - rareJumpProbReal n) + (rareJumpProbReal n / 2 + rareJumpProbReal n / 2)) := by
          rw [← ENNReal.ofReal_add hzero_nonneg hside_sum_nonneg]
    _ = 1 := by
          have hweights :
              ((1 - rareJumpProbReal n) + (rareJumpProbReal n / 2 + rareJumpProbReal n / 2)) =
                (1 : ℝ) := by
            ring
          rw [hweights]
          norm_num

/-- Helper for Exercise 7.1.1: every strongly measurable real function is integrable against the
three-point rare-jump marginal because that marginal is a finite sum of Dirac masses. -/
private lemma integrable_rareJumpMarginal (n : ℕ) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    Integrable f (rareJumpMarginal n) := by
  -- Proof comment: each Dirac component is integrable, and finite sums preserve integrability.
  have h0 :
      Integrable f (ENNReal.ofReal (1 - rareJumpProbReal n) • Measure.dirac 0) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h1 :
      Integrable f (ENNReal.ofReal (rareJumpProbReal n / 2) • Measure.dirac (n + 1 : ℝ)) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h2 :
      Integrable f (ENNReal.ofReal (rareJumpProbReal n / 2) •
        Measure.dirac (-(n + 1 : ℝ))) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  simpa [rareJumpMarginal] using
    (integrable_add_measure).2
      ⟨(integrable_add_measure).2 ⟨h0, h1⟩, h2⟩

/-- Helper for Exercise 7.1.1: integrating a real function against the rare-jump marginal reduces
to the corresponding three-point weighted average. -/
private lemma integral_rareJumpMarginal (n : ℕ) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    ∫ x, f x ∂rareJumpMarginal n =
      (1 - rareJumpProbReal n) * f 0 +
        (rareJumpProbReal n / 2) * f (n + 1 : ℝ) +
          (rareJumpProbReal n / 2) * f (-(n + 1 : ℝ)) := by
  -- Proof comment: expand the finite measure into its three Dirac components and evaluate each
  -- Bochner integral explicitly.
  have h0 :
      Integrable f (ENNReal.ofReal (1 - rareJumpProbReal n) • Measure.dirac 0) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h1 :
      Integrable f (ENNReal.ofReal (rareJumpProbReal n / 2) • Measure.dirac (n + 1 : ℝ)) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h2 :
      Integrable f (ENNReal.ofReal (rareJumpProbReal n / 2) •
        Measure.dirac (-(n + 1 : ℝ))) := by
    refine (integrable_dirac' hf ?_).smul_measure ?_
    · simp
    · simp
  have h01 :
      Integrable f
        (ENNReal.ofReal (1 - rareJumpProbReal n) • Measure.dirac 0 +
          ENNReal.ofReal (rareJumpProbReal n / 2) • Measure.dirac (n + 1 : ℝ)) := by
    exact (integrable_add_measure).2 ⟨h0, h1⟩
  rw [rareJumpMarginal, integral_add_measure h01 h2, integral_add_measure h0 h1,
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac' f 0 hf, integral_dirac' f (n + 1 : ℝ) hf,
    integral_dirac' f (-(n + 1 : ℝ)) hf]
  have hzero_nonneg : 0 ≤ 1 - rareJumpProbReal n := rareJumpZeroWeight_nonneg n
  have hside_nonneg : 0 ≤ rareJumpProbReal n / 2 := by
    exact div_nonneg (rareJumpProbReal_nonneg n) (by norm_num)
  simp [ENNReal.toReal_ofReal hzero_nonneg, ENNReal.toReal_ofReal hside_nonneg, add_assoc]

/-- Helper for Exercise 7.1.1: the rare-jump marginal has zero mean, finite second moment, and
unit variance. -/
private lemma rareJumpMarginalMoments (n : ℕ) :
    MemLp id 2 (rareJumpMarginal n) ∧
      (∫ x, x ∂rareJumpMarginal n = 0) ∧
      Var[id; rareJumpMarginal n] = 1 := by
  -- Proof comment: compute the first two moments directly from the three atoms of the marginal.
  haveI : IsProbabilityMeasure (rareJumpMarginal n) := rareJumpMarginalIsProbability n
  have hmean : ∫ x, x ∂rareJumpMarginal n = 0 := by
    calc
      ∫ x, x ∂rareJumpMarginal n
          = (1 - rareJumpProbReal n) * (0 : ℝ) +
              (rareJumpProbReal n / 2) * (n + 1 : ℝ) +
                (rareJumpProbReal n / 2) * (-(n + 1 : ℝ)) := by
              simpa using integral_rareJumpMarginal n stronglyMeasurable_id
      _ = 0 := by ring
  have hsecond :
      ∫ x, x ^ (2 : ℕ) ∂rareJumpMarginal n = 1 := by
    calc
      ∫ x, x ^ (2 : ℕ) ∂rareJumpMarginal n
          = (rareJumpProbReal n / 2) * ((n + 1 : ℝ) ^ (2 : ℕ)) +
              (rareJumpProbReal n / 2) * ((n + 1 : ℝ) ^ (2 : ℕ)) := by
              rw [integral_rareJumpMarginal n (f := fun x : ℝ ↦ x ^ (2 : ℕ)) (by fun_prop)]
              ring
      _ = 1 := by
            unfold rareJumpProbReal
            have hsq_ne : ((n + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 := by
              positivity
            field_simp [hsq_ne]
            norm_num
  have hmemLp : MemLp id 2 (rareJumpMarginal n) := by
    -- Proof comment: the square function is integrable because the marginal has finite support.
    exact (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 <| by
      simpa using
        (integrable_rareJumpMarginal n (f := fun x : ℝ ↦ x ^ (2 : ℕ)) (by fun_prop))
  have hvar : Var[id; rareJumpMarginal n] = 1 := by
    -- Proof comment: `Var[X] = E[X^2] - E[X]^2`, and the mean is already zero.
    calc
      Var[id; rareJumpMarginal n]
          = ∫ x, x ^ (2 : ℕ) ∂rareJumpMarginal n - (∫ x, x ∂rareJumpMarginal n) ^ (2 : ℕ) := by
              simpa using (variance_eq_sub hmemLp)
      _ = 1 := by rw [hsecond, hmean]; ring
  exact ⟨hmemLp, hmean, hvar⟩

/-- Helper for Exercise 7.1.1: the nonzero event under the rare-jump marginal has exactly the
rare-jump probability `1 / (n + 1)^2`. -/
private lemma rareJumpMarginalNonzeroMass (n : ℕ) :
    rareJumpMarginal n {x : ℝ | x ≠ 0} = ENNReal.ofReal (rareJumpProbReal n) := by
  -- Proof comment: only the two symmetric nonzero atoms contribute to this event.
  have hne : (n + 1 : ℝ) ≠ 0 := by
    positivity
  have hneg' : (-1 + -(n : ℝ)) ≠ 0 := by
    nlinarith
  have hside_nonneg : 0 ≤ rareJumpProbReal n / 2 := by
    exact div_nonneg (rareJumpProbReal_nonneg n) (by norm_num)
  have hside_sum_nonneg : 0 ≤ rareJumpProbReal n / 2 + rareJumpProbReal n / 2 := by
    nlinarith
  have hside_add :
      ENNReal.ofReal (rareJumpProbReal n / 2) + ENNReal.ofReal (rareJumpProbReal n / 2) =
        ENNReal.ofReal (rareJumpProbReal n / 2 + rareJumpProbReal n / 2) := by
    exact (ENNReal.ofReal_add hside_nonneg hside_nonneg).symm
  calc
    rareJumpMarginal n {x : ℝ | x ≠ 0}
        = ENNReal.ofReal (rareJumpProbReal n / 2) +
            ENNReal.ofReal (rareJumpProbReal n / 2) := by
            simp [rareJumpMarginal, hne, hneg']
    _ = ENNReal.ofReal (rareJumpProbReal n) := by
          rw [hside_add]
          ring

/-- Helper for Exercise 7.1.1: once a path is eventually zero, its coordinate partial sums are
eventually constant and therefore converge. -/
private lemma tendstoPartialSumCoordinateProcessOfEventuallyZero (ω : ℕ → ℝ)
    (hω : ∀ᶠ n in atTop, ω n = 0) :
    ∃ l : ℝ, Tendsto (fun n ↦ partialSum coordinateProcess n ω) atTop (𝓝 l) := by
  -- Proof comment: after the last nonzero coordinate, every tail block in
  -- `partialSum_sub_eq_sum_Ico` vanishes.
  rcases Filter.eventually_atTop.1 hω with ⟨N, hN⟩
  refine ⟨partialSum coordinateProcess N ω, ?_⟩
  have hconst :
      (fun n ↦ partialSum coordinateProcess n ω) =ᶠ[atTop]
        fun _ ↦ partialSum coordinateProcess N ω := by
    refine Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    have htail :
        ∑ i ∈ Finset.Ico N n, coordinateProcess i ω = 0 := by
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      exact hN i (Finset.mem_Ico.1 hi).1
    have hdiff := partialSum_sub_eq_sum_Ico coordinateProcess hn ω
    have hEq : partialSum coordinateProcess n ω - partialSum coordinateProcess N ω = 0 := by
      simpa [htail] using hdiff
    exact sub_eq_zero.mp hEq
  exact Tendsto.congr' hconst.symm tendsto_const_nhds

-- Proof sketch: take a product probability measure on `ℝ^ℕ` whose `n`th coordinate is usually
-- `0` but equals `± (n + 1)` with probability of order `(n + 1)⁻²`. Then the coordinates are
-- independent, centered, and square integrable with nonsummable variances, while Borel--Cantelli
-- gives only finitely many nonzero coordinates almost surely, so the partial sums converge almost
-- surely.
/-- Exercise 7.1.1 (2): (ii) The converse in part (i) does not hold: there exists a probability
measure on `ℝ^ℕ` whose coordinate process is independent, centered, and square integrable, whose
partial sums converge almost surely, but whose variance series is not summable. -/
theorem exists_counterexample_to_converse_of_summable_variance
    :
    ∃ P : ProbabilityMeasure (ℕ → ℝ),
      iIndepFun coordinateProcess P ∧
        (∀ n, MemLp (coordinateProcess n) 2 P) ∧
        (∀ n, P[coordinateProcess n] = 0) ∧
        (∃ Y : (ℕ → ℝ) → ℝ, Measurable Y ∧
          ∀ᵐ ω ∂P.toMeasure,
            Tendsto (fun n ↦ partialSum coordinateProcess n ω) atTop (𝓝 (Y ω))) ∧
        ¬ Summable (fun n ↦ Var[coordinateProcess n; P]) := by
  -- Route correction: instead of searching for an explicit measurable limit on `ℝ^ℕ`, first show
  -- the partial sums converge almost surely because the path is eventually zero, then invoke the
  -- measurable-selection theorem for almost-sure limits.
  letI : ∀ n, IsProbabilityMeasure (rareJumpMarginal n) := rareJumpMarginalIsProbability
  let P0 : Measure (ℕ → ℝ) := Measure.infinitePi rareJumpMarginal
  let P : ProbabilityMeasure (ℕ → ℝ) := ⟨P0, inferInstance⟩
  have hcoordLaw : ∀ n, HasLaw (coordinateProcess n) (rareJumpMarginal n) P0 := by
    -- Proof comment: each coordinate projection on the infinite product has its prescribed marginal
    -- law via the canonical measure-preserving evaluation map.
    intro n
    simpa [P0, coordinateProcess] using
      (MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi rareJumpMarginal n) :
        HasLaw (Function.eval n) (rareJumpMarginal n) P0)
  have hIndep0 : iIndepFun coordinateProcess P0 := by
    -- Proof comment: independence is the standard infinite-product independence of the coordinate
    -- projections specialized to the identity maps on each factor.
    simpa [P0, coordinateProcess] using
      (iIndepFun_infinitePi (P := rareJumpMarginal) (fun _ ↦ measurable_id) :
        iIndepFun (fun i ω ↦ ω i) P0)
  have hcoordIdent : ∀ n, IdentDistrib (coordinateProcess n) id P0 (rareJumpMarginal n) := by
    -- Proof comment: the coordinate map and the identity have the same pushforward measure.
    intro n
    refine ⟨(hcoordLaw n).aemeasurable, aemeasurable_id, ?_⟩
    simpa using (hcoordLaw n).map_eq
  have hMemLp0 : ∀ n, MemLp (coordinateProcess n) 2 P0 := by
    -- Proof comment: transport `L²` integrability from the one-dimensional marginal law along the
    -- coordinate projection map.
    intro n
    exact (hcoordIdent n).symm.memLp_snd (rareJumpMarginalMoments n).1
  have hCentered0 : ∀ n, P0[coordinateProcess n] = 0 := by
    -- Proof comment: the coordinate expectation equals the marginal expectation, which was already
    -- computed to vanish.
    intro n
    simpa [rareJumpMarginalMoments n |>.2.1] using (hcoordLaw n).integral_eq
  have hVar0 : ∀ n, Var[coordinateProcess n; P0] = 1 := by
    -- Proof comment: the coordinate variance is exactly the variance of its marginal law.
    intro n
    simpa [rareJumpMarginalMoments n |>.2.2] using (hcoordLaw n).variance_eq
  let A : ℕ → Set (ℕ → ℝ) := fun n ↦ {ω | coordinateProcess n ω ≠ 0}
  have hA_prob : ∀ n, P0 (A n) = ENNReal.ofReal (rareJumpProbReal n) := by
    -- Proof comment: rewrite the event through the coordinate map and apply the marginal
    -- computation of the nonzero mass.
    intro n
    have hnonzero_meas : MeasurableSet {x : ℝ | x ≠ 0} := by
      exact (measurableSet_singleton (0 : ℝ)).compl
    calc
      P0 (A n) = (Measure.map (Function.eval n) P0) {x : ℝ | x ≠ 0} := by
        rw [Measure.map_apply (by fun_prop) hnonzero_meas]
        simp [A, coordinateProcess]
      _ = rareJumpMarginal n {x : ℝ | x ≠ 0} := by
        simpa [coordinateProcess] using
          congrArg (fun ν : Measure ℝ => ν {x : ℝ | x ≠ 0}) (hcoordLaw n).map_eq
      _ = ENNReal.ofReal (rareJumpProbReal n) := rareJumpMarginalNonzeroMass n
  let pA : ℕ → ENNReal := fun n ↦ P0 (A n)
  have hrare_summable : Summable rareJumpProbReal := by
    -- Proof comment: this is the shifted `p`-series with exponent `2`.
    have hsquare : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (2 : ℕ))⁻¹) := by
      exact Real.summable_nat_pow_inv.mpr (by norm_num)
    simpa [rareJumpProbReal] using
      (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ) ^ (2 : ℕ))⁻¹) 1).2 hsquare
  have hpA_eq : pA = fun n ↦ ENNReal.ofReal (rareJumpProbReal n) := by
    funext n
    exact hA_prob n
  let tA : ENNReal := ∑' n, pA n
  have hA_tsum_lt_top : tA < ⊤ := by
    -- Proof comment: the Borel--Cantelli input is exactly the summable rare-jump series.
    simpa [tA, hpA_eq] using hrare_summable.tsum_ofReal_lt_top
  have hA_tsum_ne_top : tA ≠ ⊤ :=
    hA_tsum_lt_top.ne
  have hAe_eventually_zero : ∀ᵐ ω ∂P0, ∀ᶠ n in atTop, ω n = 0 := by
    -- Proof comment: first Borel--Cantelli says that only finitely many nonzero coordinates occur
    -- almost surely.
    filter_upwards
      [MeasureTheory.ae_eventually_notMem (μ := P0) (s := A)
        (by simpa [pA, tA] using hA_tsum_ne_top)]
      with ω hω
    filter_upwards [hω] with n hn
    simpa [A, coordinateProcess] using hn
  have hAe_tendsto :
      ∀ᵐ ω ∂P0, ∃ l : ℝ, Tendsto (fun n ↦ partialSum coordinateProcess n ω) atTop (𝓝 l) := by
    -- Proof comment: eventual zeros force the partial sums to stabilize.
    filter_upwards [hAe_eventually_zero] with ω hω
    exact tendstoPartialSumCoordinateProcessOfEventuallyZero ω hω
  have hPartialMeas : ∀ n, AEStronglyMeasurable (partialSum coordinateProcess n) P0 := by
    -- Proof comment: each partial sum is a finite sum of measurable coordinate projections.
    intro n
    refine (Finset.measurable_sum (Finset.range n) fun i _ ↦ ?_).aestronglyMeasurable
    simpa [coordinateProcess] using measurable_pi_apply i
  obtain ⟨Y, hY_strong, hY_tendsto⟩ :=
    exists_stronglyMeasurable_limit_of_tendsto_ae hPartialMeas hAe_tendsto
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [P] using hIndep0
  · simpa [P] using hMemLp0
  · simpa [P] using hCentered0
  · refine ⟨Y, hY_strong.measurable, ?_⟩
    simpa [P] using hY_tendsto
  · -- Proof comment: the variance sequence is identically `1`, so it cannot be summable.
    have hnotConst : ¬ Summable (fun _ : ℕ ↦ (1 : ℝ)) := by
      simp [summable_const_iff]
    intro hsum
    exact hnotConst (hsum.congr hVar0)
