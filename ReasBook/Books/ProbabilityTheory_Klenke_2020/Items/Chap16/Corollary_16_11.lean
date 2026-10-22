/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ComplexConjugate

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Corollary 16.11: the canonical embedding `ℝ → EuclideanSpace ℝ (Fin 1)`. -/
private noncomputable def realToEuclidean1 : ℝ → E1 := fun t ↦ EuclideanSpace.single 0 t

/-- Helper for Corollary 16.11: the unique coordinate map `EuclideanSpace ℝ (Fin 1) → ℝ`. -/
private def euclidean1ToReal : E1 → ℝ := fun x ↦ x 0

/-- Helper for Corollary 16.11: the canonical embedding `ℝ → EuclideanSpace ℝ (Fin 1)` is
measurable. -/
private lemma measurable_realToEuclidean1 : Measurable realToEuclidean1 := by
  have hsingle : Continuous fun t : ℝ ↦ (Pi.single (0 : Fin 1) t : Fin 1 → ℝ) := by
    refine _root_.continuous_pi ?_
    intro i
    fin_cases i
    simpa using continuous_id
  simpa [realToEuclidean1, EuclideanSpace.single] using
    ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 1 => ℝ)).comp hsingle).measurable

/-- Helper for Corollary 16.11: the canonical embedding is a.e.-measurable for every real
measure. -/
private lemma aemeasurable_realToEuclidean1 (μ : Measure ℝ) :
    AEMeasurable realToEuclidean1 μ :=
  measurable_realToEuclidean1.aemeasurable

/-- Helper for Corollary 16.11: pushing a real probability law along `realToEuclidean1`
preserves its characteristic function after reading the unique coordinate. -/
private lemma charFun_map_realToEuclidean1 (μ : ProbabilityMeasure ℝ) (x : E1) :
    charFun
        (μ.map (aemeasurable_realToEuclidean1 (μ : Measure ℝ)) : Measure E1) x =
      charFun (μ : Measure ℝ) (euclidean1ToReal x) := by
  change
    charFun (Measure.map realToEuclidean1 (μ : Measure ℝ)) x =
      charFun (μ : Measure ℝ) (euclidean1ToReal x)
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply_real,
    MeasureTheory.integral_map (aemeasurable_realToEuclidean1 (μ : Measure ℝ)) (by fun_prop)]
  congr with t
  congr 1
  have hinner : inner ℝ (EuclideanSpace.single (0 : Fin 1) t) x = euclidean1ToReal x * t := by
    simpa [euclidean1ToReal, mul_comm] using
      (EuclideanSpace.inner_single_left (i := (0 : Fin 1)) t x)
  exact congrArg (fun z : ℂ ↦ z * Complex.I) (by exact_mod_cast hinner)

/-- Helper for Corollary 16.11: the characteristic function of each probability law in a sequence
is itself a characteristic function in the CFP sense. -/
private lemma charFunSequence_isCFP
    {ρs : ℕ → ProbabilityMeasure ℝ} (n : ℕ) :
    IsCFP (fun t : ℝ ↦ charFun (ρs n : Measure ℝ) t) := by
  simpa using MeasureTheory.ProbabilityMeasure.isCFP_charFun (ρs n)

/-- Helper for Corollary 16.11: if the `n`th convolution powers of `ρs n` are eventually `μ`,
then the powered characteristic functions converge pointwise to `charFun μ`. -/
private lemma exactRootCharPow_tendsto
    {μ : ProbabilityMeasure ℝ} {ρs : ℕ → ProbabilityMeasure ℝ}
    (hpowρ : ∀ᶠ n : ℕ in atTop, ρs n ^ n = μ) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ ↦ charFun (ρs n : Measure ℝ) t ^ n) atTop
        (𝓝 (charFun (μ : Measure ℝ) t)) := by
  intro t
  have hEventually :
      (fun n : ℕ ↦ charFun (ρs n : Measure ℝ) t ^ n) =ᶠ[atTop]
        fun _ : ℕ ↦ charFun (μ : Measure ℝ) t := by
    filter_upwards [hpowρ] with n hn
    -- Proof comment: once `ρs n ^ n = μ`, the powered characteristic function is literally
    -- `charFun μ` at the fixed frequency `t`.
    simpa [hn] using
      (congrArg (fun f : ℝ → ℂ ↦ f t)
        (MeasureTheory.ProbabilityMeasure.charFun_pow (ρs n) n)).symm
  exact Tendsto.congr' hEventually.symm tendsto_const_nhds

/-- Helper for Corollary 16.11: a positive lower bound on `r^n` controls the logarithmic defect
`n * (1 - r)`. -/
private lemma natMulOneSub_le_negLog_of_pow_ge {r c : ℝ} {n : ℕ}
    (hr_nonneg : 0 ≤ r) (hc_pos : 0 < c) (hc_le : c ≤ r ^ n) :
    (n : ℝ) * (1 - r) ≤ -Real.log c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hc_le_one : c ≤ 1 := by simpa using hc_le
    have hlog_nonpos : Real.log c ≤ 0 := Real.log_nonpos hc_pos.le hc_le_one
    have hneg_nonneg : 0 ≤ -Real.log c := by linarith
    simpa using hneg_nonneg
  · have hr_pow_pos : 0 < r ^ n := lt_of_lt_of_le hc_pos hc_le
    have hr_ne_zero : r ≠ 0 := by
      intro hr_zero
      rw [hr_zero, zero_pow hn.ne'] at hr_pow_pos
      exact lt_irrefl _ hr_pow_pos
    have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne_zero)
    have hlog_le :
        Real.log c ≤ (n : ℝ) * (r - 1) := by
      calc
        Real.log c ≤ Real.log (r ^ n) := Real.log_le_log hc_pos hc_le
        _ = (n : ℝ) * Real.log r := by
          rw [← Real.rpow_natCast, Real.log_rpow hr_pos]
        _ ≤ (n : ℝ) * (r - 1) := by
          exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr_pos) (by positivity)
    linarith

/-- Helper for Corollary 16.11: if `χ` is a CFP, then `t ↦ χ t * conj (χ t)` is again a CFP. -/
private lemma isCFPMulConj {χ : ℝ → ℂ} (hχ : IsCFP χ) :
    IsCFP (fun t ↦ χ t * conj (χ t)) := by
  rcases hχ with ⟨μ, rfl⟩
  let ν : ProbabilityMeasure ℝ :=
    μ.map ((measurable_const.mul measurable_id).aemeasurable :
      AEMeasurable (fun x : ℝ ↦ (-1 : ℝ) * x) (μ : Measure ℝ))
  refine ⟨μ * ν, ?_⟩
  funext t
  have hν :
      charFun (ν : Measure ℝ) t = conj (charFun (μ : Measure ℝ) t) := by
    -- Proof comment: reflecting the law replaces `t` by `-t`, which conjugates the
    -- characteristic function.
    calc
      charFun (ν : Measure ℝ) t = charFun (μ : Measure ℝ) ((-1 : ℝ) * t) := by
        simpa [ν] using (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) (-1) t)
      _ = charFun (μ : Measure ℝ) (-t) := by simp
      _ = conj (charFun (μ : Measure ℝ) t) := MeasureTheory.charFun_neg t
  calc
    charFun ((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun (μ : Measure ℝ) t * charFun (ν : Measure ℝ) t := by
            simpa using
              (MeasureTheory.charFun_conv
                (μ := (μ : Measure ℝ)) (ν := (ν : Measure ℝ)) t)
    _ = charFun (μ : Measure ℝ) t * conj (charFun (μ : Measure ℝ) t) := by rw [hν]

/-- Helper for Corollary 16.11: the doubled-frequency real-part defect of a CFP on `ℝ` is
controlled by the standard factor `4` bound. -/
private lemma oneSubReIsCFPTwoMulLeFourMul {χ : ℝ → ℂ}
    (hχ : IsCFP χ) (t : ℝ) :
    1 - Complex.re (χ (2 * t)) ≤ 4 * (1 - Complex.re (χ t)) := by
  rcases hχ with ⟨μ, rfl⟩
  let ν : ProbabilityMeasure E1 := μ.map (aemeasurable_realToEuclidean1 (μ : Measure ℝ))
  have hraw :
      1 - Complex.re
            (charFun ((ν : ProbabilityMeasure E1) : Measure E1) ((2 : ℝ) • realToEuclidean1 t))
        ≤
          4 * (1 -
            Complex.re
              (charFun ((ν : ProbabilityMeasure E1) : Measure E1) (realToEuclidean1 t))) := by
    -- Proof comment: apply Lemma 15.11 to the identity random variable on the pushed-forward
    -- one-dimensional Euclidean law.
    simpa [ν] using
      (one_sub_re_charFun_two_smul_le_four_mul
        (P := (μ : Measure ℝ)) (X := realToEuclidean1) measurable_realToEuclidean1
        (realToEuclidean1 t))
  have htwo :
      charFun ((ν : ProbabilityMeasure E1) : Measure E1) ((2 : ℝ) • realToEuclidean1 t) =
        charFun (μ : Measure ℝ) (2 * t) := by
    calc
      charFun ((ν : ProbabilityMeasure E1) : Measure E1) ((2 : ℝ) • realToEuclidean1 t)
          = charFun (μ : Measure ℝ) (euclidean1ToReal ((2 : ℝ) • realToEuclidean1 t)) := by
              simpa [ν] using charFun_map_realToEuclidean1 (μ := μ)
                ((2 : ℝ) • realToEuclidean1 t)
      _ = charFun (μ : Measure ℝ) (2 * t) := by
            simp [euclidean1ToReal, realToEuclidean1]
  have hone :
      charFun ((ν : ProbabilityMeasure E1) : Measure E1) (realToEuclidean1 t) =
        charFun (μ : Measure ℝ) t := by
    calc
      charFun ((ν : ProbabilityMeasure E1) : Measure E1) (realToEuclidean1 t)
          = charFun (μ : Measure ℝ) (euclidean1ToReal (realToEuclidean1 t)) := by
              simpa [ν] using charFun_map_realToEuclidean1 (μ := μ) (realToEuclidean1 t)
      _ = charFun (μ : Measure ℝ) t := by
            simp [euclidean1ToReal, realToEuclidean1]
  rw [htwo, hone] at hraw
  simpa using hraw

/-- Helper for Corollary 16.11: exact convolution roots force a uniform local logarithmic-defect
bound around `0`. -/
private lemma exactRootLocalModulusDefectBound
    {μ : ProbabilityMeasure ℝ} {ρs : ℕ → ProbabilityMeasure ℝ}
    (hpowρ : ∀ᶠ n : ℕ in atTop, ρs n ^ n = μ) :
    ∃ ε > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Set.Icc (-ε) ε, (n : ℝ) * (1 - ‖charFun (ρs n : Measure ℝ) s‖ ^ 2) ≤ C := by
  have hnear :
      {s : ℝ | charFun (μ : Measure ℝ) s ∈ Metric.ball (1 : ℂ) (1 / 2)} ∈ 𝓝 (0 : ℝ) := by
    have hEvent :
        {s : ℝ |
            charFun (μ : Measure ℝ) s ∈
              Metric.ball (charFun (μ : Measure ℝ) 0) (1 / 2)} ∈ 𝓝 (0 : ℝ) := by
      exact
        (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt.tendsto.eventually
          (Metric.ball_mem_nhds _ (show 0 < (1 / 2 : ℝ) by norm_num))
    simpa [MeasureTheory.charFun_zero (μ := (μ : Measure ℝ))] using hEvent
  rcases Metric.mem_nhds_iff.mp hnear with ⟨δ, hδpos, hδsubset⟩
  let ε : ℝ := δ / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < δ := by
    dsimp [ε]
    linarith
  have hsmall :
      ∀ s ∈ Set.Icc (-ε) ε, (1 / 2 : ℝ) < ‖charFun (μ : Measure ℝ) s‖ := by
    intro s hs
    have hsabs : |s| ≤ ε := by
      exact abs_le.mpr ⟨hs.1, hs.2⟩
    have hsball : s ∈ Metric.ball (0 : ℝ) δ := by
      change dist s 0 < δ
      simpa [Real.dist_eq] using lt_of_le_of_lt hsabs hεlt
    have hclose : ‖charFun (μ : Measure ℝ) s - 1‖ < (1 / 2 : ℝ) := by
      have hsballφ : charFun (μ : Measure ℝ) s ∈ Metric.ball (1 : ℂ) (1 / 2) := hδsubset hsball
      simpa [Metric.mem_ball, dist_eq_norm] using hsballφ
    have hone_le : (1 : ℝ) ≤ ‖1 - charFun (μ : Measure ℝ) s‖ + ‖charFun (μ : Measure ℝ) s‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_add_le (1 - charFun (μ : Measure ℝ) s) (charFun (μ : Measure ℝ) s))
    have hclose' : ‖1 - charFun (μ : Measure ℝ) s‖ < (1 / 2 : ℝ) := by
      simpa [norm_sub_rev] using hclose
    nlinarith
  refine ⟨ε, hεpos, -Real.log (1 / 16 : ℝ), ?_, ?_⟩
  · exact neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  · filter_upwards [hpowρ] with n hn
    intro s hs
    have hμlower : (1 / 2 : ℝ) < ‖charFun (μ : Measure ℝ) s‖ := hsmall s hs
    have hpowEq :
        charFun (ρs n : Measure ℝ) s ^ n = charFun (μ : Measure ℝ) s := by
      simpa [hn] using
        (congrArg (fun f : ℝ → ℂ ↦ f s)
          (MeasureTheory.ProbabilityMeasure.charFun_pow (ρs n) n)).symm
    have hpowlower : (1 / 2 : ℝ) < ‖charFun (ρs n : Measure ℝ) s ^ n‖ := by
      simpa [hpowEq] using hμlower
    have hnormSq_le_one : ‖charFun (ρs n : Measure ℝ) s‖ ^ 2 ≤ 1 := by
      have hnorm_le_one :
          ‖charFun (ρs n : Measure ℝ) s‖ ≤ 1 :=
        MeasureTheory.norm_charFun_le_one (μ := (ρs n : Measure ℝ)) s
      have hnorm_nonneg : 0 ≤ ‖charFun (ρs n : Measure ℝ) s‖ := norm_nonneg _
      nlinarith [sq_nonneg (1 - ‖charFun (ρs n : Measure ℝ) s‖), hnorm_nonneg, hnorm_le_one]
    have hpowSq_ge : (1 / 16 : ℝ) ≤ (‖charFun (ρs n : Measure ℝ) s‖ ^ 2) ^ n := by
      have hsq : (1 / 16 : ℝ) < ‖charFun (ρs n : Measure ℝ) s ^ n‖ ^ 2 := by
        nlinarith [hpowlower, sq_nonneg ‖charFun (ρs n : Measure ℝ) s ^ n‖]
      calc
        (1 / 16 : ℝ) ≤ ‖charFun (ρs n : Measure ℝ) s ^ n‖ ^ 2 := le_of_lt hsq
        _ = (‖charFun (ρs n : Measure ℝ) s‖ ^ 2) ^ n := by
            calc
              ‖charFun (ρs n : Measure ℝ) s ^ n‖ ^ 2 =
                  (‖charFun (ρs n : Measure ℝ) s‖ ^ n) ^ 2 := by
                    rw [norm_pow]
              _ = ‖charFun (ρs n : Measure ℝ) s‖ ^ (n * 2) := by
                    rw [pow_mul]
              _ = ‖charFun (ρs n : Measure ℝ) s‖ ^ (2 * n) := by
                    rw [Nat.mul_comm]
              _ = (‖charFun (ρs n : Measure ℝ) s‖ ^ 2) ^ n := by
                    rw [pow_mul]
    -- Proof comment: on the small interval, the exact `n`th-power identity transfers the lower
    -- bound for `charFun μ` into a uniform logarithmic-defect bound for the roots.
    exact natMulOneSub_le_negLog_of_pow_ge
      (by positivity) (by norm_num) hpowSq_ge

/-- Helper for Corollary 16.11: a local logarithmic-defect bound for exact roots propagates to a
Gaussian lower bound away from the origin. -/
private theorem charFunLargeFrequencyGaussianLowerBoundOfLocalDefect
    {μ : ProbabilityMeasure ℝ} {ρs : ℕ → ProbabilityMeasure ℝ} {ε C : ℝ}
    (hpowρ : ∀ᶠ n : ℕ in atTop, ρs n ^ n = μ)
    (hεpos : 0 < ε) (hCpos : 0 < C)
    (hlocal : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Set.Icc (-ε) ε, (n : ℝ) * (1 - ‖charFun (ρs n : Measure ℝ) s‖ ^ 2) ≤ C) :
    ∃ γ > 0, ∀ t : ℝ, ε ≤ |t| →
      (1 / 2 : ℝ) * Real.exp (-γ * t ^ 2) ≤ ‖charFun (μ : Measure ℝ) t‖ := by
  have hdyadic :
      ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
        ∀ s ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε),
          (n : ℝ) * (1 - ‖charFun (ρs n : Measure ℝ) s‖ ^ 2) ≤ (4 ^ k : ℝ) * C := by
    intro k
    induction k with
    | zero =>
        -- Proof comment: the assumed local defect bound is the dyadic base case.
        filter_upwards [hlocal] with n hn s hs
        simpa using hn s (by simpa using hs)
    | succ k ih =>
        filter_upwards [ih] with n hn s hs
        let u : ℝ := s / 2
        have hs_two : 2 * u = s := by
          dsimp [u]
          ring_nf
        have hpow2 : ((2 ^ (k + 1) : ℝ) * ε) = 2 * ((2 ^ k : ℝ) * ε) := by
          simp [pow_succ, mul_left_comm, mul_comm]
        have hu :
            u ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε) := by
          rw [hpow2] at hs
          constructor
          · have hsleft := hs.1
            dsimp [u]
            nlinarith
          · have hsright := hs.2
            dsimp [u]
            nlinarith
        have hdbl :
            1 - ‖charFun (ρs n : Measure ℝ) s‖ ^ 2 ≤
              4 * (1 - ‖charFun (ρs n : Measure ℝ) u‖ ^ 2) := by
          have hχ :=
            oneSubReIsCFPTwoMulLeFourMul
              (hχ := isCFPMulConj (charFunSequence_isCFP (ρs := ρs) n)) u
          have hre_mul_conj (x : ℝ) :
              Complex.re
                  (charFun (ρs n : Measure ℝ) x * conj (charFun (ρs n : Measure ℝ) x)) =
                ‖charFun (ρs n : Measure ℝ) x‖ ^ 2 := by
            have hnormSq :
                charFun (ρs n : Measure ℝ) x * conj (charFun (ρs n : Measure ℝ) x) =
                  (Complex.normSq (charFun (ρs n : Measure ℝ) x) : ℂ) := by
              rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
            rw [hnormSq, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
          -- Proof comment: apply the doubled-frequency estimate to the CFP
          -- `t ↦ φₙ(t) * conj (φₙ(t)) = ‖φₙ(t)‖²`.
          simpa [u, hs_two, hre_mul_conj] using hχ
        calc
          (n : ℝ) * (1 - ‖charFun (ρs n : Measure ℝ) s‖ ^ 2)
              ≤ (n : ℝ) * (4 * (1 - ‖charFun (ρs n : Measure ℝ) u‖ ^ 2)) := by
                  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
                  gcongr
          _ = 4 * ((n : ℝ) * (1 - ‖charFun (ρs n : Measure ℝ) u‖ ^ 2)) := by ring
          _ ≤ 4 * ((4 ^ k : ℝ) * C) := by
                have huBound := hn u hu
                nlinarith
          _ = (4 ^ (k + 1) : ℝ) * C := by
                simp [pow_succ, mul_left_comm, mul_comm]
  refine ⟨4 * C / ε ^ 2, by positivity, ?_⟩
  intro t hεle
  have hexists : ∃ m : ℕ, |t| ≤ (2 ^ m : ℝ) * ε := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (|t| / ε) (show (1 : ℝ) < 2 by norm_num)
    have hm' : |t| / ε < (2 ^ m : ℝ) := by
      simpa using hm
    have hmul := (div_lt_iff₀ hεpos).mp hm'
    exact ⟨m, le_of_lt (by simpa [mul_comm] using hmul)⟩
  let k : ℕ := Nat.find hexists
  have htk : |t| ≤ (2 ^ k : ℝ) * ε := Nat.find_spec hexists
  have htIcc : t ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε) := by
    simpa [abs_le] using htk
  have hbound_t :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * (1 - ‖charFun (ρs n : Measure ℝ) t‖ ^ 2) ≤ (4 ^ k : ℝ) * C := by
    filter_upwards [hdyadic k] with n hn
    exact hn t htIcc
  let B : ℝ := (4 ^ k : ℝ) * C
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hmodel :
      Tendsto (fun n : ℕ ↦ (1 - B / n) ^ n) atTop (𝓝 (Real.exp (-B))) := by
    -- Proof comment: compare the dyadic defect bound with the explicit exponential model.
    simpa [B, sub_eq_add_neg, neg_div] using Real.tendsto_one_add_div_pow_exp (-B)
  have hmodelEventually :
      ∀ᶠ n : ℕ in atTop, Real.exp (-B) / 2 < (1 - B / n) ^ n := by
    have hhalf_lt : Real.exp (-B) / 2 < Real.exp (-B) := by
      have hexp_pos : 0 < Real.exp (-B) := Real.exp_pos (-B)
      nlinarith
    exact hmodel.eventually (Ioi_mem_nhds hhalf_lt)
  have hlarge :
      ∀ᶠ n : ℕ in atTop, B < n := by
    exact tendsto_natCast_atTop_atTop.eventually_gt_atTop B
  have hpowLower :
      ∀ᶠ n : ℕ in atTop,
        Real.exp (-B) / 2 ≤ (‖charFun (ρs n : Measure ℝ) t‖ ^ 2) ^ n := by
    filter_upwards [hbound_t, hmodelEventually, hlarge] with n hn hmodeln hnlarge
    have hn_nat_pos : 0 < n := by
      by_contra hnzero
      have hnzero' : n = 0 := Nat.eq_zero_of_not_pos hnzero
      subst hnzero'
      exact (not_lt.mpr hBnonneg) (by simpa using hnlarge)
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast hn_nat_pos
    have hdefect : 1 - ‖charFun (ρs n : Measure ℝ) t‖ ^ 2 ≤ B / n := by
      rw [le_div_iff₀ hnpos]
      simpa [B, mul_comm, mul_left_comm, mul_assoc] using hn
    have hbase_le : 1 - B / n ≤ ‖charFun (ρs n : Measure ℝ) t‖ ^ 2 := by
      linarith
    have hbase_nonneg : 0 ≤ 1 - B / n := by
      have hdiv_lt : B / n < 1 := by
        rw [div_lt_iff₀ hnpos]
        linarith
      linarith
    have hpow_le :
        (1 - B / n) ^ n ≤ (‖charFun (ρs n : Measure ℝ) t‖ ^ 2) ^ n := by
      exact pow_le_pow_left₀ hbase_nonneg hbase_le n
    exact le_trans (le_of_lt hmodeln) hpow_le
  have hpowEqEventually :
      ∀ᶠ n : ℕ in atTop,
        (‖charFun (ρs n : Measure ℝ) t‖ ^ 2) ^ n = ‖charFun (μ : Measure ℝ) t‖ ^ 2 := by
    filter_upwards [hpowρ] with n hn
    have hpowEq :
        charFun (ρs n : Measure ℝ) t ^ n = charFun (μ : Measure ℝ) t := by
      simpa [hn] using
        (congrArg (fun f : ℝ → ℂ ↦ f t)
          (MeasureTheory.ProbabilityMeasure.charFun_pow (ρs n) n)).symm
    calc
      (‖charFun (ρs n : Measure ℝ) t‖ ^ 2) ^ n
          = ‖charFun (ρs n : Measure ℝ) t ^ n‖ ^ 2 := by
              calc
                (‖charFun (ρs n : Measure ℝ) t‖ ^ 2) ^ n
                    = ‖charFun (ρs n : Measure ℝ) t‖ ^ (2 * n) := by
                        rw [pow_mul]
                _ = ‖charFun (ρs n : Measure ℝ) t‖ ^ (n * 2) := by
                      rw [Nat.mul_comm]
                _ = (‖charFun (ρs n : Measure ℝ) t‖ ^ n) ^ 2 := by
                      rw [pow_mul]
                _ = ‖charFun (ρs n : Measure ℝ) t ^ n‖ ^ 2 := by
                      rw [norm_pow]
      _ = ‖charFun (μ : Measure ℝ) t‖ ^ 2 := by rw [hpowEq]
  have hlimit_lower_sq : Real.exp (-B) / 2 ≤ ‖charFun (μ : Measure ℝ) t‖ ^ 2 := by
    obtain ⟨n, hnLower, hnEq⟩ := (hpowLower.and hpowEqEventually).exists
    exact le_trans hnLower (le_of_eq hnEq)
  have hnorm_le_one :
      ‖charFun (μ : Measure ℝ) t‖ ≤ 1 :=
    MeasureTheory.norm_charFun_le_one (μ := (μ : Measure ℝ)) t
  have hnormSq_le :
      ‖charFun (μ : Measure ℝ) t‖ ^ 2 ≤ ‖charFun (μ : Measure ℝ) t‖ := by
    nlinarith [sq_nonneg (1 - ‖charFun (μ : Measure ℝ) t‖), norm_nonneg (charFun (μ : Measure ℝ) t),
      hnorm_le_one]
  have hdyadicLower :
      (1 / 2 : ℝ) * Real.exp (-B) ≤ ‖charFun (μ : Measure ℝ) t‖ := by
    calc
      (1 / 2 : ℝ) * Real.exp (-B) = Real.exp (-B) / 2 := by
        ring
      _ ≤ ‖charFun (μ : Measure ℝ) t‖ ^ 2 := hlimit_lower_sq
      _ ≤ ‖charFun (μ : Measure ℝ) t‖ := hnormSq_le
  have hkBound : (4 ^ k : ℝ) ≤ 4 * t ^ 2 / ε ^ 2 := by
    by_cases hkzero : k = 0
    · have hsq : 1 ≤ t ^ 2 / ε ^ 2 := by
        have hsquare' : ε ^ 2 ≤ |t| ^ 2 := by
          nlinarith [hεle]
        have hsquare : ε ^ 2 ≤ t ^ 2 := by
          simpa [sq_abs] using hsquare'
        rw [one_le_div₀ (sq_pos_of_pos hεpos)]
        simpa [sq_abs] using hsquare
      rw [hkzero]
      have hmult : t ^ 2 / ε ^ 2 ≤ 4 * t ^ 2 / ε ^ 2 := by
        have hratio_nonneg : 0 ≤ t ^ 2 / ε ^ 2 := by positivity
        calc
          t ^ 2 / ε ^ 2 = 1 * (t ^ 2 / ε ^ 2) := by ring
          _ ≤ 4 * (t ^ 2 / ε ^ 2) := by
                gcongr
                norm_num
          _ = 4 * t ^ 2 / ε ^ 2 := by ring
      exact le_trans hsq hmult
    · have hkpos : 0 < k := Nat.pos_iff_ne_zero.mpr hkzero
      have hprev_not : ¬ |t| ≤ (2 ^ (k - 1) : ℝ) * ε := by
        intro hprev
        have hmin : k ≤ k - 1 := Nat.find_min' hexists hprev
        exact (not_le_of_gt (Nat.sub_lt hkpos (by decide))) hmin
      have hprev_lt : (2 ^ (k - 1) : ℝ) * ε < |t| := by
        exact lt_of_not_ge hprev_not
      have hdiv_lt : (2 ^ (k - 1) : ℝ) < |t| / ε := by
        rw [lt_div_iff₀ hεpos]
        simpa [mul_comm] using hprev_lt
      have hsq_lt : ((2 ^ (k - 1) : ℝ) ^ 2) < (|t| / ε) ^ 2 := by
        gcongr
      have hpow_two : ((2 ^ (k - 1) : ℝ) ^ 2) = (4 ^ (k - 1) : ℝ) := by
        calc
          ((2 ^ (k - 1) : ℝ) ^ 2) = (2 : ℝ) ^ ((k - 1) * 2) := by
            rw [pow_mul]
          _ = (2 : ℝ) ^ (2 * (k - 1)) := by
            rw [Nat.mul_comm]
          _ = ((2 : ℝ) ^ 2) ^ (k - 1) := by
            rw [pow_mul]
          _ = (4 ^ (k - 1) : ℝ) := by
            norm_num
      have hdiv_sq : (|t| / ε) ^ 2 = t ^ 2 / ε ^ 2 := by
        calc
          (|t| / ε) ^ 2 = |t| ^ 2 / ε ^ 2 := by ring
          _ = t ^ 2 / ε ^ 2 := by rw [sq_abs]
      have hpow_lt : (4 ^ (k - 1) : ℝ) < t ^ 2 / ε ^ 2 := by
        simpa [hpow_two, hdiv_sq] using hsq_lt
      have hk_pow : (4 ^ k : ℝ) = (4 ^ (k - 1) : ℝ) * 4 := by
        have hk_nat : (k - 1) + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
        calc
          (4 ^ k : ℝ) = (4 : ℝ) ^ ((k - 1) + 1) := by
            rw [hk_nat]
          _ = (4 ^ (k - 1) : ℝ) * 4 := by
            rw [pow_add, pow_one]
      calc
        (4 ^ k : ℝ) = (4 ^ (k - 1) : ℝ) * 4 := hk_pow
        _ ≤ (t ^ 2 / ε ^ 2) * 4 := by
              exact le_of_lt (by gcongr)
        _ = 4 * t ^ 2 / ε ^ 2 := by ring
  have hgammaBound : ((4 ^ k : ℝ) * C) ≤ (4 * C / ε ^ 2) * t ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hkBound hCpos.le
    calc
      (4 ^ k : ℝ) * C ≤ (4 * t ^ 2 / ε ^ 2) * C := hmul
      _ = (4 * C / ε ^ 2) * t ^ 2 := by
            ring
  have hexpBound :
      (1 / 2 : ℝ) * Real.exp (-(4 * C / ε ^ 2 * t ^ 2)) ≤
        (1 / 2 : ℝ) * Real.exp (-B) := by
    have hexp_le :
        Real.exp (-(4 * C / ε ^ 2 * t ^ 2)) ≤ Real.exp (-B) := by
      apply Real.exp_le_exp.mpr
      linarith [hgammaBound]
    nlinarith
  have hexpBound' :
      (1 / 2 : ℝ) * Real.exp (-((4 * C / ε ^ 2) * t ^ 2)) ≤
        (1 / 2 : ℝ) * Real.exp (-B) := by
    simpa [mul_assoc] using hexpBound
  -- Proof comment: the minimal dyadic scale controls the exponent by a quadratic function of `t`.
  have hbound := le_trans hexpBound' hdyadicLower
  convert hbound using 1
  ring_nf

/-- An infinitely divisible probability law on `ℝ` has a characteristic function with a Gaussian
lower bound. -/
theorem charFun_gaussian_lower_bound_of_isInfinitelyDivisible
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    ∃ γ > 0, ∀ t : ℝ, (1 / 2 : ℝ) * Real.exp (-γ * t ^ 2) ≤ ‖charFun (μ : Measure ℝ) t‖ := by
  classical
  let rootLawPNat : ℕ+ → ProbabilityMeasure ℝ := fun n ↦ Classical.choose (hμ.exists_root n)
  have hrootLawPowPNat : ∀ n : ℕ+, rootLawPNat n ^ (n : ℕ) = μ := by
    intro n
    exact Classical.choose_spec (hμ.exists_root n)
  let rootLaw : ℕ → ProbabilityMeasure ℝ := fun n ↦ rootLawPNat (Nat.toPNat' n)
  have hpowρ : ∀ᶠ n : ℕ in atTop, rootLaw n ^ n = μ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    -- Proof comment: after reindexing the positive roots along `Nat.toPNat'`, the exact
    -- convolution-root identity holds for every sufficiently large natural number.
    simpa [rootLaw, PNat.toPNat'_coe hn] using hrootLawPowPNat (Nat.toPNat' n)
  rcases exactRootLocalModulusDefectBound (μ := μ) (ρs := rootLaw) hpowρ with
    ⟨ε₀, hε₀pos, C, hCpos, hlocal₀⟩
  have hnear :
      {s : ℝ | charFun (μ : Measure ℝ) s ∈ Metric.ball (1 : ℂ) (1 / 2)} ∈ 𝓝 (0 : ℝ) := by
    -- Proof comment: continuity of `charFun μ` at the origin gives a neighborhood where the
    -- characteristic function stays within distance `1/2` of `1`.
    have hEvent :
        {s : ℝ |
            charFun (μ : Measure ℝ) s ∈
              Metric.ball (charFun (μ : Measure ℝ) 0) (1 / 2)} ∈ 𝓝 (0 : ℝ) := by
      exact
        (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt.tendsto.eventually
          (Metric.ball_mem_nhds _ (show 0 < (1 / 2 : ℝ) by norm_num))
    simpa [MeasureTheory.charFun_zero (μ := (μ : Measure ℝ))] using hEvent
  rcases Metric.mem_nhds_iff.mp hnear with ⟨δ, hδpos, hδsubset⟩
  let ε : ℝ := min ε₀ (δ / 2)
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hεδ : ε < δ := by
    have hδhalf : δ / 2 < δ := by
      linarith
    exact lt_of_le_of_lt (min_le_right _ _) hδhalf
  have hlocal :
      ∀ᶠ n : ℕ in atTop,
        ∀ s ∈ Set.Icc (-ε) ε, (n : ℝ) * (1 - ‖charFun (rootLaw n : Measure ℝ) s‖ ^ 2) ≤ C := by
    filter_upwards [hlocal₀] with n hn s hs
    have hε_le_ε₀ : ε ≤ ε₀ := min_le_left _ _
    apply hn s
    constructor
    · nlinarith [hs.1, hε_le_ε₀]
    · nlinarith [hs.2, hε_le_ε₀]
  rcases charFunLargeFrequencyGaussianLowerBoundOfLocalDefect
      (μ := μ) (ρs := rootLaw) (ε := ε) (C := C) hpowρ hεpos hCpos hlocal with
    ⟨γ, hγpos, hlarge⟩
  have hsmall :
      ∀ t : ℝ, |t| < ε → (1 / 2 : ℝ) < ‖charFun (μ : Measure ℝ) t‖ := by
    intro t ht
    have htball : t ∈ Metric.ball (0 : ℝ) δ := by
      change dist t 0 < δ
      simpa [Real.dist_eq] using lt_of_lt_of_le ht hεδ.le
    have hclose : ‖charFun (μ : Measure ℝ) t - 1‖ < (1 / 2 : ℝ) := by
      have htballφ : charFun (μ : Measure ℝ) t ∈ Metric.ball (1 : ℂ) (1 / 2) := hδsubset htball
      simpa [Metric.mem_ball, dist_eq_norm] using htballφ
    have hone_le : (1 : ℝ) ≤ ‖1 - charFun (μ : Measure ℝ) t‖ + ‖charFun (μ : Measure ℝ) t‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_add_le (1 - charFun (μ : Measure ℝ) t) (charFun (μ : Measure ℝ) t))
    have hclose' : ‖1 - charFun (μ : Measure ℝ) t‖ < (1 / 2 : ℝ) := by
      simpa [norm_sub_rev] using hclose
    nlinarith
  refine ⟨γ, hγpos, ?_⟩
  intro t
  by_cases hεle : ε ≤ |t|
  · exact hlarge t hεle
  · have habs_lt : |t| < ε := lt_of_not_ge hεle
    have hsmall_t : (1 / 2 : ℝ) < ‖charFun (μ : Measure ℝ) t‖ := hsmall t habs_lt
    have hleft_le :
        (1 / 2 : ℝ) * Real.exp (-γ * t ^ 2) ≤ 1 / 2 := by
      have hexp_le_one : Real.exp (-γ * t ^ 2) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [sq_nonneg t, hγpos]
      nlinarith
    -- Proof comment: once `t` stays in the small continuity neighborhood, the norm is already
    -- strictly above `1/2`, so the Gaussian lower bound is automatic.
    exact le_trans hleft_le (le_of_lt hsmall_t)

end MeasureTheory.ProbabilityMeasure

/-- Helper for Corollary 16.11: every infinitely divisible characteristic function on `ℝ` comes
from an infinitely divisible probability law on `ℝ`. -/
private theorem existsInfinitelyDivisibleMeasureOfIsInfinitelyDivisibleCFP
    {φ : ℝ → ℂ} (hφ : IsInfinitelyDivisibleCFP φ) :
    ∃ μ : ProbabilityMeasure ℝ,
      charFun (μ : Measure ℝ) = φ ∧ MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ := by
  rcases hφ (1 : ℕ+) with ⟨φ1, hφ1cfp, hroot1⟩
  rcases hφ1cfp with ⟨μ, hμchar1⟩
  have hchar : charFun (μ : Measure ℝ) = φ := by
    funext t
    calc
      charFun (μ : Measure ℝ) t = φ1 t := by
        rw [hμchar1]
      _ = φ1 t ^ (1 : ℕ) := by
        simp
      _ = φ t := by
        simpa using (congrArg (fun f : ℝ → ℂ ↦ f t) hroot1).symm
  refine ⟨μ, hchar, ?_⟩
  refine ⟨?_⟩
  intro n
  rcases hφ n with ⟨φn, hφncfp, hrootn⟩
  rcases hφncfp with ⟨ν, hνchar⟩
  refine ⟨ν, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  -- Proof comment: the `n`th CFP root of `φ` is the characteristic function of some `ν`, so
  -- `charFun_pow` identifies `ν ^ n` with `μ` after rewriting both sides to `φ`.
  calc
    charFun ((ν ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun (ν : Measure ℝ) t ^ (n : ℕ) := by
            simpa using
              congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow ν (n : ℕ))
    _ = φn t ^ (n : ℕ) := by
          rw [hνchar]
    _ = φ t := by
          simpa using (congrArg (fun f : ℝ → ℂ ↦ f t) hrootn).symm
    _ = charFun (μ : Measure ℝ) t := by
          rw [hchar]

/-- Corollary 16.11: every infinitely divisible characteristic function on `ℝ` admits a Gaussian
lower bound; there is `γ > 0` such that `|φ(t)| ≥ (1 / 2) e^{-γ t^2}` for all real `t`. -/
-- Proof sketch: realize `φ` as the characteristic function of an infinitely divisible
-- probability law, then apply the owner-side Gaussian lower bound already proved for that law.
theorem infinitelyDivisibleCFP_gaussian_lower_bound
    {φ : ℝ → ℂ} (hφ : IsInfinitelyDivisibleCFP φ) :
    ∃ γ > 0, ∀ t : ℝ, (1 / 2 : ℝ) * Real.exp (-γ * t ^ 2) ≤ ‖φ t‖ := by
  rcases existsInfinitelyDivisibleMeasureOfIsInfinitelyDivisibleCFP hφ with ⟨μ, hμchar, hμinf⟩
  rcases
      MeasureTheory.ProbabilityMeasure.charFun_gaussian_lower_bound_of_isInfinitelyDivisible hμinf
      with ⟨γ, hγpos, hbound⟩
  refine ⟨γ, hγpos, ?_⟩
  intro t
  -- Proof comment: rewrite the source-facing characteristic function to the owner law.
  simpa [hμchar] using hbound t

/-- Helper for Corollary 16.11: if the stretched exponential is a CFP, then scaling its witness
produces all positive integer roots, so it is infinitely divisible in the CFP sense. -/
private theorem stretchedExponentialIsInfinitelyDivisibleCFPOfIsCFP
    {α : ℝ} (hα : 0 < α) :
    IsCFP (fun t : ℝ ↦ Complex.exp (-(|t| ^ α : ℝ))) →
      IsInfinitelyDivisibleCFP (fun t : ℝ ↦ Complex.exp (-(|t| ^ α : ℝ))) := by
  intro hcfp
  rcases hcfp with ⟨μ, hμchar⟩
  intro n
  let c : ℝ := (n : ℝ) ^ (-1 / α)
  let ν : ProbabilityMeasure ℝ :=
    μ.map
      ((measurable_const.mul measurable_id).aemeasurable :
        AEMeasurable (fun x : ℝ ↦ c * x) (μ : Measure ℝ))
  refine ⟨fun t : ℝ ↦ Complex.exp (-(|t| ^ α / (n : ℝ) : ℝ)), ?_, ?_⟩
  · refine ⟨ν, ?_⟩
    funext t
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast n.pos
    have hc_pos : 0 < c := by
      dsimp [c]
      exact Real.rpow_pos_of_pos hn_pos _
    have hscale :
        |c * t| ^ α = |t| ^ α / (n : ℝ) := by
      calc
        |c * t| ^ α = (c * |t|) ^ α := by
          rw [abs_mul, abs_of_nonneg hc_pos.le]
        _ = c ^ α * |t| ^ α := by
          rw [Real.mul_rpow hc_pos.le (abs_nonneg t)]
        _ = ((n : ℝ) ^ (-1 / α)) ^ α * |t| ^ α := by
          rfl
        _ = (n : ℝ) ^ (-1 : ℝ) * |t| ^ α := by
          have hmul : (-1 / α) * α = (-1 : ℝ) := by
            field_simp [hα.ne']
          rw [← Real.rpow_mul hn_pos.le, hmul]
        _ = (n : ℝ)⁻¹ * |t| ^ α := by
          rw [Real.rpow_neg_one]
        _ = |t| ^ α / (n : ℝ) := by
          ring
    -- Proof comment: scaling the underlying law by `c = n^(-1 / α)` divides the exponent by `n`.
    calc
      charFun (ν : Measure ℝ) t = charFun (μ : Measure ℝ) (c * t) := by
        simpa [ν, c] using (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) c t)
      _ = Complex.exp (-(|c * t| ^ α : ℝ)) := by
            rw [hμchar]
      _ = Complex.exp (-(|t| ^ α / (n : ℝ) : ℝ)) := by
            rw [hscale]
  · funext t
    symm
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast n.ne_zero
    have hmulReal : (n : ℝ) * (-(|t| ^ α / (n : ℝ) : ℝ)) = -( |t| ^ α : ℝ) := by
      field_simp [hn0]
    -- Proof comment: the explicit root exponent multiplies back to the original stretched
    -- exponent after taking the `n`th power.
    calc
      Complex.exp (-(|t| ^ α / (n : ℝ) : ℝ)) ^ (n : ℕ)
          = Complex.exp ((n : ℂ) * (-(|t| ^ α / (n : ℝ) : ℝ))) := by
              rw [← Complex.exp_nat_mul]
      _ = Complex.exp (-(|t| ^ α : ℝ)) := by
            congr 1
            exact_mod_cast hmulReal

/-- Helper for Corollary 16.11: for `α > 2`, the stretched exponential eventually lies below any
Gaussian lower bound. -/
private theorem existsStretchedExponentialBelowGaussian
    {α γ : ℝ} (hα : 2 < α) (hγ : 0 < γ) :
    ∃ t > 0, Real.exp (-(t ^ α : ℝ)) < (1 / 2 : ℝ) * Real.exp (-γ * t ^ 2) := by
  have hα' : 0 < α - 2 := by
    linarith
  have hγnonneg : 0 ≤ γ := hγ.le
  have hlarge :
      ∀ᶠ t : ℝ in atTop, γ + Real.log 2 < t ^ (α - 2) := by
    exact (_root_.tendsto_rpow_atTop hα').eventually_gt_atTop (γ + Real.log 2)
  have hgtOne : ∀ᶠ t : ℝ in atTop, 1 < t := eventually_gt_atTop 1
  rcases (hgtOne.and hlarge).exists with ⟨t, htgtOne, hdom⟩
  have htpos : 0 < t := lt_trans zero_lt_one htgtOne
  have hlog_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have htSqGe : 1 ≤ t ^ 2 := by
    nlinarith
  have hsplit : t ^ α = t ^ (α - 2) * t ^ 2 := by
    calc
      t ^ α = t ^ ((α - 2) + 2) := by
        congr 1
        linarith
      _ = t ^ (α - 2) * t ^ 2 := by
            simpa using (Real.rpow_add htpos (α - 2) (2 : ℝ))
  have hlin :
      γ * t ^ 2 + Real.log 2 < t ^ α := by
    have hmul : (γ + Real.log 2) * t ^ 2 < t ^ α := by
      have htmp := mul_lt_mul_of_pos_right hdom (show 0 < t ^ 2 by positivity)
      calc
        (γ + Real.log 2) * t ^ 2 < t ^ (α - 2) * t ^ 2 := htmp
        _ = t ^ α := hsplit.symm
    have hleft :
        γ * t ^ 2 + Real.log 2 ≤ (γ + Real.log 2) * t ^ 2 := by
      nlinarith [hγnonneg, hlog_nonneg, htSqGe]
    exact lt_of_le_of_lt hleft hmul
  have hhalfExp : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  refine ⟨t, htpos, ?_⟩
  -- Proof comment: once `t^(α-2)` dominates `γ + log 2`, exponentiating the rearranged
  -- inequality gives the desired strict comparison.
  calc
    Real.exp (-(t ^ α : ℝ)) < Real.exp (-(γ * t ^ 2 + Real.log 2)) := by
      apply Real.exp_lt_exp.mpr
      linarith
    _ = Real.exp (-γ * t ^ 2) * Real.exp (-Real.log 2) := by
          have hsplitExp : -(γ * t ^ 2 + Real.log 2) = -γ * t ^ 2 + -Real.log 2 := by
            ring_nf
          rw [hsplitExp, Real.exp_add]
    _ = (1 / 2 : ℝ) * Real.exp (-γ * t ^ 2) := by
          rw [hhalfExp]
          ring_nf

/-- For `α > 2`, the stretched exponential `t ↦ exp (-|t|^α)` is not a characteristic function
on `ℝ`. -/
-- Proof sketch: if the stretched exponential were a CFP, the scaling identity
-- `exp (-|t|^α) = (exp (-|t|^α / n))^n` would make it infinitely divisible. The Gaussian lower
-- bound from Corollary 16.11 would then contradict the strictly faster decay when `α > 2`.
theorem stretchedExponential_not_isCFP_of_two_lt
    {α : ℝ} (hα : 2 < α) :
    ¬ IsCFP (fun t : ℝ ↦ Complex.exp (-(|t| ^ α : ℝ))) := by
  intro hcfp
  have hInfDiv :
      IsInfinitelyDivisibleCFP (fun t : ℝ ↦ Complex.exp (-(|t| ^ α : ℝ))) :=
    stretchedExponentialIsInfinitelyDivisibleCFPOfIsCFP (show 0 < α by linarith) hcfp
  rcases infinitelyDivisibleCFP_gaussian_lower_bound hInfDiv with ⟨γ, hγpos, hbound⟩
  rcases existsStretchedExponentialBelowGaussian hα hγpos with ⟨t, htpos, hlt⟩
  have hgauss := hbound t
  have hnorm_exp : ‖Complex.exp (-(t ^ α : ℝ))‖ = Real.exp (-(t ^ α : ℝ)) := by
    simpa using Complex.norm_exp_ofReal (-(t ^ α : ℝ))
  -- Proof comment: at the chosen large positive frequency, the Gaussian lower bound is strictly
  -- larger than the stretched exponential, contradicting the norm identity for `Complex.exp`.
  exact (not_le_of_gt hlt) (by
    simpa [abs_of_pos htpos, hnorm_exp] using hgauss)
