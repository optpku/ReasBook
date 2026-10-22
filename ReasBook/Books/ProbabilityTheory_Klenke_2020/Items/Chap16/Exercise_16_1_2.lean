/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

local notation "E1" => EuclideanSpace ℝ (Fin 1)

variable {φ : ℝ → ℂ} {φs : ℕ+ → ℝ → ℂ}

/-- Helper for Exercise 16.1.2: the canonical embedding of `ℝ` into `EuclideanSpace ℝ (Fin 1)`. -/
noncomputable def realToEuclidean1 : ℝ → E1 := fun t ↦ EuclideanSpace.single 0 t

/-- Helper for Exercise 16.1.2: read the unique coordinate of `EuclideanSpace ℝ (Fin 1)`. -/
def euclidean1ToReal : E1 → ℝ := fun x ↦ x 0

/-- Helper for Exercise 16.1.2: the canonical embedding `ℝ → ℝ¹` is continuous. -/
lemma continuous_realToEuclidean1 : Continuous realToEuclidean1 := by
  -- Proof comment: `EuclideanSpace.single` is the standard continuous one-coordinate insertion.
  have hsingle : Continuous fun t : ℝ ↦ (Pi.single (0 : Fin 1) t : Fin 1 → ℝ) := by
    refine continuous_pi ?_
    intro i
    fin_cases i
    simpa using continuous_id
  simpa [realToEuclidean1, EuclideanSpace.single] using
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 1 => ℝ)).comp hsingle

/-- Helper for Exercise 16.1.2: the canonical embedding `ℝ → ℝ¹` preserves distances. -/
lemma dist_realToEuclidean1 (x y : ℝ) :
    dist (realToEuclidean1 x) (realToEuclidean1 y) = dist x y := by
  simpa [realToEuclidean1] using EuclideanSpace.dist_single_same (i := (0 : Fin 1)) x y

/-- Helper for Exercise 16.1.2: the canonical embedding `ℝ → ℝ¹` is a.e.-measurable for every
measure. -/
lemma aemeasurable_realToEuclidean1 (μ : Measure ℝ) : AEMeasurable realToEuclidean1 μ :=
  continuous_realToEuclidean1.measurable.aemeasurable

/-- Helper for Exercise 16.1.2: push a real probability law to `EuclideanSpace ℝ (Fin 1)` along
the canonical embedding. -/
noncomputable def pushRealToEuclidean1 (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure E1 :=
  μ.map (aemeasurable_realToEuclidean1 (μ : Measure ℝ))

/-- Helper for Exercise 16.1.2: transporting a real probability law along `realToEuclidean1`
preserves the characteristic function after reading the unique coordinate. -/
lemma charFun_map_realToEuclidean1 (μ : ProbabilityMeasure ℝ) (x : E1) :
    charFun (pushRealToEuclidean1 μ : Measure E1) x =
      charFun (μ : Measure ℝ) (euclidean1ToReal x) := by
  -- Proof comment: rewrite the pushforward characteristic function by `integral_map`, then reduce
  -- the one-dimensional inner product to multiplication by the unique coordinate.
  change charFun (Measure.map realToEuclidean1 (μ : Measure ℝ)) x =
    charFun (μ : Measure ℝ) (euclidean1ToReal x)
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply_real,
    MeasureTheory.integral_map (aemeasurable_realToEuclidean1 (μ : Measure ℝ)) (by fun_prop)]
  congr with t
  congr 1
  have hinner : inner ℝ (EuclideanSpace.single (0 : Fin 1) t) x = euclidean1ToReal x * t := by
    simpa [euclidean1ToReal, mul_comm] using
      (EuclideanSpace.inner_single_left (i := (0 : Fin 1)) t x)
  exact congrArg (fun z : ℂ ↦ z * Complex.I) (by exact_mod_cast hinner)

/-- Helper for Exercise 16.1.2: weak convergence of probability laws on `ℝ` upgrades to compact
uniform convergence of the characteristic functions. -/
lemma charFun_tendstoUniformlyOn_of_tendstoReal
    {P : ProbabilityMeasure ℝ} {Ps : ℕ → ProbabilityMeasure ℝ}
    (hP : Tendsto Ps atTop (𝓝 P)) :
    ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n t ↦ charFun (Ps n) t) (charFun P) atTop K := by
  let F : ℕ → ℝ → ℂ := fun n t ↦ charFun (Ps n : Measure ℝ) t
  have h_pointwise : ∀ t : ℝ, Tendsto (fun n ↦ F n t) atTop (𝓝 (charFun P t)) := by
    exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hP
  let Qs : ℕ → ProbabilityMeasure E1 := fun n ↦ pushRealToEuclidean1 (Ps n)
  have h_measures :
      (((↑) : ProbabilityMeasure E1 → Measure E1) '' Set.range Qs) =
        Set.range (fun n ↦ ((Qs n : ProbabilityMeasure E1) : Measure E1)) := by
    ext μ
    constructor
    · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Qs n, ⟨n, rfl⟩, rfl⟩
  have h_pointwise_push :
      ∀ x : E1,
        Tendsto (fun n ↦ charFun ((Qs n : ProbabilityMeasure E1) : Measure E1) x) atTop
          (𝓝 (charFun (pushRealToEuclidean1 P : Measure E1) x)) := by
    intro x
    -- Proof comment: the transported characteristic functions are exactly the original ones read
    -- through the unique coordinate.
    simpa [Qs, charFun_map_realToEuclidean1] using h_pointwise (euclidean1ToReal x)
  have h_tight_range :
      IsTightMeasureSet (Set.range fun n ↦ ((Qs n : ProbabilityMeasure E1) : Measure E1)) := by
    exact isTightMeasureSet_of_tendsto_charFun (by fun_prop) h_pointwise_push
  have h_tight :
      IsTightMeasureSet (((↑) : ProbabilityMeasure E1 → Measure E1) '' Set.range Qs) := by
    rw [h_measures]
    exact h_tight_range
  have h_eqcont_push_set :
      (charFun '' (((↑) : ProbabilityMeasure E1 → Measure E1) '' Set.range Qs)).UniformEquicontinuous := by
    exact tight_probabilityMeasureFamily_charFunSet_uniformEquicontinuous (Set.range Qs) h_tight
  have h_charFuns_push :
      charFun '' (((↑) : ProbabilityMeasure E1 → Measure E1) '' Set.range Qs) =
        Set.range (fun n x ↦ charFun (Qs n : Measure E1) x) := by
    ext φ
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      rcases hμ with ⟨ν, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(Qs n : Measure E1), ⟨Qs n, ⟨n, rfl⟩, rfl⟩, rfl⟩
  have h_eqcont_push : UniformEquicontinuous (fun n x ↦ charFun (Qs n : Measure E1) x) := by
    refine uniformEquicontinuous_iff_range.2 ?_
    simpa [h_charFuns_push] using h_eqcont_push_set
  have h_eqcont : UniformEquicontinuous F := by
    rw [Metric.uniformEquicontinuous_iff] at h_eqcont_push ⊢
    intro ε hε
    rcases h_eqcont_push ε hε with ⟨δ, hδpos, hδ⟩
    refine ⟨δ, hδpos, ?_⟩
    intro x y hxy n
    have hxyE : dist (realToEuclidean1 x) (realToEuclidean1 y) < δ := by
      simpa [dist_realToEuclidean1] using hxy
    simpa [F, Qs, charFun_map_realToEuclidean1] using
      hδ (realToEuclidean1 x) (realToEuclidean1 y) hxyE n
  intro K hK
  let FK : ℕ → K → ℝ := fun n x ↦ dist (F n x.1) (charFun (P : Measure ℝ) x.1)
  have hFK_pointwise : ∀ x : K, Tendsto (fun n ↦ FK n x) atTop (𝓝 0) := by
    intro x
    -- Proof comment: pointwise convergence of the characteristic functions is exactly convergence
    -- of the pointwise distance to the limit `0`.
    have hdist :
        Tendsto
          (fun n ↦ dist (F n x.1) (charFun (P : Measure ℝ) x.1))
          atTop
          (𝓝 (dist (charFun (P : Measure ℝ) x.1) (charFun (P : Measure ℝ) x.1))) := by
      exact (h_pointwise x.1).dist tendsto_const_nhds
    simpa [FK, F] using hdist
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcharFunP_cont : Continuous fun x : K ↦ charFun (P : Measure ℝ) x.1 := by
    simpa using
      (MeasureTheory.continuous_charFun (μ := (P : Measure ℝ))).comp continuous_subtype_val
  have hcharFunP_uc : UniformContinuous fun x : K ↦ charFun (P : Measure ℝ) x.1 :=
    CompactSpace.uniformContinuous_of_continuous hcharFunP_cont
  have hFK_eqcont : UniformEquicontinuous FK := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    rcases (Metric.uniformEquicontinuous_iff.mp h_eqcont) (ε / 2) (by positivity) with
      ⟨δ₁, hδ₁pos, hδ₁⟩
    rcases (Metric.uniformContinuous_iff.mp hcharFunP_uc) (ε / 2) (by positivity) with
      ⟨δ₂, hδ₂pos, hδ₂⟩
    refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
    intro x y hxy n
    have hFxy : dist (F n x.1) (F n y.1) < ε / 2 :=
      hδ₁ x.1 y.1 (lt_of_lt_of_le hxy (min_le_left _ _)) n
    have hPxy : dist (charFun (P : Measure ℝ) x.1) (charFun (P : Measure ℝ) y.1) < ε / 2 :=
      hδ₂ (lt_of_lt_of_le hxy (min_le_right _ _))
    calc
      dist (FK n x) (FK n y)
          ≤ dist (F n x.1) (F n y.1) +
              dist (charFun (P : Measure ℝ) x.1) (charFun (P : Measure ℝ) y.1) := by
                simpa [FK] using
                  dist_dist_dist_le (F n x.1) (charFun (P : Measure ℝ) x.1)
                    (F n y.1) (charFun (P : Measure ℝ) y.1)
      _ < ε := by nlinarith
  have hFK_uniform :
      TendstoUniformlyOn (fun n x ↦ FK n x) (fun _ : K ↦ (0 : ℝ)) atTop (Set.univ : Set K) :=
    tendstoUniformlyOn_of_pointwise_of_uniformEquicontinuous hFK_pointwise hFK_eqcont isCompact_univ
  rw [Metric.tendstoUniformlyOn_iff] at hFK_uniform ⊢
  intro ε hε
  filter_upwards [hFK_uniform ε hε] with n hn x hx
  simpa [FK, F, dist_comm] using hn ⟨x, hx⟩ (by simp)

/-- Helper for Exercise 16.1.2: if the linearized sequence `n * (z n - 1)` converges in `ℂ`,
then the original sequence converges to `1`. -/
lemma tendstoOne_of_tendstoNatMulSubOne {z : ℕ → ℂ} {w : ℂ}
    (hz : Tendsto (fun n : ℕ ↦ (n : ℂ) * (z n - 1)) atTop (𝓝 w)) :
    Tendsto z atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℂ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hsubMul :
      Tendsto (fun n : ℕ ↦ ((n : ℂ) * (z n - 1)) * ((n : ℂ)⁻¹)) atTop (𝓝 0) := by
    -- Proof comment: multiply the convergent linearized sequence by `1 / n`, which tends to `0`.
    simpa using hz.mul hinv
  have hsubEventually :
      (fun n : ℕ ↦ ((n : ℂ) * (z n - 1)) * ((n : ℂ)⁻¹)) =ᶠ[atTop] fun n ↦ z n - 1 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    -- Proof comment: away from `n = 0`, the extra factor `n * n⁻¹` collapses to `1`.
    calc
      ((n : ℂ) * (z n - 1)) * ((n : ℂ)⁻¹)
          = ((n : ℂ) * ((n : ℂ)⁻¹)) * (z n - 1) := by ac_rfl
      _ = z n - 1 := by rw [mul_inv_cancel₀ hn0, one_mul]
  have hsub : Tendsto (fun n : ℕ ↦ z n - 1) atTop (𝓝 0) :=
    hsubMul.congr' hsubEventually
  -- Proof comment: add back the constant `1` to recover convergence of `z n`.
  simpa using hsub.const_add (1 : ℂ)

/-- Helper for Exercise 16.1.2: every characteristic function on `ℝ` is continuous at the
origin. -/
lemma continuousAt_zero_of_isCFP {χ : ℝ → ℂ} (hχ : IsCFP χ) :
    ContinuousAt χ 0 := by
  rcases hχ with ⟨μ, rfl⟩
  -- Proof comment: once `χ` is identified with a characteristic function, continuity at `0`
  -- is the standard characteristic-function continuity theorem.
  simpa using (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt

/-- Helper for Exercise 16.1.2: every characteristic function on `ℝ` is continuous. -/
lemma continuous_of_isCFP {χ : ℝ → ℂ} (hχ : IsCFP χ) :
    Continuous χ := by
  rcases hχ with ⟨μ, rfl⟩
  -- Proof comment: characteristic functions are globally continuous on `ℝ`.
  simpa using (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ)))

/-- Helper for Exercise 16.1.2: every characteristic function on `ℝ` is normalized by `χ(0)=1`.
-/
lemma zero_eq_one_of_isCFP {χ : ℝ → ℂ} (hχ : IsCFP χ) :
    χ 0 = 1 := by
  rcases hχ with ⟨μ, rfl⟩
  -- Proof comment: characteristic functions evaluate to the total mass at the origin.
  simpa using (MeasureTheory.charFun_zero (μ := (μ : Measure ℝ)))

/-- Helper for Exercise 16.1.2: every characteristic-function value lies in the closed unit disk.
-/
lemma norm_le_one_of_isCFP {χ : ℝ → ℂ} (hχ : IsCFP χ) (t : ℝ) :
    ‖χ t‖ ≤ 1 := by
  rcases hχ with ⟨μ, rfl⟩
  -- Proof comment: characteristic functions of probability laws have norm at most one.
  simpa using (MeasureTheory.norm_charFun_le_one (μ := (μ : Measure ℝ)) t)

/-- Helper for Exercise 16.1.2: an exact positive-integer CFP root family packages `φ` as an
infinitely divisible characteristic function. -/
lemma exactRootFamily_isInfinitelyDivisibleCFP
    (hcfp : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ n : ℕ+, ∀ t : ℝ, (φs n t) ^ (n : ℕ) = φ t) :
    IsInfinitelyDivisibleCFP φ := by
  intro n
  refine ⟨φs n, hcfp n, ?_⟩
  funext t
  exact (hpow n t).symm

/-- Helper for Exercise 16.1.2: the modulus-square characteristic function
`t ↦ χ t * star (χ t)` is again a CFP. -/
lemma isCFP_mul_conj {χ : ℝ → ℂ} (hχ : IsCFP χ) :
    IsCFP (fun t ↦ χ t * star (χ t)) := by
  rcases hχ with ⟨μ, rfl⟩
  let ν : ProbabilityMeasure ℝ :=
    μ.map
      ((measurable_const.mul measurable_id).aemeasurable :
        AEMeasurable (fun x : ℝ ↦ (-1 : ℝ) * x) (μ : Measure ℝ))
  refine ⟨μ * ν, ?_⟩
  funext t
  have hν :
      charFun (ν : Measure ℝ) t = star (charFun (μ : Measure ℝ) t) := by
    -- Proof comment: the reflected law evaluates the characteristic function at `-t`.
    calc
      charFun (ν : Measure ℝ) t = charFun (μ : Measure ℝ) ((-1 : ℝ) * t) := by
        simpa [ν] using (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) (-1) t)
      _ = charFun (μ : Measure ℝ) (-t) := by simp
      _ = star (charFun (μ : Measure ℝ) t) := MeasureTheory.charFun_neg t
  -- Proof comment: convolution with the reflected law turns the product with the complex
  -- conjugate into a characteristic function again.
  calc
    charFun ((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun (μ : Measure ℝ) t * charFun (ν : Measure ℝ) t := by
            simpa using
              (MeasureTheory.charFun_conv (μ := (μ : Measure ℝ)) (ν := (ν : Measure ℝ)) t)
    _ = charFun (μ : Measure ℝ) t * star (charFun (μ : Measure ℝ) t) := by
          rw [hν]

/-- Helper for Exercise 16.1.2: a positive lower bound on `r^n` bounds the logarithmic defect
`n * (1 - r)`. -/
lemma natMulOneSub_le_negLog_of_pow_ge {r c : ℝ} {n : ℕ}
    (hr_nonneg : 0 ≤ r) (_hr_le_one : r ≤ 1) (hc_pos : 0 < c) (hc_le : c ≤ r ^ n) :
    (n : ℝ) * (1 - r) ≤ -Real.log c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hc_le_one : c ≤ 1 := by simpa using hc_le
    have hlog_nonpos : Real.log c ≤ 0 := Real.log_nonpos hc_pos.le hc_le_one
    -- Proof comment: in the zeroth-power case the left side vanishes.
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
    -- Proof comment: compare `log c` with `n * log r`, then use `log r ≤ r - 1`.
    linarith

/-- Helper for Exercise 16.1.2: the Chapter 15 doubled-frequency defect inequality specializes
from `ℝ¹` back to `ℝ`. -/
lemma one_sub_re_isCFP_two_mul_le_four_mul {χ : ℝ → ℂ}
    (hχ : IsCFP χ) (t : ℝ) :
    1 - Complex.re (χ (2 * t)) ≤ 4 * (1 - Complex.re (χ t)) := by
  rcases hχ with ⟨μ, rfl⟩
  let ν : ProbabilityMeasure E1 := pushRealToEuclidean1 μ
  have hraw :
      1 - Complex.re (charFun ((ν : ProbabilityMeasure E1) : Measure E1) ((2 : ℝ) • realToEuclidean1 t))
        ≤ 4 * (1 - Complex.re (charFun ((ν : ProbabilityMeasure E1) : Measure E1) (realToEuclidean1 t))) := by
    -- Proof comment: apply Lemma 15.11(v) to the identity random variable on the transported
    -- one-dimensional Euclidean law.
    simpa using
      (one_sub_re_charFun_two_smul_le_four_mul
        (P := ((ν : ProbabilityMeasure E1) : Measure E1))
        (X := fun x : E1 ↦ x) measurable_id (realToEuclidean1 t))
  have htwo :
      charFun ((ν : ProbabilityMeasure E1) : Measure E1) ((2 : ℝ) • realToEuclidean1 t) =
        charFun (μ : Measure ℝ) (2 * t) := by
    calc
      charFun ((ν : ProbabilityMeasure E1) : Measure E1) ((2 : ℝ) • realToEuclidean1 t)
          = charFun (μ : Measure ℝ) (euclidean1ToReal ((2 : ℝ) • realToEuclidean1 t)) := by
              simpa [ν] using
                charFun_map_realToEuclidean1 (μ := μ) ((2 : ℝ) • realToEuclidean1 t)
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
  -- Proof comment: once both characteristic-function values are rewritten to `ℝ`, the transported
  -- defect inequality is exactly the desired statement.
  rw [htwo, hone] at hraw
  simpa using hraw

/-- Helper for Exercise 16.1.2: a positive bound on `n * (1 - rₙ)` for `ℕ+`-indexed terms keeps
the powers `rₙ^n` uniformly away from `0`. -/
lemma pNat_posLowerBound_of_natMulOneSub_le
    {r : ℕ+ → ℝ} {C : ℝ}
    (hbound : ∀ n : ℕ+, (n : ℝ) * (1 - r n) ≤ C) :
    ∃ c > 0, ∀ᶠ n : ℕ+ in atTop, c ≤ r n ^ (n : ℕ) := by
  have hmodelNat :
      Tendsto (fun n : ℕ ↦ (1 - C / n) ^ n) atTop (𝓝 (Real.exp (-C))) := by
    -- Proof comment: compare with the standard exponential model `(1 - C / n)^n → e^{-C}`.
    simpa [sub_eq_add_neg, neg_div] using Real.tendsto_one_add_div_pow_exp (-C)
  have hmodel :
      Tendsto (fun n : ℕ+ ↦ (1 - C / n) ^ (n : ℕ)) atTop (𝓝 (Real.exp (-C))) := by
    simpa using hmodelNat.comp tendsto_PNat_val_atTop_atTop
  have hmodelEventually :
      ∀ᶠ n : ℕ+ in atTop, Real.exp (-C) / 2 < (1 - C / n) ^ (n : ℕ) := by
    have hhalf_lt : Real.exp (-C) / 2 < Real.exp (-C) := by
      have hexp_pos : 0 < Real.exp (-C) := Real.exp_pos (-C)
      nlinarith
    exact hmodel.eventually (Ioi_mem_nhds hhalf_lt)
  have hlarge :
      ∀ᶠ n : ℕ+ in atTop, C < (n : ℝ) := by
    have hcast : Tendsto (fun n : ℕ+ ↦ (n : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop
    exact hcast.eventually_gt_atTop C
  refine ⟨Real.exp (-C) / 2, by positivity, ?_⟩
  filter_upwards [hmodelEventually, hlarge] with n hmodeln hnlarge
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  have hdefect : 1 - r n ≤ C / n := by
    rw [le_div_iff₀ hnpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbound n
  have hbase_le : 1 - C / n ≤ r n := by
    linarith
  have hbase_nonneg : 0 ≤ 1 - C / n := by
    have hdiv_lt : C / n < 1 := by
      rw [div_lt_iff₀ hnpos]
      linarith
    linarith
  have hpow_le : (1 - C / n) ^ (n : ℕ) ≤ r n ^ (n : ℕ) := by
    exact pow_le_pow_left₀ hbase_nonneg hbase_le (n : ℕ)
  -- Proof comment: the explicit exponential model transfers to `rₙ^n` through monotonicity.
  exact le_trans (le_of_lt hmodeln) hpow_le

/-- Helper for Exercise 16.1.2: on the closed unit disk, the squared distance to `1` is
controlled by the real-part defect. -/
lemma sq_norm_sub_one_le_two_mul_one_sub_re {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖z - 1‖ ^ 2 ≤ 2 * (1 - Complex.re z) := by
  have hzsq : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz, norm_nonneg z]
  -- Proof comment: expand `‖z - 1‖²` through `normSq` and use `‖z‖² ≤ 1`.
  calc
    ‖z - 1‖ ^ 2 = Complex.normSq (z - 1) := by rw [← Complex.normSq_eq_norm_sq]
    _ = Complex.normSq z + 1 - 2 * Complex.re z := by
      rw [Complex.normSq_sub]
      simp
    _ ≤ 1 + 1 - 2 * Complex.re z := by
      nlinarith
    _ = 2 * (1 - Complex.re z) := by ring

/-- Helper for Exercise 16.1.2: on a small symmetric interval around `0`, exact CFP roots of `φ`
satisfy a uniform logarithmic-defect bound. -/
lemma exactRootLocalModulusDefectBound
    (hcfp : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ n : ℕ+, ∀ t : ℝ, (φs n t) ^ (n : ℕ) = φ t) :
    ∃ ε > 0, ∃ C > 0, ∀ n : ℕ+, ∀ s ∈ Set.Icc (-ε) ε,
      (n : ℝ) * (1 - ‖φs n s‖ ^ 2) ≤ C := by
  have hφeq : φ = φs 1 := by
    funext x
    simpa using (hpow 1 x).symm
  have hφ0 : ContinuousAt φ 0 := by
    -- Proof comment: the exact-root target is just the first root, hence continuous at `0`.
    simpa [hφeq] using continuousAt_zero_of_isCFP (hcfp 1)
  have hφzero : φ 0 = 1 := by
    -- Proof comment: evaluating the first exact root at `0` gives the normalization of `φ`.
    simpa [hφeq] using zero_eq_one_of_isCFP (hcfp 1)
  have hnear :
      {s : ℝ | φ s ∈ Metric.ball (φ 0) ((1 / 2 : ℝ))} ∈ 𝓝 (0 : ℝ) :=
    hφ0.tendsto.eventually (Metric.ball_mem_nhds (φ 0) (by norm_num))
  rcases Metric.mem_nhds_iff.mp hnear with ⟨δ, hδpos, hδsubset⟩
  let ε : ℝ := δ / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < δ := by
    dsimp [ε]
    linarith
  have hsmall :
      ∀ s ∈ Set.Icc (-ε) ε, (1 / 2 : ℝ) < ‖φ s‖ := by
    intro s hs
    have hsabs : |s| ≤ ε := by
      exact abs_le.mpr ⟨hs.1, hs.2⟩
    have hsball : s ∈ Metric.ball (0 : ℝ) δ := by
      change dist s 0 < δ
      simpa [Real.dist_eq] using lt_of_le_of_lt hsabs hεlt
    have hclose : ‖φ s - 1‖ < (1 / 2 : ℝ) := by
      have hsballφ : φ s ∈ Metric.ball (φ 0) ((1 / 2 : ℝ)) := hδsubset hsball
      simpa [Metric.mem_ball, dist_eq_norm, hφzero] using hsballφ
    have hone_le : (1 : ℝ) ≤ ‖1 - φ s‖ + ‖φ s‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_add_le (1 - φ s) (φ s))
    have hclose' : ‖1 - φ s‖ < (1 / 2 : ℝ) := by
      simpa [norm_sub_rev] using hclose
    nlinarith
  refine ⟨ε, hεpos, -Real.log (1 / 4 : ℝ), ?_, ?_⟩
  · exact neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  · intro n s hs
    have hφlower : (1 / 2 : ℝ) < ‖φ s‖ := hsmall s hs
    have hnormSq_le_one : ‖φs n s‖ ^ 2 ≤ 1 := by
      have hnorm_le_one : ‖φs n s‖ ≤ 1 := norm_le_one_of_isCFP (hcfp n) s
      have hnorm_nonneg : 0 ≤ ‖φs n s‖ := norm_nonneg _
      nlinarith [sq_nonneg (1 - ‖φs n s‖), hnorm_nonneg, hnorm_le_one]
    have hpowSq_ge : (1 / 4 : ℝ) ≤ (‖φs n s‖ ^ 2) ^ (n : ℕ) := by
      have hsq : (1 / 4 : ℝ) < ‖φ s‖ ^ 2 := by
        nlinarith [hφlower, sq_nonneg ‖φ s‖]
      calc
        (1 / 4 : ℝ) ≤ ‖φ s‖ ^ 2 := le_of_lt hsq
        _ = ‖φs n s ^ (n : ℕ)‖ ^ 2 := by rw [hpow n s]
        _ = (‖φs n s‖ ^ 2) ^ (n : ℕ) := by
            calc
              ‖φs n s ^ (n : ℕ)‖ ^ 2 = (‖φs n s‖ ^ (n : ℕ)) ^ 2 := by rw [norm_pow]
              _ = ‖φs n s‖ ^ ((n : ℕ) * 2) := by rw [pow_mul]
              _ = ‖φs n s‖ ^ (2 * (n : ℕ)) := by rw [Nat.mul_comm]
              _ = (‖φs n s‖ ^ 2) ^ (n : ℕ) := by rw [pow_mul]
    -- Proof comment: the exact identity `φₙ(s)^n = φ(s)` gives a pointwise lower bound on the
    -- powered roots, and the logarithmic-defect estimate converts it into a first-order bound.
    exact natMulOneSub_le_negLog_of_pow_ge
      (by positivity) hnormSq_le_one (by norm_num) hpowSq_ge

/-- Helper for Exercise 16.1.2: the exact-root target `φ` never vanishes. -/
lemma exactRootTargetNonvanishing
    (hcfp : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ n : ℕ+, ∀ t : ℝ, (φs n t) ^ (n : ℕ) = φ t) :
    ∀ t : ℝ, φ t ≠ 0 := by
  rcases exactRootLocalModulusDefectBound (φ := φ) (φs := φs) hcfp hpow with
    ⟨ε, hεpos, C, hCpos, hlocal⟩
  have hdyadic :
      ∀ k : ℕ, ∀ n : ℕ+, ∀ s ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε),
        (n : ℝ) * (1 - ‖φs n s‖ ^ 2) ≤ (4 ^ k : ℝ) * C := by
    intro k
    induction k with
    | zero =>
        intro n s hs
        simpa using hlocal n s (by simpa using hs)
    | succ k ih =>
        intro n s hs
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
            1 - ‖φs n s‖ ^ 2 ≤ 4 * (1 - ‖φs n u‖ ^ 2) := by
          have hχ :=
            one_sub_re_isCFP_two_mul_le_four_mul (hχ := isCFP_mul_conj (hcfp n)) u
          have hre_mul_conj (x : ℝ) :
              Complex.re (φs n x * star (φs n x)) = ‖φs n x‖ ^ 2 := by
            have hnormSq :
                φs n x * star (φs n x) = (Complex.normSq (φs n x) : ℂ) := by
              rw [mul_comm]
              simpa using (Complex.normSq_eq_conj_mul_self (z := φs n x)).symm
            rw [hnormSq, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
          -- Proof comment: the modulus-square characteristic function satisfies the same doubling
          -- defect inequality, now transported back to `ℝ`.
          have hχ' := hχ
          rw [hre_mul_conj, hre_mul_conj] at hχ'
          simpa [u, hs_two] using hχ'
        calc
          (n : ℝ) * (1 - ‖φs n s‖ ^ 2)
              ≤ (n : ℝ) * (4 * (1 - ‖φs n u‖ ^ 2)) := by
                  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
                  gcongr
          _ = 4 * ((n : ℝ) * (1 - ‖φs n u‖ ^ 2)) := by ring
          _ ≤ 4 * ((4 ^ k : ℝ) * C) := by
                have huBound := ih n u hu
                nlinarith
          _ = (4 ^ (k + 1) : ℝ) * C := by
                simp [pow_succ, mul_left_comm, mul_comm]
  intro t
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (|t| / ε) (show (1 : ℝ) < 2 by norm_num)
  have htk : |t| ≤ (2 ^ k : ℝ) * ε := by
    have hk' : |t| / ε < (2 ^ k : ℝ) := by simpa using hk
    have := (div_lt_iff₀ hεpos).mp hk'
    exact le_of_lt (by simpa [mul_comm] using this)
  have htIcc : t ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε) := by
    simpa [abs_le] using htk
  have hbound_t :
      ∀ n : ℕ+, (n : ℝ) * (1 - ‖φs n t‖ ^ 2) ≤ (4 ^ k : ℝ) * C := by
    intro n
    exact hdyadic k n t htIcc
  obtain ⟨c, hcpos, hcEventually⟩ :=
    pNat_posLowerBound_of_natMulOneSub_le
      (C := (4 ^ k : ℝ) * C) hbound_t
  obtain ⟨n, hn⟩ := hcEventually.exists
  have hpowSq :
      (‖φs n t‖ ^ 2) ^ (n : ℕ) = ‖φ t‖ ^ 2 := by
    calc
      (‖φs n t‖ ^ 2) ^ (n : ℕ) = ‖φs n t ^ (n : ℕ)‖ ^ 2 := by
        calc
          (‖φs n t‖ ^ 2) ^ (n : ℕ) = ‖φs n t‖ ^ (2 * (n : ℕ)) := by rw [pow_mul]
          _ = ‖φs n t‖ ^ ((n : ℕ) * 2) := by rw [Nat.mul_comm]
          _ = (‖φs n t‖ ^ (n : ℕ)) ^ 2 := by rw [pow_mul]
          _ = ‖φs n t ^ (n : ℕ)‖ ^ 2 := by rw [norm_pow]
      _ = ‖φ t‖ ^ 2 := by rw [hpow n t]
  have hlimit_lower : c ≤ ‖φ t‖ ^ 2 := by
    simpa [hpowSq] using hn
  have hnormsq_pos : 0 < ‖φ t‖ ^ 2 := lt_of_lt_of_le hcpos hlimit_lower
  -- Proof comment: a strictly positive norm square rules out a zero of `φ`.
  exact fun hzero ↦ by
    simp [hzero] at hnormsq_pos

/-- Helper for Exercise 16.1.2: a closed-unit-disk sequence whose exact-root exponential limit is
nonzero must converge to `1`. -/
lemma unitDiskRoot_tendstoOne_of_tendstoExpNatMulSub {z : ℕ → ℂ} {c : ℂ}
    (hz : ∀ n : ℕ, ‖z n‖ ≤ 1) (hc : c ≠ 0)
    (hexp :
      Tendsto (fun n : ℕ ↦ Complex.exp ((n : ℂ) * (z n - 1))) atTop (𝓝 c)) :
    Tendsto z atTop (𝓝 1) := by
  have hlogNorm :
      Tendsto (fun n : ℕ ↦ Real.log ‖Complex.exp ((n : ℂ) * (z n - 1))‖)
        atTop (𝓝 (Real.log ‖c‖)) := by
    -- Proof comment: the exponential limit is nonzero, so taking norms and then logs is
    -- continuous at the limit.
    exact (Real.continuousAt_log (norm_ne_zero_iff.mpr hc)).tendsto.comp hexp.norm
  have hscaledRe :
      Tendsto (fun n : ℕ ↦ (n : ℝ) * (Complex.re (z n) - 1)) atTop
        (𝓝 (Real.log ‖c‖)) := by
    -- Proof comment: `‖exp w‖ = exp (Re w)` converts the logarithmic norm limit into a bound on
    -- the real-part defect.
    simpa [Complex.norm_exp, Complex.mul_re, Complex.sub_re] using hlogNorm
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hReSubMul :
      Tendsto
        (fun n : ℕ ↦ ((n : ℝ) * (Complex.re (z n) - 1)) * ((n : ℝ)⁻¹))
        atTop (𝓝 0) := by
    -- Proof comment: multiply the bounded scaled defect by `1 / n` to recover the unscaled one.
    simpa using hscaledRe.mul hinv
  have hReSubEventually :
      (fun n : ℕ ↦ ((n : ℝ) * (Complex.re (z n) - 1)) * ((n : ℝ)⁻¹)) =ᶠ[atTop]
        fun n ↦ Complex.re (z n) - 1 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    -- Proof comment: away from `n = 0`, the extra factor `n * n⁻¹` is exactly `1`.
    calc
      ((n : ℝ) * (Complex.re (z n) - 1)) * ((n : ℝ)⁻¹)
          = ((n : ℝ) * ((n : ℝ)⁻¹)) * (Complex.re (z n) - 1) := by ring
      _ = Complex.re (z n) - 1 := by
          rw [mul_inv_cancel₀ hn0, one_mul]
  have hReSub : Tendsto (fun n : ℕ ↦ Complex.re (z n) - 1) atTop (𝓝 0) :=
    hReSubMul.congr' hReSubEventually
  have hRe : Tendsto (fun n : ℕ ↦ Complex.re (z n)) atTop (𝓝 1) := by
    -- Proof comment: the real parts converge to `1`.
    simpa using hReSub.const_add (1 : ℝ)
  have hsq :
      Tendsto (fun n : ℕ ↦ ‖z n - 1‖ ^ 2) atTop (𝓝 0) := by
    have hupper :
        Tendsto (fun n : ℕ ↦ 2 * (1 - Complex.re (z n))) atTop (𝓝 0) := by
      -- Proof comment: once the real parts converge to `1`, the unit-disk upper bound tends to
      -- `0`.
      have hOneMinusRe : Tendsto (fun n : ℕ ↦ 1 - Complex.re (z n)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hRe
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2)).mul hOneMinusRe
    -- Proof comment: squeeze `‖z n - 1‖²` between `0` and the real-part defect.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards with n
      exact sq_nonneg ‖z n - 1‖
    · filter_upwards with n
      exact sq_norm_sub_one_le_two_mul_one_sub_re (hz n)
  have hnormSub : Tendsto (fun n : ℕ ↦ ‖z n - 1‖) atTop (𝓝 0) := by
    -- Proof comment: taking square roots converts the squared-norm estimate into norm
    -- convergence.
    let f : ℝ → ℝ := Real.sqrt
    have hsqrt :
        Tendsto (fun n : ℕ ↦ Real.sqrt (‖z n - 1‖ ^ 2)) atTop (𝓝 0) := by
      have hf : Continuous f := by
        simpa [f] using Real.continuous_sqrt
      have hcomp : Tendsto (f ∘ fun n : ℕ ↦ ‖z n - 1‖ ^ 2) atTop (𝓝 (f 0)) :=
        hf.continuousAt.tendsto.comp hsq
      have hsqrt' :
          Tendsto (fun n : ℕ ↦ Real.sqrt (‖z n - 1‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) := by
        change Tendsto (f ∘ fun n : ℕ ↦ ‖z n - 1‖ ^ 2) atTop (𝓝 (f 0))
        exact hcomp
      simpa [f] using hsqrt'
    have hnorm_eq_sqrt :
        (fun n : ℕ ↦ ‖z n - 1‖) = fun n : ℕ ↦ f (‖z n - 1‖ ^ 2) := by
      funext n
      symm
      simp [f]
    rw [hnorm_eq_sqrt]
    simpa [f] using hsqrt
  -- Proof comment: convergence of the norms `‖z n - 1‖` is exactly convergence of `z n` to `1`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa using hnormSub

/-- Helper for Exercise 16.1.2: a continuous zero-free complex-valued function on `ℝ` normalized
by `φ 0 = 1` admits a unique continuous lift through `Complex.exp` starting at `0`. -/
lemma existsUnique_continuousExpLift {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφne : ∀ x : ℝ, φ x ≠ 0) (hφ0 : φ 0 = 1) :
    ∃! Ψ : C(ℝ, ℂ), Ψ 0 = 0 ∧ ∀ t : ℝ, Complex.exp (Ψ t) = φ t := by
  let f : C(ℝ, {z : ℂ // z ≠ 0}) :=
    ⟨fun t ↦ ⟨φ t, hφne t⟩, hφc.subtype_mk _⟩
  have he :
      (fun z : ℂ ↦ (⟨Complex.exp z, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) 0 = f 0 := by
    -- Proof comment: the chosen lift must start above `φ 0 = 1`.
    ext
    simp [f, hφ0]
  rcases Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 he with
    ⟨Ψ, hΨ, hΨuniq⟩
  refine ⟨Ψ, ?_, ?_⟩
  · rcases hΨ with ⟨hΨ0, hΨexp⟩
    refine ⟨hΨ0, ?_⟩
    intro t
    -- Proof comment: after forgetting the nonzero subtype, the lifted map exponentiates back to
    -- `φ`.
    simpa [f] using congrArg Subtype.val (congr_fun hΨexp t)
  · intro Ψ' hΨ'
    apply hΨuniq
    rcases hΨ' with ⟨hΨ'0, hΨ'exp⟩
    refine ⟨hΨ'0, ?_⟩
    funext t
    -- Proof comment: uniqueness of lifts is checked in the nonzero subtype by rebuilding the
    -- covering equation pointwise.
    change (⟨Complex.exp (Ψ' t), (Ψ' t).exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) = f t
    apply Subtype.ext
    simpa [f] using hΨ'exp t

/-- Helper for Exercise 16.1.2: dividing the logarithmic lift by `n` and exponentiating still
lands over the original exponential path after taking the `n`th power. -/
lemma expDivPath_coversExpPath
    {Ψ : C(ℝ, ℂ)} (n : ℕ+) (s : ℝ) :
    (Complex.exp (Ψ s / (n : ℂ))) ^ (n : ℕ) = Complex.exp (Ψ s) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt n.pos)
  have hmul : (n : ℂ) * (Ψ s / (n : ℂ)) = Ψ s := by
    field_simp [hn0]
  -- Proof comment: rewrite the `n`th power of an exponential as one exponential and cancel the
  -- factor `n` against the division by `n`.
  calc
    (Complex.exp (Ψ s / (n : ℂ))) ^ (n : ℕ) = Complex.exp ((n : ℂ) * (Ψ s / (n : ℂ))) := by
      rw [← Complex.exp_nat_mul]
    _ = Complex.exp (Ψ s) := by rw [hmul]

/-- Helper for Exercise 16.1.2: after fixing a global logarithmic lift of `φ`, each exact
positive-integer root is the corresponding divided exponential lift. -/
lemma exactRoot_eq_expDivLift
    (hcfp : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ n : ℕ+, ∀ x : ℝ, (φs n x) ^ (n : ℕ) = φ x)
    {Ψ : C(ℝ, ℂ)}
    (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ s : ℝ, Complex.exp (Ψ s) = φ s) :
    ∀ n : ℕ+, ∀ s : ℝ, φs n s = Complex.exp (Ψ s / (n : ℂ)) := by
  intro n s
  let T : Set ℂ := Set.range fun ζ : rootsOfUnity (n : ℕ) ℂ => ((ζ : Units ℂ) : ℂ)
  let q : ℝ → ℂ := fun u ↦ φs n u / Complex.exp (Ψ u / (n : ℂ))
  have hqcont : Continuous q := by
    have hnum : Continuous fun u : ℝ ↦ φs n u := by
      -- Proof comment: each exact root is continuous because it is a characteristic function.
      exact continuous_of_isCFP (hcfp n)
    have hden : Continuous fun u : ℝ ↦ Complex.exp (Ψ u / (n : ℂ)) := by
      -- Proof comment: the denominator is the exponential of the scaled logarithmic lift.
      simpa using Complex.continuous_exp.comp (Ψ.continuous.div_const (n : ℂ))
    exact hnum.div hden (fun u ↦ Complex.exp_ne_zero _)
  have hqmaps : Set.MapsTo q (Set.univ : Set ℝ) T := by
    haveI : NeZero (n : ℕ) := ⟨Nat.ne_of_gt n.pos⟩
    intro u hu
    refine ⟨rootsOfUnity.mkOfPowEq (q u) ?_, ?_⟩
    · -- Proof comment: the quotient has `n`th power `1`, so it is an `n`th root of unity.
      calc
        (q u) ^ (n : ℕ)
            = φs n u ^ (n : ℕ) / (Complex.exp (Ψ u / (n : ℂ))) ^ (n : ℕ) := by
                simp [q, div_pow]
        _ = φ u / Complex.exp (Ψ u) := by
              rw [hpow n u, expDivPath_coversExpPath (Ψ := Ψ) n u]
        _ = Complex.exp (Ψ u) / Complex.exp (Ψ u) := by rw [← hΨexp u]
        _ = 1 := by exact div_self (Complex.exp_ne_zero _)
    · simp [T, q, rootsOfUnity.coe_mkOfPowEq]
  have hTdiscrete : IsDiscrete T := by
    exact (Set.finite_range fun ζ : rootsOfUnity (n : ℕ) ℂ => ((ζ : Units ℂ) : ℂ)).isDiscrete
  have hconst : q s = q 0 := by
    -- Route correction: compare the two candidate lifts via their quotient, which now lands in a
    -- finite discrete set on the connected real line.
    exact isPreconnected_univ.constant_of_mapsTo hTdiscrete hqcont.continuousOn hqmaps trivial
      trivial
  have hqzero : q 0 = 1 := by
    -- Proof comment: at the origin both lifts are normalized to `1`.
    simp [q, hΨ0, zero_eq_one_of_isCFP (hcfp n)]
  have hqone : q s = 1 := hconst.trans hqzero
  have hden_ne : Complex.exp (Ψ s / (n : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  -- Proof comment: once the quotient is constant and equals `1` at `0`, clearing the
  -- denominator gives the desired pointwise identity.
  have hqeq : φs n s = 1 * Complex.exp (Ψ s / (n : ℂ)) := by
    exact (div_eq_iff hden_ne).mp (by simpa [q] using hqone)
  calc
    φs n s = 1 * Complex.exp (Ψ s / (n : ℂ)) := hqeq
    _ = Complex.exp (Ψ s / (n : ℂ)) := by simp

/-- Helper for Exercise 16.1.2: exact positive-integer CFP roots of `φ` converge pointwise to
`1`. -/
lemma exactRoots_tendstoOneAt
    (hcfp : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ n : ℕ+, ∀ t : ℝ, (φs n t) ^ (n : ℕ) = φ t) :
    ∀ t : ℝ, Tendsto (fun n : ℕ+ ↦ φs n t) atTop (𝓝 1) := by
  have hφne : ∀ t : ℝ, φ t ≠ 0 := by
    -- Proof comment: the exact-root family itself already forces nonvanishing of the common
    -- target.
    exact exactRootTargetNonvanishing (φ := φ) (φs := φs) hcfp hpow
  have hφc : Continuous φ := by
    have hφeq : φ = φs 1 := by
      funext x
      simpa using (hpow 1 x).symm
    -- Proof comment: `φ` is the first exact root, hence continuous as a characteristic function.
    simpa [hφeq] using continuous_of_isCFP (hcfp 1)
  have hφ0 : φ 0 = 1 := by
    -- Proof comment: evaluate the exact power identity at `0` and use the CFP normalization.
    simpa [zero_eq_one_of_isCFP (hcfp 1)] using (hpow 1 0).symm
  intro t
  obtain ⟨Ψ, hΨ, _⟩ := existsUnique_continuousExpLift (φ := φ) hφc hφne hφ0
  rcases hΨ with ⟨hΨ0, hΨexp⟩
  have hformula :
      ∀ n : ℕ+, φs n t = Complex.exp (Ψ t / (n : ℂ)) := by
    intro n
    -- Proof comment: compare the exact root with the divided global lift at the fixed frequency
    -- `t`.
    simpa using
      exactRoot_eq_expDivLift (φ := φ) (φs := φs) hcfp hpow
        (Ψ := Ψ) hΨ0 hΨexp n t
  have hInvNat : Tendsto (fun n : ℕ ↦ ((n : ℂ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hInv : Tendsto (fun n : ℕ+ ↦ ((n : ℂ)⁻¹)) atTop (𝓝 0) := by
    -- Proof comment: transfer reciprocal convergence from `ℕ` to `ℕ+`.
    simpa using hInvNat.comp tendsto_PNat_val_atTop_atTop
  have hScaled :
      Tendsto (fun n : ℕ+ ↦ Ψ t / (n : ℂ)) atTop (𝓝 0) := by
    -- Proof comment: the lift endpoint is fixed while `1 / n → 0`.
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ+ ↦ Ψ t) atTop (𝓝 (Ψ t))).mul hInv
  have hExp :
      Tendsto (fun n : ℕ+ ↦ Complex.exp (Ψ t / (n : ℂ))) atTop (𝓝 (Complex.exp 0)) := by
    exact (Complex.continuous_exp.continuousAt.tendsto.comp hScaled)
  -- Proof comment: substituting the endpoint formula leaves the standard `exp (a / n) → 1`
  -- limit.
  simpa [hformula] using hExp

/-- Helper for Exercise 16.1.2: probability-law witnesses for the positive-integer roots converge
weakly to `diracProba 0`. -/
lemma rootWitnessMeasures_tendsto_diracZero
    (hcfp : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ n : ℕ+, ∀ t : ℝ, (φs n t) ^ (n : ℕ) = φ t) :
    ∃ μs : ℕ → ProbabilityMeasure ℝ,
      (∀ n : ℕ, charFun (μs n) = φs (Nat.toPNat' n)) ∧
        Tendsto μs atTop (𝓝 (diracProba 0)) := by
  have hrootLimitPNat : ∀ t : ℝ, Tendsto (fun n : ℕ+ ↦ φs n t) atTop (𝓝 1) :=
    exactRoots_tendstoOneAt (φ := φ) hcfp hpow
  choose μsPNat hμsPNat using hcfp
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦ μsPNat (Nat.toPNat' n)
  have hμs : ∀ n : ℕ, charFun (μs n) = φs (Nat.toPNat' n) := by
    intro n
    simpa [μs] using hμsPNat (Nat.toPNat' n)
  have hrootLimit : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs (Nat.toPNat' n) t) atTop (𝓝 1) := by
    intro t
    let rootSeq : ℕ → ℂ := fun n ↦ φs (Nat.toPNat' n) t
    have hrootSeqPNat : Tendsto (fun n : ℕ+ ↦ rootSeq n) atTop (𝓝 1) := by
      -- Proof comment: reindexing along `Nat.toPNat'` agrees with the original `ℕ+` sequence.
      simpa [rootSeq] using hrootLimitPNat t
    exact (PNat.tendsto_comp_val_iff (f := rootSeq) (l := 𝓝 (1 : ℂ))).mp hrootSeqPNat
  have hμs_apply : ∀ n : ℕ, ∀ t : ℝ, charFun (μs n) t = φs (Nat.toPNat' n) t := by
    intro n t
    exact congrArg (fun f : ℝ → ℂ ↦ f t) (hμs n)
  have hchar :
      ∀ t : ℝ,
        Tendsto (fun n : ℕ ↦ charFun (μs n) t) atTop
          (𝓝 (charFun (diracProba (0 : ℝ)) t)) := by
    intro t
    -- Proof comment: rewrite the pointwise root limit as convergence to the characteristic
    -- function of the Dirac mass at the origin.
    simpa [hμs_apply, MeasureTheory.diracProba, MeasureTheory.charFun_dirac] using
      hrootLimit t
  refine ⟨μs, hμs, ?_⟩
  -- Proof comment: Lévy's continuity theorem upgrades pointwise characteristic-function
  -- convergence to weak convergence of the witnessing laws.
  exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 hchar

-- Proof sketch: for each positive integer `n`, realize `φs n` as the characteristic function of
-- a probability measure `μₙ`. Since `(φs n)^n = φ`, the measures `μₙ` are `n`th convolution roots
-- of a fixed infinitely divisible law, so Lévy's continuity theorem forces `μₙ` to converge
-- weakly to `δ₀`. The compact-uniform convergence of the characteristic functions then follows
-- from the weak-convergence-to-uniform-on-compacts theorem for characteristic functions.
/-- Exercise 16.1.2 (1): if `φₙ` is a CFP for each positive integer `n` and
`φₙ(t)^n = φ(t)` for every real `t`, then `φₙ → 1` uniformly on every compact subset of `ℝ`. -/
theorem cfp_power_roots_tendstoUniformlyOn_one
    (hcfp : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ n : ℕ+, ∀ t : ℝ, (φs n t) ^ (n : ℕ) = φ t) :
    ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n t ↦ φs n t) (fun _ : ℝ ↦ (1 : ℂ)) atTop K := by
  intro K hK
  obtain ⟨μs, hμs, hμtendsto⟩ := rootWitnessMeasures_tendsto_diracZero (φ := φ) hcfp hpow
  have hμs_apply : ∀ n : ℕ, ∀ t : ℝ, charFun (μs n) t = φs (Nat.toPNat' n) t := by
    intro n t
    exact congrArg (fun f : ℝ → ℂ ↦ f t) (hμs n)
  have hnatUniform :
      TendstoUniformlyOn (fun n t ↦ φs (Nat.toPNat' n) t) (fun _ : ℝ ↦ (1 : ℂ)) atTop K := by
    have hcharUniform :=
      (charFun_tendstoUniformlyOn_of_tendstoReal (P := diracProba (0 : ℝ)) hμtendsto) K hK
    rw [Metric.tendstoUniformlyOn_iff] at hcharUniform ⊢
    intro ε εpos
    filter_upwards [hcharUniform ε εpos] with n hn t ht
    -- Proof comment: rewrite the witnessing characteristic functions and the Dirac limit.
    simpa [hμs_apply, MeasureTheory.diracProba, MeasureTheory.charFun_dirac] using hn t ht
  rw [Metric.tendstoUniformlyOn_iff] at hnatUniform ⊢
  intro ε εpos
  have hEventuallyNat := hnatUniform ε εpos
  refine (tendsto_PNat_val_atTop_atTop.eventually hEventuallyNat).mono ?_
  intro n hn t ht
  -- Proof comment: on positive indices, the `ℕ`-reindexing `Nat.toPNat'` returns the original
  -- `ℕ+` index.
  simpa [PNat.toPNat'_coe n.pos] using hn t ht

end

-- Proof sketch: apply the Gaussian lower bound available for infinitely divisible characteristic
-- functions. The lower bound is strictly positive at every real argument, so the characteristic
-- function cannot vanish anywhere.
/-- Exercise 16.1.2 (2): an infinitely divisible characteristic function on `ℝ` has no zeros. -/
theorem infinitelyDivisibleCFP_ne_zero
    {φ : ℝ → ℂ} (hφ : IsInfinitelyDivisibleCFP φ) :
    ∀ t : ℝ, φ t ≠ 0 := by
  classical
  let ψs : ℕ+ → ℝ → ℂ := fun n ↦ Classical.choose (hφ n)
  have hcfp : ∀ n : ℕ+, IsCFP (ψs n) := by
    intro n
    exact (Classical.choose_spec (hφ n)).1
  have hpow : ∀ n : ℕ+, ∀ t : ℝ, (ψs n t) ^ (n : ℕ) = φ t := by
    intro n t
    simpa using (congrArg (fun f : ℝ → ℂ ↦ f t) (Classical.choose_spec (hφ n)).2).symm
  intro t
  have hrootLimit : Tendsto (fun n : ℕ+ ↦ ψs n t) atTop (𝓝 1) :=
    exactRoots_tendstoOneAt (φ := φ) (φs := ψs) hcfp hpow t
  by_contra hzero
  have hzeroRoots : ∀ n : ℕ+, ψs n t = 0 := by
    intro n
    have : (ψs n t) ^ (n : ℕ) = 0 := by simpa [hzero] using hpow n t
    exact eq_zero_of_pow_eq_zero this
  have hconstZero : Tendsto (fun n : ℕ+ ↦ (0 : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa [hzeroRoots] using hrootLimit
  have hzeroNeOne : (0 : ℂ) ≠ 1 := by norm_num
  exact hzeroNeOne (tendsto_nhds_unique tendsto_const_nhds hconstZero)

namespace MeasureTheory.ProbabilityMeasure

/-- The characteristic function of an infinitely divisible probability law on `ℝ` has no zeros. -/
theorem charFun_ne_zero_of_isInfinitelyDivisible {μ : ProbabilityMeasure ℝ}
    (hμ : IsInfinitelyDivisible μ) :
    ∀ t : ℝ, charFun (μ : Measure ℝ) t ≠ 0 := by
  intro t
  exact infinitelyDivisibleCFP_ne_zero (charFun_isInfinitelyDivisible hμ) t

end MeasureTheory.ProbabilityMeasure
