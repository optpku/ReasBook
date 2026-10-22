/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open MeasureTheory.Filtration
open scoped ENNReal Topology

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
variable {X : NNReal → Ω → ℝ}

/- Exercise 21.4.2 is `source-facing`: it concerns continuous-time martingale convergence on
`[0, ∞)` to the canonical limit process `ℱ.limitProcess X μ`.

Domain-style sampling for the owner abstraction:
* `HasRightContinuousPaths X` in Definition 21.21 is the local `core/canonical` owner for the path
  regularity input; the stronger càdlàg condition is only a derived specialization.
* `stronglyMeasurable_limitProcess` is the owner theorem for terminal measurability of
  `ℱ.limitProcess X μ`, and it already works for `NNReal`-indexed filtrations.
* The discrete chapter owners `Submartingale.memLp_limitProcess`,
  `Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable`, and
  `Submartingale.tendsto_eLpNorm_one_limitProcess` determine the correct statement shape, but they
  live over `ℕ`-indexed filtrations, so they guide the bridge design here rather than replacing the
  present theorems by exact recalls.

Primitive data versus derived API:
* primitive inputs: right continuity, submartingale or martingale structure, and the textbook
  boundedness / uniform-integrability / `L^p` hypotheses;
* derived object: the limit random variable is the canonical owner object `ℱ.limitProcess X μ`,
  not extra public data.

Accordingly, only terminal strong measurability is a direct recall, while the almost-sure and
`eLpNorm` formulations below remain `bridge/view` companions for the continuous-time setting. -/

/- The canonical limit process is already `⨆ t, ℱ t`-strongly measurable by the general owner
declaration for `Filtration.limitProcess`. -/
recall stronglyMeasurable_limitProcess

section

variable (hX_rc : HasRightContinuousPaths X)
include hX_rc

local notation "X∞" => ℱ.limitProcess X μ

omit hX_rc in
/-- Helper for Exercise 21.4.2: sample the ambient filtration along a monotone deterministic time
map `τ : ℕ → ℝ≥0`. -/
private def sampledFiltration (τ : ℕ → NNReal) (hτ : Monotone τ) :
    Filtration ℕ ‹MeasurableSpace Ω› :=
  Filtration.mk (fun n => ℱ (τ n))
    (fun _ _ hij => ℱ.mono (hτ hij))
    (fun n => ℱ.le (τ n))

omit hX_rc in
/-- Helper for Exercise 21.4.2: a martingale remains a martingale after monotone deterministic
sampling. -/
private theorem sampledMartingaleOfMonotone
    (hX : Martingale X ℱ μ)
    {τ : ℕ → NNReal} (hτ : Monotone τ) :
    Martingale (fun n ω ↦ X (τ n) ω) (sampledFiltration (ℱ := ℱ) τ hτ) μ := by
  -- Proof comment: the sampled process inherits adaptation, integrability, and the one-step
  -- conditional-expectation identity directly from the ambient martingale.
  refine martingale_nat ?_ ?_ ?_
  · intro n
    simpa [sampledFiltration] using hX.stronglyAdapted (τ n)
  · intro n
    exact hX.integrable (τ n)
  · intro n
    simpa [sampledFiltration] using
      (hX.condExp_ae_eq (i := τ n) (j := τ (n + 1)) (hτ (Nat.le_succ n))).symm

omit hX_rc in
/-- Helper for Exercise 21.4.2: a submartingale remains a submartingale after monotone
deterministic sampling. -/
private theorem sampledSubmartingaleOfMonotone
    (hX : Submartingale X ℱ μ)
    {τ : ℕ → NNReal} (hτ : Monotone τ) :
    Submartingale (fun n ω ↦ X (τ n) ω) (sampledFiltration (ℱ := ℱ) τ hτ) μ := by
  -- Proof comment: the sampled process keeps strong adaptation, integrability, and the
  -- conditional-expectation inequality from the ambient submartingale.
  refine submartingale_nat ?_ ?_ ?_
  · intro n
    simpa [sampledFiltration] using hX.stronglyAdapted (τ n)
  · intro n
    exact hX.integrable (τ n)
  · intro n
    simpa [sampledFiltration] using
      hX.ae_le_condExp (i := τ n) (j := τ (n + 1)) (hτ (Nat.le_succ n))

omit hX_rc in
/-- Helper for Exercise 21.4.2: the dyadic time grid with mesh `2^{-n}`. -/
private noncomputable def dyadicTime (n k : ℕ) : NNReal :=
  (k : NNReal) / (2 : NNReal) ^ n

omit hX_rc in
/-- Helper for Exercise 21.4.2: each dyadic row is monotone in the discrete index. -/
private theorem monotone_dyadicTime (n : ℕ) :
    Monotone (dyadicTime n) := by
  intro i j hij
  unfold dyadicTime
  have hcast : (i : NNReal) ≤ j := by
    exact_mod_cast hij
  have hfactor_nonneg : 0 ≤ ((2 : NNReal) ^ n)⁻¹ := by
    exact inv_nonneg.mpr (pow_nonneg (show (0 : NNReal) ≤ 2 by positivity) _)
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hcast hfactor_nonneg

omit hX_rc in
/-- Helper for Exercise 21.4.2: the `n`-th dyadic row of the process `X`. -/
private noncomputable def dyadicRowProcess
    (X : NNReal → Ω → ℝ) (n : ℕ) : ℕ → Ω → ℝ :=
  fun k ω ↦ X (dyadicTime n k) ω

omit hX_rc in
/-- Helper for Exercise 21.4.2: the sampled filtration attached to the `n`-th dyadic row. -/
private noncomputable def dyadicRowFiltration
    (ℱ : Filtration NNReal ‹MeasurableSpace Ω›) (n : ℕ) : Filtration ℕ ‹MeasurableSpace Ω› :=
  sampledFiltration (ℱ := ℱ) (dyadicTime n) (monotone_dyadicTime n)

omit hX_rc in
/-- Helper for Exercise 21.4.2: the natural-time skeleton of `X`. -/
private def natSkeletonProcess (X : NNReal → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun k ω ↦ X (k : NNReal) ω

omit hX_rc in
/-- Helper for Exercise 21.4.2: the sampled filtration attached to the natural-time skeleton. -/
private def natSkeletonFiltration
    (ℱ : Filtration NNReal ‹MeasurableSpace Ω›) : Filtration ℕ ‹MeasurableSpace Ω› :=
  sampledFiltration (ℱ := ℱ) (fun k : ℕ ↦ (k : NNReal)) Nat.mono_cast

omit hX_rc in
/-- Helper for Exercise 21.4.2: the `n`-th dyadic row contains the natural-time skeleton along the
subsequence `k = 2^n * m`. -/
private theorem dyadicTime_mul_pow (n m : ℕ) :
    dyadicTime n ((2 ^ n) * m) = m := by
  -- Proof comment: after casting to `NNReal`, the factor `(2 : NNReal)^n` cancels with the
  -- denominator of the dyadic row.
  unfold dyadicTime
  rw [Nat.cast_mul]
  have hpow_cast : ((2 ^ n : ℕ) : NNReal) = (2 : NNReal) ^ n := by
    simp
  have hpow_ne : (2 : NNReal) ^ n ≠ 0 := by positivity
  rw [hpow_cast, mul_comm, mul_div_assoc, div_self hpow_ne, mul_one]

omit hX_rc [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.2: the positive-part bound restricts to every dyadic row. -/
private theorem bddAbovePosPart_dyadicRow
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) (n : ℕ) :
    BddAbove (range fun k ↦ μ[fun ω ↦ (dyadicRowProcess X n k ω)⁺]) := by
  rcases hpos with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact hR (mem_range.2 ⟨dyadicTime n k, rfl⟩)

omit hX_rc [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.2: the positive-part bound restricts to the natural-time skeleton. -/
private theorem bddAbovePosPart_natSkeleton
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) :
    BddAbove (range fun k ↦ μ[fun ω ↦ (natSkeletonProcess X k ω)⁺]) := by
  rcases hpos with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact hR (mem_range.2 ⟨(k : NNReal), rfl⟩)

omit hX_rc in
/-- Helper for Exercise 21.4.2: every fixed dyadic row converges almost surely by the discrete
Chapter 11 theorem. -/
private theorem dyadicRow_convergence_to_limitProcess_of_bdd_pos_part
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) (n : ℕ) :
    Integrable ((dyadicRowFiltration ℱ n).limitProcess (dyadicRowProcess X n) μ) μ ∧
      ∀ᵐ ω ∂μ,
        Tendsto (fun k ↦ dyadicRowProcess X n k ω) atTop
          (𝓝 (((dyadicRowFiltration ℱ n).limitProcess
            (dyadicRowProcess X n) μ) ω)) := by
  -- Proof comment: the `n`-th dyadic row is an ordinary discrete submartingale with the same
  -- positive-part bound as the ambient process.
  have hrow :
      Submartingale (dyadicRowProcess X n) (dyadicRowFiltration ℱ n) μ := by
    simpa [dyadicRowProcess, dyadicRowFiltration] using
      sampledSubmartingaleOfMonotone (X := X) (ℱ := ℱ) (μ := μ) hX (monotone_dyadicTime n)
  exact
    submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
      (ℱ := dyadicRowFiltration ℱ n)
      (μ := μ)
      (X := dyadicRowProcess X n)
      hrow
      (bddAbovePosPart_dyadicRow (X := X) hpos n)

omit hX_rc in
/-- Helper for Exercise 21.4.2: the natural-time skeleton converges almost surely by the discrete
Chapter 11 theorem. -/
private theorem natSkeleton_convergence_to_limitProcess_of_bdd_pos_part
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) :
    Integrable ((natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ) μ ∧
      ∀ᵐ ω ∂μ,
        Tendsto (fun k ↦ natSkeletonProcess X k ω) atTop
          (𝓝 (((natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ) ω)) := by
  -- Proof comment: the natural-time samples are the simplest discrete skeleton of the ambient
  -- process.
  have hnat :
      Submartingale (natSkeletonProcess X) (natSkeletonFiltration ℱ) μ := by
    simpa [natSkeletonProcess, natSkeletonFiltration] using
      sampledSubmartingaleOfMonotone (X := X) (ℱ := ℱ) (μ := μ) hX Nat.mono_cast
  exact
    submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
      (ℱ := natSkeletonFiltration ℱ)
      (μ := μ)
      (X := natSkeletonProcess X)
      hnat
      (bddAbovePosPart_natSkeleton (X := X) hpos)

omit hX_rc in
/-- Helper for Exercise 21.4.2: the dyadic-row limit process agrees almost surely with the
natural-time limit process. -/
private theorem dyadicRowLimitProcess_ae_eq_natLimitProcess
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) (n : ℕ) :
    (dyadicRowFiltration ℱ n).limitProcess (dyadicRowProcess X n) μ =ᵐ[μ]
      (natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ := by
  let rowLimit :
      Ω → ℝ := (dyadicRowFiltration ℱ n).limitProcess (dyadicRowProcess X n) μ
  let natLimit :
      Ω → ℝ := (natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ
  have hrow :=
    (dyadicRow_convergence_to_limitProcess_of_bdd_pos_part
      (X := X) (ℱ := ℱ) (μ := μ) hX hpos n).2
  have hnat :=
    (natSkeleton_convergence_to_limitProcess_of_bdd_pos_part
      (X := X) (ℱ := ℱ) (μ := μ) hX hpos).2
  have hsubseq : Tendsto (fun m : ℕ ↦ (2 ^ n) * m) atTop atTop := by
    exact tendsto_id.const_mul_atTop' (show 0 < (2 ^ n : ℕ) by positivity)
  -- Proof comment: the subsequence `m ↦ 2^n * m` turns the `n`-th dyadic row into the natural
  -- skeleton, so uniqueness of limits identifies the two limit processes.
  filter_upwards [hrow, hnat] with ω hrowω hnatω
  have hrowSub :
      Tendsto (fun m : ℕ ↦ dyadicRowProcess X n ((2 ^ n) * m) ω) atTop
        (𝓝 (rowLimit ω)) :=
    hrowω.comp hsubseq
  have hrowAsNat :
      Tendsto (fun m : ℕ ↦ natSkeletonProcess X m ω) atTop (𝓝 (rowLimit ω)) := by
    simpa [rowLimit, natLimit, dyadicRowProcess, natSkeletonProcess, dyadicTime_mul_pow] using
      hrowSub
  exact tendsto_nhds_unique hrowAsNat hnatω

omit hX_rc in
/-- Helper for Exercise 21.4.2: every fixed dyadic row converges almost surely to the same
natural-time limit process. -/
private theorem dyadicRow_ae_tendsto_natLimitProcess_of_bdd_pos_part
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) (n : ℕ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun k ↦ dyadicRowProcess X n k ω) atTop
        (𝓝 (((natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ) ω)) := by
  have hrow :=
    (dyadicRow_convergence_to_limitProcess_of_bdd_pos_part
      (X := X) (ℱ := ℱ) (μ := μ) hX hpos n).2
  have hEq :=
    dyadicRowLimitProcess_ae_eq_natLimitProcess
      (X := X) (ℱ := ℱ) (μ := μ) hX hpos n
  -- Proof comment: after replacing the rowwise limit process by its almost-surely equal natural
  -- counterpart, the discrete convergence statement becomes uniform in the target limit.
  filter_upwards [hrow, hEq] with ω hrowω hEqω
  simpa [hEqω] using hrowω

omit hX_rc in
/-- Helper for Exercise 21.4.2: on a probability space, a uniform `L^p` bound with `1 < p`
upgrades to a uniform `L¹` bound for an `NNReal`-indexed submartingale. -/
private theorem eLpNormOneBoundedOfLpBoundedNNReal
    {p : ℝ} (hX : Submartingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ t : NNReal, eLpNorm (X t) (ENNReal.ofReal p) μ ≤ C) :
    ∃ R : NNReal, ∀ t : NNReal, eLpNorm (X t) 1 μ ≤ R := by
  rcases hbounded with ⟨C, hC⟩
  refine ⟨C, fun t ↦ ?_⟩
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have h1_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hcompare :
      eLpNorm (X t) 1 μ ≤
        eLpNorm (X t) (ENNReal.ofReal p) μ * μ Set.univ ^ (1 - 1 / p) := by
    simpa [hp0.ne', ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le, one_div] using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ h1_le_p
        (((hX.stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable) :
          eLpNorm (X t) 1 μ ≤
            eLpNorm (X t) (ENNReal.ofReal p) μ *
              μ Set.univ ^
                (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal))
  calc
    eLpNorm (X t) 1 μ
        ≤ eLpNorm (X t) (ENNReal.ofReal p) μ * μ Set.univ ^ (1 - 1 / p) := hcompare
    _ = eLpNorm (X t) (ENNReal.ofReal p) μ := by simp
    _ ≤ C := hC t

omit hX_rc [IsProbabilityMeasure μ] in
/-- Helper for Exercise 21.4.2: a uniform `L¹` bound controls the expectations of the positive
parts. -/
private theorem bddAbovePosPartOfELpNormOneBounded
    (hX : Submartingale X ℱ μ)
    (hbounded : ∃ R : NNReal, ∀ t : NNReal, eLpNorm (X t) 1 μ ≤ R) :
    BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺]) := by
  rcases hbounded with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hpos_le_norm :
      ∀ᵐ ω ∂μ, (X t ω)⁺ ≤ ‖X t ω‖ := by
    filter_upwards with ω
    by_cases hω : 0 ≤ X t ω
    · rw [posPart_eq_self.2 hω, Real.norm_eq_abs, abs_of_nonneg hω]
    · have hω' : X t ω ≤ 0 := le_of_not_ge hω
      rw [posPart_eq_zero.2 hω']
      exact norm_nonneg _
  have hposInt : Integrable (fun ω ↦ (X t ω)⁺) μ := by
    simpa using (hX.integrable t).pos_part
  have hnormInt : Integrable (fun ω ↦ ‖X t ω‖) μ := (hX.integrable t).norm
  have hnormBound : ∫ ω, ‖X t ω‖ ∂μ ≤ R := by
    have hRt : eLpNorm (X t) 1 μ ≤ R := hR t
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable t)] at hRt
    exact (ENNReal.ofReal_le_coe).1 hRt
  exact (integral_mono_ae hposInt hnormInt hpos_le_norm).trans hnormBound

omit hX_rc in
/-- Helper for Exercise 21.4.2: a continuous-time submartingale has nondecreasing expectations. -/
private theorem expectationAtZero_le_expectationNNReal
    (hX : Submartingale X ℱ μ) (t : NNReal) :
    μ[X 0] ≤ μ[X t] := by
  -- Proof comment: normalize the owner set-integral monotonicity on `univ` to plain expectations.
  simpa [MeasureTheory.setIntegral_univ] using
    hX.setIntegral_le (show (0 : NNReal) ≤ t by exact zero_le t) MeasurableSet.univ

omit hX_rc in
/-- Helper for Exercise 21.4.2: bounded positive-part expectations control the negative parts in
continuous time. -/
private theorem negPartExpectationBound_ofBddPosPartNNReal
    (hX : Submartingale X ℱ μ) {B : ℝ}
    (hB : ∀ t : NNReal, μ[fun ω ↦ (X t ω)⁺] ≤ B) (t : NNReal) :
    μ[fun ω ↦ (X t ω)⁻] ≤ B + |μ[X 0]| := by
  have hmono : μ[X 0] ≤ μ[X t] :=
    expectationAtZero_le_expectationNNReal (X := X) (ℱ := ℱ) (μ := μ) hX t
  have hdecomp :
      μ[X t] = μ[fun ω ↦ (X t ω)⁺] - μ[fun ω ↦ (X t ω)⁻] := by
    -- Proof comment: decompose the expectation into the positive and negative parts.
    simpa using integral_eq_integral_pos_part_sub_integral_neg_part (hX.integrable t)
  have hstep : μ[fun ω ↦ (X t ω)⁻] ≤ μ[fun ω ↦ (X t ω)⁺] + |μ[X 0]| := by
    -- Proof comment: rearrange the decomposition and bound `-μ[X 0]` by `|μ[X 0]|`.
    linarith [hmono, hdecomp, neg_le_abs (μ[X 0])]
  exact le_trans hstep (add_le_add (hB t) le_rfl)

omit hX_rc in
/-- Helper for Exercise 21.4.2: bounded positive-part expectations give a uniform continuous-time
`L¹` bound. -/
private theorem submartingaleELpNormOneBoundedOfBddPosPartNNReal
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (Set.range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) :
    ∃ R : NNReal, ∀ t : NNReal, eLpNorm (X t) 1 μ ≤ R := by
  rcases hpos with ⟨B, hBdd⟩
  have hB : ∀ t : NNReal, μ[fun ω ↦ (X t ω)⁺] ≤ B := by
    intro t
    exact hBdd (Set.mem_range.2 ⟨t, rfl⟩)
  have hB_nonneg : 0 ≤ B := by
    have hpos_nonneg : 0 ≤ μ[fun ω ↦ (X 0 ω)⁺] := by
      refine integral_nonneg_of_ae ?_
      filter_upwards with ω
      exact posPart_nonneg (X 0 ω)
    exact hpos_nonneg.trans (hB 0)
  have hR_nonneg : 0 ≤ 2 * B + |μ[X 0]| := by
    exact add_nonneg (mul_nonneg (by positivity) hB_nonneg) (abs_nonneg _)
  let R : NNReal := ⟨2 * B + |μ[X 0]|, hR_nonneg⟩
  refine ⟨R, fun t ↦ ?_⟩
  have hnegB : μ[fun ω ↦ (X t ω)⁻] ≤ B + |μ[X 0]| :=
    negPartExpectationBound_ofBddPosPartNNReal (X := X) (ℱ := ℱ) (μ := μ) hX hB t
  have hposInt : Integrable (fun ω ↦ (X t ω)⁺) μ := by
    -- Proof comment: the positive part of an integrable slice is still integrable.
    simpa using (hX.integrable t).pos_part
  have hnegInt : Integrable (fun ω ↦ (X t ω)⁻) μ := by
    -- Proof comment: the negative part is handled by the same owner API.
    simpa using (hX.integrable t).neg_part
  have hnorm_eq : ∀ ω, ‖X t ω‖ = (X t ω)⁺ + (X t ω)⁻ := by
    intro ω
    by_cases hω : 0 ≤ X t ω
    · -- Proof comment: on the nonnegative branch, the negative part vanishes.
      rw [Real.norm_eq_abs, abs_of_nonneg hω, posPart_eq_self.2 hω, negPart_eq_zero.2 hω, add_zero]
    · have hω' : X t ω ≤ 0 := le_of_not_ge hω
      -- Proof comment: on the nonpositive branch, the positive part vanishes and the negative
      -- part records `-X t ω`.
      rw [Real.norm_eq_abs, abs_of_nonpos hω', posPart_eq_zero.2 hω', negPart_eq_neg.2 hω',
        zero_add]
  have hnorm_bound : ∫ ω, ‖X t ω‖ ∂μ ≤ 2 * B + |μ[X 0]| := by
    -- Proof comment: rewrite the norm as positive part plus negative part, then combine the two
    -- expectation bounds.
    calc
      ∫ ω, ‖X t ω‖ ∂μ = ∫ ω, ((X t ω)⁺ + (X t ω)⁻) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with ω
        exact hnorm_eq ω
      _ = μ[fun ω ↦ (X t ω)⁺] + μ[fun ω ↦ (X t ω)⁻] := by
        rw [integral_add hposInt hnegInt]
      _ ≤ B + (B + |μ[X 0]|) := add_le_add (hB t) hnegB
      _ = 2 * B + |μ[X 0]| := by ring
  -- Proof comment: convert the real `L¹` bound into the owner `eLpNorm` bound using the `p = 1`
  -- normalization.
  calc
    eLpNorm (X t) 1 μ = ENNReal.ofReal (∫ ω, ‖X t ω‖ ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable t)]
    _ ≤ ENNReal.ofReal (2 * B + |μ[X 0]|) :=
      ENNReal.ofReal_le_ofReal hnorm_bound
    _ = R := by
      simpa [R] using (ENNReal.ofReal_eq_coe_nnreal hR_nonneg)

omit hX_rc in
/-- Helper for Exercise 21.4.2: precomposing a uniformly integrable family with a deterministic
time map preserves uniform integrability. -/
private theorem uniformIntegrable_comp
    {ι κ : Type*} {f : ι → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) (τ : κ → ι) :
    UniformIntegrable (fun k ω ↦ f (τ k) ω) 1 μ := by
  refine ⟨fun k ↦ hf.aestronglyMeasurable (τ k), ?_, ?_⟩
  · -- Proof comment: the small-set control is inherited pointwise from the original family.
    intro ε hε
    rcases hf.unifIntegrable hε with ⟨δ, hδ, hδ_bound⟩
    exact ⟨δ, hδ, fun k s hs hμs ↦ hδ_bound (τ k) s hs hμs⟩
  · -- Proof comment: the same global `L¹` bound works after deterministic reindexing.
    rcases hf.2.2 with ⟨C, hC⟩
    exact ⟨C, fun k ↦ hC (τ k)⟩

omit hX_rc in
/-- Helper for Exercise 21.4.2: if one discrete sampled process converges almost surely both to its
canonical limit process and to a given target, then these limits agree almost surely. -/
private theorem sampledLimitProcess_ae_eq_of_ae_tendsto
    {Y : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : Ω → ℝ}
    (hYlimit :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (𝒢.limitProcess Y μ ω)))
    (hYZ :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (Z ω))) :
    𝒢.limitProcess Y μ =ᵐ[μ] Z := by
  -- Proof comment: pointwise uniqueness of limits identifies the sampled canonical limit with the
  -- comparison target.
  filter_upwards [hYlimit, hYZ] with ω hωLimit hωZ
  exact tendsto_nhds_unique hωLimit hωZ

omit hX_rc in
/-- Helper for Exercise 21.4.2: the canonical ceiling dyadic approximation of a continuous time. -/
private noncomputable def dyadicRightApprox (t : NNReal) (n : ℕ) : NNReal :=
  ((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : NNReal) / (2 : NNReal) ^ n

omit hX_rc in
/-- Helper for Exercise 21.4.2: the ceiling dyadic approximation stays to the right of the target
time. -/
private theorem le_dyadicRightApprox (t : NNReal) (n : ℕ) :
    t ≤ dyadicRightApprox t n := by
  -- Proof comment: `Nat.ceil` rounds the scaled time upward, so dividing by the same dyadic mesh
  -- keeps the approximant on or to the right of `t`.
  unfold dyadicRightApprox
  have hpow_pos : 0 < (2 : NNReal) ^ n := by positivity
  rw [le_div_iff₀ hpow_pos]
  exact_mod_cast Nat.le_ceil ((t : ℝ) * (2 : ℝ) ^ n)

omit hX_rc in
/-- Helper for Exercise 21.4.2: the ceiling dyadic approximations converge back to the target
time. -/
private theorem tendsto_dyadicRightApprox (t : NNReal) :
    Tendsto (dyadicRightApprox t) atTop (𝓝 t) := by
  -- Proof comment: this is the standard `ceil (t * 2^n) / 2^n → t` limit on the dyadic mesh.
  refine (NNReal.tendsto_coe).mp ?_
  simpa [dyadicRightApprox] using
    (tendsto_nat_ceil_mul_div_atTop (a := (t : ℝ)) t.2).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

omit hX_rc in
/-- Helper for Exercise 21.4.2: once `q` lies strictly to the right of `t`, the dyadic ceiling
approximants are eventually bounded above by `q`. -/
private theorem dyadicRightApprox_eventually_le {t q : NNReal} (hqt : t < q) :
    ∃ N : ℕ, ∀ m : ℕ, dyadicRightApprox t (N + m) ≤ q := by
  have hEventually :
      ∀ᶠ n : ℕ in atTop, dyadicRightApprox t n < q := by
    -- Proof comment: the right-dyadic approximants converge back to `t`, so they eventually stay
    -- inside the left-neighborhood `(-∞, q)`.
    exact (tendsto_dyadicRightApprox t) (Iio_mem_nhds hqt)
  rw [Filter.eventually_atTop] at hEventually
  rcases hEventually with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m
  exact (hN (N + m) (Nat.le_add_right N m)).le

omit hX_rc in
/-- Helper for Exercise 21.4.2: the dyadic row value at the ceiling index is exactly the sampled
value at the right-dyadic approximation. -/
private theorem dyadicRowProcess_rightApprox
    (X : NNReal → Ω → ℝ) (t : NNReal) (n : ℕ) (ω : Ω) :
    dyadicRowProcess X n (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)) ω =
      X (dyadicRightApprox t n) ω := by
  -- Proof comment: both sides are the same dyadic sample, written once through the row API and
  -- once through the explicit ceiling approximation.
  simp [dyadicRowProcess, dyadicTime, dyadicRightApprox]

/-- Helper for Exercise 21.4.2: right continuity transports a strict upper-threshold witness to
all sufficiently fine right-dyadic approximations. -/
private theorem eventually_gt_dyadicRightApprox_of_lt
    {ω : Ω} {t : NNReal} {c : ℝ} (hc : c < X t ω) :
    ∃ N : ℕ, ∀ m : ℕ, c < X (dyadicRightApprox t (N + m)) ω := by
  have hstrict :
      ∀ᶠ s in 𝓝[Set.Ici t] t, c < X s ω := by
    -- Proof comment: right continuity turns the strict inequality at `t` into a right-neighborhood
    -- on which the same inequality still holds.
    simpa [Set.mem_Ioi] using (hX_rc ω t) (Ioi_mem_nhds hc)
  have happrox_mem : ∀ᶠ n : ℕ in atTop, dyadicRightApprox t n ∈ Set.Ici t := by
    -- Proof comment: every ceiling approximation stays on the right side of `t`.
    exact Eventually.of_forall fun n ↦ le_dyadicRightApprox t n
  have happrox :
      Tendsto (dyadicRightApprox t) atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_dyadicRightApprox t) happrox_mem
  have hstrictApprox : ∀ᶠ n : ℕ in atTop, c < X (dyadicRightApprox t n) ω :=
    happrox hstrict
  rw [Filter.eventually_atTop] at hstrictApprox
  rcases hstrictApprox with ⟨N, hN⟩
  exact ⟨N, fun m ↦ hN (N + m) (Nat.le_add_right N m)⟩

/-- Helper for Exercise 21.4.2: right continuity transports a strict lower-threshold witness to
all sufficiently fine right-dyadic approximations. -/
private theorem eventually_lt_dyadicRightApprox_of_lt
    {ω : Ω} {t : NNReal} {c : ℝ} (hc : X t ω < c) :
    ∃ N : ℕ, ∀ m : ℕ, X (dyadicRightApprox t (N + m)) ω < c := by
  have hstrict :
      ∀ᶠ s in 𝓝[Set.Ici t] t, X s ω < c := by
    -- Proof comment: the same right-neighborhood argument works for an upper barrier `c`.
    simpa [Set.mem_Iio] using (hX_rc ω t) (Iio_mem_nhds hc)
  have happrox_mem : ∀ᶠ n : ℕ in atTop, dyadicRightApprox t n ∈ Set.Ici t := by
    -- Proof comment: the dyadic approximants remain inside the right-continuity domain.
    exact Eventually.of_forall fun n ↦ le_dyadicRightApprox t n
  have happrox :
      Tendsto (dyadicRightApprox t) atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_dyadicRightApprox t) happrox_mem
  have hstrictApprox : ∀ᶠ n : ℕ in atTop, X (dyadicRightApprox t n) ω < c :=
    happrox hstrict
  rw [Filter.eventually_atTop] at hstrictApprox
  rcases hstrictApprox with ⟨N, hN⟩
  exact ⟨N, fun m ↦ hN (N + m) (Nat.le_add_right N m)⟩

omit hX_rc in
/-- Helper for Exercise 21.4.2: every fixed dyadic row has almost surely finite rational
upcrossings on one rational interval under the ambient continuous-time uniform `L¹` bound. -/
private theorem dyadicRowUpcrossingsAeLtTopRat
    (hX : Submartingale X ℱ μ)
    (hbounded : ∃ R : NNReal, ∀ t : NNReal, eLpNorm (X t) 1 μ ≤ R)
    (n : ℕ) {a b : ℚ} (hab : a < b) :
    ∀ᵐ ω ∂μ, upcrossings (a : ℝ) (b : ℝ) (dyadicRowProcess X n) ω < ∞ := by
  have hrow :
      Submartingale (dyadicRowProcess X n) (dyadicRowFiltration ℱ n) μ := by
    -- Proof comment: deterministic monotone sampling turns the `n`-th dyadic row into a discrete
    -- submartingale.
    simpa [dyadicRowProcess, dyadicRowFiltration] using
      sampledSubmartingaleOfMonotone (X := X) (ℱ := ℱ) (μ := μ) hX (monotone_dyadicTime n)
  rcases hbounded with ⟨R, hR⟩
  -- Proof comment: the ambient `L¹` bound restricts termwise to the dyadic row, so the discrete
  -- upcrossing theorem applies directly.
  exact hrow.upcrossings_ae_lt_top' (R := R) (a := (a : ℝ)) (b := (b : ℝ))
    (hab := Rat.cast_lt.2 hab) fun k ↦ by
    simpa [dyadicRowProcess] using hR (dyadicTime n k)

omit hX_rc in
/-- Helper for Exercise 21.4.2: outside one full-measure event, every dyadic row has finite
rational upcrossings. -/
private theorem ae_allDyadicRowUpcrossingsAeLtTop
    (hX : Submartingale X ℱ μ)
    (hbounded : ∃ R : NNReal, ∀ t : NNReal, eLpNorm (X t) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ,
      ∀ n : ℕ, ∀ a b : ℚ, a < b →
        upcrossings (a : ℝ) (b : ℝ) (dyadicRowProcess X n) ω < ∞ := by
  -- Proof comment: intersect the rowwise discrete upcrossing events over the countable family of
  -- dyadic rows and rational intervals.
  simp only [ae_all_iff, eventually_imp_distrib_left]
  intro n a b hab
  exact dyadicRowUpcrossingsAeLtTopRat
    (X := X) (ℱ := ℱ) (μ := μ) hX hbounded n hab

omit hX_rc in
/-- Helper for Exercise 21.4.2: the finer dyadic row agrees with the coarser row on even indices. -/
private theorem dyadicRowProcess_refine_even
    (n k : ℕ) (ω : Ω) :
    dyadicRowProcess X (n + 1) (2 * k) ω = dyadicRowProcess X n k ω := by
  -- Proof comment: the mesh `2 ^ (-(n + 1))` hits the coarser mesh `2 ^ (-n)` exactly at even
  -- indices.
  unfold dyadicRowProcess dyadicTime
  have htwo : (2 : NNReal) ≠ 0 := by positivity
  calc
    X (((2 * k : ℕ) : NNReal) / (2 : NNReal) ^ (n + 1)) ω
        = X (((k : NNReal) * 2) / ((2 : NNReal) ^ n * 2)) ω := by
            simp [Nat.cast_mul, pow_succ, mul_assoc, mul_left_comm, mul_comm]
    _ = X ((k : NNReal) / (2 : NNReal) ^ n) ω := by
          rw [mul_div_mul_right _ _ htwo]

omit hX_rc in
/-- Helper for Exercise 21.4.2: every coarse dyadic crossing already appears in the next finer row
no later than the corresponding even index. -/
private theorem dyadicRowCrossingTime_le_refine
    {a b : ℝ} (n N k : ℕ) (ω : Ω) :
    upperCrossingTime a b (dyadicRowProcess X (n + 1)) (2 * N) k ω ≤
        2 * upperCrossingTime a b (dyadicRowProcess X n) N k ω ∧
      lowerCrossingTime a b (dyadicRowProcess X (n + 1)) (2 * N) k ω ≤
        2 * lowerCrossingTime a b (dyadicRowProcess X n) N k ω := by
  induction k with
  | zero =>
      refine ⟨by simp, ?_⟩
      by_cases hcoarse : lowerCrossingTime a b (dyadicRowProcess X n) N 0 ω = N
      · -- Proof comment: if the coarse lower crossing already stabilized at the horizon, the
        -- refined lower crossing is automatically bounded by the doubled horizon.
        simpa [hcoarse] using
          (lowerCrossingTime_le
            (a := a) (b := b) (f := dyadicRowProcess X (n + 1)) (N := 2 * N) (n := 0) (ω := ω))
      · have hcoarse_lt :
            lowerCrossingTime a b (dyadicRowProcess X n) N 0 ω < N :=
          lt_of_le_of_ne lowerCrossingTime_le hcoarse
        have hmem :
            dyadicRowProcess X n (lowerCrossingTime a b (dyadicRowProcess X n) N 0 ω) ω ∈
              Set.Iic a := by
          -- Proof comment: once the coarse lower crossing is strictly before the horizon, the
          -- hitting-time API certifies that the process is already below the lower barrier there.
          simpa [lowerCrossingTime] using
            (hittingBtwn_mem_set_of_hittingBtwn_lt
              (u := dyadicRowProcess X n) (s := Set.Iic a)
              (n := upperCrossingTime a b (dyadicRowProcess X n) N 0 ω)
              (m := N) (ω := ω) hcoarse_lt)
        have hmem_refined :
            dyadicRowProcess X (n + 1)
                (2 * lowerCrossingTime a b (dyadicRowProcess X n) N 0 ω) ω ∈
              Set.Iic a := by
          have hrefine :
              dyadicRowProcess X (n + 1)
                  (2 * hittingBtwn (dyadicRowProcess X n) (Set.Iic a) 0 N ω) ω =
                dyadicRowProcess X n
                  (hittingBtwn (dyadicRowProcess X n) (Set.Iic a) 0 N ω) ω := by
            simpa [lowerCrossingTime] using
              (dyadicRowProcess_refine_even (X := X) (n := n)
                (k := lowerCrossingTime a b (dyadicRowProcess X n) N 0 ω) (ω := ω))
          simpa [lowerCrossingTime, Set.mem_Iic, hrefine] using hmem
        -- Proof comment: the same even index is a valid lower-crossing witness in the refined row.
        rw [lowerCrossingTime]
        refine hittingBtwn_le_of_mem ?_ ?_ hmem_refined
        · simp
        · exact Nat.mul_le_mul_left 2 lowerCrossingTime_le
  | succ k ih =>
      have ihUpper := ih.1
      have ihLower := ih.2
      have hUpper :
          upperCrossingTime a b (dyadicRowProcess X (n + 1)) (2 * N) (k + 1) ω ≤
            2 * upperCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω := by
        by_cases hcoarse : upperCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω = N
        · -- Proof comment: if the coarse upper crossing already stabilized at the horizon, the
          -- refined upper crossing is bounded by the doubled horizon for free.
          simpa [hcoarse] using
            (upperCrossingTime_le
              (a := a) (b := b) (f := dyadicRowProcess X (n + 1)) (N := 2 * N)
              (n := k + 1) (ω := ω))
        · have hcoarse_lt :
              upperCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω < N :=
            lt_of_le_of_ne upperCrossingTime_le hcoarse
          have hmem :
              dyadicRowProcess X n (upperCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω) ω ∈
                Set.Ici b := by
            -- Proof comment: a genuine coarse upper crossing supplies an above-barrier witness in
            -- the refined row at the doubled index.
            simpa [upperCrossingTime_succ_eq (ω := ω)] using
              (hittingBtwn_mem_set_of_hittingBtwn_lt
                (u := dyadicRowProcess X n) (s := Set.Ici b)
                (n := lowerCrossingTime a b (dyadicRowProcess X n) N k ω)
                (m := N) (ω := ω) hcoarse_lt)
          have hmem_refined :
              dyadicRowProcess X (n + 1)
                  (2 * upperCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω) ω ∈
                Set.Ici b := by
            have hrefine :
                dyadicRowProcess X (n + 1)
                    (2 * upperCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω) ω =
                  dyadicRowProcess X n
                    (upperCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω) ω := by
              simpa using
                (dyadicRowProcess_refine_even (X := X) (n := n)
                  (k := upperCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω) (ω := ω))
            simpa [Set.mem_Ici, hrefine] using hmem
          rw [upperCrossingTime_succ_eq ω]
          refine hittingBtwn_le_of_mem ?_ ?_ hmem_refined
          · exact le_trans ihLower (Nat.mul_le_mul_left 2 lowerCrossingTime_le_upperCrossingTime_succ)
          · exact Nat.mul_le_mul_left 2 upperCrossingTime_le
      have hLower :
          lowerCrossingTime a b (dyadicRowProcess X (n + 1)) (2 * N) (k + 1) ω ≤
            2 * lowerCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω := by
        by_cases hcoarse : lowerCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω = N
        · -- Proof comment: the same stabilization argument handles the lower crossing.
          simpa [hcoarse] using
            (lowerCrossingTime_le
              (a := a) (b := b) (f := dyadicRowProcess X (n + 1)) (N := 2 * N)
              (n := k + 1) (ω := ω))
        · have hcoarse_lt :
              lowerCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω < N :=
            lt_of_le_of_ne lowerCrossingTime_le hcoarse
          have hmem :
              dyadicRowProcess X n (lowerCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω) ω ∈
                Set.Iic a := by
            -- Proof comment: after the refined upper crossing, the doubled coarse lower crossing
            -- is still a valid lower-barrier witness.
            simpa [lowerCrossingTime] using
              (hittingBtwn_mem_set_of_hittingBtwn_lt
                (u := dyadicRowProcess X n) (s := Set.Iic a)
                (n := upperCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω)
                (m := N) (ω := ω) hcoarse_lt)
          have hmem_refined :
              dyadicRowProcess X (n + 1)
                  (2 * lowerCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω) ω ∈
                Set.Iic a := by
            have hrefine :
                dyadicRowProcess X (n + 1)
                    (2 * lowerCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω) ω =
                  dyadicRowProcess X n
                    (lowerCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω) ω := by
              simpa using
                (dyadicRowProcess_refine_even (X := X) (n := n)
                  (k := lowerCrossingTime a b (dyadicRowProcess X n) N (k + 1) ω) (ω := ω))
            simpa [Set.mem_Iic, hrefine] using hmem
          rw [lowerCrossingTime]
          refine hittingBtwn_le_of_mem ?_ ?_ hmem_refined
          · exact le_trans hUpper (Nat.mul_le_mul_left 2 upperCrossingTime_le_lowerCrossingTime)
          · exact Nat.mul_le_mul_left 2 lowerCrossingTime_le
      exact ⟨hUpper, hLower⟩

omit hX_rc in
/-- Helper for Exercise 21.4.2: refining the dyadic mesh cannot decrease finite-horizon
upcrossings. -/
private theorem dyadicRowUpcrossingsBefore_le_succ
    {a b : ℝ} (hab : a < b) (n N : ℕ) (ω : Ω) :
    upcrossingsBefore a b (dyadicRowProcess X n) N ω ≤
      upcrossingsBefore a b (dyadicRowProcess X (n + 1)) (2 * N) ω := by
  -- Proof comment: every coarse upper crossing remains a genuine upper crossing in the next finer
  -- row before the doubled horizon.
  simp only [upcrossingsBefore]
  gcongr sSup {k | ?_} with k
  · exact upperCrossingTime_lt_bddAbove hab
  · intro hk
    exact lt_of_le_of_lt
      (dyadicRowCrossingTime_le_refine (X := X) (a := a) (b := b) n N k ω).1
      (Nat.mul_lt_mul_of_pos_left hk (by decide))

omit hX_rc in
/-- Helper for Exercise 21.4.2: the full dyadic upcrossing count is monotone under row
refinement. -/
private theorem dyadicRowUpcrossings_mono
    {a b : ℚ} (hab : a < b) (ω : Ω) :
    Monotone (fun n ↦ upcrossings (a : ℝ) (b : ℝ) (dyadicRowProcess X n) ω) := by
  -- Proof comment: after taking the supremum over horizons, the finite-horizon refinement bound
  -- becomes monotonicity of the full dyadic envelope.
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [upcrossings]
  refine iSup_le fun N ↦ ?_
  refine le_iSup_of_le (2 * N) ?_
  exact_mod_cast
    (dyadicRowUpcrossingsBefore_le_succ (X := X) (a := (a : ℝ)) (b := (b : ℝ))
      (hab := Rat.cast_lt.2 hab) n N ω)

omit hX_rc in
/-- Helper for Exercise 21.4.2: the dyadic upcrossing envelope on one rational interval is almost
surely finite under a uniform continuous-time `L¹` bound. -/
private theorem aeLtTop_dyadicRowUpcrossingsSup
    (hX : Submartingale X ℱ μ)
    (hbounded : ∃ R : NNReal, ∀ t : NNReal, eLpNorm (X t) 1 μ ≤ R)
    {a b : ℚ} (hab : a < b) :
    ∀ᵐ ω ∂μ, (⨆ n : ℕ, upcrossings (a : ℝ) (b : ℝ) (dyadicRowProcess X n) ω) < ∞ := by
  -- Route correction: rowwise finiteness is too weak, so the right replacement is a single
  -- monotone dyadic envelope whose integral is still controlled by the discrete upcrossing bound.
  rcases hbounded with ⟨R, hR⟩
  let U : ℕ → Ω → ℝ≥0∞ := fun n ω ↦
    upcrossings (a : ℝ) (b : ℝ) (dyadicRowProcess X n) ω
  let C : ℝ≥0∞ := R + ‖(a : ℝ)‖₊ * μ Set.univ
  have hR' : ∀ t : NNReal, ∫⁻ ω, ‖X t ω - (a : ℝ)‖₊ ∂μ ≤ C := by
    -- Proof comment: the ambient `L¹` bound also controls the shifted norms that appear in Doob's
    -- upcrossing inequality.
    simp_rw [eLpNorm_one_eq_lintegral_enorm] at hR
    intro t
    refine (lintegral_mono ?_ :
      ∫⁻ ω, ‖X t ω - (a : ℝ)‖₊ ∂μ ≤ ∫⁻ ω, ‖X t ω‖₊ + ‖(a : ℝ)‖₊ ∂μ).trans ?_
    · intro ω
      simp_rw [sub_eq_add_neg, ← nnnorm_neg (a : ℝ), ← ENNReal.coe_add, ENNReal.coe_le_coe]
      exact nnnorm_add_le _ _
    · simp_rw [lintegral_add_right _ measurable_const, lintegral_const]
      exact add_le_add (hR t) le_rfl
  have hrow : ∀ n, Submartingale (dyadicRowProcess X n) (dyadicRowFiltration ℱ n) μ := by
    intro n
    -- Proof comment: each dyadic row is still a discrete submartingale under deterministic
    -- monotone sampling.
    simpa [dyadicRowProcess, dyadicRowFiltration] using
      sampledSubmartingaleOfMonotone (X := X) (ℱ := ℱ) (μ := μ) hX (monotone_dyadicTime n)
  have hmeas : ∀ n, Measurable (U n) := by
    intro n
    -- Proof comment: measurability comes from the discrete strong-adaptation API on each row.
    exact (hrow n).stronglyAdapted.measurable_upcrossings (Rat.cast_lt.2 hab)
  have hrowBound :
      ∀ n, ∫⁻ ω, U n ω ∂μ ≤ C / ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
    intro n
    have hup :
        ENNReal.ofReal ((b : ℝ) - (a : ℝ)) * ∫⁻ ω, U n ω ∂μ ≤
          ⨆ N, ∫⁻ ω, ENNReal.ofReal ((dyadicRowProcess X n N ω - (a : ℝ))⁺) ∂μ := by
      simpa [U] using
        (hrow n).mul_lintegral_upcrossings_le_lintegral_pos_part (a := (a : ℝ)) (b := (b : ℝ))
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le] at hup
    · refine hup.trans ?_
      gcongr
      refine iSup_le fun N ↦ ?_
      have hpointwise :
          ∀ ω,
            ENNReal.ofReal ((dyadicRowProcess X n N ω - (a : ℝ))⁺) ≤
              ‖X (dyadicTime n N) ω - (a : ℝ)‖₊ := by
        intro ω
        rw [dyadicRowProcess, ENNReal.ofReal_le_iff_le_toReal, ENNReal.coe_toReal, coe_nnnorm]
        · by_cases! hnonneg : 0 ≤ X (dyadicTime n N) ω - (a : ℝ)
          · rw [posPart_eq_self.2 hnonneg, Real.norm_eq_abs, abs_of_nonneg hnonneg]
          · rw [posPart_eq_zero.2 hnonneg.le]
            exact norm_nonneg _
        · finiteness
      exact (lintegral_mono hpointwise).trans (by simpa [C, dyadicRowProcess] using hR' (dyadicTime n N))
    · left
      simp only [Ne, ENNReal.ofReal_eq_zero, sub_nonpos, not_le]
      exact Rat.cast_lt.2 hab
    · left
      finiteness
  have hlintegral :
      ∫⁻ ω, (⨆ n : ℕ, U n ω) ∂μ = ⨆ n : ℕ, ∫⁻ ω, U n ω ∂μ := by
    -- Proof comment: the dyadic envelope is monotone in the row index, so monotone convergence
    -- moves the row supremum outside the integral.
    rw [lintegral_iSup']
    · intro n
      exact (hmeas n).aemeasurable
    · filter_upwards with ω n m hnm
      exact dyadicRowUpcrossings_mono (X := X) hab ω hnm
  have hEnvelopeBound :
      ∫⁻ ω, (⨆ n : ℕ, U n ω) ∂μ ≤ C / ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
    rw [hlintegral]
    exact iSup_le hrowBound
  have hEnvelopeMeas :
      Measurable (fun ω ↦ ⨆ n : ℕ, U n ω) := by
    exact Measurable.iSup fun n ↦ hmeas n
  -- Proof comment: finite integral of the monotone dyadic envelope implies almost-sure finiteness.
  have hEnvelopeFinite :
      ∫⁻ ω, (⨆ n : ℕ, U n ω) ∂μ ≠ ⊤ := by
    refine (lt_of_le_of_lt hEnvelopeBound ?_).ne
    have hden : ENNReal.ofReal ((b : ℝ) - (a : ℝ)) ≠ 0 := by
      have hsubpos : 0 < (b : ℝ) - (a : ℝ) := sub_pos.mpr (Rat.cast_lt.2 hab)
      exact (ENNReal.ofReal_pos.mpr hsubpos).ne'
    exact ENNReal.div_lt_top
      (by simpa [C] using ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, by simp⟩)
      hden
  filter_upwards [ae_lt_top hEnvelopeMeas hEnvelopeFinite] with ω hω
  exact hω

omit hX_rc in
/-- Helper for Exercise 21.4.2: a finite dyadic envelope yields one uniform natural-number bound
for all dyadic-row finite-horizon upcrossing counts on the same inner interval. -/
private theorem natBoundOfDyadicUpcrossingsBeforeEnvelope
    {ω : Ω} {a' b' : ℚ}
    (hω_sup :
      (⨆ n : ℕ, upcrossings (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n) ω) < ∞) :
    ∃ K : ℕ, ∀ n N : ℕ,
      upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n) N ω ≤ K := by
  let envelope : ℝ≥0∞ :=
    ⨆ n : ℕ, upcrossings (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n) ω
  lift envelope to NNReal using hω_sup.ne with r hr
  obtain ⟨K, hK⟩ := exists_nat_ge r
  refine ⟨K, ?_⟩
  intro n N
  have hBefore :
      (upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n) N ω : ℝ≥0∞) ≤
        upcrossings (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n) ω := by
    exact le_iSup (fun M : ℕ =>
      (upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n) M ω : ℝ≥0∞)) N
  have hRow :
      upcrossings (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n) ω ≤
        envelope := by
    exact le_iSup (fun m : ℕ =>
      upcrossings (a' : ℝ) (b' : ℝ) (dyadicRowProcess X m) ω) n
  have hEnvelopeLe : envelope ≤ (K : ℝ≥0∞) := by
    have hrK : (r : ℝ≥0∞) ≤ (K : ℝ≥0∞) := by
      exact_mod_cast hK
    simpa [hr] using hrK
  -- Proof comment: each finite-horizon count is bounded first by its rowwise full upcrossing
  -- count and then by the global dyadic envelope bound.
  simpa using hBefore.trans (hRow.trans hEnvelopeLe)

omit hX_rc in
/-- Helper for Exercise 21.4.2: successive inner-barrier witnesses along one dyadic row force the
finite-horizon upcrossing count to exceed the length of the witness prefix. -/
private theorem lt_upcrossingsBefore_ofDyadicWitnessPrefix
    {ω : Ω} {a' b' : ℚ} {K n0 : ℕ}
    (habInner : (a' : ℝ) < (b' : ℝ))
    (lowerIndex upperIndex : Fin (K + 1) → ℕ)
    (hLowerValue :
      ∀ k : Fin (K + 1), dyadicRowProcess X n0 (lowerIndex k) ω < (a' : ℝ))
    (hUpperValue :
      ∀ k : Fin (K + 1), (b' : ℝ) < dyadicRowProcess X n0 (upperIndex k) ω)
    (hLowerLeUpper : ∀ k : Fin (K + 1), lowerIndex k ≤ upperIndex k)
    (hUpperLeNextLower :
      ∀ j : ℕ, ∀ hj : j < K,
        upperIndex ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
          lowerIndex ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩) :
    K < upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n0)
      (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1) ω := by
  have hPrefix :
      ∀ j : ℕ, ∀ hj : j ≤ K,
        j < upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n0)
          (upperIndex ⟨j, Nat.lt_succ_of_le hj⟩ + 1) ω := by
    intro j
    induction j with
    | zero =>
        intro hj
        let k0 : Fin (K + 1) := ⟨0, Nat.succ_pos _⟩
        have hStep :
            upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n0) 0 ω <
              upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n0)
                (upperIndex k0 + 1) ω := by
          -- Proof comment: the first lower and upper witnesses already realize one inner
          -- upcrossing on the chosen dyadic row.
          refine upcrossingsBefore_lt_of_exists_upcrossing
            (a := (a' : ℝ)) (b := (b' : ℝ)) (f := dyadicRowProcess X n0)
            (N := 0) (N₁ := lowerIndex k0) (N₂ := upperIndex k0) (ω := ω)
            habInner ?_ ?_ ?_ ?_
          · exact zero_le (lowerIndex k0)
          · exact hLowerValue k0
          · exact hLowerLeUpper k0
          · exact hUpperValue k0
        simpa [k0, upcrossingsBefore_zero] using hStep
    | succ j ih =>
        intro hj
        have hj' : j ≤ K := Nat.le_of_succ_le hj
        let kj : Fin (K + 1) := ⟨j, Nat.lt_succ_of_le hj'⟩
        let kj1 : Fin (K + 1) := ⟨j + 1, Nat.lt_succ_of_le hj⟩
        have hjlt : j < K := lt_of_lt_of_le (Nat.lt_succ_self j) hj
        have hSep : upperIndex kj < lowerIndex kj1 := by
          have hWeak : upperIndex kj ≤ lowerIndex kj1 := hUpperLeNextLower j hjlt
          refine lt_of_le_of_ne hWeak ?_
          intro hEq
          have hUpperLt :
              dyadicRowProcess X n0 (upperIndex kj) ω < (a' : ℝ) := by
            simpa [hEq] using hLowerValue kj1
          exact (not_lt_of_ge habInner.le) (lt_trans (hUpperValue kj) hUpperLt)
        have hStep :
            upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n0) (upperIndex kj + 1) ω <
              upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n0)
                (upperIndex kj1 + 1) ω := by
          -- Proof comment: once the next lower witness occurs strictly after the previous upper
          -- witness, the discrete upcrossing counter increases by one more.
          refine upcrossingsBefore_lt_of_exists_upcrossing
            (a := (a' : ℝ)) (b := (b' : ℝ)) (f := dyadicRowProcess X n0)
            (N := upperIndex kj + 1) (N₁ := lowerIndex kj1) (N₂ := upperIndex kj1) (ω := ω)
            habInner ?_ ?_ ?_ ?_
          · exact Nat.succ_le_of_lt hSep
          · exact hLowerValue kj1
          · exact hLowerLeUpper kj1
          · exact hUpperValue kj1
        have ihSucc :
            j + 1 ≤ upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n0)
              (upperIndex kj + 1) ω := by
          exact Nat.succ_le_of_lt (ih hj')
        exact lt_of_le_of_lt ihSucc hStep
  exact hPrefix K le_rfl

omit hX_rc in
/-- Helper for Exercise 21.4.2: if the `(k + 1)`-st continuous upper crossing were not before the
horizon, then the finite-horizon upcrossing count could not exceed `k`. -/
private theorem upperCrossingTime_lt_of_lt_upcrossingsBeforeNNReal
    {ω : Ω} {a b : ℝ} {T : NNReal} (hT : 0 < T) {k : ℕ}
    (hk : k < upcrossingsBefore a b X T ω) :
    upperCrossingTime a b X T (k + 1) ω < T := by
  by_contra hUpper
  have hSupLe : upcrossingsBefore a b X T ω ≤ k := by
    -- Proof comment: if the `(k + 1)`-st upper crossing already hit the horizon, monotonicity of
    -- crossing times rules out any witness index strictly larger than `k`.
    simp only [upcrossingsBefore]
    refine csSup_le ?_ ?_
    · refine ⟨0, ?_⟩
      simpa using hT
    · intro n hn
      by_contra hkn
      have hk1n : k + 1 ≤ n := Nat.succ_le_of_lt (lt_of_not_ge hkn)
      exact hUpper <| lt_of_le_of_lt
        (upperCrossingTime_mono (a := a) (b := b) (f := X) (N := T) (ω := ω) hk1n) hn
  exact not_lt_of_ge hSupLe hk

omit hX_rc in
/-- Helper for Exercise 21.4.2: every realized continuous lower crossing in a finite prefix occurs
strictly before the horizon. -/
private theorem lowerCrossingTime_lt_of_lt_upcrossingsBeforeNNReal
    {ω : Ω} {a b : ℝ} {T : NNReal} (hT : 0 < T) {k : ℕ}
    (hk : k < upcrossingsBefore a b X T ω) :
    lowerCrossingTime a b X T k ω < T := by
  -- Proof comment: each lower crossing in the finite prefix sits before the next upper crossing,
  -- which itself must already occur before the horizon.
  exact lt_of_le_of_lt
    (lowerCrossingTime_le_upperCrossingTime_succ (a := a) (b := b) (f := X) (N := T)
      (n := k) (ω := ω))
    (upperCrossingTime_lt_of_lt_upcrossingsBeforeNNReal (X := X) hT hk)

/-- Helper for Exercise 21.4.2: a realized continuous lower crossing before the horizon lands in
the lower barrier `Set.Iic a`. -/
private theorem lowerCrossingValue_le_of_ltNNReal
    {ω : Ω} {a b : ℝ} {T : NNReal} {k : ℕ}
    (hk : lowerCrossingTime a b X T k ω < T) :
    X (lowerCrossingTime a b X T k ω) ω ≤ a := by
  classical
  let s : Set NNReal :=
    Set.Icc (upperCrossingTime a b X T k ω) T ∩ {t : NNReal | X t ω ∈ Set.Iic a}
  have hs_exists : ∃ j ∈ Set.Icc (upperCrossingTime a b X T k ω) T, X j ω ∈ Set.Iic a := by
    by_contra hs_exists
    have hEq : lowerCrossingTime a b X T k ω = T := by
      rw [lowerCrossingTime, hittingBtwn, if_neg hs_exists]
    exact hk.ne hEq
  have hs_nonempty : s.Nonempty := by
    rcases hs_exists with ⟨j, hjIcc, hjmem⟩
    exact ⟨j, ⟨hjIcc, hjmem⟩⟩
  have hs_bddBelow : BddBelow s := by
    dsimp [s]
    exact bddBelow_Icc.inter_of_left
  have hs_eq :
      lowerCrossingTime a b X T k ω = sInf s := by
    rw [lowerCrossingTime, hittingBtwn, if_pos hs_exists]
  have hs_closure : lowerCrossingTime a b X T k ω ∈ closure s := by
    rw [hs_eq]
    exact csInf_mem_closure hs_nonempty hs_bddBelow
  have hs_subset :
      s ⊆ Set.Ici (lowerCrossingTime a b X T k ω) := by
    intro t ht
    rw [hs_eq]
    exact (isGLB_csInf hs_nonempty hs_bddBelow).1 ht
  have hcont :
      ContinuousWithinAt (fun t : NNReal ↦ X t ω) s (lowerCrossingTime a b X T k ω) :=
    (hX_rc ω (lowerCrossingTime a b X T k ω)).mono hs_subset
  have hmaps : MapsTo (fun t : NNReal ↦ X t ω) s (Set.Iic a) := by
    intro t ht
    exact ht.2
  have hmem_closure : X (lowerCrossingTime a b X T k ω) ω ∈ closure (Set.Iic a) :=
    hcont.mem_closure hs_closure hmaps
  rw [isClosed_Iic.closure_eq] at hmem_closure
  simpa [Set.mem_Iic] using hmem_closure

/-- Helper for Exercise 21.4.2: a realized continuous upper crossing before the horizon lands in
the upper barrier `Set.Ici b`. -/
private theorem upperCrossingValue_ge_of_ltNNReal
    {ω : Ω} {a b : ℝ} {T : NNReal} {k : ℕ}
    (hk : upperCrossingTime a b X T (k + 1) ω < T) :
    b ≤ X (upperCrossingTime a b X T (k + 1) ω) ω := by
  classical
  let s : Set NNReal :=
    Set.Icc (lowerCrossingTime a b X T k ω) T ∩ {t : NNReal | X t ω ∈ Set.Ici b}
  have hs_exists : ∃ j ∈ Set.Icc (lowerCrossingTime a b X T k ω) T, X j ω ∈ Set.Ici b := by
    by_contra hs_exists
    have hEq : upperCrossingTime a b X T (k + 1) ω = T := by
      rw [upperCrossingTime_succ_eq, hittingBtwn, if_neg hs_exists]
    exact hk.ne hEq
  have hs_nonempty : s.Nonempty := by
    rcases hs_exists with ⟨j, hjIcc, hjmem⟩
    exact ⟨j, ⟨hjIcc, hjmem⟩⟩
  have hs_bddBelow : BddBelow s := by
    dsimp [s]
    exact bddBelow_Icc.inter_of_left
  have hs_eq :
      upperCrossingTime a b X T (k + 1) ω = sInf s := by
    rw [upperCrossingTime_succ_eq, hittingBtwn, if_pos hs_exists]
  have hs_closure : upperCrossingTime a b X T (k + 1) ω ∈ closure s := by
    rw [hs_eq]
    exact csInf_mem_closure hs_nonempty hs_bddBelow
  have hs_subset :
      s ⊆ Set.Ici (upperCrossingTime a b X T (k + 1) ω) := by
    intro t ht
    rw [hs_eq]
    exact (isGLB_csInf hs_nonempty hs_bddBelow).1 ht
  have hcont :
      ContinuousWithinAt (fun t : NNReal ↦ X t ω) s (upperCrossingTime a b X T (k + 1) ω) :=
    (hX_rc ω (upperCrossingTime a b X T (k + 1) ω)).mono hs_subset
  have hmaps : MapsTo (fun t : NNReal ↦ X t ω) s (Set.Ici b) := by
    intro t ht
    exact ht.2
  have hmem_closure : X (upperCrossingTime a b X T (k + 1) ω) ω ∈ closure (Set.Ici b) :=
    hcont.mem_closure hs_closure hmaps
  rw [isClosed_Ici.closure_eq] at hmem_closure
  simpa [Set.mem_Ici] using hmem_closure

/-- Helper for Exercise 21.4.2: a strict lower-barrier witness at a continuous lower crossing
persists on all sufficiently fine right-dyadic samples of one row. -/
private theorem eventuallyDyadicRowLtOfLowerCrossing
    {ω : Ω} {a a' b : ℚ} {T : NNReal} {k : ℕ}
    (hT : 0 < T)
    (hk : k < upcrossingsBefore (a : ℝ) (b : ℝ) X T ω)
    (haa' : a < a') :
    ∃ N : ℕ, ∀ n ≥ N,
      dyadicRowProcess X n
        (Nat.ceil (((lowerCrossingTime (a : ℝ) (b : ℝ) X T k ω : NNReal) : ℝ) *
          (2 : ℝ) ^ n)) ω < (a' : ℝ) := by
  have hltT :
      lowerCrossingTime (a : ℝ) (b : ℝ) X T k ω < T :=
    lowerCrossingTime_lt_of_lt_upcrossingsBeforeNNReal (X := X) hT hk
  have hLowerLe :
      X (lowerCrossingTime (a : ℝ) (b : ℝ) X T k ω) ω ≤ (a : ℝ) :=
    lowerCrossingValue_le_of_ltNNReal (X := X) (hX_rc := hX_rc) hltT
  have hStrict :
      X (lowerCrossingTime (a : ℝ) (b : ℝ) X T k ω) ω < (a' : ℝ) :=
    lt_of_le_of_lt hLowerLe (Rat.cast_lt.2 haa')
  -- Route correction: use the direct crossing-value adapter first, then transport the strict
  -- inner-barrier inequality to the dyadic right-approximants by right continuity.
  rcases eventually_lt_dyadicRightApprox_of_lt
      (X := X)
      (hX_rc := hX_rc)
      (ω := ω)
      (t := lowerCrossingTime (a : ℝ) (b : ℝ) X T k ω)
      (c := (a' : ℝ))
      hStrict with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- Proof comment: after rewriting the dyadic row sample as the right-dyadic approximation,
  -- the eventual inequality is exactly the transported right-continuity estimate.
  simpa [dyadicRowProcess_rightApprox] using hN m

/-- Helper for Exercise 21.4.2: a strict upper-barrier witness at a continuous upper crossing
persists on all sufficiently fine right-dyadic samples of one row. -/
private theorem eventuallyDyadicRowGtOfUpperCrossing
    {ω : Ω} {a b' b : ℚ} {T : NNReal} {k : ℕ}
    (hT : 0 < T)
    (hk : k < upcrossingsBefore (a : ℝ) (b : ℝ) X T ω)
    (hb'b : b' < b) :
    ∃ N : ℕ, ∀ n ≥ N,
      (b' : ℝ) <
        dyadicRowProcess X n
          (Nat.ceil (((upperCrossingTime (a : ℝ) (b : ℝ) X T (k + 1) ω : NNReal) : ℝ) *
            (2 : ℝ) ^ n)) ω := by
  have hltT :
      upperCrossingTime (a : ℝ) (b : ℝ) X T (k + 1) ω < T :=
    upperCrossingTime_lt_of_lt_upcrossingsBeforeNNReal (X := X) hT hk
  have hUpperGe :
      (b : ℝ) ≤ X (upperCrossingTime (a : ℝ) (b : ℝ) X T (k + 1) ω) ω :=
    upperCrossingValue_ge_of_ltNNReal (X := X) (hX_rc := hX_rc) hltT
  have hStrict :
      (b' : ℝ) < X (upperCrossingTime (a : ℝ) (b : ℝ) X T (k + 1) ω) ω :=
    lt_of_lt_of_le (Rat.cast_lt.2 hb'b) hUpperGe
  -- Route correction: the upper-threshold transport is the exact analogue of the lower one after
  -- inserting the direct `hittingBtwn`-to-value bridge.
  rcases eventually_gt_dyadicRightApprox_of_lt
      (X := X)
      (hX_rc := hX_rc)
      (ω := ω)
      (t := upperCrossingTime (a : ℝ) (b : ℝ) X T (k + 1) ω)
      (c := (b' : ℝ))
      hStrict with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- Proof comment: rewrite the sampled dyadic row value back to the right-dyadic approximation
  -- and apply the eventual strict lower bound.
  simpa [dyadicRowProcess_rightApprox] using hN m

omit hX_rc in
/-- Helper for Exercise 21.4.2: for `NNReal`-indexed paths, finite total upcrossings are
equivalent to one uniform natural-number bound on every finite horizon. -/
private theorem upcrossingsLtTopNNReal_iff
    {ω : Ω} {a b : ℝ} :
    upcrossings a b X ω < ∞ ↔ ∃ k, ∀ T : NNReal, upcrossingsBefore a b X T ω ≤ k := by
  -- Proof comment: the discrete mathlib proof only uses the `iSup` definition of full
  -- upcrossings, so the same argument applies verbatim to the `NNReal` time index.
  have htop : upcrossings a b X ω < ∞ ↔ ∃ r : NNReal, upcrossings a b X ω ≤ r := by
    constructor
    · intro h
      lift upcrossings a b X ω to NNReal using h.ne with r hr
      exact ⟨r, le_rfl⟩
    · rintro ⟨r, hr⟩
      exact lt_of_le_of_lt hr ENNReal.coe_lt_top
  constructor
  · intro h
    rcases htop.mp h with ⟨r, hr⟩
    obtain ⟨k, hk⟩ := exists_nat_ge r
    refine ⟨k, fun T ↦ ?_⟩
    have hT :
        (upcrossingsBefore a b X T ω : ℝ≥0∞) ≤ r := by
      exact (le_iSup (fun N ↦ (upcrossingsBefore a b X N ω : ℝ≥0∞)) T).trans hr
    have hT' : ((upcrossingsBefore a b X T ω : ℕ) : NNReal) ≤ r :=
      ENNReal.coe_le_coe.mp hT
    exact_mod_cast hT'.trans hk
  · rintro ⟨k, hk⟩
    exact htop.mpr ⟨k, by
      rw [upcrossings]
      refine iSup_le fun T ↦ ?_
      exact_mod_cast hk T⟩

/-- Helper for Exercise 21.4.2: a finite dyadic upcrossing envelope on an inner rational interval
forces finite continuous-time upcrossings on every enclosing outer rational interval. -/
private theorem upcrossingsLtTopOfDyadicEnvelope
    {ω : Ω} {a a' b' b : ℚ}
    (haa' : a < a') (ha'b' : a' < b') (hb'b : b' < b)
    (hω_sup :
      (⨆ n : ℕ, upcrossings (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n) ω) < ∞) :
    upcrossings (a : ℝ) (b : ℝ) X ω < ∞ := by
  classical
  rcases natBoundOfDyadicUpcrossingsBeforeEnvelope (X := X) (ω := ω) hω_sup with ⟨K, hK⟩
  have hBound : ∀ T : NNReal, upcrossingsBefore (a : ℝ) (b : ℝ) X T ω ≤ K := by
    intro T
    by_contra hTooMany
    have hTooMany' : K < upcrossingsBefore (a : ℝ) (b : ℝ) X T ω :=
      Nat.lt_of_not_ge hTooMany
    have hT : 0 < T := by
      by_contra hT
      have hT0 : T = 0 := le_antisymm (le_of_not_gt hT) bot_le
      have hZero : upcrossingsBefore (a : ℝ) (b : ℝ) X 0 ω = 0 := by
        simp [upcrossingsBefore]
      have hTooManyZero : K < 0 := by
        simpa [hT0, hZero] using hTooMany'
      exact Nat.not_lt_zero K hTooManyZero
    have hOuterPrefix :
        K + 1 ≤ upcrossingsBefore (a : ℝ) (b : ℝ) X T ω :=
      Nat.succ_le_of_lt hTooMany'
    have hPrefixIndex :
        ∀ j : Fin (K + 1), (j : ℕ) < upcrossingsBefore (a : ℝ) (b : ℝ) X T ω := by
      intro j
      exact lt_of_lt_of_le j.2 hOuterPrefix
    have hLowerEventually :
        ∀ j : Fin (K + 1),
          ∃ N : ℕ, ∀ n ≥ N,
            dyadicRowProcess X n
              (Nat.ceil
                (((lowerCrossingTime (a : ℝ) (b : ℝ) X T (j : ℕ) ω : NNReal) : ℝ) *
                  (2 : ℝ) ^ n)) ω <
              (a' : ℝ) := by
      intro j
      exact eventuallyDyadicRowLtOfLowerCrossing
        (X := X)
        (hX_rc := hX_rc)
        (ω := ω)
        (T := T)
        (k := j)
        hT
        (hPrefixIndex j)
        haa'
    have hUpperEventually :
        ∀ j : Fin (K + 1),
          ∃ N : ℕ, ∀ n ≥ N,
            (b' : ℝ) <
              dyadicRowProcess X n
                (Nat.ceil
                  (((upperCrossingTime (a : ℝ) (b : ℝ) X T ((j : ℕ) + 1) ω : NNReal) : ℝ) *
                    (2 : ℝ) ^ n)) ω := by
      intro j
      exact eventuallyDyadicRowGtOfUpperCrossing
        (X := X)
        (hX_rc := hX_rc)
        (ω := ω)
        (T := T)
        (k := j)
        hT
        (hPrefixIndex j)
        hb'b
    choose lowerStage hLowerStage using hLowerEventually
    choose upperStage hUpperStage using hUpperEventually
    let n0 : ℕ := max (Finset.univ.sup lowerStage) (Finset.univ.sup upperStage)
    let lowerIndex : Fin (K + 1) → ℕ := fun j ↦
      Nat.ceil
        (((lowerCrossingTime (a : ℝ) (b : ℝ) X T (j : ℕ) ω : NNReal) : ℝ) * (2 : ℝ) ^ n0)
    let upperIndex : Fin (K + 1) → ℕ := fun j ↦
      Nat.ceil
        (((upperCrossingTime (a : ℝ) (b : ℝ) X T ((j : ℕ) + 1) ω : NNReal) : ℝ) * (2 : ℝ) ^ n0)
    have hn0_lower : ∀ j : Fin (K + 1), lowerStage j ≤ n0 := by
      intro j
      exact le_trans (Finset.le_sup (s := Finset.univ) (f := lowerStage) (Finset.mem_univ j))
        (le_max_left _ _)
    have hn0_upper : ∀ j : Fin (K + 1), upperStage j ≤ n0 := by
      intro j
      exact le_trans (Finset.le_sup (s := Finset.univ) (f := upperStage) (Finset.mem_univ j))
        (le_max_right _ _)
    have hLowerValue :
        ∀ j : Fin (K + 1), dyadicRowProcess X n0 (lowerIndex j) ω < (a' : ℝ) := by
      intro j
      simpa [lowerIndex] using hLowerStage j n0 (hn0_lower j)
    have hUpperValue :
        ∀ j : Fin (K + 1), (b' : ℝ) < dyadicRowProcess X n0 (upperIndex j) ω := by
      intro j
      simpa [upperIndex] using hUpperStage j n0 (hn0_upper j)
    have hScale_nonneg : 0 ≤ (2 : ℝ) ^ n0 := by positivity
    have hLowerLeUpper : ∀ j : Fin (K + 1), lowerIndex j ≤ upperIndex j := by
      intro j
      dsimp [lowerIndex, upperIndex]
      refine Nat.ceil_le.mpr ?_
      have hTime :
          (((lowerCrossingTime (a : ℝ) (b : ℝ) X T (j : ℕ) ω : NNReal) : ℝ)) ≤
            (((upperCrossingTime (a : ℝ) (b : ℝ) X T ((j : ℕ) + 1) ω : NNReal) : ℝ)) := by
        exact_mod_cast
          (lowerCrossingTime_le_upperCrossingTime_succ
            (a := (a : ℝ))
            (b := (b : ℝ))
            (f := X)
            (N := T)
            (n := (j : ℕ))
            (ω := ω))
      have hScaled := mul_le_mul_of_nonneg_right hTime hScale_nonneg
      exact hScaled.trans (Nat.le_ceil _)
    have hUpperLeNextLower :
        ∀ j : ℕ, ∀ hj : j < K,
          upperIndex ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
            lowerIndex ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩ := by
      intro j hj
      dsimp [upperIndex, lowerIndex]
      refine Nat.ceil_le.mpr ?_
      have hTime :
          (((upperCrossingTime (a : ℝ) (b : ℝ) X T (j + 1) ω : NNReal) : ℝ)) ≤
            (((lowerCrossingTime (a : ℝ) (b : ℝ) X T (j + 1) ω : NNReal) : ℝ)) := by
        exact_mod_cast
          (upperCrossingTime_le_lowerCrossingTime
            (a := (a : ℝ))
            (b := (b : ℝ))
            (f := X)
            (N := T)
            (n := j + 1)
            (ω := ω))
      have hScaled := mul_le_mul_of_nonneg_right hTime hScale_nonneg
      exact hScaled.trans (Nat.le_ceil _)
    have hDyadicTooMany :
        K < upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n0)
          (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1) ω := by
      -- Proof comment: once one row is fine enough for every witness in the prefix, the
      -- transported alternating lower/upper values force more than `K` inner dyadic upcrossings.
      exact lt_upcrossingsBefore_ofDyadicWitnessPrefix
        (X := X)
        (ω := ω)
        (habInner := Rat.cast_lt.2 ha'b')
        lowerIndex
        upperIndex
        hLowerValue
        hUpperValue
        hLowerLeUpper
        hUpperLeNextLower
    exact not_lt_of_ge
      (hK n0 (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1))
      hDyadicTooMany
  have hUpcrossingsLe : upcrossings (a : ℝ) (b : ℝ) X ω ≤ (K : ℝ≥0∞) := by
    rw [upcrossings]
    refine iSup_le fun T ↦ ?_
    exact_mod_cast hBound T
  exact lt_of_le_of_lt hUpcrossingsLe ENNReal.coe_lt_top

/-- Helper for Exercise 21.4.2: a uniform continuous-time `L¹` bound forces the full-time
upcrossing count to be finite almost surely for every rational interval. -/
private theorem submartingaleUpcrossingsAeLtTopNNReal
    (hX : Submartingale X ℱ μ)
    (hbounded : ∃ R : NNReal, ∀ t : NNReal, eLpNorm (X t) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b → upcrossings (a : ℝ) (b : ℝ) X ω < ∞ := by
  simp only [ae_all_iff, eventually_imp_distrib_left]
  intro a b hab
  obtain ⟨a', haa', ha'b⟩ := exists_rat_btwn hab
  obtain ⟨b', ha'b', hb'b⟩ := exists_rat_btwn ha'b
  have hEnvelope :
      ∀ᵐ ω ∂μ, (⨆ n : ℕ, upcrossings (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n) ω) < ∞ :=
    aeLtTop_dyadicRowUpcrossingsSup
      (X := X) (ℱ := ℱ) (μ := μ) hX hbounded ha'b'
  -- Proof comment: choose inner rationals `a < a' < b' < b`, control the dyadic envelope on the
  -- inner interval, and then push that envelope back to the outer continuous-time interval.
  filter_upwards [hEnvelope] with ω hω_sup
  exact upcrossingsLtTopOfDyadicEnvelope
    (X := X) (hX_rc := hX_rc) (ω := ω) haa' ha'b' hb'b hω_sup

omit hX_rc in
/-- Helper for Exercise 21.4.2: convergence of the natural-time skeleton supplies a finite full
tail `liminf` for the continuous-time norm profile. -/
private theorem liminfLtTopOfNatSkeletonTendstoNNReal
    (ω : Ω) {c : ℝ}
    (hω : Tendsto (fun n : ℕ ↦ X (n : NNReal) ω) atTop (𝓝 c)) :
    liminf (fun t : NNReal => (‖X t ω‖₊ : ℝ≥0∞)) atTop < ∞ := by
  let B : ℝ≥0∞ := ENNReal.ofReal (‖c‖ + 1)
  let Bnn : NNReal := ⟨‖c‖ + 1, by positivity⟩
  have hNorm :
      Tendsto (fun n : ℕ ↦ ‖X (n : NNReal) ω‖) atTop (𝓝 ‖c‖) :=
    hω.norm
  have hEventually :
      ∀ᶠ n : ℕ in atTop, ‖X (n : NNReal) ω‖ < ‖c‖ + 1 := by
    -- Proof comment: once the natural-time samples are close to `c`, their norms stay below the
    -- fixed finite envelope `‖c‖ + 1`.
    exact hNorm.eventually (Iio_mem_nhds <| by linarith [norm_nonneg c])
  rcases Filter.eventually_atTop.1 hEventually with ⟨N, hN⟩
  have hFreq :
      ∃ᶠ t : NNReal in atTop, (‖X t ω‖₊ : ℝ≥0∞) ≤ B := by
    -- Proof comment: the cofinal natural-number times witness the same bound in the ambient
    -- `NNReal` filter.
    rw [Filter.frequently_atTop]
    intro T
    let n : ℕ := max N (Nat.ceil (T : ℝ))
    refine ⟨(n : NNReal), ?_, ?_⟩
    · have hceil : T ≤ (Nat.ceil (T : ℝ) : NNReal) := by
        exact_mod_cast Nat.le_ceil (T : ℝ)
      exact le_trans hceil (by exact_mod_cast le_max_right N (Nat.ceil (T : ℝ)))
    · have hnlt : ‖X (n : NNReal) ω‖ < ‖c‖ + 1 := hN n (le_max_left N (Nat.ceil (T : ℝ)))
      have hnnreal : ‖X (n : NNReal) ω‖₊ ≤ Bnn := hnlt.le
      have hBnn : ((Bnn : NNReal) : ℝ≥0∞) = B := by
        exact (ENNReal.ofReal_eq_coe_nnreal (by positivity)).symm
      exact hBnn ▸ ENNReal.coe_le_coe.mpr hnnreal
  have hLiminf : liminf (fun t : NNReal => (‖X t ω‖₊ : ℝ≥0∞)) atTop ≤ B :=
    liminf_le_of_frequently_le' hFreq
  exact lt_of_le_of_lt hLiminf (by simp [B])

omit hX_rc in
/-- Helper for Exercise 21.4.2: a finite alternating witness prefix forces the corresponding
continuous upper crossing to occur before the witness horizon. -/
private theorem upperCrossingTime_lt_ofContinuousWitnessPrefix
    {ω : Ω} {a b : ℝ} {K : ℕ}
    (hab : a < b)
    (lowerTime upperTime : Fin (K + 1) → NNReal)
    (hLowerValue : ∀ k : Fin (K + 1), X (lowerTime k) ω < a)
    (hUpperValue : ∀ k : Fin (K + 1), b < X (upperTime k) ω)
    (hLowerLeUpper : ∀ k : Fin (K + 1), lowerTime k ≤ upperTime k)
    (hUpperLeNextLower :
      ∀ j : ℕ, ∀ hj : j < K,
        upperTime ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
          lowerTime ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩) :
    upperCrossingTime a b X ((Finset.univ.sup upperTime : NNReal) + 1) (K + 1) ω <
      ((Finset.univ.sup upperTime : NNReal) + 1) := by
  let T : NNReal := (Finset.univ.sup upperTime : NNReal) + 1
  have hUpper_lt_T : ∀ k : Fin (K + 1), upperTime k < T := by
    intro k
    have hle : upperTime k ≤ Finset.univ.sup upperTime := by
      exact Finset.le_sup (s := Finset.univ) (f := upperTime) (Finset.mem_univ k)
    exact lt_of_le_of_lt hle (lt_add_of_pos_right _ (by norm_num : (0 : NNReal) < 1))
  have hUpper_le_T : ∀ k : Fin (K + 1), upperTime k ≤ T := fun k ↦ (hUpper_lt_T k).le
  have hLower_le_T : ∀ k : Fin (K + 1), lowerTime k ≤ T := by
    intro k
    exact le_trans (hLowerLeUpper k) (hUpper_le_T k)
  have hLowerBound :
      ∀ n : ℕ, ∀ hnK : n ≤ K,
        lowerCrossingTime a b X T n ω ≤ lowerTime ⟨n, Nat.lt_succ_of_le hnK⟩ := by
    intro n hnK
    induction' n with n ih
    · -- Proof comment: the first lower crossing starts from `⊥`, so the first lower witness
      -- immediately bounds the hitting time from above.
      rw [lowerCrossingTime]
      exact hittingBtwn_le_of_mem
        bot_le
        (hLower_le_T ⟨0, Nat.zero_lt_succ K⟩)
        (hLowerValue ⟨0, Nat.zero_lt_succ K⟩).le
    · have hn_lt_K : n < K := Nat.lt_of_succ_le hnK
      have hn_le_K : n ≤ K := Nat.le_of_lt hn_lt_K
      have hUpperPrev :
          upperCrossingTime a b X T (n + 1) ω ≤ upperTime ⟨n, Nat.lt_succ_of_le hn_le_K⟩ := by
        -- Proof comment: once the `n`-th lower crossing is bounded by its witness, the
        -- corresponding upper witness bounds the next upper crossing by `hittingBtwn_le_of_mem`.
        rw [upperCrossingTime_succ_eq]
        exact hittingBtwn_le_of_mem
          (le_trans (ih hn_le_K) (hLowerLeUpper ⟨n, Nat.lt_succ_of_le hn_le_K⟩))
          (hUpper_le_T ⟨n, Nat.lt_succ_of_le hn_le_K⟩)
          (hUpperValue ⟨n, Nat.lt_succ_of_le hn_le_K⟩).le
      have hStart :
          upperCrossingTime a b X T (n + 1) ω ≤ lowerTime ⟨n + 1, Nat.lt_succ_of_le hnK⟩ := by
        exact le_trans hUpperPrev (hUpperLeNextLower n hn_lt_K)
      -- Proof comment: the next lower witness now bounds the following lower crossing in the same
      -- way.
      rw [lowerCrossingTime]
      exact hittingBtwn_le_of_mem
        hStart
        (hLower_le_T ⟨n + 1, Nat.lt_succ_of_le hnK⟩)
        (hLowerValue ⟨n + 1, Nat.lt_succ_of_le hnK⟩).le
  have hUpperFinal :
      upperCrossingTime a b X T (K + 1) ω ≤ upperTime ⟨K, Nat.lt_succ_self K⟩ := by
    -- Proof comment: the last upper witness bounds the `(K + 1)`-st upper crossing.
    rw [upperCrossingTime_succ_eq]
    exact hittingBtwn_le_of_mem
      (le_trans (hLowerBound K le_rfl) (hLowerLeUpper ⟨K, Nat.lt_succ_self K⟩))
      (hUpper_le_T ⟨K, Nat.lt_succ_self K⟩)
      (hUpperValue ⟨K, Nat.lt_succ_self K⟩).le
  -- Route correction: for `NNReal`-indexed paths the stable conclusion is the realized crossing
  -- time bound itself; `upcrossingsBefore` is not the right finite-horizon interface here.
  have hUpperFinal_lt : upperCrossingTime a b X T (K + 1) ω < T :=
    lt_of_le_of_lt hUpperFinal (hUpper_lt_T ⟨K, Nat.lt_succ_self K⟩)
  simpa [T] using hUpperFinal_lt

/-- Helper for Exercise 21.4.2: a realized continuous upper crossing before the horizon already
contributes one index to the finite-horizon upcrossing count. -/
private theorem leUpcrossingsBeforeOfUpperCrossingTimeLtNNReal
    {ω : Ω} {a b : ℝ} {T : NNReal} {n : ℕ}
    (hBound : BddAbove {m | upperCrossingTime a b X T m ω < T})
    (hn : upperCrossingTime a b X T n ω < T) :
    n ≤ upcrossingsBefore a b X T ω := by
  -- Proof comment: the witness index `n` belongs to the set whose `sSup` defines
  -- `upcrossingsBefore`.
  simp only [upcrossingsBefore]
  exact le_csSup hBound hn

omit hX_rc in
/-- Helper for Exercise 21.4.2: frequent visits below `a` and above `b` yield any prescribed
finite alternating prefix of continuous witness times. -/
private theorem existsAlternatingWitnessPrefixOfFrequently
    {ω : Ω} {a b : ℝ} {K : ℕ}
    (hLower : ∃ᶠ t : NNReal in atTop, X t ω < a)
    (hUpper : ∃ᶠ t in atTop, b < X t ω) :
    ∃ lowerTime upperTime : Fin (K + 1) → NNReal,
      (∀ k : Fin (K + 1), X (lowerTime k) ω < a) ∧
      (∀ k : Fin (K + 1), b < X (upperTime k) ω) ∧
      (∀ k : Fin (K + 1), lowerTime k < upperTime k) ∧
      (∀ j : ℕ, ∀ hj : j < K,
        upperTime ⟨j, Nat.lt_succ_of_lt hj⟩ <
          lowerTime ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩) := by
  classical
  rw [Filter.frequently_atTop] at hLower hUpper
  have hPair :
      ∀ T : NNReal,
        ∃ p : NNReal × NNReal,
          T ≤ p.1 ∧ X p.1 ω < a ∧ p.1 + 1 ≤ p.2 ∧ b < X p.2 ω := by
    intro T
    rcases hLower T with ⟨s, hsT, hsVal⟩
    rcases hUpper (s + 1) with ⟨u, huS, huVal⟩
    exact ⟨⟨s, u⟩, hsT, hsVal, huS, huVal⟩
  let witnessPair : ℕ → NNReal × NNReal :=
    Nat.rec (Classical.choose (hPair 0))
      fun n p ↦ Classical.choose (hPair (p.2 + 1))
  let lowerTime : Fin (K + 1) → NNReal := fun k ↦ (witnessPair k).1
  let upperTime : Fin (K + 1) → NNReal := fun k ↦ (witnessPair k).2
  have hLowerValueNat : ∀ n : ℕ, X (witnessPair n).1 ω < a := by
    intro n
    induction n with
    | zero =>
        simpa [witnessPair] using (Classical.choose_spec (hPair 0)).2.1
    | succ n ih =>
        simpa [witnessPair] using
          (Classical.choose_spec (hPair ((witnessPair n).2 + 1))).2.1
  have hUpperValueNat : ∀ n : ℕ, b < X (witnessPair n).2 ω := by
    intro n
    induction n with
    | zero =>
        simpa [witnessPair] using (Classical.choose_spec (hPair 0)).2.2.2
    | succ n ih =>
        simpa [witnessPair] using
          (Classical.choose_spec (hPair ((witnessPair n).2 + 1))).2.2.2
  have hLowerGapNat : ∀ n : ℕ, (witnessPair n).1 + 1 ≤ (witnessPair n).2 := by
    intro n
    induction n with
    | zero =>
        simpa [witnessPair] using (Classical.choose_spec (hPair 0)).2.2.1
    | succ n ih =>
        simpa [witnessPair] using
          (Classical.choose_spec (hPair ((witnessPair n).2 + 1))).2.2.1
  have hNextGapNat : ∀ n : ℕ, (witnessPair n).2 + 1 ≤ (witnessPair (n + 1)).1 := by
    intro n
    -- Proof comment: each recursive step chooses the next lower witness strictly to the right of
    -- the previous upper witness.
    simpa [witnessPair] using
      (Classical.choose_spec (hPair ((witnessPair n).2 + 1))).1
  refine ⟨lowerTime, upperTime, ?_, ?_, ?_, ?_⟩
  · intro k
    exact hLowerValueNat k
  · intro k
    exact hUpperValueNat k
  · intro k
    have hstep : lowerTime k + 1 ≤ upperTime k := hLowerGapNat k
    exact lt_of_lt_of_le (lt_add_of_pos_right _ (by norm_num : (0 : NNReal) < 1)) hstep
  · intro j hj
    have hstep :
        upperTime ⟨j, Nat.lt_succ_of_lt hj⟩ + 1 ≤
          lowerTime ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩ :=
      hNextGapNat j
    exact lt_of_lt_of_le (lt_add_of_pos_right _ (by norm_num : (0 : NNReal) < 1)) hstep

/-- Helper for Exercise 21.4.2: one alternating continuous witness prefix can be frozen onto a
single dyadic row on any strictly smaller inner interval. -/
private theorem dyadicWitnessPrefixOfContinuousWitnessPrefix
    {ω : Ω} {a b : ℝ} {a' b' : ℚ} {K : ℕ}
    (haa' : a < (a' : ℝ))
    (hb'b : (b' : ℝ) < b)
    (lowerTime upperTime : Fin (K + 1) → NNReal)
    (hLowerValue : ∀ k : Fin (K + 1), X (lowerTime k) ω < a)
    (hUpperValue : ∀ k : Fin (K + 1), b < X (upperTime k) ω)
    (hLowerLtUpper : ∀ k : Fin (K + 1), lowerTime k < upperTime k)
    (hUpperLtNextLower :
      ∀ j : ℕ, ∀ hj : j < K,
        upperTime ⟨j, Nat.lt_succ_of_lt hj⟩ <
          lowerTime ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩) :
    ∃ n0 : ℕ, ∃ lowerIndex upperIndex : Fin (K + 1) → ℕ,
      (∀ k : Fin (K + 1), dyadicRowProcess X n0 (lowerIndex k) ω < (a' : ℝ)) ∧
      (∀ k : Fin (K + 1), (b' : ℝ) < dyadicRowProcess X n0 (upperIndex k) ω) ∧
      (∀ k : Fin (K + 1), lowerIndex k ≤ upperIndex k) ∧
      (∀ j : ℕ, ∀ hj : j < K,
        upperIndex ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
          lowerIndex ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩) := by
  have hLowerEventually :
      ∀ k : Fin (K + 1),
        ∃ N : ℕ, ∀ n ≥ N,
          dyadicRowProcess X n
            (Nat.ceil (((lowerTime k : NNReal) : ℝ) * (2 : ℝ) ^ n)) ω < (a' : ℝ) := by
    intro k
    have hStrict : X (lowerTime k) ω < (a' : ℝ) :=
      lt_of_lt_of_le (hLowerValue k) haa'.le
    rcases eventually_lt_dyadicRightApprox_of_lt
        (X := X)
        (hX_rc := hX_rc)
        (ω := ω)
        (t := lowerTime k)
        (c := (a' : ℝ))
        hStrict with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    -- Proof comment: after rewriting the dyadic-row value as the right-dyadic approximation,
    -- the eventual inner-barrier estimate is exactly the transported right-continuity bound.
    simpa [dyadicRowProcess_rightApprox] using hN m
  have hUpperEventually :
      ∀ k : Fin (K + 1),
        ∃ N : ℕ, ∀ n ≥ N,
          (b' : ℝ) <
            dyadicRowProcess X n
              (Nat.ceil (((upperTime k : NNReal) : ℝ) * (2 : ℝ) ^ n)) ω := by
    intro k
    have hStrict : (b' : ℝ) < X (upperTime k) ω :=
      lt_trans hb'b (hUpperValue k)
    rcases eventually_gt_dyadicRightApprox_of_lt
        (X := X)
        (hX_rc := hX_rc)
        (ω := ω)
        (t := upperTime k)
        (c := (b' : ℝ))
        hStrict with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    -- Proof comment: rewrite the sampled dyadic-row value back to the right-dyadic approximation
    -- and apply the eventual strict lower bound.
    simpa [dyadicRowProcess_rightApprox] using hN m
  choose lowerStage hLowerStage using hLowerEventually
  choose upperStage hUpperStage using hUpperEventually
  let n0 : ℕ := max (Finset.univ.sup lowerStage) (Finset.univ.sup upperStage)
  let lowerIndex : Fin (K + 1) → ℕ := fun k ↦
    Nat.ceil (((lowerTime k : NNReal) : ℝ) * (2 : ℝ) ^ n0)
  let upperIndex : Fin (K + 1) → ℕ := fun k ↦
    Nat.ceil (((upperTime k : NNReal) : ℝ) * (2 : ℝ) ^ n0)
  have hn0_lower : ∀ k : Fin (K + 1), lowerStage k ≤ n0 := by
    intro k
    exact le_trans (Finset.le_sup (s := Finset.univ) (f := lowerStage) (Finset.mem_univ k))
      (le_max_left _ _)
  have hn0_upper : ∀ k : Fin (K + 1), upperStage k ≤ n0 := by
    intro k
    exact le_trans (Finset.le_sup (s := Finset.univ) (f := upperStage) (Finset.mem_univ k))
      (le_max_right _ _)
  refine ⟨n0, lowerIndex, upperIndex, ?_, ?_, ?_, ?_⟩
  · intro k
    simpa [lowerIndex] using hLowerStage k n0 (hn0_lower k)
  · intro k
    simpa [upperIndex] using hUpperStage k n0 (hn0_upper k)
  · have hScale_nonneg : 0 ≤ (2 : ℝ) ^ n0 := by positivity
    intro k
    dsimp [lowerIndex, upperIndex]
    refine Nat.ceil_le.mpr ?_
    have hTime :
        (((lowerTime k : NNReal) : ℝ)) ≤ (((upperTime k : NNReal) : ℝ)) := by
      exact_mod_cast (hLowerLtUpper k).le
    exact (mul_le_mul_of_nonneg_right hTime hScale_nonneg).trans (Nat.le_ceil _)
  · have hScale_nonneg : 0 ≤ (2 : ℝ) ^ n0 := by positivity
    intro j hj
    dsimp [upperIndex, lowerIndex]
    refine Nat.ceil_le.mpr ?_
    have hTime :
        (((upperTime ⟨j, Nat.lt_succ_of_lt hj⟩ : NNReal) : ℝ)) ≤
          (((lowerTime ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩ : NNReal) : ℝ)) := by
      exact_mod_cast (hUpperLtNextLower j hj).le
    exact (mul_le_mul_of_nonneg_right hTime hScale_nonneg).trans (Nat.le_ceil _)

/-- Helper for Exercise 21.4.2: a finite dyadic-envelope bound on an inner rational interval
prevents frequent visits to any enclosing outer interval at infinity. -/
private theorem notFrequentlyOfDyadicEnvelopeLtTopNNReal
    {ω : Ω} {a b : ℝ} {a' b' : ℚ}
    (haa' : a < (a' : ℝ))
    (ha'b' : (a' : ℝ) < (b' : ℝ))
    (hb'b : (b' : ℝ) < b)
    (hω_sup :
      (⨆ n : ℕ, upcrossings (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n) ω) < ∞) :
    ¬((∃ᶠ t : NNReal in atTop, X t ω < a) ∧ ∃ᶠ t in atTop, b < X t ω) := by
  rcases natBoundOfDyadicUpcrossingsBeforeEnvelope (X := X) (ω := ω) hω_sup with ⟨K, hK⟩
  rintro ⟨hLower, hUpper⟩
  rcases existsAlternatingWitnessPrefixOfFrequently
      (X := X) (ω := ω) (K := K) hLower hUpper with
    ⟨lowerTime, upperTime, hLowerValue, hUpperValue, hLowerLtUpper, hUpperLtNextLower⟩
  rcases dyadicWitnessPrefixOfContinuousWitnessPrefix
      (X := X)
      (hX_rc := hX_rc)
      (ω := ω)
      (a := a)
      (b := b)
      (a' := a')
      (b' := b')
      (K := K)
      haa'
      hb'b
      lowerTime
      upperTime
      hLowerValue
      hUpperValue
      hLowerLtUpper
      hUpperLtNextLower with
    ⟨n0, lowerIndex, upperIndex, hLowerRow, hUpperRow, hLowerLeUpper, hUpperLeNextLower⟩
  have hTooMany :
      K < upcrossingsBefore (a' : ℝ) (b' : ℝ) (dyadicRowProcess X n0)
        (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1) ω := by
    -- Proof comment: once all witnesses live on one dyadic row, the rowwise witness-prefix lemma
    -- turns them into more than `K` inner dyadic upcrossings.
    exact lt_upcrossingsBefore_ofDyadicWitnessPrefix
      (X := X)
      (ω := ω)
      (habInner := ha'b')
      lowerIndex
      upperIndex
      hLowerRow
      hUpperRow
      hLowerLeUpper
      hUpperLeNextLower
  exact not_lt_of_ge
    (hK n0 (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1))
    hTooMany

omit hX_rc in
/-- Helper for Exercise 21.4.2: almost surely every rational dyadic upcrossing envelope is
finite under the uniform continuous-time `L¹` bound. -/
private theorem aeAllDyadicEnvelopeLtTopRat
    (hX : Submartingale X ℱ μ)
    (hbounded : ∃ R : NNReal, ∀ t : NNReal, eLpNorm (X t) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b →
      (⨆ n : ℕ, upcrossings (a : ℝ) (b : ℝ) (dyadicRowProcess X n) ω) < ∞ := by
  simp only [ae_all_iff, eventually_imp_distrib_left]
  intro a b hab
  exact aeLtTop_dyadicRowUpcrossingsSup
    (X := X) (ℱ := ℱ) (μ := μ) hX hbounded hab

/-- Helper for Exercise 21.4.2: finite rational dyadic envelopes together with a finite `liminf`
force an `NNReal`-indexed sample path to converge. -/
private theorem existsTendsto_ofLiminfLtTop_ofDyadicEnvelopeLtTopNNReal
    (ω : Ω)
    (hLiminf : liminf (fun t : NNReal => (‖X t ω‖₊ : ℝ≥0∞)) atTop < ∞)
    (hEnvelope :
      ∀ a b : ℚ, a < b →
        (⨆ n : ℕ, upcrossings (a : ℝ) (b : ℝ) (dyadicRowProcess X n) ω) < ∞) :
    ∃ c, Tendsto (fun t : NNReal ↦ X t ω) atTop (𝓝 c) := by
  by_cases h : IsBoundedUnder (· ≤ ·) atTop fun t => |X t ω|
  · rw [isBoundedUnder_le_abs] at h
    -- Proof comment: in the bounded case, the no-upcrossings criterion now consumes the dyadic
    -- envelope event directly instead of any continuous crossing-count bound.
    refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ h.1 h.2
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    obtain ⟨a', haa', ha'b⟩ := exists_rat_btwn (Rat.cast_lt.1 hab)
    obtain ⟨b', ha'b', hb'b⟩ := exists_rat_btwn ha'b
    exact notFrequentlyOfDyadicEnvelopeLtTopNNReal
      (X := X)
      (hX_rc := hX_rc)
      (ω := ω)
      (a := (a : ℝ))
      (b := (b : ℝ))
      (a' := a')
      (b' := b')
      (Rat.cast_lt.2 haa')
      (Rat.cast_lt.2 ha'b')
      (Rat.cast_lt.2 hb'b)
      (hEnvelope a' b' ha'b')
  · obtain ⟨a, b, hab, hLowerFreq, hUpperFreq⟩ :=
      ENNReal.exists_upcrossings_of_not_bounded_under hLiminf.ne h
    obtain ⟨a', haa', ha'b⟩ := exists_rat_btwn hab
    obtain ⟨b', ha'b', hb'b⟩ := exists_rat_btwn ha'b
    -- Proof comment: if the path were not eventually bounded, the ENNReal witness pair would
    -- contradict the corresponding finite dyadic envelope on a strictly smaller inner interval.
    exact False.elim <|
      notFrequentlyOfDyadicEnvelopeLtTopNNReal
        (X := X)
        (hX_rc := hX_rc)
        (ω := ω)
        (a := (a : ℝ))
        (b := (b : ℝ))
        (a' := a')
        (b' := b')
        (Rat.cast_lt.2 haa')
        (Rat.cast_lt.2 ha'b')
        (Rat.cast_lt.2 hb'b)
        (hEnvelope a' b' ha'b')
        ⟨hLowerFreq, hUpperFreq⟩

omit hX_rc in
/-- Helper for Exercise 21.4.2: if a nonnegative `NNReal`-indexed error profile does not converge
to `0` at infinity, one can sample it along a monotone cofinal bad sequence that stays uniformly
away from `0`. -/
private theorem existsMonotoneBadSubsequenceOfNotTendstoZero
    {f : NNReal → ℝ≥0∞} (hnot : ¬ Tendsto f atTop (𝓝 0)) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧
      ∃ τ : ℕ → NNReal, Monotone τ ∧ Tendsto τ atTop atTop ∧ ∀ n, ε < f (τ n) := by
  rw [ENNReal.tendsto_nhds_zero] at hnot
  push Not at hnot
  rcases hnot with ⟨ε, hε, hfreq⟩
  rw [Filter.frequently_atTop] at hfreq
  choose next hnext_ge hnext_bad using hfreq
  let τ : ℕ → NNReal :=
    Nat.rec (next 0) (fun n tn ↦ next (max tn ((n + 1 : ℕ) : NNReal)))
  have hτ_step : ∀ n, τ n ≤ τ (n + 1) := by
    intro n
    have hge :
        max (τ n) ((n + 1 : ℕ) : NNReal) ≤ τ (n + 1) := by
      simpa [τ] using hnext_ge (max (τ n) ((n + 1 : ℕ) : NNReal))
    exact le_trans (le_max_left _ _) hge
  have hτ_mono : Monotone τ :=
    monotone_nat_of_le_succ hτ_step
  have hτ_lower : ∀ n, ((n : ℕ) : NNReal) ≤ τ n := by
    intro n
    induction n with
    | zero =>
        simpa [τ] using (zero_le (next 0) : (0 : NNReal) ≤ next 0)
    | succ n ih =>
        have hge :
            max (τ n) ((n + 1 : ℕ) : NNReal) ≤ τ (n + 1) := by
          simpa [τ] using hnext_ge (max (τ n) ((n + 1 : ℕ) : NNReal))
        exact le_trans (le_max_right _ _) hge
  refine ⟨ε, hε, τ, hτ_mono, ?_, ?_⟩
  · -- Proof comment: the recursive choice stays above the natural-number clock, hence is cofinal.
    exact hτ_mono.tendsto_atTop_atTop fun b ↦
      ⟨Nat.ceil (b : ℝ), le_trans (by exact_mod_cast Nat.le_ceil (b : ℝ))
        (hτ_lower (Nat.ceil (b : ℝ)))⟩
  · -- Proof comment: every recursively chosen sample point still witnesses the bad lower bound.
    intro n
    cases n with
    | zero =>
        simpa [τ] using hnext_bad 0
    | succ n =>
        simpa [τ] using hnext_bad (max (τ n) ((n + 1 : ℕ) : NNReal))

omit hX_rc in
/-- Helper for Exercise 21.4.2: the natural-time limit process is strongly measurable for the
ambient terminal sigma-algebra. -/
private theorem natSkeletonLimitProcess_stronglyMeasurable :
    StronglyMeasurable[⨆ t, ℱ t]
      ((natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ) := by
  -- Proof comment: first use the discrete owner theorem on the sampled natural-time filtration,
  -- then enlarge the terminal sigma-algebra to the ambient continuous-time one.
  refine
    (MeasureTheory.Filtration.stronglyMeasurable_limitProcess
      (Ω := Ω)
      (m := ‹MeasurableSpace Ω›)
      (ι := ℕ)
      (ℱ := natSkeletonFiltration ℱ)
      (f := natSkeletonProcess X)
      (μ := μ)).mono ?_
  refine sSup_le ?_
  rintro _ ⟨n, rfl⟩
  exact le_sSup ⟨(n : NNReal), rfl⟩

omit hX_rc in
/-- Helper for Exercise 21.4.2: any almost-sure terminal limit identifies the ambient canonical
limit process. -/
private theorem limitProcessAeEqOfAeTendstoNNReal
    {Z : Ω → ℝ}
    (hZsm : StronglyMeasurable[⨆ t, ℱ t] Z)
    (hZlimit :
      ∀ᵐ ω ∂μ, Tendsto (fun t : NNReal ↦ X t ω) atTop (𝓝 (Z ω))) :
    X∞ =ᵐ[μ] Z := by
  classical
  let hlimit :
      ∃ g : Ω → ℝ,
        StronglyMeasurable[⨆ t, ℱ t] g ∧
          ∀ᵐ ω ∂μ, Tendsto (fun t : NNReal ↦ X t ω) atTop (𝓝 (g ω)) :=
    ⟨Z, hZsm, hZlimit⟩
  rw [Filtration.limitProcess, dif_pos hlimit]
  have hchosen :
      ∀ᵐ ω ∂μ,
        Tendsto (fun t : NNReal ↦ X t ω) atTop
          (𝓝 (Classical.choose hlimit ω)) :=
    (Classical.choose_spec hlimit).2
  -- Proof comment: the chosen owner limit and the comparison limit are both pointwise limits of
  -- the same path, so they coincide almost surely by uniqueness in Hausdorff spaces.
  filter_upwards [hchosen, hZlimit] with ω hωChosen hωZ
  exact tendsto_nhds_unique hωChosen hωZ

omit hX_rc in
/-- Helper for Exercise 21.4.2: any full-time path limit must agree with the natural-time limit
process because both limits are seen along the cofinal natural-number subsequence. -/
private theorem tendsto_natSkeletonLimit_of_fullTimeLimit
    (ω : Ω) {c : ℝ}
    (hfull : Tendsto (fun t : NNReal ↦ X t ω) atTop (𝓝 c))
    (hnat :
      Tendsto (fun n : ℕ ↦ X (n : NNReal) ω) atTop
        (𝓝 (((natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ) ω))) :
    Tendsto (fun t : NNReal ↦ X t ω) atTop
      (𝓝 (((natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ) ω)) := by
  have hfullNat :
      Tendsto (fun n : ℕ ↦ X (n : NNReal) ω) atTop (𝓝 c) :=
    hfull.comp tendsto_natCast_atTop_atTop
  have hc :
      c = ((natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ) ω :=
    tendsto_nhds_unique hfullNat hnat
  -- Proof comment: after identifying the two candidate limits on the natural-number subsequence,
  -- rewrite the ambient full-time limit to the natural-time limit process.
  simpa [hc] using hfull

/-- Helper for Exercise 21.4.2: the real frontier is the full-time convergence from the existing
natural-time limit process. -/
private theorem aeTendsto_natSkeletonLimitProcess_of_bdd_pos_part
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun t : NNReal ↦ X t ω) atTop
        (𝓝 (((natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ) ω)) := by
  have hL1 :
      ∃ R : NNReal, ∀ t : NNReal, eLpNorm (X t) 1 μ ≤ R :=
    submartingaleELpNormOneBoundedOfBddPosPartNNReal (X := X) (ℱ := ℱ) (μ := μ) hX hpos
  have hEnvelope :
      ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b →
        (⨆ n : ℕ, upcrossings (a : ℝ) (b : ℝ) (dyadicRowProcess X n) ω) < ∞ :=
    aeAllDyadicEnvelopeLtTopRat (X := X) (ℱ := ℱ) (μ := μ) hX hL1
  have hNat :=
    (natSkeleton_convergence_to_limitProcess_of_bdd_pos_part
      (X := X) (ℱ := ℱ) (μ := μ) hX hpos).2
  have hNatLiminf :
      ∀ᵐ ω ∂μ, liminf (fun t : NNReal => (‖X t ω‖₊ : ℝ≥0∞)) atTop < ∞ := by
    -- Proof comment: the natural-time discrete convergence already yields a finite liminf witness
    -- for the ambient continuous-time filter.
    filter_upwards [hNat] with ω hω
    exact liminfLtTopOfNatSkeletonTendstoNNReal (X := X) ω hω
  -- Proof comment: finite rational dyadic envelopes plus the liminf bound produce a pathwise
  -- full-time limit, and the natural-time skeleton identifies that limit with the sampled
  -- canonical limit process already available in the file.
  filter_upwards [hEnvelope, hNat, hNatLiminf] with ω hEnvelopeω hNatω hLiminfω
  obtain ⟨c, hfullω⟩ :=
    existsTendsto_ofLiminfLtTop_ofDyadicEnvelopeLtTopNNReal
      (X := X) (hX_rc := hX_rc) ω hLiminfω hEnvelopeω
  exact tendsto_natSkeletonLimit_of_fullTimeLimit
    (X := X) (ℱ := ℱ) (μ := μ) ω hfullω hNatω

-- Proof sketch: restrict the right-continuous process to a countable dense time skeleton, apply
-- Doob's inequality from Exercise 21.4.1 together with the discrete convergence theorems of
-- Chapter 11
-- to the sampled process, and then use right continuity to upgrade convergence along the
-- skeleton to convergence as `t → ∞` in continuous time, with canonical limit `X∞`.
/-- Exercise 21.4.2, Theorem 11.4 analogue: a right-continuous submartingale on `[0,∞)` whose
positive-part expectations are bounded above has an integrable canonical limit process, and the
process converges almost surely to that limit. -/
theorem rightContinuous_submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) :
    Integrable X∞ μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := by
  let natLimit : Ω → ℝ :=
    (natSkeletonFiltration ℱ).limitProcess (natSkeletonProcess X) μ
  have hNatInt : Integrable natLimit μ :=
    (natSkeleton_convergence_to_limitProcess_of_bdd_pos_part
      (X := X) (ℱ := ℱ) (μ := μ) hX hpos).1
  have hNatSm : StronglyMeasurable[⨆ t, ℱ t] natLimit :=
    natSkeletonLimitProcess_stronglyMeasurable (X := X) (ℱ := ℱ) (μ := μ)
  have hFullNat :
      ∀ᵐ ω ∂μ, Tendsto (fun t : NNReal ↦ X t ω) atTop (𝓝 (natLimit ω)) :=
    aeTendsto_natSkeletonLimitProcess_of_bdd_pos_part
      (X := X) (ℱ := ℱ) (μ := μ) (hX_rc := hX_rc) hX hpos
  have hEqLimit : X∞ =ᵐ[μ] natLimit :=
    limitProcessAeEqOfAeTendstoNNReal
      (X := X) (ℱ := ℱ) (μ := μ) hNatSm hFullNat
  have hXInfInt : Integrable X∞ μ := hNatInt.congr hEqLimit.symm
  have hFull :
      ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := by
    -- Proof comment: rewrite the full-time convergence target from the sampled natural-time limit
    -- to the ambient canonical limit process using the owner equality established above.
    filter_upwards [hFullNat, hEqLimit] with ω hω hEqω
    simpa [natLimit, hEqω] using hω
  exact ⟨hXInfInt, hFull⟩

/-- Exercise 21.4.2, Theorem 11.4 analogue, convergence component. -/
theorem rightContinuous_submartingale_ae_tendsto_limitProcess_of_bdd_pos_part
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) :
    ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := by
  exact
    (rightContinuous_submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
      hX_rc hX hpos).2

/-- Exercise 21.4.2, Theorem 11.7 analogue for martingales: a uniformly integrable
right-continuous martingale on `[0,∞)` has an integrable canonical limit process, and the process
converges almost surely to that limit. -/
theorem rightContinuous_martingale_convergence_to_integrable_limitProcess_of_uniformIntegrable
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Integrable X∞ μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := by
  obtain ⟨R, hR⟩ := hUI.2.2
  have hpos :
      BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺]) :=
    bddAbovePosPartOfELpNormOneBounded (X := X) (ℱ := ℱ) (μ := μ) hX.submartingale ⟨R, hR⟩
  -- Proof comment: uniform integrability gives the `L¹` bound needed to invoke the
  -- source-facing continuous-time submartingale theorem.
  simpa using
    rightContinuous_submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
      (X := X) (ℱ := ℱ) (μ := μ) hX_rc hX.submartingale hpos

/-- Exercise 21.4.2, Theorem 11.7 analogue, convergence component for martingales. -/
theorem rightContinuous_martingale_ae_tendsto_limitProcess_of_uniformIntegrable
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := by
  exact
    (rightContinuous_martingale_convergence_to_integrable_limitProcess_of_uniformIntegrable
      hX_rc hX hUI).2

/-- Exercise 21.4.2, `L¹` bridge companion: a uniformly integrable right-continuous martingale on
`[0,∞)` converges to its canonical limit process in the raw `eLpNorm` formulation of `L¹`. -/
theorem rightContinuous_martingale_tendsto_eLpNorm_one_limitProcess_of_uniformIntegrable
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Tendsto (fun t ↦ eLpNorm (X t - X∞) 1 μ) atTop (𝓝 0) := by
  by_contra hnot
  obtain ⟨ε, hε, τ, hτ_mono, hτ_tendsto, hτ_bad⟩ :=
    existsMonotoneBadSubsequenceOfNotTendstoZero
      (f := fun t ↦ eLpNorm (X t - X∞) 1 μ) hnot
  let Y : ℕ → Ω → ℝ := fun n ω ↦ X (τ n) ω
  let 𝒢 : Filtration ℕ ‹MeasurableSpace Ω› := sampledFiltration (ℱ := ℱ) τ hτ_mono
  have hY : Martingale Y 𝒢 μ := by
    -- Proof comment: the bad-time sampler preserves the martingale structure.
    simpa [Y, 𝒢] using
      sampledMartingaleOfMonotone (X := X) (ℱ := ℱ) (μ := μ) hX hτ_mono
  have hYUI : UniformIntegrable Y 1 μ :=
    uniformIntegrable_comp (μ := μ) (f := X) hUI τ
  have hYtendstoXInf :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (X∞ ω)) := by
    have hfull :
        ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) :=
      rightContinuous_martingale_ae_tendsto_limitProcess_of_uniformIntegrable
        (X := X) (ℱ := ℱ) (μ := μ) hX_rc hX hUI
    -- Proof comment: full-time almost-sure convergence restricts along every cofinal sampled path.
    filter_upwards [hfull] with ω hω
    simpa [Y] using hω.comp hτ_tendsto
  have hYlimit :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (𝒢.limitProcess Y μ ω)) :=
    hY.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hYUI
  have hEq :
      𝒢.limitProcess Y μ =ᵐ[μ] X∞ :=
    sampledLimitProcess_ae_eq_of_ae_tendsto
      (μ := μ) (Y := Y) (𝒢 := 𝒢) (Z := X∞) hYlimit hYtendstoXInf
  have hdisc :
      Tendsto (fun n ↦ eLpNorm (Y n - X∞) 1 μ) atTop (𝓝 0) := by
    have hdisc' :
        Tendsto (fun n ↦ eLpNorm (Y n - 𝒢.limitProcess Y μ) 1 μ) atTop (𝓝 0) :=
      hY.submartingale.tendsto_eLpNorm_one_limitProcess hYUI
    have hEqNorm :
        (fun n ↦ eLpNorm (Y n - 𝒢.limitProcess Y μ) 1 μ) =
          fun n ↦ eLpNorm (Y n - X∞) 1 μ := by
      funext n
      exact eLpNorm_congr_ae ((EventuallyEq.refl (ae μ) (Y n)).sub hEq)
    rw [hEqNorm] at hdisc'
    exact hdisc'
  have hsmall : ∀ᶠ n in atTop, eLpNorm (Y n - X∞) 1 μ ≤ ε :=
    (ENNReal.tendsto_nhds_zero.1 hdisc) ε hε
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  exact (not_le.mpr (by simpa [Y] using hτ_bad N)) (hN N le_rfl)

/-- Exercise 21.4.2, Theorem 11.10 analogue: an `L^p`-bounded right-continuous martingale with
`1 < p` has a canonical limit process that is terminally strongly measurable, belongs to
`L^p(μ)`, and captures the almost-sure limit. -/
theorem rightContinuous_martingale_convergence_to_memLp_limitProcess_of_lp_bounded
    {p : ℝ} (hX : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ t : NNReal, eLpNorm (X t) (ENNReal.ofReal p) μ ≤ C) :
    StronglyMeasurable[⨆ t, ℱ t] X∞ ∧
      MemLp X∞ (ENNReal.ofReal p) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω))) := by
  obtain ⟨R, hR⟩ :=
    eLpNormOneBoundedOfLpBoundedNNReal (X := X) (ℱ := ℱ) (μ := μ) hX.submartingale hp hbounded
  have hpos :
      BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺]) :=
    bddAbovePosPartOfELpNormOneBounded (X := X) (ℱ := ℱ) (μ := μ) hX.submartingale ⟨R, hR⟩
  have hfull :
      ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) :=
    (rightContinuous_submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
      (X := X) (ℱ := ℱ) (μ := μ) hX_rc hX.submartingale hpos).2
  let Y : ℕ → Ω → ℝ := fun n ω ↦ X (n : NNReal) ω
  let 𝒢 : Filtration ℕ ‹MeasurableSpace Ω› :=
    sampledFiltration (ℱ := ℱ) (fun n : ℕ ↦ (n : NNReal)) Nat.mono_cast
  have hnat : Martingale Y 𝒢 μ := by
    -- Proof comment: the natural-time skeleton is a discrete martingale on the sampled
    -- filtration.
    simpa [Y, 𝒢] using
      sampledMartingaleOfMonotone (X := X) (ℱ := ℱ) (μ := μ) hX Nat.mono_cast
  have hdiscBound : ∃ C : NNReal, ∀ n : ℕ, eLpNorm (Y n) (ENNReal.ofReal p) μ ≤ C := by
    rcases hbounded with ⟨C, hC⟩
    exact ⟨C, fun n ↦ by simpa [Y] using hC (n : NNReal)⟩
  have hmemNat : MemLp (𝒢.limitProcess Y μ) (ENNReal.ofReal p) μ := by
    -- Proof comment: the natural-time sampled martingale is uniformly `L^p`-bounded, so the
    -- discrete limit process is itself in `L^p`.
    rcases hdiscBound with ⟨C, hC⟩
    exact hnat.submartingale.memLp_limitProcess (R := C) hC
  have hnatTendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (𝒢.limitProcess Y μ ω)) := by
    -- Proof comment: apply the discrete almost-sure convergence theorem to the natural skeleton.
    exact hnat.submartingale.ae_tendsto_limitProcess (R := R) fun n ↦ by
      simpa [Y] using hR (n : NNReal)
  have hnatToXInf :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ Y n ω) atTop (𝓝 (X∞ ω)) := by
    -- Proof comment: full-time convergence specializes to the natural-number subsequence.
    filter_upwards [hfull] with ω hω
    simpa [Y] using hω.comp tendsto_natCast_atTop_atTop
  have hEqNat :
      𝒢.limitProcess Y μ =ᵐ[μ] X∞ := by
    -- Proof comment: both the natural-time skeleton and the full process converge along the
    -- natural times, so their pointwise limits coincide almost surely.
    filter_upwards [hnatTendsto, hnatToXInf] with ω hωNat hωFull
    exact tendsto_nhds_unique hωNat hωFull
  have hmemXInf : MemLp X∞ (ENNReal.ofReal p) μ := by
    have hXinfAEMeas : AEStronglyMeasurable X∞ μ :=
      (MeasureTheory.Filtration.stronglyMeasurable_limit_process'
        (Ω := Ω) (m := ‹MeasurableSpace Ω›) (ι := NNReal) (ℱ := ℱ) (f := X) (μ := μ)
      ).aestronglyMeasurable
    have hEqNorm :
        ∀ᵐ ω ∂μ,
          ‖𝒢.limitProcess Y μ ω‖ = ‖X∞ ω‖ := by
      filter_upwards [hEqNat] with ω hω
      simp [hω]
    exact hmemNat.congr_norm hXinfAEMeas hEqNorm
  -- Proof comment: combine the ambient limit-process measurability with the `MemLp` transfer from
  -- the discrete natural-time skeleton and the previously established a.e. convergence.
  exact ⟨stronglyMeasurable_limitProcess, hmemXInf, hfull⟩

/-- Exercise 21.4.2, Theorem 11.10 analogue, `L^p` bridge companion: an `L^p`-bounded
right-continuous martingale with `1 < p` converges to its canonical limit process in the raw
`eLpNorm` formulation of `L^p`. -/
theorem rightContinuous_martingale_tendsto_eLpNorm_limitProcess_of_lp_bounded
    {p : ℝ} (hX : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ t : NNReal, eLpNorm (X t) (ENNReal.ofReal p) μ ≤ C) :
    Tendsto (fun t ↦ eLpNorm (X t - X∞) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  by_contra hnot
  obtain ⟨ε, hε, τ, hτ_mono, hτ_tendsto, hτ_bad⟩ :=
    existsMonotoneBadSubsequenceOfNotTendstoZero
      (f := fun t ↦ eLpNorm (X t - X∞) (ENNReal.ofReal p) μ) hnot
  let Y : ℕ → Ω → ℝ := fun n ω ↦ X (τ n) ω
  let 𝒢 : Filtration ℕ ‹MeasurableSpace Ω› := sampledFiltration (ℱ := ℱ) τ hτ_mono
  have hY : Martingale Y 𝒢 μ := by
    -- Proof comment: as in the `L¹` case, deterministic monotone sampling preserves the
    -- martingale structure.
    simpa [Y, 𝒢] using
      sampledMartingaleOfMonotone (X := X) (ℱ := ℱ) (μ := μ) hX hτ_mono
  have hYBound : ∃ C : NNReal, ∀ n : ℕ, eLpNorm (Y n) (ENNReal.ofReal p) μ ≤ C := by
    rcases hbounded with ⟨C, hC⟩
    exact ⟨C, fun n ↦ by simpa [Y] using hC (τ n)⟩
  have hYtendstoXInf :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (X∞ ω)) := by
    have hfull :
        ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) :=
      (rightContinuous_martingale_convergence_to_memLp_limitProcess_of_lp_bounded
        (X := X) (ℱ := ℱ) (μ := μ) hX_rc hX hp hbounded).2.2
    -- Proof comment: the full-time almost-sure limit restricts to the bad sampled sequence.
    filter_upwards [hfull] with ω hω
    simpa [Y] using hω.comp hτ_tendsto
  have hYlimit :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (𝒢.limitProcess Y μ ω)) := by
    -- Proof comment: apply the discrete Chapter 11 `L^p` convergence theorem to the sampled
    -- martingale.
    simpa using
      (martingale_convergence_to_memLp_limitProcess_of_lp_bounded
        (X := Y) (ℱ := 𝒢) (μ := μ) hY hp hYBound).2.2.1
  have hEq :
      𝒢.limitProcess Y μ =ᵐ[μ] X∞ :=
    sampledLimitProcess_ae_eq_of_ae_tendsto
      (μ := μ) (Y := Y) (𝒢 := 𝒢) (Z := X∞) hYlimit hYtendstoXInf
  have hdisc :
      Tendsto (fun n ↦ eLpNorm (Y n - X∞) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
    have hdisc' :
        Tendsto (fun n ↦ eLpNorm (Y n - 𝒢.limitProcess Y μ) (ENNReal.ofReal p) μ) atTop
          (𝓝 0) := by
      simpa using
        martingale_tendsto_eLpNorm_limitProcess_of_lp_bounded
          (X := Y) (ℱ := 𝒢) (μ := μ) hY hp hYBound
    have hEqNorm :
        (fun n ↦ eLpNorm (Y n - 𝒢.limitProcess Y μ) (ENNReal.ofReal p) μ) =
          fun n ↦ eLpNorm (Y n - X∞) (ENNReal.ofReal p) μ := by
      funext n
      exact eLpNorm_congr_ae ((EventuallyEq.refl (ae μ) (Y n)).sub hEq)
    rw [hEqNorm] at hdisc'
    exact hdisc'
  have hsmall : ∀ᶠ n in atTop, eLpNorm (Y n - X∞) (ENNReal.ofReal p) μ ≤ ε :=
    (ENNReal.tendsto_nhds_zero.1 hdisc) ε hε
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  exact (not_le.mpr (by simpa [Y] using hτ_bad N)) (hN N le_rfl)

omit hX_rc

end

end ProbabilityTheory
