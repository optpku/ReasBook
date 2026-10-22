/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_74
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_71

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
local notation "TimeFiltration" => Filtration NNReal mΩ

variable {ℱ : TimeFiltration}

/-- Helper for Corollary 21.76: the exponent comparison `1 ≤ 2` in `ℝ≥0∞`. -/
lemma oneLeTwoENNReal : (1 : ℝ≥0∞) ≤ 2 :=
  show (1 : ℝ≥0∞) ≤ 2 from one_le_two

/-- Helper for Corollary 21.76: a continuous local martingale is a local martingale up to the
deterministic horizon `∞`. -/
lemma continuousLocalMartingaleUpToInfinity {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    IsContinuousLocalMartingaleUpTo ℱ μ (fun _ ↦ ∞) M :=
  ⟨(isLocalMartingaleUpTo_iff ℱ μ (fun _ ↦ ∞) M).2
      ((isLocalMartingale_iff ℱ μ M).1 hM.local_martingale),
    hM.continuous⟩

/-- Helper for Corollary 21.76: stopping a process at the constant time `t` does nothing before
time `t`. -/
lemma stoppedProcessConst_eq_of_le {M : NNReal → Ω → ℝ} {s t : NNReal} (hst : s ≤ t) :
    stoppedProcess M (fun _ ↦ t) s = M s :=
  funext fun ω ↦
    stoppedProcess_eq_of_le (ω := ω) (i := s) (ENNReal.coe_le_coe.2 hst)

/-- Helper for Corollary 21.76: the constant stopping time `t` is strictly below `∞`. -/
lemma constStoppingTime_ltInfinity [Nonempty Ω] (t : NNReal) :
    (fun _ : Ω ↦ (t : ENNReal)) < fun _ ↦ (∞ : ENNReal) :=
  by
    exact (Function.const_lt_const (β := Ω) (a := (t : ENNReal)) (b := (∞ : ENNReal))).2
      ENNReal.coe_lt_top

/-- Helper for Corollary 21.76: integrability of the bracket process yields integrability after
stopping at a deterministic horizon. -/
lemma integrableStoppedValueBracketConst {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbracket_int : IsIntegrableProcess (continuousSquareVariationProcess hM) μ) (t : NNReal) :
    Integrable (stoppedValue (continuousSquareVariationProcess hM) (fun _ ↦ t)) μ :=
  (stoppedValue_const (continuousSquareVariationProcess hM) t).symm ▸ hbracket_int t

-- Proof sketch: localize `M` by bounded stopping times below `τ`, use the square-variation
-- identity to obtain a common second-moment bound for the doubly stopped slices
-- `M^(τ₀ ∧ τ_n)`, pass the martingale identities to the limit in `L¹`, and then transfer the
-- same uniform `L²` bound to the exact stopped process `M^τ₀`.
/-- Helper for Corollary 21.76: if `M` is a continuous local martingale up to `τ`, `τ₀ < τ` is a
finite stopping time, the square-variation process is integrable at `τ₀`, and `M 0 ∈ L²(μ)`,
then the stopped process `M^τ₀` is a martingale with a uniform `L²` bound. -/
theorem stoppedProcess_martingale_and_l2_bounded_of_localMartingaleUpTo_of_memLp_two
    {τ τ₀ : Ω → ENNReal} {M A : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M)
    (hτ : IsStoppingTime ℱ τ) (hτ₀ : IsStoppingTime ℱ τ₀) (hτ₀_lt : τ₀ < τ)
    (hA : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAτ₀ : Integrable (stoppedValue A τ₀) μ)
    (hM0_sq : MemLp (M 0) 2 μ) :
    Martingale (stoppedProcess M τ₀) ℱ μ ∧
      ∃ C : NNReal, ∀ t : NNReal, eLpNorm (stoppedProcess M τ₀ t) 2 μ ≤ C := by
  have hτ₀_fin : ∀ ω : Ω, τ₀ ω ≠ ∞ := fun ω ↦ ne_top_of_lt (hτ₀_lt ω)
  have _hSliceVariationBound :
      ∀ t ω, stoppedValue A (fun ω' ↦ min (τ₀ ω') (t : ENNReal)) ω ≤ stoppedValue A τ₀ ω := by
    intro t ω
    exact stoppedValue_le_stoppedValue_of_monotone
      (X := A) hA.monotone (σ := fun ω' ↦ min (τ₀ ω') (t : ENNReal)) (ρ := τ₀)
      (fun ω' ↦ min_le_left _ _) hτ₀_fin ω
  have hM_boundedApprox :
      HasBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M :=
    (isLocalMartingaleUpTo_iff_exists_bounded_stopped_martingale_sequence
      (ℱ := ℱ) (μ := μ) (τ := τ) (M := M) hM.adapted hM.continuous).1
      hM.local_martingale_upTo
  rcases hM_boundedApprox with ⟨τSeq, hApprox, hBoundedSeq⟩
  let ρ : ℕ → Ω → ENNReal := fun n ω ↦ min (τ₀ ω) (τSeq n ω)
  have hρ_fin : ∀ n : ℕ, ∀ ω : Ω, ρ n ω ≠ ∞ := by
    intro n ω
    exact ne_top_of_le_ne_top (hτ₀_fin ω) (min_le_left _ _)
  have hEventually :
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, τ₀ ω ≤ τSeq n ω :=
    ae_eventually_le_localizingApprox_of_lt
      (τ := τ) (τ₀ := τ₀) (τSeq := τSeq) hApprox hτ₀_lt
  have hApproxMart :
      ∀ n : ℕ, Martingale (stoppedProcess M (ρ n)) ℱ μ := by
    intro n
    have hDoubleStop :
        stoppedProcess (stoppedProcess M (τSeq n)) τ₀ = stoppedProcess M (ρ n) := by
      simpa [ρ, min_comm] using
        (stoppedProcess_stoppedProcess' :
          stoppedProcess (stoppedProcess M (τSeq n)) τ₀ =
            stoppedProcess M (fun ω ↦ min (τ₀ ω) (τSeq n ω)))
    have hStoppedMart :
        Martingale (stoppedProcess (stoppedProcess M (τSeq n)) τ₀) ℱ μ :=
      martingale_stoppedProcess_of_bounded
        (ℱ := ℱ) (μ := μ) (X := stoppedProcess M (τSeq n)) (hBoundedSeq n).1
        (continuous_stoppedProcess_of_continuous hM.continuous) (hBoundedSeq n).2 hτ₀
    -- Proof comment: each bounded owner `M^(τ_n)` stays a martingale after the extra stop at
    -- `τ₀`, and the double stop is exactly `M^(τ₀ ∧ τ_n)`.
    exact hDoubleStop ▸ hStoppedMart
  have hApproxSlice_tendsto :
      ∀ t : NNReal,
        ∀ᵐ ω ∂μ,
          Tendsto (fun n ↦ stoppedProcess M (ρ n) t ω) atTop
            (𝓝 (stoppedProcess M τ₀ t ω)) := by
    intro t
    filter_upwards [hEventually] with ω hω
    have hEventuallyEq :
        (fun n ↦ stoppedProcess M (ρ n) t ω) =ᶠ[atTop] fun _ ↦ stoppedProcess M τ₀ t ω := by
      filter_upwards [hω] with n hn
      have hρ_eq : ρ n ω = τ₀ ω := by
        simp [ρ, min_eq_left hn]
      simp [hρ_eq]
    -- Proof comment: once `τ_n(ω)` lies above `τ₀(ω)`, the approximate stopped process is
    -- literally the exact stopped process at time `t`.
    exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
  have hApproxSlice_meas :
      ∀ n : ℕ, ∀ t : NNReal, AEStronglyMeasurable (stoppedProcess M (ρ n) t) μ := by
    intro n t
    exact (hApproxMart n).integrable t |>.aestronglyMeasurable
  have hApproxSlice_sq :
      ∀ n : ℕ, ∀ t : NNReal,
        Integrable (fun ω ↦ (stoppedProcess M (ρ n) t ω) ^ 2) μ ∧
          ∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ ≤
            μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A τ₀] := by
    intro n t
    let σt : Ω → ENNReal := fun ω ↦ min (ρ n ω) (t : ENNReal)
    have hσt_stop : IsStoppingTime ℱ σt := (hτ₀.min (hApprox.2.1 n)).min_const t
    have hσt_fin : ∀ ω : Ω, σt ω ≠ ∞ := by
      intro ω
      exact ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
    have hσt_le_τSeq : ∀ ω, σt ω ≤ τSeq n ω := by
      intro ω
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hσt_le_τ₀ : ∀ ω, σt ω ≤ τ₀ ω := by
      intro ω
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hVariationInt :
        Integrable (stoppedValue A σt) μ := by
      exact integrable_stoppedValue_of_monotone_of_le
        (ℱ := ℱ) (μ := μ) (X := A) hA.adapted hA.zero hA.monotone
        hA.continuous hσt_stop hτ₀ hσt_le_τ₀ hτ₀_fin hAτ₀
    have hVariationIntegral_le :
        μ[stoppedValue A σt] ≤ μ[stoppedValue A τ₀] := by
      exact integral_stoppedValue_le_of_monotone_of_le
        (μ := μ) (X := A) hA.monotone
        (σ := σt) (ρ := τ₀) hσt_le_τ₀ hτ₀_fin hVariationInt hAτ₀
    rcases
        stoppedValue_sq_integrable_and_integral_eq_initial_add_variation_of_boundedOwner
          (ℱ := ℱ) (μ := μ) (M := M) (A := A) hA
          (hτ' := hApprox.2.1 n) (hσ := hσt_stop) (hσ_fin := hσt_fin)
          (hσ_le := hσt_le_τSeq) (hOwner := (hBoundedSeq n).1)
          (hOwner_bdd := (hBoundedSeq n).2) hVariationInt with
      ⟨hSqInt, hSqEq⟩
    constructor
    · simpa [σt, ρ, stoppedValue_min_const_eq_stoppedProcess] using hSqInt
    · -- Proof comment: the fixed-time triple stop `τ₀ ∧ τ_n ∧ t` fits the same compensated-square
      -- owner, and the remaining bracket term is again bounded by `A_{τ₀}`.
      calc
        ∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ =
            μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A σt] := by
              simpa [σt, ρ, stoppedValue_min_const_eq_stoppedProcess] using hSqEq
        _ ≤ μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A τ₀] := by
              gcongr
  let B : ℝ := μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A τ₀]
  have hInitialSquare_nonneg : 0 ≤ μ[fun ω ↦ (M 0 ω) ^ 2] := by
    exact integral_nonneg fun ω ↦ sq_nonneg (M 0 ω)
  have hAτ₀_nonneg : 0 ≤ μ[stoppedValue A τ₀] := by
    have hAτ₀_nonneg_ae : ∀ᵐ ω ∂μ, 0 ≤ stoppedValue A τ₀ ω := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      -- Proof comment: monotonicity of the square-variation path and `A 0 = 0` force
      -- `A_{τ₀(ω)} ≥ 0`.
      simpa [stoppedValue, hA.zero] using
        (hA.monotone ω (show (0 : NNReal) ≤ (τ₀ ω).untopA by exact zero_le _))
    exact integral_nonneg_ae hAτ₀_nonneg_ae
  have hB_nonneg : 0 ≤ B := add_nonneg hInitialSquare_nonneg hAτ₀_nonneg
  have hApproxSlice_UI :
      ∀ t : NNReal, UniformIntegrable (fun n : ℕ ↦ stoppedProcess M (ρ n) t) 1 μ := by
    intro t
    -- Proof comment: the common second-moment estimate for the localized slices upgrades to
    -- uniform integrability in `L¹`.
    exact uniformIntegrable_one_of_integrable_sq_bdd
      (μ := μ) (f := fun n : ℕ ↦ stoppedProcess M (ρ n) t)
      (fun n ↦ hApproxSlice_meas n t) (fun n ↦ (hApproxSlice_sq n t).1)
      hB_nonneg (fun n ↦ by simpa [B] using (hApproxSlice_sq n t).2)
  have hStoppedSlice_integrable :
      ∀ t : NNReal, Integrable (stoppedProcess M τ₀ t) μ := by
    intro t
    -- Proof comment: the exact slice is the almost-sure limit of a uniformly integrable family.
    exact (hApproxSlice_UI t).integrable_of_ae_tendsto (hApproxSlice_tendsto t)
  have hApproxSlice_tendsto_L1 :
      ∀ t : NNReal,
        Tendsto
          (fun n ↦
            eLpNorm
              (fun ω ↦ stoppedProcess M (ρ n) t ω - stoppedProcess M τ₀ t ω)
              1 μ)
          atTop (𝓝 0) := by
    intro t
    -- Proof comment: fixed-time almost-sure convergence plus uniform integrability gives `L¹`
    -- convergence of the localized slices to the exact stopped slice.
    exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun n ↦ hApproxSlice_meas n t)
      (memLp_one_iff_integrable.2 (hStoppedSlice_integrable t))
      (hApproxSlice_UI t).unifIntegrable (hApproxSlice_tendsto t)
  have hStoppedSetIntegralEq :
      ∀ ⦃s t : NNReal⦄, s ≤ t → ∀ ⦃u : Set Ω⦄, u ∈ ℱ s →
        ∫ ω in u, stoppedProcess M τ₀ s ω ∂μ =
          ∫ ω in u, stoppedProcess M τ₀ t ω ∂μ := by
    intro s t hst u hu
    have hLimit_s :
        Tendsto (fun n ↦ ∫ ω in u, stoppedProcess M (ρ n) s ω ∂μ) atTop
          (𝓝 (∫ ω in u, stoppedProcess M τ₀ s ω ∂μ)) :=
      tendsto_restrictedIntegral_of_tendsto_L1
        (μ := μ) (s := u) (hStoppedSlice_integrable s)
        (fun n ↦ (hApproxMart n).integrable s) (hApproxSlice_tendsto_L1 s)
    have hLimit_t :
        Tendsto (fun n ↦ ∫ ω in u, stoppedProcess M (ρ n) t ω ∂μ) atTop
          (𝓝 (∫ ω in u, stoppedProcess M τ₀ t ω ∂μ)) :=
      tendsto_restrictedIntegral_of_tendsto_L1
        (μ := μ) (s := u) (hStoppedSlice_integrable t)
        (fun n ↦ (hApproxMart n).integrable t) (hApproxSlice_tendsto_L1 t)
    have hEqSeq :
        ∀ n, ∫ ω in u, stoppedProcess M (ρ n) s ω ∂μ =
          ∫ ω in u, stoppedProcess M (ρ n) t ω ∂μ := by
      intro n
      simpa using (hApproxMart n).setIntegral_eq hst hu
    have hLimit_t' :
        Tendsto (fun n ↦ ∫ ω in u, stoppedProcess M (ρ n) s ω ∂μ) atTop
          (𝓝 (∫ ω in u, stoppedProcess M τ₀ t ω ∂μ)) := by
      refine Tendsto.congr' ?_ hLimit_t
      exact Filter.Eventually.of_forall hEqSeq
    -- Proof comment: the restricted-integral martingale identity for each localized owner passes
    -- to the limit because both fixed-time slice families converge in `L¹`.
    exact tendsto_nhds_unique hLimit_s hLimit_t'
  have hStrongStopped : StronglyAdapted ℱ (stoppedProcess M τ₀) :=
    hM.adapted.stronglyAdapted.stoppedProcess hM.continuous hτ₀
  have hStoppedMart : Martingale (stoppedProcess M τ₀) ℱ μ := by
    refine ⟨hStrongStopped, ?_⟩
    intro s t hst
    -- Proof comment: identify the conditional expectation at time `s` by the equality of all
    -- restricted integrals over `ℱ s`.
    exact ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hStoppedSlice_integrable t)
      (fun u _ _ ↦ (hStoppedSlice_integrable s).integrableOn)
      (fun u hu _ ↦ hStoppedSetIntegralEq hst hu)
      ((hStrongStopped s).aestronglyMeasurable)
  let q : ℝ≥0∞ := ENNReal.ofReal (2 : ℝ)
  let C : NNReal := ⟨B ^ (1 / 2 : ℝ), Real.rpow_nonneg hB_nonneg _⟩
  have hApproxSlice_eLpNorm_two_le :
      ∀ n : ℕ, ∀ t : NNReal, eLpNorm (stoppedProcess M (ρ n) t) q μ ≤ C := by
    intro n t
    have hMemLp : MemLp (stoppedProcess M (ρ n) t) q μ := by
      refine (integrable_norm_rpow_iff (hApproxSlice_meas n t) ?_ ?_).1 ?_
      · norm_num [q]
      · simp [q]
      · simpa [q, Real.norm_eq_abs, sq_abs] using (hApproxSlice_sq n t).1
    have hNorm :
        eLpNorm (stoppedProcess M (ρ n) t) q μ =
          ENNReal.ofReal
            ((∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
      -- Proof comment: for `p = 2`, the `eLpNorm` is the square root of the second moment.
      simpa [q, Real.norm_eq_abs, sq_abs] using
        (MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm
          (f := stoppedProcess M (ρ n) t) (p := q) (μ := μ)
          (by norm_num [q]) (by simp [q]) hMemLp)
    have hSq_nonneg : 0 ≤ ∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ := by
      exact integral_nonneg fun ω ↦ sq_nonneg _
    have hPow :
        (∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ B ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hSq_nonneg (by simpa [B] using (hApproxSlice_sq n t).2) (by norm_num)
    calc
      eLpNorm (stoppedProcess M (ρ n) t) q μ =
          ENNReal.ofReal
            ((∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := hNorm
      _ ≤ ENNReal.ofReal (B ^ (1 / 2 : ℝ)) := ENNReal.ofReal_le_ofReal hPow
      _ ≤ C := by simp [C]
  have hStopped_eLpNorm_two_le :
      ∀ t : NNReal, eLpNorm (stoppedProcess M τ₀ t) q μ ≤ C := by
    intro t
    -- Proof comment: lower semicontinuity of `eLpNorm` under almost-sure convergence transfers
    -- the common `L²` bound from the localized slices to the exact stopped slice.
    exact MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
      (u := atTop) (f := fun n : ℕ ↦ stoppedProcess M (ρ n) t)
      (g := stoppedProcess M τ₀ t) (C := C)
      (Filter.Eventually.of_forall fun n ↦ hApproxSlice_eLpNorm_two_le n t)
      (fun n ↦ hApproxSlice_meas n t) (hApproxSlice_tendsto t)
  exact ⟨hStoppedMart, ⟨C, fun t ↦ by simpa [q] using hStopped_eLpNorm_two_le t⟩⟩

/-- Helper for Corollary 21.76: the deterministic stopped process is an `L²`-bounded martingale. -/
lemma stoppedProcessMartingaleAndL2BoundOfIntegrableBracket {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) (hM0_sq : MemLp (M 0) 2 μ)
    (hbracket_int : IsIntegrableProcess (continuousSquareVariationProcess hM) μ) :
    ∀ t : NNReal,
      Martingale (stoppedProcess M (fun _ ↦ t)) ℱ μ ∧
        ∃ C : NNReal, ∀ u : NNReal, eLpNorm (stoppedProcess M (fun _ ↦ t) u) 2 μ ≤ C :=
  fun t ↦
    letI : Nonempty Ω := MeasureTheory.nonempty_of_isProbabilityMeasure μ
    stoppedProcess_martingale_and_l2_bounded_of_localMartingaleUpTo_of_memLp_two
      (hM := continuousLocalMartingaleUpToInfinity (ℱ := ℱ) (μ := μ) hM)
      (hτ := fun _ ↦ le_top)
      (hτ₀ := isStoppingTime_const ℱ t)
      (hτ₀_lt := constStoppingTime_ltInfinity (Ω := Ω) t)
      (hA := continuousSquareVariationProcess_spec hM)
      (hAτ₀ := integrableStoppedValueBracketConst (ℱ := ℱ) (μ := μ) hM hbracket_int t)
      (hM0_sq := hM0_sq)

/-- Helper for Corollary 21.76: an `L²` bound for the stopped martingale at time `t` yields
`MemLp` for the terminal marginal. -/
lemma stoppedProcessSelf_memLp_of_l2Bound {M : NNReal → Ω → ℝ} (t : NNReal)
    (hMart : Martingale (stoppedProcess M (fun _ ↦ t)) ℱ μ)
    (hBound : ∃ C : NNReal, ∀ u : NNReal, eLpNorm (stoppedProcess M (fun _ ↦ t) u) 2 μ ≤ C) :
    MemLp (stoppedProcess M (fun _ ↦ t) t) 2 μ :=
  match hBound with
  | ⟨_, hC⟩ =>
      ⟨(hMart.integrable t).aestronglyMeasurable, lt_of_le_of_lt (hC t) ENNReal.coe_lt_top⟩

/-- Helper for Corollary 21.76: integrable bracket marginals imply square integrability of the
martingale marginals. -/
lemma squareIntegrableProcessOfIntegrableBracket {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) (hM0_sq : MemLp (M 0) 2 μ)
    (hbracket_int : IsIntegrableProcess (continuousSquareVariationProcess hM) μ) :
    IsSquareIntegrableProcess M μ :=
  fun t ↦
    match
        stoppedProcessMartingaleAndL2BoundOfIntegrableBracket
          (ℱ := ℱ) (μ := μ) hM hM0_sq hbracket_int t with
    | ⟨hMart, hBound⟩ =>
        Eq.mp
          (congrArg (fun X ↦ MemLp X 2 μ)
            (stoppedProcessConst_eq_of_le (M := M) (s := t) (t := t) le_rfl))
          (stoppedProcessSelf_memLp_of_l2Bound (ℱ := ℱ) (μ := μ) t hMart hBound)

/-- Helper for Corollary 21.76: deterministic stopping transfers the martingale set-integral
identity back to the original process. -/
lemma setIntegralEqOfIntegrableBracket {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) (hM0_sq : MemLp (M 0) 2 μ)
    (hbracket_int : IsIntegrableProcess (continuousSquareVariationProcess hM) μ)
    {s t : NNReal} (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, M t ω ∂μ = ∫ ω in A, M s ω ∂μ :=
  match
      stoppedProcessMartingaleAndL2BoundOfIntegrableBracket
        (ℱ := ℱ) (μ := μ) hM hM0_sq hbracket_int t with
  | ⟨hMart, _⟩ =>
      let hEqT :
          ∫ ω in A, stoppedProcess M (fun _ ↦ t) t ω ∂μ = ∫ ω in A, M t ω ∂μ :=
        congrArg (fun f ↦ ∫ ω in A, f ω ∂μ)
          (stoppedProcessConst_eq_of_le (M := M) (s := t) (t := t) le_rfl)
      let hEqS :
          ∫ ω in A, stoppedProcess M (fun _ ↦ t) s ω ∂μ = ∫ ω in A, M s ω ∂μ :=
        congrArg (fun f ↦ ∫ ω in A, f ω ∂μ)
          (stoppedProcessConst_eq_of_le (M := M) (s := s) (t := t) hst)
      Eq.trans hEqT.symm <| Eq.trans (hMart.setIntegral_eq hst hA).symm hEqS

/-- Helper for Corollary 21.76: negating the set-integral identity produces the supermartingale
inequality for `-M`. -/
lemma negSetIntegralLeOfIntegrableBracket {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) (hM0_sq : MemLp (M 0) 2 μ)
    (hbracket_int : IsIntegrableProcess (continuousSquareVariationProcess hM) μ)
    {s t : NNReal} (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, -M s ω ∂μ ≤ ∫ ω in A, -M t ω ∂μ :=
  le_of_eq <|
    let hEqNeg :
        -(∫ ω in A, M s ω ∂μ) = -(∫ ω in A, M t ω ∂μ) :=
      congrArg Neg.neg <|
        (setIntegralEqOfIntegrableBracket
          (ℱ := ℱ) (μ := μ) hM hM0_sq hbracket_int hst hA).symm
    Eq.trans (integral_neg (f := fun ω ↦ M s ω)).symm <|
      Eq.trans hEqNeg (integral_neg (f := fun ω ↦ M t ω))

-- Proof sketch: apply the square-variation theory to the canonical bracket process `⟨M⟩[hM]`;
-- the integrability of `M 0 ^ 2` and of the bracket
-- marginals upgrades the local-martingale identity for `M² - ⟨M⟩` to a genuine martingale and
-- yields `L²`-integrability of every time marginal of `M`.
/-- Corollary 21.76: if a continuous local martingale has square-integrable
initial value and integrable canonical bracket marginals, then it is a square-integrable
martingale. -/
theorem square_integrable_martingale_of_integrable_bracket
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (_hM0_sq : MemLp (M 0) 2 μ)
    (_hbracket_int : IsIntegrableProcess (continuousSquareVariationProcess hM) μ) :
    Martingale M ℱ μ ∧ IsSquareIntegrableProcess M μ :=
  let hSquareInt : IsSquareIntegrableProcess M μ :=
    squareIntegrableProcessOfIntegrableBracket (ℱ := ℱ) (μ := μ) hM _hM0_sq _hbracket_int
  let hSub : Submartingale M ℱ μ :=
    submartingale_of_setIntegral_le hM.adapted.stronglyAdapted
      (fun t ↦
        memLp_one_iff_integrable.mp <| (hSquareInt t).mono_exponent oneLeTwoENNReal)
      (fun s t hst A hA ↦
        le_of_eq <|
          (setIntegralEqOfIntegrableBracket
            (ℱ := ℱ) (μ := μ) hM _hM0_sq _hbracket_int hst hA).symm)
  let hSubNeg : Submartingale (-M) ℱ μ :=
    submartingale_of_setIntegral_le hM.adapted.stronglyAdapted.neg
      (fun t ↦
        (memLp_one_iff_integrable.mp <|
          (hSquareInt t).mono_exponent oneLeTwoENNReal).neg)
      (fun s t hst A hA ↦
        negSetIntegralLeOfIntegrableBracket
          (ℱ := ℱ) (μ := μ) hM _hM0_sq _hbracket_int hst hA)
  ⟨(martingale_iff).2 ⟨hSubNeg.neg, hSub⟩, hSquareInt⟩

-- Proof sketch: since `Mlocc ℱ μ` is the set-level view of the owner
-- `IsContinuousLocalMartingale ℱ μ`, apply
-- `square_integrable_martingale_of_integrable_bracket` directly to `hM` and its canonical
-- bracket `⟨M⟩[hM]`.
/-- Helper for Corollary 21.76 in the textbook notation `M ∈ 𝓜_{loc,c}`. This is the thin
bridge from the set-level view `Mlocc ℱ μ` to the owner theorem
`square_integrable_martingale_of_integrable_bracket`. -/
theorem square_integrable_martingale_of_mem_Mlocc_of_integrable_bracket
    {M : NNReal → Ω → ℝ} (hM : M ∈ Mlocc ℱ μ)
    (_hM0_sq : MemLp (M 0) 2 μ)
    (_hbracket_int : IsIntegrableProcess (continuousSquareVariationProcess hM) μ) :
    Martingale M ℱ μ ∧ IsSquareIntegrableProcess M μ :=
  square_integrable_martingale_of_integrable_bracket hM _hM0_sq _hbracket_int

end ProbabilityTheory
