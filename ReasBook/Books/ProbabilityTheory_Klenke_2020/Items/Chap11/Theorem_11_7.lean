/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {μ : Measure Ω}
variable {X : ℕ → Ω → ℝ}

local notation "supermartingaleLimit" => fun ω ↦ -(ℱ.limitProcess (-X) μ ω)

private theorem uniformIntegrable_neg
    (hUI : UniformIntegrable X 1 μ) :
    UniformIntegrable (-X) 1 μ := by
  rcases hUI with ⟨hX_meas, hX_unif, hX_bdd⟩
  rcases hX_bdd with ⟨C, hC⟩
  refine ⟨fun n ↦ (hX_meas n).neg, hX_unif.neg, ⟨C, fun n ↦ ?_⟩⟩
  simpa using hC n

/- For Theorem 11.7, item (1), the martingale and submartingale cases use the
owner-level declaration that `ℱ.limitProcess X μ` is `⨆ n, ℱ n`-strongly
measurable. -/
recall MeasureTheory.Filtration.stronglyMeasurable_limitProcess

/-- Helper for Theorem 11.7: the canonical supermartingale limit random variable
`ω ↦ -ℱ.limitProcess (-X) μ ω` is `⨆ n, ℱ n`-strongly measurable. -/
theorem supermartingale_stronglyMeasurable_limitProcess
    : StronglyMeasurable[⨆ n, ℱ n] supermartingaleLimit := by
  have h_limit : StronglyMeasurable[⨆ n, ℱ n] (ℱ.limitProcess (-X) μ) :=
    stronglyMeasurable_limitProcess
  change StronglyMeasurable[⨆ n, ℱ n] (fun ω ↦ -(ℱ.limitProcess (-X) μ ω))
  simpa using h_limit.neg

variable [IsFiniteMeasure μ]

/-- Helper for Theorem 11.7: the canonical limit process of a uniformly integrable
submartingale is integrable; the martingale case is the specialization
`hX.submartingale`. -/
theorem submartingale_integrable_limitProcess_of_uniformIntegrable
    (hX : Submartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Integrable (ℱ.limitProcess X μ) μ := by
  obtain ⟨R, hR⟩ := hUI.2.2
  exact (hX.memLp_limitProcess hR).integrable le_rfl

/-- Helper for Theorem 11.7: the canonical supermartingale limit random variable
`ω ↦ -ℱ.limitProcess (-X) μ ω` is integrable. -/
theorem supermartingale_integrable_limitProcess_of_uniformIntegrable
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Integrable supermartingaleLimit μ := by
  have h_limit :
      Integrable (ℱ.limitProcess (-X) μ) μ :=
    submartingale_integrable_limitProcess_of_uniformIntegrable hX.neg
      (uniformIntegrable_neg hUI)
  change Integrable (fun ω ↦ -(ℱ.limitProcess (-X) μ ω)) μ
  simpa using h_limit.neg

/- For Theorem 11.7, item (3), the submartingale statement, and hence also the
martingale case, is exactly the owner-level convergence theorem to
`ℱ.limitProcess X μ`. -/
recall MeasureTheory.Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable

/-- Helper for Theorem 11.7: the supermartingale case follows by applying the owner
theorem to `-X` and negating the limit. -/
theorem supermartingale_ae_tendsto_limitProcess_of_uniformIntegrable
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (supermartingaleLimit ω)) := by
  have h_neg_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ -X n ω) atTop (𝓝 (ℱ.limitProcess (-X) μ ω)) :=
    hX.neg.ae_tendsto_limitProcess_of_uniformIntegrable (uniformIntegrable_neg hUI)
  filter_upwards [h_neg_tendsto] with ω hω
  simpa using hω.neg

/- For Theorem 11.7, item (4), the submartingale statement, and hence also the
martingale case, is exactly the owner-level `L¹` convergence theorem to
`ℱ.limitProcess X μ`. -/
recall MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess

/-- Helper for Theorem 11.7: `X` converges in `L¹` to
`ω ↦ -ℱ.limitProcess (-X) μ ω`. -/
theorem supermartingale_tendsto_eLpNorm_one_limitProcess_of_uniformIntegrable
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Tendsto (fun n ↦ eLpNorm (X n - supermartingaleLimit) 1 μ) atTop (𝓝 0) := by
  have h_neg_tendsto :
      Tendsto (fun n ↦ eLpNorm (-X n - ℱ.limitProcess (-X) μ) 1 μ) atTop (𝓝 0) :=
    hX.neg.tendsto_eLpNorm_one_limitProcess (uniformIntegrable_neg hUI)
  have h_eq :
      (fun n ↦ eLpNorm (X n - supermartingaleLimit) 1 μ) =
        fun n ↦ eLpNorm (-X n - ℱ.limitProcess (-X) μ) 1 μ := by
    funext n
    calc
      eLpNorm (X n - supermartingaleLimit) 1 μ =
          eLpNorm (-(-X n - ℱ.limitProcess (-X) μ)) 1 μ := by
            refine eLpNorm_congr_ae (.of_forall fun ω ↦ ?_)
            simp [sub_eq_add_neg, add_comm]
      _ = eLpNorm (-X n - ℱ.limitProcess (-X) μ) 1 μ := by
            rw [eLpNorm_neg]
  rw [h_eq]
  exact h_neg_tendsto

/- For Theorem 11.7, the martingale conditional-expectation identity is the
canonical mathlib statement
`MeasureTheory.Martingale.ae_eq_condExp_limitProcess`, with limit random
variable `ℱ.limitProcess X μ`. -/
recall MeasureTheory.Martingale.ae_eq_condExp_limitProcess

-- Proof sketch: combine the `L¹` convergence of `X` to `ℱ.limitProcess X μ` with continuity of
-- conditional expectation in `L¹`, then pass to the limit in the submartingale inequalities
-- `X n ≤ 𝔼[X m | ℱ n]` for `m ≥ n`.
/-- Theorem 11.7: for a uniformly integrable submartingale, each time slice is
almost surely bounded above by the conditional expectation of the canonical
limit process. -/
theorem submartingale_ae_le_condExp_limitProcess_of_uniformIntegrable
    (hX : Submartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) (n : ℕ) :
    X n ≤ᵐ[μ] μ[ℱ.limitProcess X μ | ℱ n] := by
  let L : Ω → ℝ := ℱ.limitProcess X μ
  have hLInt : Integrable L μ := by
    -- Proof comment: the limiting process is integrable by the uniform-integrability theorem above.
    simpa [L] using submartingale_integrable_limitProcess_of_uniformIntegrable hX hUI
  have hNegPartAesm :
      AEStronglyMeasurable (fun ω ↦ (μ[L | ℱ n] ω - X n ω)⁻) μ := by
    -- Proof comment: the limit gap is `ℱ n`-measurable, so its negative part is a.e. strongly
    -- measurable and we may apply `eLpNorm_eq_zero_iff` later.
    exact continuous_negPart.comp_aestronglyMeasurable
      (((stronglyMeasurable_condExp.mono (ℱ.le n)).sub
        ((hX.stronglyMeasurable n).mono (ℱ.le n))).aestronglyMeasurable)
  have hCondExpErrorTends :
      Tendsto (fun m ↦ eLpNorm (μ[X m - L | ℱ n]) 1 μ) atTop (𝓝 0) := by
    -- Proof comment: conditional expectation is an `L¹` contraction, so the conditional
    -- expectation of the error inherits the `L¹` convergence to the limit process.
    have hLimitTends :
        Tendsto (fun m ↦ eLpNorm (X m - L) 1 μ) atTop (𝓝 0) := by
      simpa [L] using hX.tendsto_eLpNorm_one_limitProcess hUI
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLimitTends
      (fun _ ↦ zero_le _) ?_
    intro m
    exact eLpNorm_one_condExp_le_eLpNorm (μ := μ) (m := ℱ n) (f := X m - L)
  have hGapNonneg :
      ∀ m ≥ n, 0 ≤ᵐ[μ] μ[X m - L | ℱ n] + (μ[L | ℱ n] - X n) := by
    intro m hm
    have hRewrite :
        μ[X m - X n | ℱ n] =ᵐ[μ] μ[X m - L | ℱ n] + (μ[L | ℱ n] - X n) := by
      -- Proof comment: split the increment `X m - X n` into the error term `X m - L` and the
      -- limit gap `L - X n`, then rewrite the latter conditional expectation using adaptedness.
      calc
        μ[X m - X n | ℱ n] =ᵐ[μ] μ[(X m - L) + (L - X n) | ℱ n] := by
          exact condExp_congr_ae <| Filter.Eventually.of_forall fun ω ↦ by
            change X m ω - X n ω = (X m ω - L ω) + (L ω - X n ω)
            ring
        _ =ᵐ[μ] μ[X m - L | ℱ n] + μ[L - X n | ℱ n] := by
          exact condExp_add ((hX.integrable m).sub hLInt) (hLInt.sub (hX.integrable n)) (ℱ n)
        _ =ᵐ[μ] μ[X m - L | ℱ n] + (μ[L | ℱ n] - X n) := by
          have hGapCondExp :
              μ[L - X n | ℱ n] =ᵐ[μ] μ[L | ℱ n] - X n := by
            refine (condExp_sub hLInt (hX.integrable n) (ℱ n)).trans ?_
            exact Filter.Eventually.of_forall fun ω ↦ by
              rw [condExp_of_stronglyMeasurable (ℱ.le n) (hX.stronglyMeasurable n)
                (hX.integrable n)]
          exact EventuallyEq.rfl.add hGapCondExp
    exact (hX.condExp_sub_nonneg hm).trans hRewrite.le
  have hNegPartBound :
      ∀ m ≥ n,
        eLpNorm (fun ω ↦ (μ[L | ℱ n] ω - X n ω)⁻) 1 μ ≤ eLpNorm (μ[X m - L | ℱ n]) 1 μ := by
    intro m hm
    -- Proof comment: pointwise nonnegativity of the rewritten increment bounds the negative part
    -- of the limit gap by the absolute conditional-expectation error.
    refine eLpNorm_mono_ae ?_
    filter_upwards [hGapNonneg m hm] with ω hω
    have hω' :
        0 ≤ μ[X m - L | ℱ n] ω + (μ[L | ℱ n] ω - X n ω) := by
      simpa [Pi.add_apply, Pi.sub_apply] using hω
    by_cases hGap : 0 ≤ μ[L | ℱ n] ω - X n ω
    · rw [negPart_eq_zero.2 hGap]
      simp
    · have hGap' : μ[L | ℱ n] ω - X n ω < 0 := lt_of_not_ge hGap
      have hErrNonneg : 0 ≤ μ[X m - L | ℱ n] ω := by
        linarith
      rw [negPart_eq_neg.2 (le_of_lt hGap'), norm_neg, Real.norm_eq_abs, abs_of_neg hGap',
        Real.norm_eq_abs, abs_of_nonneg hErrNonneg]
      linarith
  have hNegPartNormTendsToZero :
      Tendsto (fun _ : ℕ ↦ eLpNorm (fun ω ↦ (μ[L | ℱ n] ω - X n ω)⁻) 1 μ) atTop (𝓝 0) := by
    -- Proof comment: the negative-part seminorm is squeezed between `0` and the vanishing
    -- conditional-expectation error seminorm.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCondExpErrorTends
      (Filter.Eventually.of_forall fun _ ↦ zero_le _) ?_
    exact show
        ∀ᶠ m in atTop,
          (fun _ : ℕ ↦ eLpNorm (fun ω ↦ (μ[L | ℱ n] ω - X n ω)⁻) 1 μ) m ≤
            eLpNorm (μ[X m - L | ℱ n]) 1 μ from
      Filter.eventually_atTop.2 ⟨n, fun m hm ↦ hNegPartBound m hm⟩
  have hNegPartNormZero :
      eLpNorm (fun ω ↦ (μ[L | ℱ n] ω - X n ω)⁻) 1 μ = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hNegPartNormTendsToZero
  have hNegPartZero :
      (fun ω ↦ (μ[L | ℱ n] ω - X n ω)⁻) =ᵐ[μ] 0 := by
    -- Proof comment: vanishing `eLpNorm` forces the negative part itself to vanish a.e.
    exact (eLpNorm_eq_zero_iff hNegPartAesm one_ne_zero).1 hNegPartNormZero
  -- Proof comment: zero negative part is exactly the almost-sure order relation we need.
  filter_upwards [hNegPartZero] with ω hω
  exact sub_nonneg.mp ((negPart_eq_zero).mp hω)

-- Proof sketch: apply the previous submartingale result to `-X`, identify the limiting random
-- variable of `-X` with `fun ω ↦ -ℱ.limitProcess (-X) μ ω`, and rewrite the conditional
-- expectation using `condExp_neg`.
/-- For a uniformly integrable supermartingale, each time slice is almost surely bounded below by
the conditional expectation of its canonical limit random variable. -/
theorem supermartingale_ae_ge_condExp_limit_of_uniformIntegrable
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) (n : ℕ) :
    μ[fun ω ↦ -ℱ.limitProcess (-X) μ ω | ℱ n] ≤ᵐ[μ] X n := by
  have h_neg_le :
      -X n ≤ᵐ[μ] μ[ℱ.limitProcess (-X) μ | ℱ n] :=
    submartingale_ae_le_condExp_limitProcess_of_uniformIntegrable hX.neg
      (uniformIntegrable_neg hUI) n
  have h_neg_ge :
      -μ[ℱ.limitProcess (-X) μ | ℱ n] ≤ᵐ[μ] X n :=
    h_neg_le.mono fun ω hω ↦ by
      simpa using neg_le_neg hω
  exact (condExp_neg (ℱ.limitProcess (-X) μ) (ℱ n)).le.trans h_neg_ge
