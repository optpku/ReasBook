/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Corollary_10_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal MeasureTheory

open MeasureTheory

universe u

section

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration μ ℱ] {τ : ℕ → Ω → ℕ}

/- Corollary 10.22 is `source-facing`: it keeps the sampled martingale and supermartingale
processes indexed by the original finite stopping-time sequence. The owner filtration abstraction is
the chapter-level `stoppingTimeSequenceFiltration` from Corollary 10.12, while the finite optional
sampling input comes from Theorem 10.21. The primitive ambient hypothesis for that owner API is
`[SigmaFiniteFiltration μ ℱ]`, so this file exposes exactly that canonical assumption instead of
the stronger derived instance `[IsFiniteMeasure μ]`. -/

local notation "τ∞" => fun n ω ↦ (τ n ω : ℕ∞)

section

variable {X : ℕ → Ω → ℝ}
variable (hτ : ∀ n, IsStoppingTime ℱ (τ∞ n)) (hmono : Monotone τ)

private theorem monotone_tauInf (hmono : Monotone τ) : Monotone τ∞ := by
  intro i j hij ω
  exact WithTop.coe_le_coe.2 (hmono hij ω)

local notation "ℱτ" =>
  stoppingTimeSequenceFiltration ℱ τ∞ hτ (monotone_tauInf hmono)

/-- Helper for Corollary 10.22: the optional-sampling identity from Theorem 10.21 gives the
martingale conditional-expectation relation for the stopped-value sequence. -/
private theorem stoppedValueSequence_martingale_condExp_ae_eq
    (_hX : Martingale X ℱ μ) (_hUI : UniformIntegrable X 1 μ) (m n : ℕ) (_hmn : m ≤ n) :
    μ[stoppedValue X (τ∞ n) | ℱτ m] =ᵐ[μ] stoppedValue X (τ∞ m) :=
  -- Rewrite the induced filtration at time `m`, then apply finite optional sampling to
  -- the stopping times `τ m ≤ τ n`.
    (martingale_condExp_stoppedValue_ae_eq_of_uniformIntegrable_of_le_of_finite
      (X := X) (μ := μ) (ℱ := ℱ) _hX _hUI (hτ m) (hτ n) (fun ω ↦ hmono _hmn ω)).2

/-- Helper for Corollary 10.22: the supermartingale form of Theorem 10.21 gives the
conditional-expectation inequality for the stopped-value sequence. -/
private theorem stoppedValueSequence_supermartingale_condExp_ae_le
    (_hX : Supermartingale X ℱ μ) (_hUI : UniformIntegrable X 1 μ) (m n : ℕ) (_hmn : m ≤ n) :
    μ[stoppedValue X (τ∞ n) | ℱτ m] ≤ᵐ[μ] stoppedValue X (τ∞ m) :=
  -- Rewrite the induced filtration at time `m`, then apply the supermartingale optional
  -- sampling inequality to the stopping times `τ m ≤ τ n`.
    (supermartingale_condExp_stoppedValue_ae_le_of_uniformIntegrable_of_le_of_finite
      (X := X) (μ := μ) (ℱ := ℱ) _hX _hUI (hτ m) (hτ n) (fun ω ↦ hmono _hmn ω)).2

/-- Helper for Corollary 10.22: each sampled stopped value of a uniformly integrable
supermartingale is integrable. -/
private theorem integrable_stoppedValueSequence_of_uniformIntegrable_supermartingale
    (hτ' : ∀ n, IsStoppingTime ℱ (τ∞ n))
    (_hX : Supermartingale X ℱ μ) (_hUI : UniformIntegrable X 1 μ) (n : ℕ) :
    Integrable (stoppedValue X (τ∞ n)) μ := by
  -- Reuse the finite optional-sampling theorem at equal stopping times to obtain integrability.
  exact
    (supermartingale_condExp_stoppedValue_ae_le_of_uniformIntegrable_of_le_of_finite
      (X := X) (μ := μ) (ℱ := ℱ) _hX _hUI (hτ' n) (hτ' n) (fun ω ↦ le_rfl)).1

/-- Corollary 10.22 (1): in the martingale case, sampling a uniformly integrable martingale
along an increasing sequence of finite stopping times yields a martingale with respect to the
filtration formed by the
corresponding stopping-time `σ`-algebras. -/
-- Proof sketch: apply the uniformly integrable optional sampling identity from Theorem 10.21 to
-- each pair `τ m ≤ τ n` with `m ≤ n`; the monotonicity of the stopping times makes the
-- corresponding stopping-time `σ`-algebras into an increasing filtration.
theorem stoppedValue_martingale_of_uniformIntegrable_of_monotone_finite_stopping_times
    (_hX : Martingale X ℱ μ) (_hUI : UniformIntegrable X 1 μ) :
    Martingale (fun n ↦ stoppedValue X (τ∞ n)) ℱτ μ :=
  ⟨stronglyAdapted_stoppedValueSequence _hX.stronglyAdapted hτ (monotone_tauInf hmono),
    fun m n hmn ↦ stoppedValueSequence_martingale_condExp_ae_eq _hX _hUI m n hmn⟩

/-- Corollary 10.22 (2): in the supermartingale case, sampling a uniformly integrable
supermartingale along an increasing sequence of finite stopping times yields a
supermartingale with respect to the induced
stopping-time filtration. -/
-- Proof sketch: apply the supermartingale form of Theorem 10.21 to each pair `τ m ≤ τ n`, and use
-- the monotonicity of the stopping times to view the stopping-time `σ`-algebras as an increasing
-- filtration.
theorem stoppedValue_supermartingale_of_uniformIntegrable_of_monotone_finite_stopping_times
    (_hX : Supermartingale X ℱ μ) (_hUI : UniformIntegrable X 1 μ) :
    Supermartingale (fun n ↦ stoppedValue X (τ∞ n)) ℱτ μ :=
  ⟨stronglyAdapted_stoppedValueSequence _hX.1 hτ (monotone_tauInf hmono),
    fun m n hmn ↦ stoppedValueSequence_supermartingale_condExp_ae_le _hX _hUI m n hmn,
    fun n ↦ integrable_stoppedValueSequence_of_uniformIntegrable_supermartingale hτ _hX _hUI n⟩

end

end
