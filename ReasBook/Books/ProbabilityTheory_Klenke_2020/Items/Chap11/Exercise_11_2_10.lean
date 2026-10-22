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

section

variable (μ : Measure Ω) [IsFiniteMeasure μ]
variable (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)

local notation "TerminalValueSpace" => lpMeas ℝ ℝ (⨆ n, ℱ n) 1 μ
local notation "ProcessSpace" => ℕ → Lp ℝ 1 μ

/- Exercise 11.2.10 is `source-facing`: it identifies the actual vector space of uniformly
integrable `ℱ`-martingales with the terminal-value space `L¹(⨆ n, ℱ n)`. The
`core/canonical` owner abstractions are the existing martingale and uniform-integrability APIs on
processes, together with the `L¹` conditional-expectation operator `condExpL1CLM`. The quotient
level codomain is therefore organized as the submodule of `L¹`-classes admitting an actual
uniformly integrable martingale representative, while the conditional-expectation process map is
the `bridge/view` from a terminal class to that submodule. -/

/-- The `Lp`-valued conditional-expectation martingale attached to an `L¹(ℱ∞)` terminal class. -/
noncomputable def terminalValueMartingaleProcess :
    TerminalValueSpace →ₗ[ℝ] ProcessSpace where
  toFun X := fun n ↦ condExpL1CLM ℝ (ℱ.le n) μ (X : Lp ℝ 1 μ)
  map_add' := by
    intro X Y
    funext n
    exact map_add (condExpL1CLM ℝ (ℱ.le n) μ) (X : Lp ℝ 1 μ) (Y : Lp ℝ 1 μ)
  map_smul' := by
    intro c X
    funext n
    exact map_smul (condExpL1CLM ℝ (ℱ.le n) μ) c (X : Lp ℝ 1 μ)

/-- A quotient-level process is a uniformly integrable `ℱ`-martingale if it admits an actual
uniformly integrable martingale representative. -/
def IsUiMartingaleProcess (f : ProcessSpace) : Prop :=
  ∃ X : ℕ → Ω → ℝ, Martingale X ℱ μ ∧ UniformIntegrable X 1 μ ∧
    ∀ n, (f n : Ω → ℝ) =ᵐ[μ] X n

omit [IsFiniteMeasure μ] in
private theorem uniformIntegrable_zero_process :
    UniformIntegrable (0 : ℕ → Ω → ℝ) 1 μ := by
  refine ⟨fun _ ↦ aestronglyMeasurable_zero, ?_, ⟨0, fun _ ↦ by simp⟩⟩
  intro ε hε
  refine ⟨1, zero_lt_one, fun _ _ _ _ ↦ by simp⟩

omit [IsFiniteMeasure μ] in
private theorem uniformIntegrable_add {f g : ℕ → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) (hg : UniformIntegrable g 1 μ) :
    UniformIntegrable (f + g) 1 μ := by
  refine ⟨fun n ↦ (hf.aestronglyMeasurable n).add (hg.aestronglyMeasurable n), ?_, ?_⟩
  · exact hf.unifIntegrable.add hg.unifIntegrable le_rfl
      (fun n ↦ hf.aestronglyMeasurable n) (fun n ↦ hg.aestronglyMeasurable n)
  · rcases hf.2.2 with ⟨Cf, hCf⟩
    rcases hg.2.2 with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun n ↦ ?_⟩
    exact (eLpNorm_add_le (hf.aestronglyMeasurable n) (hg.aestronglyMeasurable n) le_rfl).trans
      (add_le_add (hCf n) (hCg n))

omit [IsFiniteMeasure μ] in
private theorem uniformIntegrable_smul (c : ℝ) {f : ℕ → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) :
    UniformIntegrable (c • f) 1 μ := by
  refine ⟨fun n ↦ (hf.aestronglyMeasurable n).const_smul c, ?_, ?_⟩
  · by_cases hc : c = 0
    · -- The zero scalar collapses the process to the trivial uniformly integrable martingale.
      subst hc
      simpa using (uniformIntegrable_zero_process (μ := μ)).unifIntegrable
    · -- Rescale the uniform-integrability estimates by `‖c‖`.
      intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ :=
        hf.unifIntegrable (ε := ε / ‖c‖) (div_pos hε (norm_pos_iff.2 hc))
      refine ⟨δ, hδpos, fun n s hs hμs ↦ ?_⟩
      have hsIndicator :
          s.indicator ((c • f) n) = c • s.indicator (f n) := by
        funext x
        by_cases hx : x ∈ s
        · simp [hx, Pi.smul_apply]
        · simp [hx, Pi.smul_apply]
      have hmul : ‖c‖ * (ε / ‖c‖) = ε := by
        field_simp [hc]
      calc
        eLpNorm (s.indicator ((c • f) n)) 1 μ
            = eLpNorm (c • s.indicator (f n)) 1 μ := by
              rw [hsIndicator]
        _ = ‖c‖ₑ * eLpNorm (s.indicator (f n)) 1 μ := by
              rw [eLpNorm_const_smul]
        _ ≤ ‖c‖ₑ * ENNReal.ofReal (ε / ‖c‖) := by
              simpa [mul_comm] using mul_le_mul_left (hδ n s hs hμs) ‖c‖ₑ
        _ = ENNReal.ofReal ε := by
              rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul]
              · rw [hmul]
              · exact norm_nonneg _
  · -- The uniform `L¹` bound scales linearly under scalar multiplication.
    rcases hf.2.2 with ⟨C, hC⟩
    refine ⟨‖c‖₊ * C, fun n ↦ ?_⟩
    calc
      eLpNorm ((c • f) n) 1 μ = ‖c‖ₑ * eLpNorm (f n) 1 μ := by
        rw [Pi.smul_apply, eLpNorm_const_smul]
      _ ≤ ‖c‖ₑ * C := by
        simpa [mul_comm] using mul_le_mul_left (hC n) ‖c‖ₑ
      _ = ↑(‖c‖₊ * C) := by
        rw [enorm_eq_nnnorm]
        rfl

/-- The quotient-level vector space of uniformly integrable `ℱ`-martingales. -/
def uiMartingaleSubmodule : Submodule ℝ ProcessSpace where
  carrier := {f | IsUiMartingaleProcess μ ℱ f}
  zero_mem' := by
    refine ⟨0, martingale_zero ℝ ℱ μ, uniformIntegrable_zero_process μ,
      fun _ ↦ Lp.coeFn_zero ℝ 1 μ⟩
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨F, hFmart, hFui, hF⟩
    rcases hg with ⟨G, hGmart, hGui, hG⟩
    refine ⟨F + G, hFmart.add hGmart, uniformIntegrable_add (μ := μ) hFui hGui, fun n ↦ ?_⟩
    -- Upgrade the representative-wise equality to the sum process.
    filter_upwards [Lp.coeFn_add (f n) (g n), hF n, hG n] with ω hfg hFω hGω
    simp only [Pi.add_apply, hfg, hFω, hGω]
  smul_mem' := by
    intro c f hf
    rcases hf with ⟨F, hFmart, hFui, hF⟩
    refine ⟨c • F, hFmart.smul c, uniformIntegrable_smul (μ := μ) c hFui, fun n ↦ ?_⟩
    -- The scalar multiple is represented coordinatewise by the scalar multiple witness.
    filter_upwards [Lp.coeFn_smul c (f n), hF n] with ω hfω hFω
    simp only [Pi.smul_apply, hfω, hFω]

local notation "UiMartingaleSpace" => uiMartingaleSubmodule μ ℱ

omit [IsFiniteMeasure μ] in
/-- Helper for Exercise 11.2.10: a terminal `L¹(ℱ∞)` class is integrable as a function. -/
private theorem terminalValueIntegrable (X : TerminalValueSpace) :
    Integrable (X : Ω → ℝ) μ := by
  -- The underlying `L¹` class is integrable by construction.
  exact memLp_one_iff_integrable.mp (Lp.memLp (X : Lp ℝ 1 μ))

/-- Helper for Exercise 11.2.10: the `Lp` conditional-expectation process agrees almost
everywhere with the honest function-valued conditional expectation. -/
private theorem terminalValueMartingaleProcess_ae_eq_condExp (X : TerminalValueSpace) (n : ℕ) :
    (terminalValueMartingaleProcess μ ℱ X n : Ω → ℝ) =ᵐ[μ] μ[(X : Ω → ℝ) | ℱ n] := by
  -- This is the basic bridge from `condExpL1CLM` to the ordinary conditional expectation.
  have hXint : Integrable (X : Ω → ℝ) μ :=
    terminalValueIntegrable (μ := μ) (ℱ := ℱ) X
  simpa [terminalValueMartingaleProcess] using
    (condExp_ae_eq_condExpL1CLM (E := ℝ) (m := ℱ n)
      (hm := ℱ.le n) (μ := μ) (f := (X : Ω → ℝ)) hXint).symm

/-- Helper for Exercise 11.2.10: each terminal `L¹(ℱ∞)` class yields a genuine uniformly
integrable martingale witness after taking conditional expectations. -/
theorem terminalValueMartingaleProcess_is_ui_martingale (X : TerminalValueSpace) :
    ∃ g : ℕ → Ω → ℝ, Martingale g ℱ μ ∧ UniformIntegrable g 1 μ ∧
      ∀ n, (terminalValueMartingaleProcess μ ℱ X n : Ω → ℝ) =ᵐ[μ] g n := by
  -- Use the honest conditional-expectation martingale as the witness process.
  have hXint : Integrable (X : Ω → ℝ) μ :=
    terminalValueIntegrable (μ := μ) (ℱ := ℱ) X
  refine ⟨fun n ↦ μ[(X : Ω → ℝ) | ℱ n], martingale_condExp (X : Ω → ℝ) ℱ μ,
    hXint.uniformIntegrable_condExp_filtration, fun n ↦ ?_⟩
  exact terminalValueMartingaleProcess_ae_eq_condExp (μ := μ) (ℱ := ℱ) X n

private theorem terminalValueMartingaleProcess_mem_uiMartingaleSubmodule (X : TerminalValueSpace) :
    terminalValueMartingaleProcess μ ℱ X ∈ UiMartingaleSpace := by
  -- The previous helper already packages the needed representative martingale.
  rcases terminalValueMartingaleProcess_is_ui_martingale μ ℱ X with ⟨g, hgmart, hgui, hg⟩
  exact ⟨g, hgmart, hgui, hg⟩

/-- Source-facing form of Exercise 11.2.10: a quotient-level `L¹` process lies in the canonical
space of uniformly integrable martingales exactly when it is the conditional-expectation
martingale of some terminal `L¹(ℱ∞)` class. -/
theorem mem_uiMartingaleSpace_iff_exists_terminalValue (f : ProcessSpace) :
    f ∈ UiMartingaleSpace ↔
      ∃ X : TerminalValueSpace, ∀ n, f n = terminalValueMartingaleProcess μ ℱ X n := by
  constructor
  · intro hf
    rcases hf with ⟨g, hgmart, hgui, hg⟩
    rcases hgui.2.2 with ⟨R, hR⟩
    have hlimitMemLp : MemLp (ℱ.limitProcess g μ) 1 μ :=
      hgmart.submartingale.memLp_limitProcess hR
    -- Package the canonical limit process as a terminal `L¹(ℱ∞)` class.
    have hlimitAEMeas :
        AEStronglyMeasurable[⨆ n, ℱ n] (ℱ.limitProcess g μ) μ :=
      (MeasureTheory.Filtration.stronglyMeasurable_limitProcess
        (f := g) (ℱ := ℱ) (μ := μ)).aestronglyMeasurable
    have htoLpAEMeas :
        AEStronglyMeasurable[⨆ n, ℱ n]
          ((MemLp.toLp (ℱ.limitProcess g μ) hlimitMemLp : Lp ℝ 1 μ) : Ω → ℝ) μ :=
      hlimitAEMeas.congr (MemLp.coeFn_toLp hlimitMemLp).symm
    let X : TerminalValueSpace :=
      ⟨MemLp.toLp (ℱ.limitProcess g μ) hlimitMemLp, htoLpAEMeas⟩
    refine ⟨X, fun n ↦ ?_⟩
    apply Lp.ext
    -- Identify the given representative with the conditional expectation of its limit.
    exact (hg n).trans <|
      (hgmart.ae_eq_condExp_limitProcess hgui n).trans <|
        (condExp_congr_ae (MemLp.coeFn_toLp hlimitMemLp).symm).trans <|
          (terminalValueMartingaleProcess_ae_eq_condExp (μ := μ) (ℱ := ℱ) X n).symm
  · rintro ⟨X, hX⟩
    have hf : f = terminalValueMartingaleProcess μ ℱ X := funext hX
    -- Reduce membership to the already constructed terminal-value martingale.
    simpa [hf] using terminalValueMartingaleProcess_mem_uiMartingaleSubmodule μ ℱ X

/-- Helper for Exercise 11.2.10: the conditional-expectation process converges in `L¹`
to the terminal value that generated it. -/
private theorem terminalValueMartingaleProcess_tendsto_terminalValue (X : TerminalValueSpace) :
    Tendsto (fun n => terminalValueMartingaleProcess μ ℱ X n) atTop (𝓝 (X : Lp ℝ 1 μ)) := by
  have hXmeas : AEStronglyMeasurable[⨆ n, ℱ n] (X : Ω → ℝ) μ :=
    lpMeas.aestronglyMeasurable X
  have hXint : Integrable (X : Ω → ℝ) μ :=
    terminalValueIntegrable (μ := μ) (ℱ := ℱ) X
  have hleSup : (⨆ n, ℱ n) ≤ ‹MeasurableSpace Ω› :=
    iSup_le fun n ↦ ℱ.le n
  have hsup :
      μ[(X : Ω → ℝ) | ⨆ n, ℱ n] =ᵐ[μ] (X : Ω → ℝ) :=
    condExp_of_aestronglyMeasurable' (m := ⨆ n, ℱ n)
      (μ := μ) hleSup hXmeas hXint
  have hcondExp :
      Tendsto
        (fun n => eLpNorm ((terminalValueMartingaleProcess μ ℱ X n : Ω → ℝ) - (X : Ω → ℝ)) 1 μ)
        atTop (𝓝 0) := by
    -- Rewrite the conditional-expectation martingale through Lévy's upward theorem.
    refine (MeasureTheory.tendsto_eLpNorm_condExp (μ := μ) (ℱ := ℱ)
      (g := (X : Ω → ℝ))).congr ?_
    intro n
    apply eLpNorm_congr_ae
    exact ((terminalValueMartingaleProcess_ae_eq_condExp (μ := μ) (ℱ := ℱ) X n).sub hsup.symm).symm
  simpa using
    (MeasureTheory.Lp.tendsto_Lp_of_tendsto_eLpNorm
      (X : Ω → ℝ) (Lp.memLp (X : Lp ℝ 1 μ)) hcondExp)

private theorem terminalValueMartingaleProcess_injective :
    Function.Injective (terminalValueMartingaleProcess μ ℱ) := by
  intro X Y hXY
  apply Subtype.ext
  -- The same `L¹` martingale sequence cannot converge to two different limits.
  exact tendsto_nhds_unique (terminalValueMartingaleProcess_tendsto_terminalValue μ ℱ X) <|
    by simpa [hXY] using terminalValueMartingaleProcess_tendsto_terminalValue μ ℱ Y

/-- The linear map underlying Exercise 11.2.10 from terminal values to uniformly integrable
`ℱ`-martingales. -/
noncomputable def terminalValueToUiMartingale :
    TerminalValueSpace →ₗ[ℝ] UiMartingaleSpace where
  toFun X := ⟨terminalValueMartingaleProcess μ ℱ X,
    terminalValueMartingaleProcess_mem_uiMartingaleSubmodule μ ℱ X⟩
  map_add' := by
    intro X Y
    apply Subtype.ext
    exact (terminalValueMartingaleProcess μ ℱ).map_add X Y
  map_smul' := by
    intro c X
    apply Subtype.ext
    exact (terminalValueMartingaleProcess μ ℱ).map_smul c X

/-- Exercise 11.2.10: the canonical bridge from terminal `L¹(ℱ∞)` classes to uniformly
integrable `ℱ`-martingales is a linear isomorphism. -/
noncomputable def terminalValueToUiMartingale_isomorphism :
    TerminalValueSpace ≃ₗ[ℝ] UiMartingaleSpace := by
  refine LinearEquiv.ofBijective (terminalValueToUiMartingale μ ℱ) ?_
  constructor
  · intro X Y hXY
    exact terminalValueMartingaleProcess_injective μ ℱ (by
      simpa [terminalValueToUiMartingale] using congrArg Subtype.val hXY)
  · intro f
    rcases (mem_uiMartingaleSpace_iff_exists_terminalValue μ ℱ f.1).mp f.2 with
      ⟨X, hX⟩
    refine ⟨X, ?_⟩
    apply Subtype.ext
    funext n
    exact (hX n).symm

/-- The linear equivalence is induced by the canonical conditional-expectation process map. -/
theorem terminalValueToUiMartingale_isomorphism_apply (X : TerminalValueSpace) :
    terminalValueToUiMartingale_isomorphism μ ℱ X =
      terminalValueToUiMartingale μ ℱ X :=
  rfl

end
