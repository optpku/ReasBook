/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

section

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ mΩ}

/- Lemma 10.20 is `source-facing`: it keeps the family of sampled values indexed by intrinsic
finite stopping times. Its `core/canonical` owner is
`Integrable.uniformIntegrable_condExp`, applied to the canonical martingale limit process
`ℱ.limitProcess X μ`. The needed `bridge/view` is the stopping-time conditional-expectation
restriction theorem, which identifies `μ[ℱ.limitProcess X μ | 𝓕_τ]` with the sampled value
`X_τ` fiberwise over `{τ = n}`. -/

-- Proof sketch: apply the `L¹` martingale convergence theorem to realize the martingale as the
-- conditional expectations of its integrable limit process; for each finite stopping time `τ`,
-- optional sampling identifies the sampled value `X_τ` with the conditional expectation of that
-- limit with respect to the stopping-time σ-algebra `𝓕_τ`; then use uniform integrability of the
-- family of conditional expectations indexed by the canonical intrinsic finite stopping-time data.
/-- Lemma 10.20: if `X` is a uniformly integrable martingale, then the family of its sampled
values `X_τ`, indexed by finite stopping times `τ`, is uniformly integrable. -/
theorem uniformIntegrable_stoppedValue_family_of_ui_martingale
    {X : ℕ → Ω → ℝ} (hX_mart : Martingale X ℱ μ) (hX_ui : UniformIntegrable X 1 μ) :
    UniformIntegrable
      (fun τ : {τ : Ω → ℕ∞ // IsStoppingTime ℱ τ ∧ ∀ ω, τ ω ≠ ⊤} ↦ stoppedValue X τ.1) 1 μ := by
  let Y : {τ : Ω → ℕ∞ // IsStoppingTime ℱ τ ∧ ∀ ω, τ ω ≠ ⊤} → Ω → ℝ :=
    fun τ ↦ μ[ℱ.limitProcess X μ | τ.2.1.measurableSpace]
  have hY_ui : UniformIntegrable Y 1 μ := by
    have hlimit_int : Integrable (ℱ.limitProcess X μ) μ :=
      submartingale_integrable_limitProcess_of_uniformIntegrable hX_mart.submartingale hX_ui
    exact hlimit_int.uniformIntegrable_condExp fun τ ↦ τ.2.1.measurableSpace_le
  refine hY_ui.ae_eq ?_
  intro τ
  rcases τ with ⟨τ, hτ, hτ_fin⟩
  change ∀ᵐ ω ∂μ, μ[ℱ.limitProcess X μ | hτ.measurableSpace] ω = stoppedValue X τ ω
  let s : ℕ → Set Ω := fun n ↦ {ω | τ ω = n}
  let p : Ω → Prop := fun ω ↦
    μ[ℱ.limitProcess X μ | hτ.measurableSpace] ω = stoppedValue X τ ω
  have hs_univ : Set.univ = ⋃ n : ℕ, s n := by
    ext ω
    simp only [s, Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    rcases ENat.ne_top_iff_exists.1 (hτ_fin ω) with ⟨n, hn⟩
    exact ⟨n, by simpa using hn.symm⟩
  have hp_univ : ∀ᵐ ω ∂μ.restrict Set.univ, p ω := by
    rw [hs_univ]
    rw [ae_restrict_iUnion_iff]
    intro n
    have hcond :
        μ[ℱ.limitProcess X μ | hτ.measurableSpace] =ᵐ[μ.restrict (s n)]
          μ[ℱ.limitProcess X μ | ℱ n] :=
      condExp_stopping_time_ae_eq_restrict_eq_of_countable hτ n
    have hmart : μ[ℱ.limitProcess X μ | ℱ n] =ᵐ[μ.restrict (s n)] X n :=
      ae_restrict_of_ae (hX_mart.ae_eq_condExp_limitProcess hX_ui n).symm
    have hstop' : ∀ᵐ ω ∂μ.restrict {ω | τ ω = n}, X n ω = stoppedValue X τ ω := by
      filter_upwards [ae_restrict_mem (ℱ.le _ _ (hτ.measurableSet_eq n))] with ω hω
      simp [stoppedValue, hω]
    have hstop : ∀ᵐ ω ∂μ.restrict (s n), X n ω = stoppedValue X τ ω := by
      simpa [s] using hstop'
    filter_upwards [hcond, hmart, hstop] with ω hω₁ hω₂ hω₃
    exact (hω₁.trans hω₂).trans hω₃
  simpa [p] using hp_univ

end
