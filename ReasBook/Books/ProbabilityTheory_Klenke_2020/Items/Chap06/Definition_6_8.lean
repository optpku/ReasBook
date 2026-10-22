/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [NormedAddCommGroup E]
variable (μ : Measure Ω) (fSeq : ℕ → Ω → E) (f : Ω → E)

/-- Definition 6.8: A sequence `fₙ : Ω → E` converges in mean to `f` with respect to `μ`
exactly when the corresponding elements of the canonical `L¹(μ)` space converge to the class of
`f`; equivalently, every term and the limit are integrable and the `L¹`-seminorm errors
`eLpNorm (fₙ - f) 1 μ` tend to `0`. -/
abbrev TendstoInMean : Prop :=
  ∃ h_memLpSeq : ∀ n, MemLp (fSeq n) 1 μ,
    ∃ h_memLp : MemLp f 1 μ,
      Tendsto (fun n ↦ (h_memLpSeq n).toLp (fSeq n)) atTop (𝓝 (h_memLp.toLp f))

theorem TendstoInMean.memLpSeq {μ : Measure Ω} {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h : TendstoInMean μ fSeq f) :
    ∀ n, MemLp (fSeq n) 1 μ := by
  rcases h with ⟨h_memLpSeq, -, -⟩
  exact h_memLpSeq

theorem TendstoInMean.memLp {μ : Measure Ω} {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h : TendstoInMean μ fSeq f) :
    MemLp f 1 μ := by
  rcases h with ⟨-, h_memLp, -⟩
  exact h_memLp

/-- Owner-level formulation of `TendstoInMean`: the associated elements of the canonical
`L¹(μ)` space converge in `MeasureTheory.Lp`. -/
theorem TendstoInMean.tendsto_toLp {μ : Measure Ω} {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h : TendstoInMean μ fSeq f) :
    Tendsto (fun n ↦ (h.memLpSeq n).toLp (fSeq n)) atTop (𝓝 (h.memLp.toLp f)) := by
  rcases h with ⟨h_memLpSeq, h_memLp, h_tendsto⟩
  simpa using h_tendsto

theorem TendstoInMean.integrableSeq {μ : Measure Ω} {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h : TendstoInMean μ fSeq f) :
    ∀ n, Integrable (fSeq n) μ := fun n ↦ memLp_one_iff_integrable.mp (h.memLpSeq n)

theorem TendstoInMean.integrable {μ : Measure Ω} {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h : TendstoInMean μ fSeq f) :
    Integrable f μ :=
  memLp_one_iff_integrable.mp h.memLp

theorem TendstoInMean.tendsto_eLpNorm {μ : Measure Ω} {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h : TendstoInMean μ fSeq f) :
    Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 μ) atTop (𝓝 0) := by
  haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fSeq h.memLpSeq f h.memLp).1 h.tendsto_toLp

theorem tendstoInMean_iff {μ : Measure Ω} {fSeq : ℕ → Ω → E} {f : Ω → E} :
    TendstoInMean μ fSeq f ↔
      (∀ n, Integrable (fSeq n) μ) ∧
        Integrable f μ ∧
        Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 μ) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨h.integrableSeq, h.integrable, h.tendsto_eLpNorm⟩
  · rcases h with ⟨h_intSeq, h_int, h_tendsto⟩
    let h_memLpSeq : ∀ n, MemLp (fSeq n) 1 μ := fun n ↦ memLp_one_iff_integrable.mpr (h_intSeq n)
    let h_memLp : MemLp f 1 μ := memLp_one_iff_integrable.mpr h_int
    refine ⟨h_memLpSeq, h_memLp, ?_⟩
    haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fSeq h_memLpSeq f h_memLp).2 h_tendsto
