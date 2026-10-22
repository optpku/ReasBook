/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter MeasureTheory
open scoped ENNReal Topology

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [NormedAddCommGroup E]

/-- Definition 7.2: for `1 ≤ p`, a sequence `fₙ : Ω → E` converges to `f` in `L^p(μ)` when each
`fₙ` and `f` belongs to `ℒ^p(μ)` and the associated classes in the canonical space
`MeasureTheory.Lp E p μ` converge. -/
abbrev TendstoInLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure Ω) (fSeq : ℕ → Ω → E)
    (f : Ω → E) : Prop :=
  ∃ h_memLpSeq : ∀ n, MemLp (fSeq n) p μ,
    ∃ h_memLp : MemLp f p μ,
      Tendsto (fun n ↦ (h_memLpSeq n).toLp (fSeq n)) atTop (𝓝 (h_memLp.toLp f))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure Ω} {fSeq : ℕ → Ω → E} {f : Ω → E}

theorem TendstoInLp.memLpSeq (h : TendstoInLp p μ fSeq f) :
    ∀ n, MemLp (fSeq n) p μ := by
  rcases h with ⟨h_memLpSeq, -, -⟩
  exact h_memLpSeq

theorem TendstoInLp.memLp (h : TendstoInLp p μ fSeq f) :
    MemLp f p μ := by
  rcases h with ⟨-, h_memLp, -⟩
  exact h_memLp

/-- Owner-level formulation of `TendstoInLp`: the corresponding elements of
`MeasureTheory.Lp E p μ` converge in the canonical `Lp` space. -/
theorem TendstoInLp.tendsto_toLp (h : TendstoInLp p μ fSeq f) :
    Tendsto (fun n ↦ (h.memLpSeq n).toLp (fSeq n)) atTop (𝓝 (h.memLp.toLp f)) := by
  rcases h with ⟨h_memLpSeq, h_memLp, h_tendsto⟩
  simpa using h_tendsto

/-- The textbook `eLpNorm` criterion is the bridge view of `TendstoInLp`, obtained from the owner
comparison theorem `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`. -/
theorem TendstoInLp.tendsto_eLpNorm (h : TendstoInLp p μ fSeq f) :
    Tendsto (fun n ↦ eLpNorm (fSeq n - f) p μ) atTop (𝓝 0) := by
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fSeq h.memLpSeq f h.memLp).1 h.tendsto_toLp

theorem tendstoInLp_iff_tendsto_eLpNorm :
    TendstoInLp p μ fSeq f ↔
      (∀ n, MemLp (fSeq n) p μ) ∧
        MemLp f p μ ∧
        Tendsto (fun n ↦ eLpNorm (fSeq n - f) p μ) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨h.memLpSeq, h.memLp, h.tendsto_eLpNorm⟩
  · rcases h with ⟨h_memLpSeq, h_memLp, h_tendsto⟩
    refine ⟨h_memLpSeq, h_memLp, ?_⟩
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fSeq h_memLpSeq f h_memLp).2 h_tendsto
