/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ

/-- A sequence `τs` localizes a process `M` up to the stopping time `τ` if `τ` and every `τₙ` are
stopping times, `τₙ` increases almost surely to `τ`, and each stopped process `M ^ {τₙ}` is a
uniformly integrable martingale. -/
def IsLocalizingSequenceUpTo (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) (τs : ℕ → Ω → ENNReal) : Prop :=
  IsStoppingTime ℱ τ ∧
    (∀ n : ℕ, IsStoppingTime ℱ (τs n)) ∧
    (∀ᵐ ω ∂μ,
      Monotone (fun n : ℕ ↦ τs n ω) ∧
        Tendsto (fun n : ℕ ↦ τs n ω) atTop (𝓝 (τ ω))) ∧
    ∀ n : ℕ,
      Martingale (stoppedProcess M (τs n)) ℱ μ ∧
        UniformIntegrable (stoppedProcess M (τs n)) 1 μ

-- Proof sketch: unfold `IsLocalizingSequenceUpTo`; the statement is exactly the conjunction of
-- the stopping-time conditions, almost-sure monotone convergence to `τ`, and the uniformly
-- integrable martingale property of each stopped process.
/-- Unfolding `IsLocalizingSequenceUpTo` gives the defining stopping-time, convergence, and stopped
martingale conditions. -/
theorem isLocalizingSequenceUpTo_iff (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) (τs : ℕ → Ω → ENNReal) :
    IsLocalizingSequenceUpTo ℱ μ τ M τs ↔
      IsStoppingTime ℱ τ ∧
        (∀ n : ℕ, IsStoppingTime ℱ (τs n)) ∧
        (∀ᵐ ω ∂μ,
          Monotone (fun n : ℕ ↦ τs n ω) ∧
            Tendsto (fun n : ℕ ↦ τs n ω) atTop (𝓝 (τ ω))) ∧
        ∀ n : ℕ,
          Martingale (stoppedProcess M (τs n)) ℱ μ ∧
            UniformIntegrable (stoppedProcess M (τs n)) 1 μ :=
  Iff.rfl

/-- Definition 21.66: an adapted real-valued process is a local martingale up to the stopping
time `τ` if it admits a localizing sequence of stopping times increasing almost surely to `τ` for
which each stopped process is a uniformly integrable martingale. -/
def IsLocalMartingaleUpTo (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) : Prop :=
  Adapted ℱ M ∧ ∃ τs : ℕ → Ω → ENNReal, IsLocalizingSequenceUpTo ℱ μ τ M τs

-- Proof sketch: unfold `IsLocalMartingaleUpTo`; the definition is exactly adaptedness together
-- with the existence of a localizing sequence up to `τ`.
/-- `IsLocalMartingaleUpTo ℱ μ τ M` means that `M` is adapted and admits a localizing sequence up
to `τ`. -/
theorem isLocalMartingaleUpTo_iff (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) :
    IsLocalMartingaleUpTo ℱ μ τ M ↔
      Adapted ℱ M ∧ ∃ τs : ℕ → Ω → ENNReal, IsLocalizingSequenceUpTo ℱ μ τ M τs :=
  Iff.rfl

/-- A real-valued process is a continuous local martingale up to the stopping time `τ` if it is a
local martingale up to `τ` and has continuous sample paths. -/
@[mk_iff isContinuousLocalMartingaleUpTo_iff]
class IsContinuousLocalMartingaleUpTo (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) : Prop where
  local_martingale_upTo : IsLocalMartingaleUpTo ℱ μ τ M
  continuous : ∀ ω : Ω, Continuous (fun t : NNReal ↦ M t ω)

namespace IsContinuousLocalMartingaleUpTo

/-- A continuous local martingale up to `τ` is adapted because its local-martingale-up-to field is
adapted. -/
theorem adapted
    {ℱ : TimeFiltration} {μ : Measure Ω} {τ : Ω → ENNReal} {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M) :
    Adapted ℱ M :=
  (isLocalMartingaleUpTo_iff ℱ μ τ M).1 hM.local_martingale_upTo |>.1

/-- A continuous local martingale up to `τ` admits a localizing sequence up to `τ` because its
local-martingale-up-to field does. -/
theorem localizing_sequence
    {ℱ : TimeFiltration} {μ : Measure Ω} {τ : Ω → ENNReal} {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M) :
    ∃ τs : ℕ → Ω → ENNReal, IsLocalizingSequenceUpTo ℱ μ τ M τs :=
  (isLocalMartingaleUpTo_iff ℱ μ τ M).1 hM.local_martingale_upTo |>.2

end IsContinuousLocalMartingaleUpTo

/-- A sequence `τs` localizes `M` if it localizes `M` up to the constant infinite stopping time. -/
abbrev IsLocalizingSequence (ℱ : TimeFiltration) (μ : Measure Ω) (M : NNReal → Ω → ℝ)
    (τs : ℕ → Ω → ENNReal) : Prop :=
  IsLocalizingSequenceUpTo ℱ μ (fun _ ↦ ∞) M τs

/-- Unfolding `IsLocalizingSequence` gives the defining stopping-time, convergence to `∞`, and
stopped-martingale conditions. -/
theorem isLocalizingSequence_iff (ℱ : TimeFiltration) (μ : Measure Ω)
    (M : NNReal → Ω → ℝ) (τs : ℕ → Ω → ENNReal) :
    IsLocalizingSequence ℱ μ M τs ↔
      (∀ n : ℕ, IsStoppingTime ℱ (τs n)) ∧
        (∀ᵐ ω ∂μ,
          Monotone (fun n : ℕ ↦ τs n ω) ∧
            Tendsto (fun n : ℕ ↦ τs n ω) atTop (𝓝 (∞ : ENNReal))) ∧
        ∀ n : ℕ,
          Martingale (stoppedProcess M (τs n)) ℱ μ ∧
            UniformIntegrable (stoppedProcess M (τs n)) 1 μ := by
  constructor
  · rintro ⟨_, hτs, hlim, hmart⟩
    exact ⟨hτs, hlim, hmart⟩
  · rintro ⟨hτs, hlim, hmart⟩
    exact ⟨by
      intro i
      simp, hτs, hlim, hmart⟩

/-- A real-valued process is a local martingale if it is a local martingale up to the constant
infinite stopping time. -/
abbrev IsLocalMartingale (ℱ : TimeFiltration) (μ : Measure Ω)
    (M : NNReal → Ω → ℝ) : Prop :=
  IsLocalMartingaleUpTo ℱ μ (fun _ ↦ ∞) M

-- Proof sketch: unfold `IsLocalMartingale`; this is the specialization of
-- `IsLocalMartingaleUpTo` to the constant stopping time `∞`.
/-- `IsLocalMartingale ℱ μ M` is the specialization of local martingales up to time `τ` to the
case `τ ≡ ∞`. -/
theorem isLocalMartingale_iff (ℱ : TimeFiltration) (μ : Measure Ω)
    (M : NNReal → Ω → ℝ) :
    IsLocalMartingale ℱ μ M ↔
      Adapted ℱ M ∧ ∃ τs : ℕ → Ω → ENNReal, IsLocalizingSequence ℱ μ M τs := by
  simpa [IsLocalMartingale, IsLocalizingSequence] using
    (isLocalMartingaleUpTo_iff ℱ μ (fun _ ↦ ∞) M)

/-- Definition 21.66: a real-valued process is a continuous local martingale if it is a local
martingale and has continuous sample paths. This is the chapter owner; `Mlocc` is its set-level
view. -/
@[mk_iff isContinuousLocalMartingale_iff]
class IsContinuousLocalMartingale (ℱ : TimeFiltration) (μ : Measure Ω)
    (M : NNReal → Ω → ℝ) : Prop where
  local_martingale : IsLocalMartingale ℱ μ M
  continuous : ∀ ω : Ω, Continuous (fun t : NNReal ↦ M t ω)

namespace IsContinuousLocalMartingale

/-- A continuous local martingale is adapted because its local-martingale field is adapted. -/
theorem adapted {ℱ : TimeFiltration} {μ : Measure Ω} {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    Adapted ℱ M :=
  (isLocalMartingale_iff ℱ μ M).1 hM.local_martingale |>.1

/-- A continuous local martingale admits a localizing sequence because its local-martingale field
does. -/
theorem localizing_sequence {ℱ : TimeFiltration} {μ : Measure Ω} {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    ∃ τs : ℕ → Ω → ENNReal, IsLocalizingSequence ℱ μ M τs :=
  (isLocalMartingale_iff ℱ μ M).1 hM.local_martingale |>.2

end IsContinuousLocalMartingale

/-- The textbook set-level view `𝓜_{loc,c}` of the owner
`IsContinuousLocalMartingale ℱ μ`. -/
abbrev Mlocc (ℱ : TimeFiltration) (μ : Measure Ω) :
    Set (NNReal → Ω → ℝ) :=
  {M | IsContinuousLocalMartingale ℱ μ M}

/-- Membership in `Mlocc ℱ μ` is the set-level form of the owner
`IsContinuousLocalMartingale ℱ μ`. -/
theorem mem_Mlocc_iff (ℱ : TimeFiltration) (μ : Measure Ω) (M : NNReal → Ω → ℝ) :
    M ∈ Mlocc ℱ μ ↔ IsContinuousLocalMartingale ℱ μ M :=
  Iff.rfl

end ProbabilityTheory
