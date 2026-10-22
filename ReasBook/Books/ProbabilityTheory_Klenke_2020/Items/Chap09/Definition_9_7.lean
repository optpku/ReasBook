/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v w

variable {I : Type u} {Ω : Type v} {E : Type w} [MeasurableSpace Ω]

/- Definition 9.7 (1): A real-valued stochastic process is simply a stochastic process with state
space `ℝ`, i.e. a map `I → Ω → ℝ`. -/
#check (I → Ω → ℝ)

/- Definition 9.7 (2): Item (ii). For a real-valued process, the canonical mathlib notion of
independent increments is `ProbabilityTheory.HasIndepIncrements`. -/
recall ProbabilityTheory.HasIndepIncrements

/- Definition 9.7 (3): Item (iii). For a real-valued process, the canonical mathlib notion of a
Gaussian process is `ProbabilityTheory.IsGaussianProcess`. -/
recall ProbabilityTheory.IsGaussianProcess

/-- Definition 9.7 (1): Item (iv), integrable. A real-valued process is integrable if each time
marginal is integrable. -/
def IsIntegrableProcess (X : I → Ω → ℝ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ t, Integrable (X t) μ

namespace IsIntegrableProcess

variable {X : I → Ω → ℝ} {μ : Measure Ω}

/-- Every time marginal of an integrable real-valued process is integrable. -/
theorem integrable (hX : IsIntegrableProcess X μ) (t : I) :
    Integrable (X t) μ :=
  hX t

end IsIntegrableProcess

/-- The defining condition for an integrable real-valued process is integrability of every time
marginal. -/
theorem isIntegrableProcess_iff (X : I → Ω → ℝ) (μ : Measure Ω := by volume_tac) :
    IsIntegrableProcess X μ ↔ ∀ t, Integrable (X t) μ :=
  Iff.rfl

/-- Definition 9.7 (2): Item (iv), square integrable. A real-valued process is square integrable
if each time marginal belongs to `L²`. -/
def IsSquareIntegrableProcess (X : I → Ω → ℝ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ t, MemLp (X t) 2 μ

namespace IsSquareIntegrableProcess

variable {X : I → Ω → ℝ} {μ : Measure Ω}

/-- Every time marginal of a square-integrable real-valued process belongs to `L²`. -/
theorem memLp (hX : IsSquareIntegrableProcess X μ) (t : I) :
    MemLp (X t) 2 μ :=
  hX t

end IsSquareIntegrableProcess

/-- The defining condition for a square-integrable real-valued process is the `L²` condition on
each time marginal. -/
theorem isSquareIntegrableProcess_iff (X : I → Ω → ℝ) (μ : Measure Ω := by volume_tac) :
    IsSquareIntegrableProcess X μ ↔ ∀ t, MemLp (X t) 2 μ :=
  Iff.rfl

variable [AddSemigroup I] [MeasurableSpace E]

/-- Definition 9.7 (3): Item (a). A process indexed by an additive time set is stationary if every
time shift has the same law as the original process. -/
def IsStationaryProcess (X : I → Ω → E) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ s, IdentDistrib (fun ω t ↦ X (s + t) ω) (fun ω t ↦ X t ω) μ μ

namespace IsStationaryProcess

variable {X : I → Ω → E} {μ : Measure Ω}

/-- A stationary process has the same law as each of its additive time shifts. -/
theorem identDistrib (hX : IsStationaryProcess X μ) (s : I) :
    IdentDistrib (fun ω t ↦ X (s + t) ω) (fun ω t ↦ X t ω) μ μ :=
  hX s

end IsStationaryProcess

/-- The defining condition for stationarity is equality in distribution of the shifted process and
the original process for every time shift. -/
theorem isStationaryProcess_iff (X : I → Ω → E) (μ : Measure Ω := by volume_tac) :
    IsStationaryProcess X μ ↔
      ∀ s, IdentDistrib (fun ω t ↦ X (s + t) ω) (fun ω t ↦ X t ω) μ μ :=
  Iff.rfl

/-- Definition 9.7 (4): Item (vi). A real-valued process has stationary increments if the law of
an increment depends only on the lag and not on the base point. -/
def HasStationaryIncrements (X : I → Ω → ℝ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ r s t,
    IdentDistrib
      (fun ω ↦ X ((s + t) + r) ω - X (t + r) ω)
      (fun ω ↦ X (s + r) ω - X r ω)
      μ μ

namespace HasStationaryIncrements

variable {X : I → Ω → ℝ} {μ : Measure Ω}

/-- A process with stationary increments has translated increments with the same law. -/
theorem identDistrib_increment (hX : HasStationaryIncrements X μ) (r s t : I) :
    IdentDistrib
      (fun ω ↦ X ((s + t) + r) ω - X (t + r) ω)
      (fun ω ↦ X (s + r) ω - X r ω)
      μ μ :=
  hX r s t

end HasStationaryIncrements

/-- The defining condition for stationary increments is equality in law between translated
increments and the corresponding increment starting at the origin shift. -/
theorem hasStationaryIncrements_iff (X : I → Ω → ℝ) (μ : Measure Ω := by volume_tac) :
    HasStationaryIncrements X μ ↔
      ∀ r s t,
        IdentDistrib
          (fun ω ↦ X ((s + t) + r) ω - X (t + r) ω)
          (fun ω ↦ X (s + r) ω - X r ω)
          μ μ :=
  Iff.rfl
