/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

/-- Helper for Theorem 25.28: the compensated square process `(X_t^2 - t)_{t ≥ 0}`. -/
abbrev compensatedSquareProcess (X : Process) : Process :=
  fun t ω ↦ X t ω ^ 2 - (t : ℝ)

/-- Helper for Theorem 25.28: the source-facing local-martingale condition
`(X_t^2 - t)_{t ≥ 0} ∈ 𝓜_loc`. -/
abbrev compensatedSquareIsLocalMartingale
    (X : Process) : Prop :=
  IsLocalMartingale ℱ μ (compensatedSquareProcess X)

/-- Theorem 25.28: Lévy's characterization of Brownian motion. In the present target file we
record the source-facing endpoint equivalence between the compensated-square local-martingale
criterion and Brownian motion; the intermediate bracket statement `⟨X⟩_t = t` is the Chapter 21
square-variation bridge between these two conditions. -/
abbrev levy_characterization_of_brownian_motion
    (X : Process) : Prop :=
  IsContinuousLocalMartingale ℱ μ X →
    X 0 = 0 →
      (compensatedSquareIsLocalMartingale X ↔ IsBrownianMotion μ X)

/-- Helper for Theorem 25.28: camelCase compatibility alias for the chapter-facing main
declaration. -/
abbrev levyCharacterizationOfBrownianMotion
    (X : Process) : Prop :=
  IsContinuousLocalMartingale ℱ μ X →
    X 0 = 0 →
      (compensatedSquareIsLocalMartingale X ↔ IsBrownianMotion μ X)

end ProbabilityTheory
