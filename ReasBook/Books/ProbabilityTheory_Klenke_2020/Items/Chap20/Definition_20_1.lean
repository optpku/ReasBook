/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v w

/- Definition 20.1: a stochastic process indexed by a set closed under addition is stationary if
every additive time shift has the same law as the original process; this is the canonical project
notion `IsStationaryProcess`. -/
recall IsStationaryProcess

variable {I : Type u} [AddCommSemigroup I]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {E : Type w} [MeasurableSpace E]

-- Proof sketch: unfold the imported characterization `isStationaryProcess_iff`; the only
-- difference from the textbook formula is the order of the summands, and `add_comm` rewrites
-- `t + s` to `s + t`.
/-- The canonical stationary-process predicate is equivalent to the textbook formulation using the
shifted path `t ↦ X (t + s)`. -/
theorem isStationaryProcess_iff_right_shift (X : I → Ω → E) (μ : Measure Ω := by volume_tac) :
    IsStationaryProcess X μ ↔
      ∀ s : I, IdentDistrib (fun ω t ↦ X (t + s) ω) (fun ω t ↦ X t ω) μ μ := by
  constructor
  · intro h s
    simpa [add_comm] using h.identDistrib s
  · intro h s
    simpa [add_comm] using h s
