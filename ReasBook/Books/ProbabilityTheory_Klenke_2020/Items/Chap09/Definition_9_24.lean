/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 9.24 (1): For a real-valued process adapted to a filtration and integrable at each
time, the canonical mathlib notion of being a martingale is
`MeasureTheory.Martingale`; its conditional-expectation identity is expressed in Lean up to
almost-everywhere equality. -/
recall MeasureTheory.Martingale

/- Definition 9.24 (2): For a real-valued process adapted to a filtration and integrable at each
time, the canonical mathlib notion of being a submartingale is
`MeasureTheory.Submartingale`; its conditional-expectation inequality is expressed in Lean as an
almost-everywhere inequality. -/
recall MeasureTheory.Submartingale

/- Definition 9.24 (3): For a real-valued process adapted to a filtration and integrable at each
time, the canonical mathlib notion of being a supermartingale is
`MeasureTheory.Supermartingale`; its conditional-expectation inequality is expressed in Lean as an
almost-everywhere inequality. -/
recall MeasureTheory.Supermartingale
