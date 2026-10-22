/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 9.2.2: a predictable discrete-time martingale is almost surely constant in time, so
for every `n : ℕ` one has `X n = X 0` almost surely. This is exactly the canonical mathlib result
`MeasureTheory.Martingale.eq_zero_of_predictable'`. -/
recall MeasureTheory.Martingale.eq_zero_of_predictable'
