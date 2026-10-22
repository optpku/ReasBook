/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 9.2.1: the textbook conditional-expectation process is the canonical mathlib
martingale `MeasureTheory.martingale_condExp`. Since mathlib totalizes conditional expectation,
the owner statement has no separate integrability hypothesis. -/
recall MeasureTheory.martingale_condExp
