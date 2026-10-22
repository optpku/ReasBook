/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 8.2: For a probability measure `P` and an event `B`, the textbook conditional
probability `P[A | B]` is the canonical event evaluation of the conditioned measure `P[|B]`;
the defining formula is the canonical theorem `ProbabilityTheory.cond_apply`, namely
`P[A | B] = (P B)⁻¹ * P (B ∩ A)`, which is `P[A ∩ B] / P[B]` with value `0` when `P B = 0`. -/
recall ProbabilityTheory.cond_apply
