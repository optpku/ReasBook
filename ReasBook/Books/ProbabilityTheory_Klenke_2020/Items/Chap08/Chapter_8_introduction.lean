/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Chapter 8 introduction: the chapter studies how partial information about a random experiment
changes probabilities of events and expectations of random variables. The core owner abstraction
for conditioning on a sub-σ-algebra is the canonical mathlib construction
`MeasureTheory.condExp`. -/
recall MeasureTheory.condExp

/- Conditioning on an event is formalized by the canonical conditioned measure
`ProbabilityTheory.cond`; the familiar scalar formula for `μ[t | s]` is derived from this owner
construction via `ProbabilityTheory.cond_apply`. -/
recall ProbabilityTheory.cond
