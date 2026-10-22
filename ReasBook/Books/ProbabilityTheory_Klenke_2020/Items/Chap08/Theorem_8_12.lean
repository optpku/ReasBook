/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 8.12 (existence): the source theorem first asserts that the conditional expectation
`E[X | ℱ]` exists. In the chapter's canonical owner-based formalization, that witness is exactly
the mathlib construction `MeasureTheory.condExp`, written `P[X | ℱ]`; Definition 8.11 introduces
this owner object and Lemma 8.10 records its defining textbook properties. -/
recall MeasureTheory.condExp

/- Theorem 8.12 (uniqueness): conditional expectation is unique up to `P`-almost-sure equality.
In the canonical mathlib formulation, this is
`MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`, specialized to a probability measure. -/
recall MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
