/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Lemma 1.51: An outer measure `μ*` is `σ`-additive on its Carathéodory-measurable sets; that
is, if `A : ℕ → Set Ω` is pairwise disjoint and each `A n` is measurable in
`MeasureTheory.OuterMeasure.caratheodory μ*`, then `μ* (⋃ n, A n) = ∑' n, μ* (A n)`. -/
recall MeasureTheory.OuterMeasure.iUnion_eq_of_caratheodory
