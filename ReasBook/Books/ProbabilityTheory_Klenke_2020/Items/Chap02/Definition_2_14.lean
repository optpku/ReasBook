/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v w

/- Definition 2.14: A family `(X_i)_{i ∈ I}` of random variables is independent exactly when it
is independent in the canonical mathlib sense `ProbabilityTheory.iIndepFun`, namely when the
generated `σ`-algebras `σ(X_i)` form an independent family. -/
recall ProbabilityTheory.iIndepFun

variable {Ω : Type u} {E : Type v} {ι : Type w}

variable [MeasurableSpace Ω] [MeasurableSpace E]

/-- A family of `E`-valued random variables is i.i.d. if it is independent and every pair of
coordinates has the same distribution. -/
abbrev IsIID (X : ι → Ω → E) (μ : Measure Ω := by volume_tac) : Prop :=
  iIndepFun X μ ∧ ∀ i j, IdentDistrib (X i) (X j) μ μ

/-- The i.i.d. shorthand means independence together with equality in distribution for every pair
of variables in the family. -/
theorem isIID_iff (X : ι → Ω → E) (μ : Measure Ω := by volume_tac) :
    IsIID X μ ↔ iIndepFun X μ ∧ ∀ i j, IdentDistrib (X i) (X j) μ μ :=
  Iff.rfl

/-- An i.i.d. family is independent. -/
theorem IsIID.iIndepFun {X : ι → Ω → E} {μ : Measure Ω} (hX : IsIID X μ) : iIndepFun X μ :=
  hX.1

/-- In an i.i.d. family, any two coordinates are identically distributed. -/
theorem IsIID.identDistrib {X : ι → Ω → E} {μ : Measure Ω} (hX : IsIID X μ) (i j : ι) :
    IdentDistrib (X i) (X j) μ μ :=
  hX.2 i j
