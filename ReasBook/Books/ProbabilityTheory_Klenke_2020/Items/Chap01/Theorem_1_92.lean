/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: apply the standard measurability theorem for countable pointwise infima of
-- measurable `EReal`-valued functions.
/-- Theorem 1.92 (1): The pointwise infimum of a sequence of measurable maps
`Ω → EReal` is measurable. -/
theorem measurable_iInf_sequence (X : ℕ → Ω → EReal) (hX : ∀ n : ℕ, Measurable (X n)) :
    Measurable (fun ω ↦ ⨅ n : ℕ, X n ω) := by
  -- The standard closure theorem for countable infima realizes the textbook preimage argument.
  simpa using Measurable.iInf hX

-- Proof sketch: apply the standard measurability theorem for countable pointwise suprema of
-- measurable `EReal`-valued functions.
/-- Theorem 1.92 (2): The pointwise supremum of a sequence of measurable maps
`Ω → EReal` is measurable. -/
theorem measurable_iSup_sequence (X : ℕ → Ω → EReal) (hX : ∀ n : ℕ, Measurable (X n)) :
    Measurable (fun ω ↦ ⨆ n : ℕ, X n ω) := by
  -- This is the dual countable-supremum closure theorem for measurable `EReal`-valued maps.
  simpa using Measurable.iSup hX

-- Proof sketch: use the standard measurability theorem for the `liminf` of a measurable sequence
-- of `EReal`-valued functions along `atTop`.
/-- Theorem 1.92 (3): The pointwise `liminf` of a sequence of measurable maps
`Ω → EReal` is measurable. -/
theorem measurable_liminf_sequence (X : ℕ → Ω → EReal) (hX : ∀ n : ℕ, Measurable (X n)) :
    Measurable (fun ω ↦ liminf (fun n : ℕ ↦ X n ω) atTop) := by
  -- Mathlib packages the textbook tail-infimum-then-supremum construction as `Measurable.liminf`.
  simpa using Measurable.liminf hX

-- Proof sketch: use the standard measurability theorem for the `limsup` of a measurable sequence
-- of `EReal`-valued functions along `atTop`.
/-- Theorem 1.92 (4): The pointwise `limsup` of a sequence of measurable maps
`Ω → EReal` is measurable. -/
theorem measurable_limsup_sequence (X : ℕ → Ω → EReal) (hX : ∀ n : ℕ, Measurable (X n)) :
    Measurable (fun ω ↦ limsup (fun n : ℕ ↦ X n ω) atTop) := by
  -- Dually, the packaged measurability theorem for `limsup` closes the final textbook clause.
  simpa using Measurable.limsup hX
