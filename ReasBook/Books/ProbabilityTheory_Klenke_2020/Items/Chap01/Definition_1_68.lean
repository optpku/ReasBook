/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Definition 1.68 (1): The class `nullSets μ`, corresponding to `𝓝_μ`, consists of all subsets
of measurable `μ`-null sets. Canonically, this is the collection of sets of `μ`-measure zero. -/
def nullSets (μ : Measure Ω) : Set (Set Ω) :=
  {N | μ N = 0}

/-- A set belongs to `nullSets μ` exactly when it is contained in a measurable set of
`μ`-measure zero. -/
theorem mem_nullSets_iff {μ : Measure Ω} {N : Set Ω} :
    N ∈ nullSets μ ↔ ∃ A : Set Ω, N ⊆ A ∧ MeasurableSet A ∧ μ A = 0 := by
  rw [show N ∈ nullSets μ ↔ μ N = 0 by rfl]
  exact exists_measurable_superset_iff_measure_eq_zero.symm

/-- Membership in `nullSets μ` is exactly the canonical condition `μ N = 0`. -/
theorem mem_nullSets {μ : Measure Ω} {N : Set Ω} :
    N ∈ nullSets μ ↔ μ N = 0 :=
  Iff.rfl

/- Definition 1.68 (2): “`E` holds `μ`-almost everywhere” is formalized by the canonical mathlib
notation `∀ᵐ ω ∂μ, E ω`; on a measurable set `A` one uses the restricted measure `μ.restrict A`,
and for a probability measure this is the usual almost-surely terminology. -/
recall MeasureTheory.ae

/- Almost-everywhere on a measurable set is expressed by the `ae` filter of the restricted
measure. -/
recall MeasureTheory.ae_restrict_iff'

/- Definition 1.68 (3): Equality modulo `μ` is the set-level almost-everywhere equality
`A =ᵐ[μ] B`, equivalently the vanishing of the symmetric-difference measure `μ (A ∆ B) = 0`. -/
recall MeasureTheory.measure_symmDiff_eq_zero_iff
