/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory
open scoped BigOperators

/- Definition 1.93: A simple real-valued function on a measurable space is the canonical mathlib
object `MeasureTheory.SimpleFunc Ω ℝ`, i.e. a bundled measurable function with finite range. The
textbook representation as a finite sum of constants times indicators of pairwise disjoint
measurable sets is recorded in the companion theorems below. -/
recall MeasureTheory.SimpleFunc

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: `SimpleFunc Ω ℝ` is by definition a measurable function with finite range, so the
-- forward implication uses `SimpleFunc.measurable` and `SimpleFunc.finite_range`, while the
-- reverse implication packages `f` with the measurable singleton fibers coming from `hf`.
/-- A real-valued map is the underlying function of a simple function exactly when it is
measurable and has finite range. -/
theorem exists_simpleFunc_iff_measurable_finite_range {f : Ω → ℝ} :
    (∃ sf : SimpleFunc Ω ℝ, (sf : Ω → ℝ) = f) ↔ Measurable f ∧ (Set.range f).Finite := by
  constructor
  · rintro ⟨sf, rfl⟩
    exact ⟨sf.measurable, sf.finite_range⟩
  · rintro ⟨hf, hfin⟩
    refine ⟨SimpleFunc.mk f (fun y ↦ MeasurableSet.preimage (measurableSet_singleton y) hf) hfin, ?_⟩
    exact SimpleFunc.coe_mk f
      (fun y ↦ MeasurableSet.preimage (measurableSet_singleton y) hf) hfin

-- Proof sketch: the indicator-sum presentation is the textbook form of simple functions; combine
-- the canonical characterization above with an induction on simple functions using
-- `SimpleFunc.induction'`. Constants give a one-set decomposition, and the piecewise step refines
-- a disjoint measurable partition by intersection with a measurable set and its complement.
/-- A real-valued map is measurable with finite range exactly when it admits a finite
representation as a sum of constants times indicators of pairwise disjoint measurable sets. -/
theorem measurable_finite_range_iff_exists_indicator_sum {f : Ω → ℝ} :
    Measurable f ∧ (Set.range f).Finite ↔
      ∃ n : ℕ, ∃ A : Fin n → Set Ω, ∃ α : Fin n → ℝ,
        (∀ i, MeasurableSet (A i)) ∧
        Pairwise (fun i j ↦ Disjoint (A i) (A j)) ∧
        ∀ x, f x = ∑ i, (A i).indicator (fun _ ↦ α i) x := sorry

/-- A real-valued map is the underlying function of a simple function exactly when it admits a
finite representation as a sum of constants times indicators of pairwise disjoint measurable
sets. -/
theorem exists_simpleFunc_iff_exists_indicator_sum {f : Ω → ℝ} :
    (∃ sf : SimpleFunc Ω ℝ, (sf : Ω → ℝ) = f) ↔
      ∃ n : ℕ, ∃ A : Fin n → Set Ω, ∃ α : Fin n → ℝ,
        (∀ i, MeasurableSet (A i)) ∧
        Pairwise (fun i j ↦ Disjoint (A i) (A j)) ∧
        ∀ x, f x = ∑ i, (A i).indicator (fun _ ↦ α i) x := by
  rw [exists_simpleFunc_iff_measurable_finite_range, measurable_finite_range_iff_exists_indicator_sum]
