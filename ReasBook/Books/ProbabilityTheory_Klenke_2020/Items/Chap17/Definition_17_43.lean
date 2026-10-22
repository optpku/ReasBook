/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

/- Definition 17.43: item (i) is the canonical mathlib notion
`ProbabilityTheory.Kernel.Invariant`, expressing that a measure is fixed by a Markov kernel under
measure-kernel composition. The companion declaration below records the textbook set `I` of
invariant probability measures, while item (ii) remains source-facing through the subharmonic,
superharmonic, and harmonic predicates. -/
recall ProbabilityTheory.Kernel.Invariant

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

/-- The set `I` of invariant distributions of a kernel `p`. -/
def invariantDistributions (p : Kernel E E) : Set (ProbabilityMeasure E) :=
  {μ | Kernel.Invariant p (μ : Measure E)}

-- Proof sketch: unfold `invariantDistributions`; membership is precisely the predicate
-- `Kernel.Invariant p` on the underlying probability measure.
/-- Definition 17.43: membership in `invariantDistributions p` means being an invariant
distribution for `p`. -/
theorem mem_invariantDistributions_iff (p : Kernel E E) (μ : ProbabilityMeasure E) :
    μ ∈ invariantDistributions p ↔ Kernel.Invariant p (μ : Measure E) := by
  -- Unfold the textbook set `I`; membership is exactly the invariant-measure predicate.
  rfl

/-- A real-valued function is subharmonic for a kernel `p` if the kernel integral `p f` exists at
every state and dominates `f`. -/
def IsSubharmonic (p : Kernel E E) (f : E → ℝ) : Prop :=
  (∀ x : E, Integrable f (p x)) ∧ ∀ x : E, f x ≤ ∫ y, f y ∂p x

-- Proof sketch: unfold `IsSubharmonic`; the right-hand side restates the existence of `p f`
-- together with the pointwise inequality `f ≤ p f`.
/-- A function is subharmonic exactly when it is integrable against each kernel row and satisfies
`f x ≤ ∫ y, f y ∂p x` for all `x`. -/
theorem isSubharmonic_iff (p : Kernel E E) (f : E → ℝ) :
    IsSubharmonic p f ↔
      (∀ x : E, Integrable f (p x)) ∧ ∀ x : E, f x ≤ ∫ y, f y ∂p x := by
  -- Unfold the predicate; the theorem is its rewrite-friendly companion form.
  rfl

/-- A real-valued function is superharmonic for a kernel `p` if the kernel integral `p f` exists
at every state and is dominated by `f`. -/
def IsSuperharmonic (p : Kernel E E) (f : E → ℝ) : Prop :=
  (∀ x : E, Integrable f (p x)) ∧ ∀ x : E, ∫ y, f y ∂p x ≤ f x

-- Proof sketch: unfold `IsSuperharmonic`; this is the textbook condition that `p f` exists and
-- that `f ≥ p f` pointwise.
/-- A function is superharmonic exactly when it is integrable against each kernel row and satisfies
`∫ y, f y ∂p x ≤ f x` for all `x`. -/
theorem isSuperharmonic_iff (p : Kernel E E) (f : E → ℝ) :
    IsSuperharmonic p f ↔
      (∀ x : E, Integrable f (p x)) ∧ ∀ x : E, ∫ y, f y ∂p x ≤ f x := by
  -- Unfold the predicate; this exposes the defining inequality in a reusable form.
  rfl

/-- A real-valued function is harmonic for a kernel `p` if the kernel integral `p f` exists at
every state and agrees with `f`. -/
def IsHarmonic (p : Kernel E E) (f : E → ℝ) : Prop :=
  (∀ x : E, Integrable f (p x)) ∧ ∀ x : E, f x = ∫ y, f y ∂p x

-- Proof sketch: unfold `IsHarmonic`; this is the textbook fixed-point condition `f = p f`
-- together with existence of the kernel integral at every state.
/-- A function is harmonic exactly when it is integrable against each kernel row and satisfies
`f x = ∫ y, f y ∂p x` for all `x`. -/
theorem isHarmonic_iff (p : Kernel E E) (f : E → ℝ) :
    IsHarmonic p f ↔
      (∀ x : E, Integrable f (p x)) ∧ ∀ x : E, f x = ∫ y, f y ∂p x := by
  -- Unfold the predicate; harmonicity is exactly the fixed-point equality with integrability.
  rfl

end ProbabilityTheory
