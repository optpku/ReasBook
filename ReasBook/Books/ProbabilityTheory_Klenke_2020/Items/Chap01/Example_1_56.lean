/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

/- The canonical bundled notion of a monotone right-continuous real function used to construct
Lebesgue--Stieltjes measures. -/
recall StieltjesFunction

/- The canonical measure attached to a Stieltjes function in mathlib. -/
recall StieltjesFunction.measure

/- The canonical Stieltjes measure gives the half-open interval `(a, b]` mass `f b - f a`. -/
recall StieltjesFunction.measure_Ioc

-- Proof sketch: use the canonical measure `f.measure` for existence, obtain sigma-finiteness from
-- local finiteness on the second-countable space `ℝ`, and prove uniqueness by measure
-- extensionality on the Borel generator of half-open intervals `(a, b]`.
/-- Example 1.56: A Stieltjes function on `ℝ` defines a unique sigma-finite Borel measure whose
value on each half-open interval `(a, b]` is `f b - f a`, i.e. the Lebesgue--Stieltjes measure
associated to `f`. -/
theorem existsUnique_sigmaFinite_measure_of_stieltjesFunction (f : StieltjesFunction ℝ) :
    ∃! μ : Measure ℝ, SigmaFinite μ ∧ ∀ a b : ℝ, μ (Ioc a b) = ENNReal.ofReal (f b - f a) := by
  refine ⟨f.measure, ?_, ?_⟩
  · constructor
    · infer_instance
    · intro a b
      simp
  · intro μ hμ
    exact (Measure.ext_of_Ioc f.measure μ fun a b hab ↦ by
      calc
        f.measure (Ioc a b) = ENNReal.ofReal (f b - f a) := f.measure_Ioc a b
        _ = μ (Ioc a b) := (hμ.2 a b).symm).symm
