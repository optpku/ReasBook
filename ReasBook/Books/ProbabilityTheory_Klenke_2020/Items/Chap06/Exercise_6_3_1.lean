/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Moments.MGFAnalytic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
-- Proof sketch: `0` belongs to `integrableExpSet X P` because `exp (0 * X) = 1` is integrable on
-- a probability space, and the interval property is the canonical convexity result
-- `convex_integrableExpSet`, transported to `OrdConnected` on `ℝ`.
/-- Exercise 6.3.1 (1): for a finite measure, hence in particular for a probability measure, the
effective domain `D = {t : ℝ | log (𝔼[exp (tX)]) < ∞}`, formalized as `integrableExpSet X P`, is
nonempty and is an interval. -/
theorem integrableExpSet_nonempty_ordConnected (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → ℝ) :
    (integrableExpSet X P).Nonempty ∧ OrdConnected (integrableExpSet X P) := by
  exact ⟨⟨0, by simp [integrableExpSet]⟩, convex_integrableExpSet.ordConnected⟩

-- Proof sketch: mathlib proves that the cumulant-generating function `cgf X P` is analytic on
-- `interior (integrableExpSet X P)` via `analyticOn_cgf`; analyticity over `ℝ` implies `C^∞`
-- regularity there by `AnalyticOn.contDiffOn_of_completeSpace`.
/-- Exercise 6.3.1 (2): for any measure, hence in particular for a probability measure, the
cumulant-generating function `Λ(t) = log (𝔼[exp (tX)])`, formalized as `cgf X P`, is infinitely
often differentiable on the interior of its effective domain. -/
theorem cgf_contDiffOn_interior_integrableExpSet (P : Measure Ω)
    (X : Ω → ℝ) :
    ContDiffOn ℝ ⊤ (cgf X P) (interior (integrableExpSet X P)) :=
  analyticOn_cgf.contDiffOn_of_completeSpace
