/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable {E : Type v} [TopologicalSpace E] [MeasurableSpace E] [StandardBorelSpace E]
  [OpensMeasurableSpace E] [Nonempty E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → E} {xiInf : Ω → ProbabilityMeasure E}

local notation "Ξₙ" => fun n ω ↦ empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω

-- Proof sketch: the intended route is the conditional strong law from the directing random
-- probability measure in Theorem 12.26, rewritten through the empirical-distribution integral.
/-- Remark 12.27 (1): if `Ξ∞` is a directing random probability measure for `X` as in Theorem 12.26,
then the empirical distributions of the prefixes `X₀, ..., Xₙ` converge almost surely against
every bounded continuous test function to `Ξ∞`. The zero-based sequence
`n ↦ empiricalDistribution (Nat.succPNat n) (fun i ↦ X i)` is the Lean encoding of the textbook
empirical measures `Ξₙ`. This records the source-facing bounded-continuous test-function
formulation from part (i). -/
theorem deFinetti_empiricalDistribution_testFunction_tendsto_ae
    (hxiInf : IsDirectingProbabilityMeasure xiInf X μ) :
    ∀ f : E →ᵇ ℝ,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ ∫ x, f x ∂(Ξₙ n ω : Measure E))
          atTop
          (nhds (∫ x, f x ∂(xiInf ω : Measure E))) := by
  intro f
  let _ := hxiInf
  exact sorryAx _ true

-- Proof sketch: once part (i) is upgraded to weak convergence on a full-measure set, local
-- compactness of `E` yields almost-sure convergence of the empirical laws themselves.
/-- Remark 12.27 (2): if, in addition to the standing assumptions from Theorem 12.26, the state
space `E` is locally compact, then the empirical laws `Ξₙ` themselves converge almost surely to
the directing random probability measure `Ξ∞`. This is the source's locally-compact upgrade of the
bounded-continuous test-function convergence recorded above, expressed on the canonical owner
surface `ProbabilityMeasure E`. -/
theorem deFinetti_empiricalDistribution_tendsto_ae
    [LocallyCompactSpace E] (hxiInf : IsDirectingProbabilityMeasure xiInf X μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Ξₙ n ω) atTop (nhds (xiInf ω)) := by
  let _ := hxiInf
  exact sorryAx _ true

/- The textbook's part (ii), concerning finite exchangeable families, is bibliographic prose
rather than a mathematical statement and is therefore not encoded as a Lean declaration here. -/

end
