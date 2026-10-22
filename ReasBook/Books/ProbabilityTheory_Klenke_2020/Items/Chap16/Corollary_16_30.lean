/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_29

namespace MeasureTheory.ProbabilityMeasure

/-- Corollary 16.30: if a real probability law lies in the domain of attraction of a stable law
with index `α`, then every absolute moment of order `β ∈ (0, α)` is finite; if `α < 2`, then
every absolute moment of order `β > α` has infinite tail integral. -/
theorem integrable_abs_rpow_of_mem_domainOfAttraction_stableWithIndex
    {ν : MeasureTheory.ProbabilityMeasure Real} {α : Real}
    (hν : MeasureTheory.ProbabilityMeasure.IsInDomainOfAttractionOfStableWithIndex ν α) :
    (∀ {β : Real}, LT.lt 0 β → LT.lt β α →
      MeasureTheory.Integrable (fun x : Real => HPow.hPow (abs x) β)
        (ν : MeasureTheory.Measure Real)) ∧
      ∀ {β : Real}, LT.lt α β → LT.lt α 2 →
        MeasureTheory.lintegral (ν : MeasureTheory.Measure Real)
          (fun x : Real => ENNReal.ofReal (HPow.hPow (abs x) β)) = ⊤ := by
  sorry

end MeasureTheory.ProbabilityMeasure
