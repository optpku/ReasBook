module

public import ReasLib.Analysis.Asymptotics.ParabolicRecurrence

open Filter
open scoped Asymptotics Topology

/- Infrastructure I.19 (Asymptotics of a parabolic scalar recurrence): A positive real
sequence tending to zero and satisfying
`ε (j + 1) = ε j - a * ε j ^ (p + 1) + O(ε j ^ (p + 2))` is asymptotic to
`(a * (p : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / (p : ℝ))` when `a > 0` and
`p` is a positive natural number. -/
#check (Asymptotics.IsEquivalent.ofParabolicRecurrence :
  ∀ {ε : ℕ → ℝ} {a : ℝ} {p : ℕ}, 0 < a → 0 < p →
    (∀ j, 0 < ε j) → Tendsto ε atTop (𝓝 0) →
    (fun j ↦ ε (j + 1) - ε j + a * ε j ^ (p + 1)) =O[atTop]
      (fun j ↦ ε j ^ (p + 2)) →
    ε ~[atTop] (fun j ↦ (a * (p : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / (p : ℝ))))
