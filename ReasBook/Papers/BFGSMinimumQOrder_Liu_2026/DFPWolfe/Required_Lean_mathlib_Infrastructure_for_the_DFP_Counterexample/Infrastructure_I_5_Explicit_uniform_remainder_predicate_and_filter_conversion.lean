module

public import ReasLib.Analysis.Asymptotics.UniformRemainder

public section

open Filter
open scoped Topology

namespace Asymptotics

universe u v

variable {Θ : Type u} {E : Type v} [Norm E]

/- Infrastructure I.5 (Explicit uniform remainder predicate and filter conversion) (1):
`IsUniformRemainderOn R s C q` means that one positive radius works for every
`θ ∈ s` in the estimate `‖R θ ε‖ ≤ C * |ε| ^ q`. -/
#check (Asymptotics.IsUniformRemainderOn :
  (Θ → ℝ → E) → Set Θ → ℝ → ℝ → Prop)

/- Infrastructure I.5 (Explicit uniform remainder predicate and filter conversion) (2):
the explicit common-radius estimate is equivalent to fixed-coefficient big-O on
`Filter.principal s ×ˢ 𝓝 0`. -/
#check (Asymptotics.IsUniformRemainderOn.isBigOWith_iff :
  ∀ (R : Θ → ℝ → E) (s : Set Θ) (C q : ℝ),
    IsBigOWith C (Filter.principal s ×ˢ 𝓝 0) (fun z : Θ × ℝ ↦ R z.1 z.2)
        (fun z : Θ × ℝ ↦ |z.2| ^ q) ↔ IsUniformRemainderOn R s C q)

/- Infrastructure I.5 (Explicit uniform remainder predicate and filter conversion) (3):
ordinary big-O on the product filter is equivalent to the existence of a coefficient
for an explicit uniform remainder estimate. -/
#check (Asymptotics.IsUniformRemainderOn.isBigO_iff :
  ∀ (R : Θ → ℝ → E) (s : Set Θ) (q : ℝ),
    (fun z : Θ × ℝ ↦ R z.1 z.2) =O[Filter.principal s ×ˢ 𝓝 0]
        (fun z : Θ × ℝ ↦ |z.2| ^ q) ↔
      ∃ C : ℝ, IsUniformRemainderOn R s C q)

/- Infrastructure I.5 (Explicit uniform remainder predicate and filter conversion) (4):
little-o on the product filter is equivalent to uniform remainder estimates with every
positive coefficient. -/
#check (Asymptotics.IsUniformRemainderOn.isLittleO_iff :
  ∀ (R : Θ → ℝ → E) (s : Set Θ) (q : ℝ),
    (fun z : Θ × ℝ ↦ R z.1 z.2) =o[Filter.principal s ×ˢ 𝓝 0]
        (fun z : Θ × ℝ ↦ |z.2| ^ q) ↔
      ∀ ⦃C : ℝ⦄, 0 < C → IsUniformRemainderOn R s C q)

end Asymptotics
