module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.Reparameterization

public section

open Filter
open scoped Topology

universe u v

namespace Asymptotics.IsBigOWith

/- Infrastructure I.7 (Weighted path specialization for $b=\epsilon$ and $r=\epsilon^2$):
a joint estimate with gauge `|b| ^ p * |r| ^ q` restricts along
`b = ε`, `r = ε ^ 2` to a uniform remainder of order `p + 2 * q`. -/
#check (Asymptotics.IsBigOWith.weightedPath :
  ∀ {Θ : Type u} {E : Type v} [Norm E]
    {R : Θ → ℝ → ℝ → E} {s : Set Θ} {B C p q : ℝ},
    IsBigOWith C (principal (s ×ˢ Set.Icc (-B) B) ×ˢ 𝓝 0)
        (fun z : (Θ × ℝ) × ℝ ↦ R z.1.1 z.1.2 z.2)
        (fun z ↦ |z.1.2| ^ p * |z.2| ^ q) →
      0 < B → 0 ≤ p → 0 ≤ q →
      IsUniformRemainderOn (fun θ ε ↦ R θ ε (ε ^ 2)) s C (p + 2 * q))

/- A joint cubic estimate in `r` has uniform order six along
`b = ε`, `r = ε ^ 2`. -/
#check (Asymptotics.IsBigOWith.weightedPathCubic :
  ∀ {Θ : Type u} {E : Type v} [Norm E]
    {R : Θ → ℝ → ℝ → E} {s : Set Θ} {B C : ℝ},
    IsBigOWith C (principal (s ×ˢ Set.Icc (-B) B) ×ˢ 𝓝 0)
        (fun z : (Θ × ℝ) × ℝ ↦ R z.1.1 z.1.2 z.2)
        (fun z ↦ |z.2| ^ (3 : ℝ)) →
      0 < B → IsUniformRemainderOn (fun θ ε ↦ R θ ε (ε ^ 2)) s C 6)

/- A joint estimate with gauge `|b| * |r| ^ 3` has uniform order seven along
`b = ε`, `r = ε ^ 2`. -/
#check (Asymptotics.IsBigOWith.weightedPathLinearCubic :
  ∀ {Θ : Type u} {E : Type v} [Norm E]
    {R : Θ → ℝ → ℝ → E} {s : Set Θ} {B C : ℝ},
    IsBigOWith C (principal (s ×ˢ Set.Icc (-B) B) ×ˢ 𝓝 0)
        (fun z : (Θ × ℝ) × ℝ ↦ R z.1.1 z.1.2 z.2)
        (fun z ↦ |z.1.2| * |z.2| ^ (3 : ℝ)) →
      0 < B → IsUniformRemainderOn (fun θ ε ↦ R θ ε (ε ^ 2)) s C 7)

end Asymptotics.IsBigOWith
