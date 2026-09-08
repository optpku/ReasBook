module

public import ReasLib.Analysis.Asymptotics.UniformRemainder

public section

open Filter
open scoped Topology

universe u v w

variable {Θ : Type u} {E : Type v} [Norm E]

/- Infrastructure I.9 (Uniform small-parameter modulus) (1): a uniformly little-o
remainder has an explicit tail-supremum modulus on some positive radius. -/
#check
  (Asymptotics.IsUniformRemainderModulusOn.of_isLittleO :
    ∀ (R : Θ → ℝ → E) (s : Set Θ) (q : ℝ),
      (fun z : Θ × ℝ ↦ R z.1 z.2) =o[Filter.principal s ×ˢ 𝓝 0]
          (fun z : Θ × ℝ ↦ |z.2| ^ q) →
        ∃ η₀ > 0, Asymptotics.IsUniformRemainderModulusOn R s q η₀
          (Asymptotics.uniformRemainderModulus R s q))

/- Infrastructure I.9 (Uniform small-parameter modulus) (2): the same modulus
simultaneously bounds every indexed orbit family below a common admissible scale. -/
#check
  (Asymptotics.IsUniformRemainderModulusOn.bound_orbits :
    ∀ {R : Θ → ℝ → E} {s : Set Θ} {q η₀ : ℝ} {ω : ℝ → ℝ},
      Asymptotics.IsUniformRemainderModulusOn R s q η₀ ω →
        ∀ {ι : Type w} (p : ι → ℕ → Θ) (ε : ι → ℕ → ℝ) (ε₀ : ι → ℝ) (η : ℝ),
          (∀ i j, p i j ∈ s) →
          (∀ i j, 0 < ε i j ∧ ε i j ≤ ε₀ i) →
          (∀ i, ε₀ i ≤ η) → η ∈ Set.Ioc 0 η₀ →
          ∀ i j, ‖R (p i j) (ε i j)‖ ≤ ω η * |ε i j| ^ q)
