module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import Mathlib.Topology.Order.OrderClosed

public section

open Filter
open scoped Topology

namespace Asymptotics.IsUniformRemainderModulusOn

universe u v w

/-- Two uniform remainder moduli combine into a product-valued modulus by taking their
pointwise maximum. -/
theorem prod
    {Θ : Type u} {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {R : Θ → ℝ → E} {S : Θ → ℝ → F} {s : Set Θ} {q η₀ : ℝ}
    {ωR ωS : ℝ → ℝ}
    (hR : IsUniformRemainderModulusOn R s q η₀ ωR)
    (hS : IsUniformRemainderModulusOn S s q η₀ ωS) :
    IsUniformRemainderModulusOn (fun θ ε ↦ (R θ ε, S θ ε)) s q η₀
      (fun η ↦ max (ωR η) (ωS η)) := by
  rw [spec] at hR hS ⊢
  refine ⟨?_, hR.2.1.max hS.2.1, ?_, ?_⟩
  · intro η hη
    exact (hR.1 η hη).trans (le_max_left (ωR η) (ωS η))
  · simpa only [max_self] using hR.2.2.1.max hS.2.2.1
  · intro θ hθ η hη ε hε hεη
    have hRbound := hR.2.2.2 θ hθ η hη ε hε hεη
    have hSbound := hS.2.2.2 θ hθ η hη ε hε hεη
    have hpow : 0 ≤ |ε| ^ q := Real.rpow_nonneg (abs_nonneg ε) q
    rw [Prod.norm_def]
    apply max_le
    · exact hRbound.trans
        (mul_le_mul_of_nonneg_right (le_max_left (ωR η) (ωS η)) hpow)
    · exact hSbound.trans
        (mul_le_mul_of_nonneg_right (le_max_right (ωR η) (ωS η)) hpow)

end Asymptotics.IsUniformRemainderModulusOn
