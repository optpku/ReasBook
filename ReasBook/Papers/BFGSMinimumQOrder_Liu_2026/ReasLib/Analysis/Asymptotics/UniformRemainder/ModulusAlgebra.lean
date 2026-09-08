module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import Mathlib.Analysis.Asymptotics.Lemmas

public section

open Filter
open scoped BigOperators Topology

namespace Asymptotics.IsUniformRemainderModulusOn

universe u v

/-- The zero remainder has the identically zero uniform remainder modulus. -/
theorem zero
    {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    (s : Set Θ) (q η₀ : ℝ) :
    IsUniformRemainderModulusOn (fun _ : Θ ↦ fun _ : ℝ ↦ (0 : E)) s q η₀
      (fun _ ↦ 0) := by
  rw [spec]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro η _
    exact le_rfl
  · intro η _ ξ _ _
    exact le_rfl
  · exact tendsto_const_nhds
  · intro θ _ η _ ε _ _
    simp only [norm_zero, zero_mul, le_refl]

/-- The sum of two uniform remainders has modulus equal to the sum of their moduli. -/
theorem add
    {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R S : Θ → ℝ → E} {s : Set Θ} {q η₀ : ℝ} {ωR ωS : ℝ → ℝ}
    (hR : IsUniformRemainderModulusOn R s q η₀ ωR)
    (hS : IsUniformRemainderModulusOn S s q η₀ ωS) :
    IsUniformRemainderModulusOn (fun θ ε ↦ R θ ε + S θ ε) s q η₀
      (fun η ↦ ωR η + ωS η) := by
  rw [spec] at hR hS ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro η hη
    exact add_nonneg (hR.1 η hη) (hS.1 η hη)
  · intro η hη ξ hξ hηξ
    exact add_le_add (hR.2.1 hη hξ hηξ) (hS.2.1 hη hξ hηξ)
  · simpa only [add_zero] using hR.2.2.1.add hS.2.2.1
  · intro θ hθ η hη ε hε hεη
    have hRbound := hR.2.2.2 θ hθ η hη ε hε hεη
    have hSbound := hS.2.2.2 θ hθ η hη ε hε hεη
    calc
      ‖R θ ε + S θ ε‖ ≤ ‖R θ ε‖ + ‖S θ ε‖ := norm_add_le _ _
      _ ≤ ωR η * |ε| ^ q + ωS η * |ε| ^ q := add_le_add hRbound hSbound
      _ = (ωR η + ωS η) * |ε| ^ q := (add_mul _ _ _).symm

/-- The difference of two uniform remainders has modulus equal to the sum of their moduli. -/
theorem sub
    {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R S : Θ → ℝ → E} {s : Set Θ} {q η₀ : ℝ} {ωR ωS : ℝ → ℝ}
    (hR : IsUniformRemainderModulusOn R s q η₀ ωR)
    (hS : IsUniformRemainderModulusOn S s q η₀ ωS) :
    IsUniformRemainderModulusOn (fun θ ε ↦ R θ ε - S θ ε) s q η₀
      (fun η ↦ ωR η + ωS η) := by
  rw [spec] at hR hS ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro η hη
    exact add_nonneg (hR.1 η hη) (hS.1 η hη)
  · intro η hη ξ hξ hηξ
    exact add_le_add (hR.2.1 hη hξ hηξ) (hS.2.1 hη hξ hηξ)
  · simpa only [add_zero] using hR.2.2.1.add hS.2.2.1
  · intro θ hθ η hη ε hε hεη
    have hRbound := hR.2.2.2 θ hθ η hη ε hε hεη
    have hSbound := hS.2.2.2 θ hθ η hη ε hε hεη
    calc
      ‖R θ ε - S θ ε‖ ≤ ‖R θ ε‖ + ‖S θ ε‖ := norm_sub_le _ _
      _ ≤ ωR η * |ε| ^ q + ωS η * |ε| ^ q := add_le_add hRbound hSbound
      _ = (ωR η + ωS η) * |ε| ^ q := (add_mul _ _ _).symm

/-- A finite sum of uniform remainders has modulus equal to the pointwise sum of the
individual moduli. -/
theorem finsetSum
    {Θ : Type u} {ι : Type v} {E : Type*} [SeminormedAddCommGroup E]
    (u : Finset ι) {R : ι → Θ → ℝ → E} {s : Set Θ} {q η₀ : ℝ}
    {ω : ι → ℝ → ℝ}
    (hR : ∀ i ∈ u, IsUniformRemainderModulusOn (R i) s q η₀ (ω i)) :
    IsUniformRemainderModulusOn (fun θ ε ↦ ∑ i ∈ u, R i θ ε) s q η₀
      (fun η ↦ ∑ i ∈ u, ω i η) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (zero (E := E) s q η₀)
  | @insert i u hi ih =>
      have hsum : IsUniformRemainderModulusOn
          (fun θ ε ↦ ∑ j ∈ u, R j θ ε) s q η₀
          (fun η ↦ ∑ j ∈ u, ω j η) :=
        ih (fun j hj ↦ hR j (Finset.mem_insert_of_mem hj))
      have hinsert : IsUniformRemainderModulusOn (R i) s q η₀ (ω i) :=
        hR i (Finset.mem_insert_self i u)
      have hadd := add hinsert hsum
      simpa only [Finset.sum_insert hi] using hadd

end Asymptotics.IsUniformRemainderModulusOn
