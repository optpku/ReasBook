module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import ReasLib.Analysis.Asymptotics.UniformRemainder.ModulusScale
public import ReasLib.Analysis.Asymptotics.UniformRemainder.Scalar

public section

open Filter
open scoped Topology

namespace Asymptotics.IsUniformRemainderModulusOn

universe u v

/-- Restricting the positive working radius preserves a uniform remainder modulus. -/
theorem mono_radius
    {Θ : Type u} {E : Type v} [Norm E]
    {R : Θ → ℝ → E} {s : Set Θ} {q η₀ η₁ : ℝ} {ω : ℝ → ℝ}
    (hω : IsUniformRemainderModulusOn R s q η₀ ω) (hη : η₁ ≤ η₀) :
    IsUniformRemainderModulusOn R s q η₁ ω := by
  rw [spec] at hω ⊢
  refine ⟨?_, ?_, hω.2.2.1, ?_⟩
  · intro η hηmem
    exact hω.1 η ⟨hηmem.1, hηmem.2.trans hη⟩
  · intro η hηmem η' hη'mem hηη'
    exact hω.2.1 ⟨hηmem.1, hηmem.2.trans hη⟩
      ⟨hη'mem.1, hη'mem.2.trans hη⟩ hηη'
  · intro θ hθ η hηmem ε hε hεη
    exact hω.2.2.2 θ hθ η ⟨hηmem.1, hηmem.2.trans hη⟩ ε hε hεη

/-- An order-`n + 1` scalar big-O estimate gives the canonical order-`n`
uniform modulus and a linear bound for that modulus. -/
theorem exists_natPow_orderDrop
    {E : Type u} [SeminormedAddCommGroup E] {r : ℝ → E} {n : ℕ}
    (h : r =O[nhds 0] (fun ε : ℝ ↦ ε ^ (n + 1))) :
    ∃ C > 0, ∃ η₀ > 0,
      IsUniformRemainderModulusOn (fun _ : Unit ↦ r) Set.univ (n : ℝ) η₀
          (uniformRemainderModulus (fun _ : Unit ↦ r) Set.univ (n : ℝ)) ∧
        ∀ η ∈ Set.Ioc 0 η₀,
          uniformRemainderModulus (fun _ : Unit ↦ r) Set.univ (n : ℝ) η ≤ C * η := by
  obtain ⟨C, hC, hUniform⟩ :=
    Asymptotics.IsUniformRemainderOn.exists_pos_of_isBigO_natPow_singleton h
  have hLittle : r =o[nhds 0] (fun ε : ℝ ↦ ε ^ n) :=
    h.trans_isLittleO (isLittleO_pow_pow n.lt_succ_self)
  obtain ⟨ηMod, hηMod, hMod⟩ := of_isLittleO_natPow_singleton hLittle
  obtain ⟨ηBound, hηBound, hBound⟩ :=
    exists_uniformRemainderModulus_natCast_le_mul hC.le hUniform
  refine ⟨C, hC, min ηMod ηBound, lt_min hηMod hηBound, ?_, ?_⟩
  · exact mono_radius hMod (min_le_left ηMod ηBound)
  · intro η hη
    exact hBound η ⟨hη.1, hη.2.trans (min_le_right ηMod ηBound)⟩

end Asymptotics.IsUniformRemainderModulusOn
