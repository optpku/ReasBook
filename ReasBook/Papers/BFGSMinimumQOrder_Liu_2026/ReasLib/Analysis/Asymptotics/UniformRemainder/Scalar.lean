module

public import ReasLib.Analysis.Asymptotics.UniformRemainder

public section

open Filter
open scoped Topology

namespace Asymptotics.IsUniformRemainderOn

universe u

/-- A scalar fixed-coefficient estimate is uniform over the singleton parameter type. -/
theorem of_isBigOWith_singleton
    {E : Type u} [Norm E] {r : ℝ → E} {C q : ℝ}
    (h : IsBigOWith C (nhds 0) r (fun ε ↦ |ε| ^ q)) :
    IsUniformRemainderOn (fun _ : Unit ↦ r) Set.univ C q := by
  apply (isBigOWith_iff (fun _ : Unit ↦ r) Set.univ C q).mp
  have hpull : IsBigOWith C (principal (Set.univ : Set Unit) ×ˢ nhds 0)
      (fun z : Unit × ℝ ↦ r z.2) (fun z : Unit × ℝ ↦ |z.2| ^ q) :=
    h.comp_tendsto (k := Prod.snd) tendsto_snd
  simpa only [Function.comp_apply] using hpull

/-- A scalar big-O estimate has a positive coefficient uniform over `Unit`. -/
theorem exists_pos_of_isBigO_singleton
    {E : Type u} [Norm E] {r : ℝ → E} {q : ℝ}
    (h : r =O[nhds 0] (fun ε ↦ |ε| ^ q)) :
    ∃ C > 0, IsUniformRemainderOn (fun _ : Unit ↦ r) Set.univ C q := by
  obtain ⟨C, hC, hbound⟩ := h.exists_pos
  exact ⟨C, hC, of_isBigOWith_singleton hbound⟩

/-- A scalar natural-power estimate is uniform over the singleton parameter type. -/
theorem of_isBigOWith_natPow_singleton
    {E : Type u} [Norm E] {r : ℝ → E} {C : ℝ} {n : ℕ}
    (h : IsBigOWith C (nhds 0) r (fun ε : ℝ ↦ ε ^ n)) :
    IsUniformRemainderOn (fun _ : Unit ↦ r) Set.univ C (n : ℝ) := by
  apply of_isBigOWith_singleton
  apply IsBigOWith.of_bound
  filter_upwards [h.bound] with ε hε
  simpa only [Real.norm_eq_abs, abs_pow, Real.rpow_natCast,
    abs_of_nonneg (pow_nonneg (abs_nonneg ε) n)] using hε

/-- A scalar natural-power big-O estimate has a positive uniform coefficient. -/
theorem exists_pos_of_isBigO_natPow_singleton
    {E : Type u} [Norm E] {r : ℝ → E} {n : ℕ}
    (h : r =O[nhds 0] (fun ε : ℝ ↦ ε ^ n)) :
    ∃ C > 0, IsUniformRemainderOn (fun _ : Unit ↦ r) Set.univ C (n : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := h.exists_pos
  exact ⟨C, hC, of_isBigOWith_natPow_singleton hbound⟩

end Asymptotics.IsUniformRemainderOn

namespace Asymptotics.IsUniformRemainderModulusOn

universe u

/-- A scalar little-o estimate supplies the canonical uniform modulus over `Unit`. -/
theorem of_isLittleO_singleton
    {E : Type u} [Norm E] {r : ℝ → E} {q : ℝ}
    (h : r =o[nhds 0] (fun ε ↦ |ε| ^ q)) :
    ∃ η₀ > 0, IsUniformRemainderModulusOn (fun _ : Unit ↦ r) Set.univ q η₀
      (uniformRemainderModulus (fun _ : Unit ↦ r) Set.univ q) := by
  apply of_isLittleO
  have hpull : (fun z : Unit × ℝ ↦ r z.2) =o[
      principal (Set.univ : Set Unit) ×ˢ nhds 0] (fun z : Unit × ℝ ↦ |z.2| ^ q) :=
    h.comp_tendsto (k := Prod.snd) tendsto_snd
  simpa only [Function.comp_apply] using hpull

/-- A scalar natural-power little-o estimate supplies the canonical uniform modulus. -/
theorem of_isLittleO_natPow_singleton
    {E : Type u} [Norm E] {r : ℝ → E} {n : ℕ}
    (h : r =o[nhds 0] (fun ε : ℝ ↦ ε ^ n)) :
    ∃ η₀ > 0, IsUniformRemainderModulusOn (fun _ : Unit ↦ r) Set.univ (n : ℝ) η₀
      (uniformRemainderModulus (fun _ : Unit ↦ r) Set.univ (n : ℝ)) := by
  apply of_isLittleO
  rw [Asymptotics.isLittleO_iff_forall_isBigOWith]
  intro C hC
  apply (Asymptotics.IsUniformRemainderOn.isBigOWith_iff
    (fun _ : Unit ↦ r) Set.univ C (n : ℝ)).mpr
  exact Asymptotics.IsUniformRemainderOn.of_isBigOWith_natPow_singleton
    (h.forall_isBigOWith hC)

end Asymptotics.IsUniformRemainderModulusOn
