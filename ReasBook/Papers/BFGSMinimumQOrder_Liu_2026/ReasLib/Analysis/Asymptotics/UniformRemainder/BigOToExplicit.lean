module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import ReasLib.Analysis.Asymptotics.UniformRemainder.Scalar
public import ReasLib.Analysis.Asymptotics.UniformRemainder.ExplicitBound
public import ReasLib.Analysis.Asymptotics.UniformRemainder
import all ReasLib.Analysis.Asymptotics.UniformRemainder

public section

open Filter
open scoped Topology

namespace Asymptotics.IsUniformRemainderOn

universe u v

/-- A product-filter big-O estimate supplies a positive coefficient and one
common explicit radius for every parameter in the prescribed set. -/
theorem exists_pos_explicit_bound_of_isBigO
    {Theta : Type u} {E : Type v} [Norm E]
    {R : Theta → ℝ → E} {s : Set Theta} {q : ℝ}
    (hR : (fun z : Theta × ℝ ↦ R z.1 z.2) =O[
      Filter.principal s ×ˢ 𝓝 0]
      (fun z : Theta × ℝ ↦ |z.2| ^ q)) :
    ∃ C > 0, ∃ delta > 0, ∀ theta ∈ s, ∀ epsilon : ℝ,
      |epsilon| < delta → ‖R theta epsilon‖ ≤ C * |epsilon| ^ q := by
  obtain ⟨C, hC, hBig⟩ := hR.exists_pos
  have hUniform : IsUniformRemainderOn R s C q :=
    (IsUniformRemainderOn.isBigOWith_iff R s C q).mp hBig
  obtain ⟨delta, hdelta, hbound⟩ := hUniform
  exact ⟨C, hC, delta, hdelta, hbound⟩

/-- A scalar natural-power big-O estimate supplies a positive coefficient and
one explicit absolute-value power bound near zero. -/
theorem exists_pos_natPow_bound_of_isBigO
    {E : Type u} [Norm E] {r : ℝ → E} {n : ℕ}
    (hR : r =O[𝓝 0] (fun epsilon : ℝ ↦ epsilon ^ n)) :
    ∃ C > 0, ∃ delta > 0, ∀ epsilon : ℝ,
      |epsilon| < delta → ‖r epsilon‖ ≤ C * |epsilon| ^ n := by
  obtain ⟨C, hC, hUniform⟩ :=
    Asymptotics.IsUniformRemainderOn.exists_pos_of_isBigO_natPow_singleton hR
  obtain ⟨delta, hdelta, hbound⟩ := hUniform
  refine ⟨C, hC, delta, hdelta, ?_⟩
  intro epsilon hepsilon
  have h := hbound () (Set.mem_univ ()) epsilon hepsilon
  simpa only [Real.rpow_natCast] using h

/-- A finite family of scalar natural-power big-O estimates has one
positive coefficient and one common explicit radius. -/
theorem exists_pos_finite_natPow_bound_of_isBigO
    {ι : Type*} [Finite ι] [Nonempty ι]
    {E : Type u} [Norm E] {r : ι → ℝ → E} {n : ℕ}
    (hR : ∀ i, r i =O[𝓝 0] (fun epsilon : ℝ ↦ epsilon ^ n)) :
    ∃ C > 0, ∃ delta > 0, ∀ i : ι, ∀ epsilon : ℝ,
      |epsilon| < delta → ‖r i epsilon‖ ≤ C * |epsilon| ^ n := by
  classical
  -- Local instance justification (finite family fold): Finset.sup' and inf'
  -- require a concrete finite enumeration, while only Finite is part of the API.
  letI := Fintype.ofFinite ι
  choose C hC delta hdelta hbound using fun i ↦
    exists_pos_natPow_bound_of_isBigO (hR i)
  let C₀ : ℝ := Finset.univ.sup' Finset.univ_nonempty C
  let delta₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty delta
  have hC₀ : 0 < C₀ := by
    dsimp only [C₀]
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact lt_of_lt_of_le (hC i) (Finset.le_sup' C (Finset.mem_univ i))
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    exact (Finset.lt_inf'_iff _).2 (fun i _ => hdelta i)
  refine ⟨C₀, hC₀, delta₀, hdelta₀, ?_⟩
  intro i epsilon hepsilon
  have hepsilon_i : |epsilon| < delta i := by
    exact lt_of_lt_of_le hepsilon (Finset.inf'_le _ (Finset.mem_univ i))
  have h_i := hbound i epsilon hepsilon_i
  have hCi : C i ≤ C₀ := by
    dsimp only [C₀]
    exact Finset.le_sup' C (Finset.mem_univ i)
  exact h_i.trans (mul_le_mul_of_nonneg_right hCi
    (pow_nonneg (abs_nonneg epsilon) n))

/-- A product-filter big-O estimate of order `n + 1` directly supplies the
canonical order-`n` modulus and its linear radius bound. -/
theorem exists_natPow_modulus_spec_of_isBigO
    {Theta : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Theta → ℝ → E} {s : Set Theta} {n : ℕ}
    (hR : (fun z : Theta × ℝ ↦ R z.1 z.2) =O[
      Filter.principal s ×ˢ 𝓝 0]
      (fun z : Theta × ℝ ↦ |z.2| ^ ((n + 1 : ℕ) : ℝ))) :
    ∃ C > 0, ∃ eta0 > 0,
      Asymptotics.IsUniformRemainderOn R s C ((n + 1 : ℕ) : ℝ) ∧
        Asymptotics.IsUniformRemainderModulusOn R s (n : ℝ) eta0
          (Asymptotics.uniformRemainderModulus R s (n : ℝ)) ∧
        ∀ eta ∈ Set.Ioc 0 eta0,
          Asymptotics.uniformRemainderModulus R s (n : ℝ) eta ≤ C * eta := by
  obtain ⟨C, hC, delta, hdelta, hboundRpow⟩ :=
    exists_pos_explicit_bound_of_isBigO hR
  have hboundNat : ∀ theta ∈ s, ∀ epsilon : ℝ, |epsilon| < delta →
      ‖R theta epsilon‖ ≤ C * |epsilon| ^ (n + 1) := by
    intro theta htheta epsilon hepsilon
    have h := hboundRpow theta htheta epsilon hepsilon
    simpa only [Real.rpow_natCast] using h
  obtain ⟨eta0, heta0, hUniform, hMod, hBound⟩ :=
    Asymptotics.IsUniformRemainderModulusOn.exists_natPow_modulus_spec_of_explicit_bound
      hdelta hC.le hboundNat
  exact ⟨C, hC, eta0, heta0, hUniform, hMod, hBound⟩

end Asymptotics.IsUniformRemainderOn
