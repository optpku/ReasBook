module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import Mathlib.Analysis.Asymptotics.Lemmas

public section

namespace Asymptotics.IsUniformRemainderOn

universe u v w

/-- Uniform remainder estimates for two components combine into the product-valued estimate
with the larger of the two coefficients. -/
theorem prod
    {Θ : Type u} {E : Type v} {F : Type w}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    {R : Θ → ℝ → E} {S : Θ → ℝ → F} {s : Set Θ} {C D q : ℝ}
    (hR : IsUniformRemainderOn R s C q)
    (hS : IsUniformRemainderOn S s D q) :
    IsUniformRemainderOn (fun θ ε ↦ (R θ ε, S θ ε)) s (max C D) q := by
  apply (isBigOWith_iff (fun θ ε ↦ (R θ ε, S θ ε)) s (max C D) q).mp
  exact ((isBigOWith_iff R s C q).mpr hR).prod_left
    ((isBigOWith_iff S s D q).mpr hS)

/-- A finite coordinate family with one common scalar remainder coefficient has the same
coefficient after assembling the coordinates into a dependent function space. -/
theorem pi
    {Θ : Type u} {ι : Type v} {E : ι → Type w} [Fintype ι]
    [∀ i, SeminormedAddCommGroup (E i)]
    {R : ∀ i, Θ → ℝ → E i} {s : Set Θ} {C q : ℝ}
    (hC : 0 ≤ C)
    (hR : ∀ i, IsUniformRemainderOn (R i) s C q) :
    IsUniformRemainderOn (fun θ ε i ↦ R i θ ε) s C q := by
  apply (isBigOWith_iff (fun θ ε ↦ fun i ↦ R i θ ε) s C q).mp
  rw [isBigOWith_pi hC]
  intro i
  exact (isBigOWith_iff (R i) s C q).mpr (hR i)

/-- A finite coordinate family with individually bounded coefficients can be assembled under
any nonnegative coefficient that dominates all coordinate bounds. -/
theorem pi_of_dominating_coefficient
    {Θ : Type u} {ι : Type v} {E : ι → Type w} [Fintype ι]
    [∀ i, SeminormedAddCommGroup (E i)]
    {R : ∀ i, Θ → ℝ → E i} {s : Set Θ} {C : ι → ℝ} {D q : ℝ}
    (hD : 0 ≤ D)
    (hR : ∀ i, IsUniformRemainderOn (R i) s (C i) q)
    (hC : ∀ i, C i ≤ D) :
    IsUniformRemainderOn (fun θ ε i ↦ R i θ ε) s D q := by
  apply (isBigOWith_iff (fun θ ε ↦ fun i ↦ R i θ ε) s D q).mp
  rw [isBigOWith_pi hD]
  intro i
  exact ((isBigOWith_iff (R i) s (C i) q).mpr (hR i)).weaken (hC i)

/-- A nonempty finite coordinate family inherits a uniform remainder bound with the exact
finite supremum of its nonnegative coordinate coefficients. -/
theorem pi_of_finset_sup
    {Θ : Type u} {ι : Type v} {E : ι → Type w} [Fintype ι] [Nonempty ι]
    [∀ i, SeminormedAddCommGroup (E i)]
    {R : ∀ i, Θ → ℝ → E i} {s : Set Θ} {C : ι → ℝ} {q : ℝ}
    (hC : ∀ i, 0 ≤ C i)
    (hR : ∀ i, IsUniformRemainderOn (R i) s (C i) q) :
    IsUniformRemainderOn (fun θ ε i ↦ R i θ ε) s
      (Finset.univ.sup' Finset.univ_nonempty C) q := by
  let D : ℝ := Finset.univ.sup' Finset.univ_nonempty C
  have hD : 0 ≤ D := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (hC i).trans (Finset.le_sup' C (Finset.mem_univ i))
  have hdom : ∀ i, C i ≤ D := by
    intro i
    exact Finset.le_sup' C (Finset.mem_univ i)
  exact pi_of_dominating_coefficient hD hR hdom

end Asymptotics.IsUniformRemainderOn
