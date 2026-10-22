/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Combination

-- Semantic recall hits verified for this item: `convex_iff_add_mem` and `Convex.sum_mem`.

section Exercise112

universe u

variable {R E : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E]

/-- Chapter01 Exercise 1.12: a set `S` is convex if and only if every finite convex combination
of points of `S` still belongs to `S`. This is the finite-family bridge to the canonical
`Convex` API. -/
theorem convex_iff_sum_smul_mem {S : Set E} :
    Convex R S ↔
      ∀ (ι : Type u) [Fintype ι] (x : ι → E) (α : ι → R),
        (∀ i, x i ∈ S) →
          (∀ i, 0 ≤ α i) → (∑ i, α i) = 1 → ∑ i, α i • x i ∈ S := by
  constructor
  · intro hS ι _ x α hx hα hsum
    have hmem : (∑ i ∈ (Finset.univ : Finset ι), α i • x i) ∈ S :=
      hS.sum_mem (fun i _ ↦ hα i) (by simpa using hsum) (fun i _ ↦ hx i)
    simpa using hmem
  · intro h
    rw [convex_iff_add_mem]
    intro x hx y hy a b ha hb hab
    let z : ULift.{u} (Fin 2) → E := fun i ↦ ![x, y] i.down
    let α : ULift.{u} (Fin 2) → R := fun i ↦ ![a, b] i.down
    have hz : ∀ i, z i ∈ S := by
      intro i
      rcases i with ⟨i⟩
      fin_cases i <;> simp [z, hx, hy]
    have hα : ∀ i, 0 ≤ α i := by
      intro i
      rcases i with ⟨i⟩
      fin_cases i <;> simp [α, ha, hb]
    have hsum : ∑ i, α i = 1 := by
      calc
        ∑ i, α i = ∑ i : Fin 2, ![a, b] i := by
          simpa [α] using
            (Fintype.sum_equiv Equiv.ulift _ (fun i : Fin 2 ↦ ![a, b] i) (fun _ ↦ rfl))
        _ = 1 := by
          simpa [Fin.sum_univ_two] using hab
    have hmem : ∑ i, α i • z i ∈ S := h (ULift.{u} (Fin 2)) z α hz hα hsum
    have hsum_smul :
        (∑ i, α i • z i) = ∑ i : Fin 2, ![a, b] i • ![x, y] i := by
      simpa [α, z] using
        (Fintype.sum_equiv Equiv.ulift _ (fun i : Fin 2 ↦ ![a, b] i • ![x, y] i)
          (fun _ ↦ rfl))
    rw [hsum_smul] at hmem
    simpa [Fin.sum_univ_two] using hmem

end Exercise112
