/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2.ch5_sec5_2_definition_5_2_extra_2

open scoped Matrix

section Lemma513

variable {m n : ℕ}

/-- For the pure-integer specialization `I = Finset.univ`, a Chvátal multiplier is simply a
nonnegative row multiplier whose left product with `A` has integral coordinates. -/
theorem isChvatalMultiplier_univ_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin m → ℝ) :
    IsChvatalMultiplier A Finset.univ u ↔
      (∀ i : Fin m, 0 ≤ u i) ∧
        ∀ j : Fin n, ∃ z : ℤ, (u ᵥ* A) j = (z : ℝ) := by
  rw [isChvatalMultiplier_iff]
  constructor
  · rintro ⟨hu_nonneg, hu_int, _hu_zero⟩
    exact ⟨hu_nonneg, fun j ↦ hu_int j (Finset.mem_univ j)⟩
  · rintro ⟨hu_nonneg, hu_int⟩
    refine ⟨hu_nonneg, fun j _ ↦ hu_int j, fun j hj ↦ ?_⟩
    exact False.elim (hj (Finset.mem_univ j))

/-- Lemma 5.13. For `P = {x : ℝ^n | A x ≤ b}` with integral data, the Chvátal closure `P^Ch`
is the `I = Finset.univ` specialization of the Chapter 5 mixed-integer Chvátal-closure owner. -/
theorem mem_pure_integer_chvatalClosure_iff
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    (x : Fin n → ℝ) :
    x ∈ chvatalClosure (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) Finset.univ ↔
      x ∈ polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) ∧
        ∀ u : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ u i) →
          (∀ j : Fin n, ∃ z : ℤ, (u ᵥ* (A.map (Int.castRingHom ℝ))) j = (z : ℝ)) →
          (u ᵥ* (A.map (Int.castRingHom ℝ))) ⬝ᵥ x ≤
            ((⌊u ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) : ℝ) := by
  simpa [Finset.mem_univ] using
    (mem_chvatalClosure_expanded_iff
      (A.map (Int.castRingHom ℝ))
      (fun i ↦ (b i : ℝ))
      Finset.univ
      x)

end Lemma513
