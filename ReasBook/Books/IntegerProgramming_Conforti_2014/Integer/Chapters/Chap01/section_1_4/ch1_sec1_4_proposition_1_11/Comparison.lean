/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Real.Basic

open scoped BigOperators

public section

variable {n : ℕ}

/-- A point lies in `convexHull ℝ S` exactly when it admits a finite convex-combination
representation by points of `S`. -/
theorem mem_convexHull_iff_exists_fin {S : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ convexHull ℝ S ↔
      ∃ m : ℕ,
        ∃ s : Fin m → (Fin n → ℝ),
          ∃ w : Fin m → ℝ,
            (∀ i, s i ∈ S) ∧
              (∀ i, 0 ≤ w i) ∧
              (∑ i, w i = 1) ∧
              (∑ i, w i • s i = x) := by
  rw [mem_convexHull_iff_exists_fintype]
  constructor
  · rintro ⟨ι, _, w, s, hw, hsum, hs, hx⟩
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    refine ⟨Fintype.card ι, fun j ↦ s (e.symm j), fun j ↦ w (e.symm j), ?_⟩
    refine ⟨fun j ↦ hs (e.symm j), fun j ↦ hw (e.symm j), ?_, ?_⟩
    · simpa [e] using
        ((Fintype.sum_equiv e w (fun j ↦ w (e.symm j)) (fun i ↦ by simp [e])).symm.trans hsum)
    · simpa [e] using
        ((Fintype.sum_equiv e (fun i ↦ w i • s i)
          (fun j ↦ w (e.symm j) • s (e.symm j)) (fun i ↦ by simp [e])).symm.trans hx)
  · rintro ⟨m, s, w, hs, hw, hsum, hx⟩
    exact ⟨Fin m, inferInstance, w, s, hw, hsum, hs, hx⟩

end
