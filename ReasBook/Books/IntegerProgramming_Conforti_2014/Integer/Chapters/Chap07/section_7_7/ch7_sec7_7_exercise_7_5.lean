/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_proposition_7_2

-- Exercise 7.5 is a source-facing companion to Proposition 7.2, so this file reuses the
-- Chapter 7.2 owner API for binary last-coordinate lifting instead of restating a local copy.

noncomputable section

section Exercise75

variable {n : ℕ}

/-- Exercise 7.5. In the `Fin (n + 1)` indexing convention of Proposition 7.2, let
`S ⊆ {0,1}^(n+1)` and suppose `∑_{i < n} αᵢ xᵢ ≤ β` is valid on `S ∩ {x_last = 1}`. If the
maximum of `∑_{i < n} αᵢ xᵢ` on `S ∩ {x_last = 0}` is attained, then the lifted inequality
`∑_{i < n} αᵢ xᵢ + λ x_last ≤ β + λ`, with
`λ = max {∑_{i < n} αᵢ xᵢ | x ∈ S, x_last = 0} - β`, is valid for `conv(S)`. The
nonemptiness of the `x_last = 0` slice is already encoded by the maximum-attainment hypothesis. -/
theorem binary_last_coordinate_lifting_from_one_slice_valid
    (S : Set (Fin (n + 1) → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hS_binary :
      S ⊆ zero_one_points (Nat.le_refl (n + 1)) (Set.univ : Set (Fin (n + 1) → ℝ)))
    (hvalid_one :
      is_valid_inequality
        (S ∩ last_coordinate_eq_set n 1)
        (Fin.snoc α 0)
        β)
    (hmax :
      IsGreatest
        (last_coordinate_slice_values S α 0)
        (sSup (last_coordinate_slice_values S α 0))) :
    is_valid_inequality
      (convexHull ℝ S)
      (Fin.snoc α
        (sSup (last_coordinate_slice_values S α 0) - β))
      (β + (sSup (last_coordinate_slice_values S α 0) - β)) := by
  -- Reduce validity on the convex hull to validity on the original binary set `S`.
  refine (is_valid_inequality_convexHull_iff).2 ?_
  intro x hxS
  have hxlast_binary :
      x (Fin.last n) = 0 ∨ x (Fin.last n) = 1 :=
    (mem_zero_one_points_univ_iff.mp (hS_binary hxS)) (Fin.last n)
  rcases hxlast_binary with hxlast0 | hxlast1
  · -- On the `x_last = 0` slice, bound the partial objective by the attained slice supremum.
    have hxslice :
        partial_lifting_value α x ∈ last_coordinate_slice_values S α 0 := by
      exact mem_last_coordinate_slice_values_iff.mpr ⟨x, hxS, hxlast0, rfl⟩
    have hpartial_le :
        partial_lifting_value α x ≤ sSup (last_coordinate_slice_values S α 0) :=
      hmax.2 hxslice
    have hbound :
        partial_lifting_value α x ≤
          β + (sSup (last_coordinate_slice_values S α 0) - β) := by
      linarith
    simpa [dotProduct_last_coordinate_lifting_coeffs, hxlast0] using hbound
  · -- On the `x_last = 1` slice, reuse the given valid inequality before adding the lift.
    have hpartial_le :
        partial_lifting_value α x ≤ β := by
      simpa [dotProduct_last_coordinate_lifting_coeffs, hxlast1] using
        hvalid_one ⟨hxS, mem_last_coordinate_eq_set_iff.mpr hxlast1⟩
    have hbound :
        partial_lifting_value α x + (sSup (last_coordinate_slice_values S α 0) - β) ≤
          β + (sSup (last_coordinate_slice_values S α 0) - β) := by
      linarith
    simpa [dotProduct_last_coordinate_lifting_coeffs, hxlast1] using hbound

end Exercise75
