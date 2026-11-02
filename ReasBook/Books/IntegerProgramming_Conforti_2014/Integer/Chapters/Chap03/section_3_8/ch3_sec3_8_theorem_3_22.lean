import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1

open scoped Matrix

/-- Theorem 3.22. Let `P := polyhedron_le_set A b` be nonempty. An inequality `c ⬝ᵥ x ≤ δ` is
valid for `P` if and only if there exists a nonnegative multiplier `u` such that `u ᵥ* A = c` and
`u ⬝ᵥ b ≤ δ`. -/
theorem valid_inequality_iff_exists_nonneg_row_multiplier
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (δ : ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty) :
    is_valid_inequality (polyhedron_le_set A b) c δ ↔
      ∃ u : Fin m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ := by
  constructor
  · intro hvalid
    -- Route correction: reuse the Chapter 3.7 multiplier theorem after unfolding the owner set.
    have hP_nonempty_raw : Set.Nonempty {x : Fin n → ℝ | A *ᵥ x ≤ b} := by
      simpa [polyhedron_le_set] using hP_nonempty
    have hvalid_raw : ∀ ⦃x : Fin n → ℝ⦄, x ∈ {x : Fin n → ℝ | A *ᵥ x ≤ b} → c ⬝ᵥ x ≤ δ := by
      simpa [is_valid_inequality, polyhedron_le_set] using hvalid
    exact exists_nonneg_row_multiplier_of_valid_inequality A b c δ hP_nonempty_raw hvalid_raw
  · rintro ⟨u, hu_nonneg, hu_row, hub⟩
    rw [is_valid_inequality_iff]
    intro x hx
    -- Convert the polyhedron certificate into the primal/dual feasible regions.
    have hx_primal : x ∈ primal_feasible_region A b := by
      simpa [polyhedron_le_set, primal_feasible_region] using hx
    have hu_dual : u ∈ dual_feasible_region A c := by
      exact (mem_dual_feasible_region_iff A c u).2 ⟨hu_row, hu_nonneg⟩
    -- Weak duality gives the bound by `u ⬝ᵥ b`, then `u ⬝ᵥ b ≤ δ` finishes.
    calc
      c ⬝ᵥ x ≤ u ⬝ᵥ b := weak_duality_feasible_pair A b c hx_primal hu_dual
      _ ≤ δ := hub
