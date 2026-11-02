import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_theorem_3_46

open scoped BigOperators Matrix

-- Declarations for this item will be appended below by the statement pipeline.

/-- Exercise 3.35. For the polyhedron
`P = {(x, z) ∈ ℝ^n × ℝ^p | A *ᵥ x + B *ᵥ z ≤ b}`, if its projection cone is `{0}`, then the
projection of `P` onto the `x`-coordinates is all of `ℝ^n`. -/
theorem x_projection_eq_univ_of_polyhedron_projection_cone_eq_zero
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (h_cone : polyhedron_projection_cone B = ({0} : Set (Fin m → ℝ))) :
    Prod.fst '' {xz : (Fin n → ℝ) × (Fin p → ℝ) | A *ᵥ xz.1 + B *ᵥ xz.2 ≤ b} = Set.univ := by
  let rays : Fin 0 → Fin m → ℝ := Fin.elim0
  have h_empty_cone :
      polyhedron_projection_cone B = finitely_generated_cone rays :=
    by
      rw [h_cone]
      ext u
      rw [Set.mem_singleton_iff, mem_finitely_generated_cone_iff]
      constructor
      · intro hu
        subst hu
        refine ⟨Fin.elim0, ?_, ?_⟩
        · intro t
          exact Fin.elim0 t
        · simp [rays]
      · rintro ⟨μ, _, hu⟩
        simpa [rays] using hu
  calc
    Prod.fst '' {xz : (Fin n → ℝ) × (Fin p → ℝ) | A *ᵥ xz.1 + B *ᵥ xz.2 ≤ b} =
        {x : Fin n → ℝ | ∀ t : Fin 0, rays t ⬝ᵥ (A *ᵥ x) ≤ rays t ⬝ᵥ b} :=
      polyhedron_x_projection_eq_generator_inequalities A B b rays h_empty_cone
    _ = Set.univ :=
      by
        ext x
        simp [rays]
