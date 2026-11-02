import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Polyhedron

open scoped Matrix

section LinearRelaxation

variable {m n p : ℕ}

/-- Definition 1.4 (1). Let `S ⊆ (ℤ^n × ℝ^p)`. A linear relaxation of `S` is a mixed polyhedron
`P'` of the form `real_mixed_polyhedron A G b` such that `S ⊆ P'`. -/
structure IsLinearRelaxation
    (S : Set (MixedRealPoint n p))
    (P' : Set (MixedRealPoint n p)) : Prop where
  presentation :
    ∃ m : ℕ,
      ∃ A : Matrix (Fin m) (Fin n) ℝ,
        ∃ G : Matrix (Fin m) (Fin p) ℝ,
          ∃ b : Fin m → ℝ, P' = real_mixed_polyhedron A G b
  subset : S ⊆ P'

namespace IsLinearRelaxation

/-- Construct `IsLinearRelaxation S P'` from an explicit mixed-system presentation of `P'` and the
containment `S ⊆ P'`. -/
def ofPresentation
    (S : Set (MixedRealPoint n p))
    (P' : Set (MixedRealPoint n p))
    (m : ℕ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (hP' : P' = real_mixed_polyhedron A G b)
    (hSP' : S ⊆ P') :
    IsLinearRelaxation S P' :=
  { presentation := ⟨m, A, G, b, hP'⟩
    subset := hSP' }

/-- Every linear relaxation is, in particular, a mixed polyhedron. -/
theorem isMixedPolyhedron
    (S : Set (MixedRealPoint n p))
    (P' : Set (MixedRealPoint n p))
    (hP' : IsLinearRelaxation S P') :
    is_mixed_polyhedron P' := by
  rcases hP'.presentation with ⟨m, A, G, b, rfl⟩
  exact is_mixed_polyhedron_real_mixed_polyhedron A G b

end IsLinearRelaxation

/-- Unfolding equation for `IsLinearRelaxation`, exposing the mixed-system presentation and the
containment `S ⊆ P'`. The standing assumption `S ⊆ (ℤ^n × ℝ^p)` is ambient source
context, not additional data of the relaxation relation. -/
theorem isLinearRelaxation_iff
    (S : Set (MixedRealPoint n p))
    (P' : Set (MixedRealPoint n p)) :
    IsLinearRelaxation S P' ↔
      ∃ m : ℕ,
        ∃ A : Matrix (Fin m) (Fin n) ℝ,
          ∃ G : Matrix (Fin m) (Fin p) ℝ,
            ∃ b : Fin m → ℝ, P' = real_mixed_polyhedron A G b ∧ S ⊆ P' := by
  constructor
  · intro hP'
    rcases hP'.presentation with ⟨m, A, G, b, hPresentation⟩
    exact ⟨m, A, G, b, hPresentation, hP'.subset⟩
  · rintro ⟨m, A, G, b, hPresentation, hSubset⟩
    exact IsLinearRelaxation.ofPresentation S P' m A G b hPresentation hSubset

end LinearRelaxation
