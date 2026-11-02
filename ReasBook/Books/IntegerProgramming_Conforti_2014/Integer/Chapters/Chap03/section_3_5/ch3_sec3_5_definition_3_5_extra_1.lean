import Mathlib.Geometry.Convex.Cone.DualFinite
import Mathlib.LinearAlgebra.Matrix.ToLin
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix
open PointedCone

section Definition35Extra1

variable {n : ℕ}

/-- Definition 3.5-extra-1 (1). A subset `P` of `ℝ^n` is a polyhedron if there are finitely many
linear inequalities `A *ᵥ x ≤ b` whose solution set is exactly `P`. -/
def is_polyhedron (P : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ, ∃ b : Fin m → ℝ,
    P = polyhedron_le_set A b

/-- A set is a polyhedron exactly when it admits a finite linear-inequality presentation. -/
theorem is_polyhedron_iff {P : Set (Fin n → ℝ)} :
    is_polyhedron P ↔
      ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ, ∃ b : Fin m → ℝ,
        P = polyhedron_le_set A b := by
  rfl

/-- Definition 3.5-extra-1 (2). A subset `P` of `ℝ^n` is a rational polyhedron if it is defined
by finitely many linear inequalities with rational coefficients and rational right-hand side. -/
def is_rational_polyhedron (P : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℚ, ∃ b : Fin m → ℚ,
    P =
      polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))

/-- A set is a rational polyhedron exactly when it admits a rational matrix presentation. -/
theorem is_rational_polyhedron_iff {P : Set (Fin n → ℝ)} :
    is_rational_polyhedron P ↔
      ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℚ, ∃ b : Fin m → ℚ,
        P =
          polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) := by
  rfl

/-- A homogeneous finite matrix-inequality system is the dual cone of the finite set of negated
row vectors of its defining matrix. -/
theorem linear_inequality_solution_set_zero_eq_dual_neg_rows
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    polyhedron_le_set A (0 : Fin m → ℝ) =
      (dual (dotProductBilin ℝ ℝ) (Set.range fun i : Fin m ↦ -(A i)) :
        Set (Fin n → ℝ)) := by
  ext x
  constructor
  · intro hx
    change ∀ ⦃y : Fin n → ℝ⦄, y ∈ Set.range (fun i : Fin m ↦ -(A i)) →
      0 ≤ dotProductBilin ℝ ℝ y x
    intro y hy
    rcases hy with ⟨i, rfl⟩
    simpa [dotProductBilin, Matrix.mulVec, dotProduct] using neg_nonneg.mpr (hx i)
  · intro hx
    change A *ᵥ x ≤ 0
    intro i
    exact neg_nonneg.mp <| by
      have hxi : 0 ≤ dotProductBilin ℝ ℝ (-(A i)) x :=
        hx (show -(A i) ∈ Set.range (fun i : Fin m ↦ -(A i)) by exact ⟨i, rfl⟩)
      simpa [dotProductBilin, Matrix.mulVec, dotProduct] using hxi

/-- Definition 3.5-extra-1 (3). A subset `C` of `ℝ^n` is a polyhedral cone if it is the
intersection of finitely many half-spaces whose boundary hyperplanes all contain the origin,
equivalently if it is the underlying set of a dually finitely generated pointed cone for the
standard dot-product pairing on `ℝ^n`. -/
def is_polyhedral_cone (C : Set (Fin n → ℝ)) : Prop :=
  ∃ K : PointedCone ℝ (Fin n → ℝ),
    K.DualFG (dotProductBilin ℝ ℝ) ∧ (K : Set (Fin n → ℝ)) = C

/-- A set is a polyhedral cone exactly when it is the underlying set of a dually finitely
generated pointed cone for the standard dot-product pairing. -/
theorem is_polyhedral_cone_iff_exists_dualFG {C : Set (Fin n → ℝ)} :
    is_polyhedral_cone C ↔
      ∃ K : PointedCone ℝ (Fin n → ℝ),
        K.DualFG (dotProductBilin ℝ ℝ) ∧ (K : Set (Fin n → ℝ)) = C := by
  rfl

/-- A set is a polyhedral cone exactly when it admits a homogeneous matrix-inequality
presentation. -/
theorem is_polyhedral_cone_iff {C : Set (Fin n → ℝ)} :
    is_polyhedral_cone C ↔
      ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ,
        C = polyhedron_le_set A (0 : Fin m → ℝ) := by
  constructor
  · rintro ⟨K, hK, rfl⟩
    rcases hK with ⟨s, hs⟩
    let e : Fin s.card ≃ ↥s := (Finset.equivFin s).symm
    let A : Matrix (Fin s.card) (Fin n) ℝ := fun i j ↦ -((e i).1 j)
    have hKset :
        (K : Set (Fin n → ℝ)) =
          (dual (dotProductBilin ℝ ℝ) (s : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
      simpa using congrArg (fun L : PointedCone ℝ (Fin n → ℝ) ↦ (L : Set (Fin n → ℝ))) hs.symm
    have hs_range : Set.range (fun i : Fin s.card ↦ -(A i)) = (s : Set (Fin n → ℝ)) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        convert (e i).2 using 1
        ext j
        simp [A]
      · intro hx
        refine ⟨e.symm ⟨x, hx⟩, ?_⟩
        ext j
        simp [A]
    refine ⟨s.card, A, ?_⟩
    calc
      (K : Set (Fin n → ℝ))
          = (dual (dotProductBilin ℝ ℝ) (s : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := hKset
      _ = (dual (dotProductBilin ℝ ℝ) (Set.range fun i : Fin s.card ↦ -(A i)) :
            Set (Fin n → ℝ)) := by rw [hs_range]
      _ = polyhedron_le_set A (0 : Fin s.card → ℝ) := by
        symm
        exact linear_inequality_solution_set_zero_eq_dual_neg_rows A
  · rintro ⟨m, A, rfl⟩
    refine ⟨dual (dotProductBilin ℝ ℝ) (Set.range fun i : Fin m ↦ -(A i)),
      PointedCone.DualFG.dual_of_finite (dotProductBilin ℝ ℝ)
        (Set.finite_range fun i : Fin m ↦ -(A i)), ?_⟩
    symm
    exact linear_inequality_solution_set_zero_eq_dual_neg_rows A

end Definition35Extra1
