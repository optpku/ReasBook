/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace

open scoped IntegerVectorNotation Matrix MixedIntegerNotation

public section

section Definition12FeasibleRegion

variable {m n p : ℕ}

/-- The nonnegative mixed polyhedron
`{(x, y) ∈ ℝ^n × ℝ^p | A x + G y ≤ b, x ≥ 0, y ≥ 0}` attached to real data `A`, `G`, and `b`. -/
def nonnegative_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) : Set (MixedRealPoint n p) :=
  {xy | A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧ 0 ≤ xy.1 ∧ 0 ≤ xy.2}

/-- Membership in `nonnegative_mixed_polyhedron A G b` is exactly the defining inequality system
`A x + G y ≤ b` together with the nonnegativity constraints on both blocks. -/
theorem mem_nonnegative_mixed_polyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xy : MixedRealPoint n p} :
    xy ∈ nonnegative_mixed_polyhedron A G b ↔
      A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧ 0 ≤ xy.1 ∧ 0 ≤ xy.2 := by
  rfl

/-- The canonical LP-relaxation feasible region
`{(x, y) ∈ ℝ_+^n × ℝ_+^p | A x + G y ≤ b}` attached to `A`, `G`, and `b`. -/
abbrev lp_relaxation_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) : Set (MixedRealPoint n p) :=
  nonnegative_mixed_polyhedron A G b

namespace lp_relaxation_feasible_set

/-- `lp_relaxation_feasible_set A G b` is definitionally the core owner
`nonnegative_mixed_polyhedron A G b`. -/
theorem eq_nonnegative_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    lp_relaxation_feasible_set A G b = nonnegative_mixed_polyhedron A G b :=
  rfl

end lp_relaxation_feasible_set

/-- Membership in the LP-relaxation feasible region means satisfying `A x + G y ≤ b` together
with the coordinatewise nonnegativity constraints `x ≥ 0` and `y ≥ 0`. -/
theorem mem_lp_relaxation_feasible_set_iff
    {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xy : MixedRealPoint n p} :
    xy ∈ lp_relaxation_feasible_set A G b ↔
      A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧ 0 ≤ xy.1 ∧ 0 ≤ xy.2 :=
  mem_nonnegative_mixed_polyhedron_iff

/-- The canonical mixed-integer feasible region
`{(x, y) ∈ ℤ_+^n × ℝ_+^p | A x + G y ≤ b}` attached to `A`, `G`, and `b`. -/
abbrev milp_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) : Set (MixedRealPoint n p) :=
  lp_relaxation_feasible_set A G b ∩ mixed_integer_lattice n p

/-- Membership in the mixed-integer feasible region means satisfying the defining inequalities,
coordinatewise nonnegativity, and membership in the canonical mixed lattice `ℤ^n × ℝ^p`. -/
theorem mem_milp_feasible_set_iff_mem_mixed_integer_lattice
    {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xy : MixedRealPoint n p} :
    xy ∈ milp_feasible_set A G b ↔
      A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧ 0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧
        xy ∈ (ℤ^n×ℝ^p) := by
  rw [milp_feasible_set, Set.mem_inter_iff, mem_lp_relaxation_feasible_set_iff]
  constructor
  · rintro ⟨⟨hineq, hx_nonneg, hy_nonneg⟩, hxy_lattice⟩
    exact ⟨hineq, hx_nonneg, hy_nonneg, hxy_lattice⟩
  · rintro ⟨hineq, hx_nonneg, hy_nonneg, hxy_lattice⟩
    exact ⟨⟨hineq, hx_nonneg, hy_nonneg⟩, hxy_lattice⟩

/-- Membership in the mixed-integer feasible region means satisfying the defining inequalities,
coordinatewise nonnegativity, and coordinatewise integrality of the `x`-block. -/
theorem mem_milp_feasible_set_iff
    {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xy : MixedRealPoint n p} :
    xy ∈ milp_feasible_set A G b ↔
      A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧ 0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧
        ∀ j : Fin n, ∃ z : ℤ, xy.1 j = (z : ℝ) := by
  rw [mem_milp_feasible_set_iff_mem_mixed_integer_lattice]
  constructor
  · rintro ⟨hineq, hx_nonneg, hy_nonneg, hxy_lattice⟩
    refine ⟨hineq, hx_nonneg, hy_nonneg, ?_⟩
    have hx_integer : xy.1 ∈ ℤ^n := by
      exact mem_integerVectors_iff.mpr <| mem_mixed_integer_lattice_exists_iff.mp hxy_lattice
    rw [mem_integerVectors_iff_forall] at hx_integer
    simpa [Set.mem_range, eq_comm] using hx_integer
  · rintro ⟨hineq, hx_nonneg, hy_nonneg, hx_integral⟩
    refine ⟨hineq, hx_nonneg, hy_nonneg, ?_⟩
    have hx_integer : xy.1 ∈ ℤ^n := by
      rw [mem_integerVectors_iff_forall]
      simpa [Set.mem_range, eq_comm] using hx_integral
    exact mem_mixed_integer_lattice_exists_iff.mpr <| mem_integerVectors_iff.mp hx_integer

/-- The MILP feasible region is contained in its LP relaxation. -/
theorem milp_feasible_set_subset_lp_relaxation_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    milp_feasible_set A G b ⊆ lp_relaxation_feasible_set A G b := by
  intro xy hxy
  rw [milp_feasible_set, Set.mem_inter_iff] at hxy
  exact hxy.1

/-- Every point of the MILP feasible region lies in the canonical mixed lattice `ℤ^n × ℝ^p`. -/
theorem milp_feasible_set_subset_mixed_integer_lattice
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    milp_feasible_set A G b ⊆ (ℤ^n×ℝ^p) := by
  intro xy hxy
  exact (mem_milp_feasible_set_iff_mem_mixed_integer_lattice.mp hxy).2.2.2

end Definition12FeasibleRegion

end
