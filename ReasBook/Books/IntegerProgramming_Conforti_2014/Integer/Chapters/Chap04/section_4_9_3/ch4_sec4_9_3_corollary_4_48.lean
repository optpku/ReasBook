/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_theorem_4_30
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_remark_4_43
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9_3.ch4_sec4_9_3_theorem_4_47

open scoped BigOperators Matrix Pointwise

-- The rational-polytope / integer-cone owners are established in Theorem 4.47. This file keeps
-- only the Corollary 4.48 lifted-polyhedron and projection layer built on those owners.
-- Domain-style sampling for this refine pass:
-- * primary domain: Balas-style lifted polyhedron projections for unions of polyhedra
-- * core/canonical owners inspected upstream: `balas_lifted_polyhedron`,
--   `mixed_integer_x_projection`, `integral_intcone`
-- * layer targeted here: `source-facing` lifted system, with the projection kept as the canonical
--   direct image under `Prod.fst` rather than as a parallel one-off owner

namespace BalasIntegralLift

/-- The lifted polyhedron `Q` from Corollary 4.48, with variables `(x, xParts, δ, μ)`
satisfying `Aᵢ xⁱ ≤ δᵢ bⁱ`, `x = ∑ xⁱ + ∑ μⱼ rʲ`,
`∑ δᵢ = 1`, `δᵢ ≥ 0`, and `μⱼ ≥ 0`. -/
def polyhedron
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ) :
    Set ((Fin n → ℝ) × (Fin k → Fin n → ℝ) × (Fin k → ℝ) × (Fin t → ℝ)) :=
  {(x, xParts, δ, μ) |
    (∀ i : Fin k,
      (A i).map (Rat.castHom ℝ) *ᵥ xParts i ≤
        δ i • (fun j : Fin (m i) ↦ (b i j : ℝ))) ∧
      (x =
        (∑ i : Fin k, xParts i) +
          ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ))) ∧
      (∑ i : Fin k, δ i = 1) ∧
      (∀ i : Fin k, 0 ≤ δ i) ∧
      (∀ j : Fin t, 0 ≤ μ j)}

/-- Membership in `polyhedron m A b r` is exactly the system
of inequalities displayed in `(4.35)`. -/
theorem mem_polyhedron_iff
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ)
    (x : Fin n → ℝ)
    (xParts : Fin k → Fin n → ℝ)
    (δ : Fin k → ℝ)
    (μ : Fin t → ℝ) :
    (x, xParts, δ, μ) ∈ polyhedron m A b r ↔
      (∀ i : Fin k,
        (A i).map (Rat.castHom ℝ) *ᵥ xParts i ≤
          δ i • (fun j : Fin (m i) ↦ (b i j : ℝ))) ∧
        (x =
          (∑ i : Fin k, xParts i) +
            ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ))) ∧
        (∑ i : Fin k, δ i = 1) ∧
        (∀ i : Fin k, 0 ≤ δ i) ∧
        (∀ j : Fin t, 0 ≤ μ j) := by
  rfl

/-- Corollary 4.48's lifted system is equivalently a Balas lifted witness for
`x - ∑ μⱼ rʲ`, together with nonnegative cone coefficients `μ`. -/
theorem mem_polyhedron_iff_mem_balas_lifted
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ)
    (x : Fin n → ℝ)
    (xParts : Fin k → Fin n → ℝ)
    (δ : Fin k → ℝ)
    (μ : Fin t → ℝ) :
    (x, xParts, δ, μ) ∈ polyhedron m A b r ↔
      (x - ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ)), xParts, δ) ∈
          balas_lifted_polyhedron m
            (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
            (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ)) ∧
        (∀ j : Fin t, 0 ≤ μ j) := by
  rw [mem_polyhedron_iff, mem_balas_lifted_polyhedron_iff]
  constructor
  · rintro ⟨hineq, hsumX, hsumδ, hδnonneg, hμnonneg⟩
    refine ⟨?_, hμnonneg⟩
    refine ⟨hineq, ?_, hsumδ, hδnonneg⟩
    exact eq_sub_iff_add_eq.mpr hsumX.symm
  · rintro ⟨hBalas, hμnonneg⟩
    rcases hBalas with ⟨hineq, hsumX, hsumδ, hδnonneg⟩
    refine ⟨hineq, ?_, hsumδ, hδnonneg, hμnonneg⟩
    exact (eq_sub_iff_add_eq.mp hsumX).symm

/-- Membership in the `x`-projection of `polyhedron m A b r` means that `x` admits compatible
lifted variables `(xParts, δ, μ)` satisfying the Corollary 4.48 system. -/
theorem mem_x_projection_iff
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ)
    (x : Fin n → ℝ) :
    x ∈ Prod.fst '' polyhedron m A b r ↔
      ∃ xParts : Fin k → Fin n → ℝ, ∃ δ : Fin k → ℝ, ∃ μ : Fin t → ℝ,
        (x, xParts, δ, μ) ∈ polyhedron m A b r := by
  constructor
  · rintro ⟨⟨x', xParts, δ, μ⟩, hxLifted, hfst⟩
    cases hfst
    exact ⟨xParts, δ, μ, hxLifted⟩
  · rintro ⟨xParts, δ, μ, hxLifted⟩
    exact ⟨(x, xParts, δ, μ), hxLifted, rfl⟩

/-- Helper for Corollary 4.48: the projection of the source-facing lift `Q` splits into Balas'
`x`-projection for the polytope union and the finitely generated cone of the common rays. -/
lemma x_projection_eq_balas_x_projection_add_cone
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ) :
    Prod.fst '' polyhedron m A b r =
      balas_x_projection m
        (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
        (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ)) +
        finitely_generated_cone (fun j : Fin t ↦ fun l : Fin n ↦ (r j l : ℝ)) := by
  ext x
  constructor
  · rintro ⟨y, hxLifted, rfl⟩
    rcases y with ⟨x', xParts, δ, μ⟩
    rw [mem_polyhedron_iff] at hxLifted
    rcases hxLifted with ⟨hineq, hsumX, hsumδ, hδnonneg, hμnonneg⟩
    refine Set.mem_add.2
      ⟨∑ i : Fin k, xParts i, ?_,
        ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ)),
        ?_, hsumX.symm⟩
    · rw [mem_balas_x_projection_iff]
      refine ⟨xParts, δ, ?_⟩
      rw [mem_balas_lifted_polyhedron_iff]
      exact ⟨hineq, rfl, hsumδ, hδnonneg⟩
    · exact (mem_finitely_generated_cone_iff).2 ⟨μ, hμnonneg, rfl⟩
  · intro hx
    rcases Set.mem_add.1 hx with ⟨xBase, hxBase, xCone, hxCone, hsumX⟩
    rw [mem_balas_x_projection_iff] at hxBase
    rcases hxBase with ⟨xParts, δ, hxBalas⟩
    rw [mem_balas_lifted_polyhedron_iff] at hxBalas
    rcases hxBalas with ⟨hineq, hBaseEq, hsumδ, hδnonneg⟩
    rcases (mem_finitely_generated_cone_iff).1 hxCone with ⟨μ, hμnonneg, hConeEq⟩
    refine ⟨(x, xParts, δ, μ), ?_, rfl⟩
    rw [mem_polyhedron_iff]
    refine ⟨hineq, ?_, hsumδ, hδnonneg, hμnonneg⟩
    calc
      x = xBase + xCone := hsumX.symm
      _ = (∑ i : Fin k, xParts i) + xCone := by rw [← hBaseEq]
      _ = (∑ i : Fin k, xParts i) +
            ∑ j : Fin t, μ j • (fun l : Fin n ↦ (r j l : ℝ)) := by
          rw [hConeEq]

/-- Corollary 4.48 in canonical form: the convex hull of the source union-plus-integral-cone
description is the Balas `x`-projection of the rational-polytope pieces plus the real cone on the
same rays. -/
theorem convexHull_eq_balas_x_projection_add_cone
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ)
    (hP_polytope : ∀ i : Fin k, (rational_matrix_polyhedron (A i) (b i)).IsRationalPolytope)
    (hP_nonempty : ∀ i : Fin k, (rational_matrix_polyhedron (A i) (b i)).Nonempty) :
    convexHull ℝ ((⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)) + integral_intcone r) =
      balas_x_projection m
        (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
        (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ)) +
        finitely_generated_cone (fun j : Fin t ↦ fun l : Fin n ↦ (r j l : ℝ)) := by
  classical
  choose vertexCount vertex hvertex using hP_polytope
  let vertexSet : Set (Fin n → ℝ) :=
    ⋃ i : Fin k,
      Set.range (fun j : Fin (vertexCount i) ↦ fun l : Fin n ↦ (vertex i j l : ℝ))
  let vertexFinset : Finset (Fin n → ℝ) :=
    Finset.univ.biUnion fun i : Fin k ↦
      Finset.univ.image (fun j : Fin (vertexCount i) ↦ fun l : Fin n ↦ (vertex i j l : ℝ))
  have hvertexSet_eq :
      vertexSet = (vertexFinset : Set (Fin n → ℝ)) := by
    ext x
    simp [vertexSet, vertexFinset]
  have hvertexSet_finite : vertexSet.Finite := by
    rw [hvertexSet_eq]
    exact vertexFinset.finite_toSet
  have hConvexHull_union_eq_vertexSet :
      convexHull ℝ (⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)) =
        convexHull ℝ vertexSet := by
    refine Set.Subset.antisymm ?_ ?_
    · refine convexHull_min ?_ (convex_convexHull ℝ vertexSet)
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
      rw [hvertex i] at hx
      exact
        (convexHull_mono (by
          intro y hy
          exact Set.mem_iUnion.2 ⟨i, hy⟩)) hx
    · refine
        convexHull_min ?_
          (convex_convexHull ℝ (⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)))
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
      refine subset_convexHull ℝ _ <| Set.mem_iUnion.2 ⟨i, ?_⟩
      rw [hvertex i]
      exact subset_convexHull ℝ _ hx
  have hConvexHull_union_closed :
      IsClosed (convexHull ℝ (⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i))) := by
    rw [hConvexHull_union_eq_vertexSet]
    exact hvertexSet_finite.isClosed_convexHull ℝ
  have hP_nonempty_real :
      ∀ i : Fin k,
        (polyhedron_le_set ((A i).map (Rat.castHom ℝ))
          (fun j : Fin (m i) ↦ (b i j : ℝ))).Nonempty := by
    intro i
    simpa [rational_matrix_polyhedron] using hP_nonempty i
  have hZeroRays :
      ∀ i : Fin k,
        polyhedron_le_set ((A i).map (Rat.castHom ℝ)) 0 =
          (PointedCone.hull ℝ ((∅ : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) := by
    intro i
    calc
      polyhedron_le_set ((A i).map (Rat.castHom ℝ)) 0 = ({0} : Set (Fin n → ℝ)) := by
        simpa [rational_matrix_polyhedron] using
          homogeneousMatrixPolyhedron_eq_singleton_zero_of_rationalPolytope
            (⟨vertexCount i, vertex i, hvertex i⟩) (hP_nonempty i)
      _ = (PointedCone.hull ℝ ((∅ : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ)) := by
        symm
        have hEmptySet :
            (((∅ : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) =
              (∅ : Set (Fin n → ℝ))) := by
          ext x
          simp
        rw [hEmptySet]
        rw [pointedCone_hull_eq_cone (∅ : Set (Fin n → ℝ))]
        exact cone_empty
  have hConvexHull_union_eq_balas :
      convexHull ℝ (⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)) =
        balas_x_projection m
          (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
          (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ)) := by
    have hClosure :
        closure (convexHull ℝ (⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i))) =
          balas_x_projection m
            (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
            (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ)) := by
      simpa [rational_matrix_polyhedron] using
        closure_convexHull_iUnion_matrix_polyhedra_eq_balas_x_projection_of_all_nonempty
          m
          (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
          (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ))
          (fun _ : Fin k ↦ (∅ : Finset (Fin n → ℝ)))
          hP_nonempty_real
          hZeroRays
    rw [hConvexHull_union_closed.closure_eq] at hClosure
    exact hClosure
  calc
    convexHull ℝ ((⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)) + integral_intcone r) =
        convexHull ℝ (⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)) +
          convexHull ℝ (integral_intcone r) := by
            rw [convexHull_add]
    _ = balas_x_projection m
          (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
          (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ)) +
            convexHull ℝ (integral_intcone r) := by
              rw [hConvexHull_union_eq_balas]
    _ = balas_x_projection m
          (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
          (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ)) +
            finitely_generated_cone (fun j : Fin t ↦ fun l : Fin n ↦ (r j l : ℝ)) := by
              rw [convexHull_integral_intcone_eq_finitely_generated_cone]

/-- Corollary 4.48. If each rational system `Aᵢ x ≤ bⁱ` cuts out a nonempty rational
polytope, then the convex hull of
`(⋃ i, rational_matrix_polyhedron (A i) (b i)) + integral_intcone r` is the projection
of the lifted polyhedron defined by the inequalities in `(4.35)` onto the `x`-coordinates. -/
theorem convexHull_eq_x_projection
    {n k t : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℚ)
    (b : ∀ i : Fin k, Fin (m i) → ℚ)
    (r : Fin t → Fin n → ℤ)
    (hP_polytope : ∀ i : Fin k, (rational_matrix_polyhedron (A i) (b i)).IsRationalPolytope)
    (hP_nonempty : ∀ i : Fin k, (rational_matrix_polyhedron (A i) (b i)).Nonempty)
    :
    convexHull ℝ ((⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)) + integral_intcone r) =
      Prod.fst '' polyhedron m A b r := by
  calc
    convexHull ℝ ((⋃ i : Fin k, rational_matrix_polyhedron (A i) (b i)) + integral_intcone r) =
        balas_x_projection m
          (fun i : Fin k ↦ (A i).map (Rat.castHom ℝ))
          (fun i : Fin k ↦ fun j : Fin (m i) ↦ (b i j : ℝ)) +
          finitely_generated_cone (fun j : Fin t ↦ fun l : Fin n ↦ (r j l : ℝ)) :=
      convexHull_eq_balas_x_projection_add_cone
        m A b r hP_polytope hP_nonempty
    _ = Prod.fst '' polyhedron m A b r := by
      symm
      exact x_projection_eq_balas_x_projection_add_cone m A b r

end BalasIntegralLift
