import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_6.ch4_sec4_6_definition_4_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: totally dual integral descriptions of rational polyhedra
-- * sampled owner declarations: Chapter 4.1 `rational_matrix_polyhedron`, `is_integral`, and
--   `ℤ^m`, plus Chapter 4.6 `totally_dual_integral`
-- * owner abstraction: the Chapter 4.6 owner `totally_dual_integral A b` on the Chapter 4.1
--   rational-system owner `rational_matrix_polyhedron A b`
-- * source/core/bridge triage: Theorem 4.26 is source-facing and should use the primitive
--   integral right-hand side data `b : Fin m → ℤ`; the cast `Int.cast ∘ b` is the canonical
--   bridge into the Chapter 4.6 owner, while membership in `ℤ^m` is derived API from
--   `mem_integerVectors_iff`
-- * primitive data: a rational matrix presentation and an integral right-hand side
-- * derived API: the induced rational polyhedron and its integrality

section Theorem426

variable {m n : ℕ}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_26.lean`: a polyhedron
presented by a rational matrix and rational right-hand side is rational. -/
private lemma rationalMatrixPolyhedronIsRational
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    is_rational_polyhedron (rational_matrix_polyhedron A b) := by
  -- Use the displayed matrix and right-hand side as the required rational presentation.
  rw [is_rational_polyhedron_iff]
  exact ⟨m, A, b, rfl⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_26.lean`: attained primal
and dual optima for the same feasible pair have the same value. -/
private lemma primalDualOptimalValuesEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    {p d : ℝ}
    (hp : IsGreatest (primal_objective_values A b c) p)
    (hd : IsLeast (dual_objective_values A b c) d) :
    p = d := by
  -- Attainment supplies the nonemptiness hypotheses required by strong duality.
  have hPrimalNonempty : Set.Nonempty (primal_feasible_region A b) := by
    rcases hp.1 with ⟨x, hx, hxp⟩
    exact ⟨x, hx⟩
  have hDualNonempty : Set.Nonempty (dual_feasible_region A c) := by
    rcases hd.1 with ⟨y, hy, hyd⟩
    exact ⟨y, hy⟩
  have hOptimalValues :=
    linear_programming_duality_optimal_value_eq A b c hPrimalNonempty hDualNonempty
  -- Replace each attained value by the corresponding supremum or infimum.
  calc
    p = sSup (primal_objective_values A b c) := hp.csSup_eq.symm
    _ = sInf (dual_objective_values A b c) := hOptimalValues
    _ = d := hd.csInf_eq

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_26.lean`: the dot product
of two integer-valued real vectors is the real cast of an integer. -/
private lemma integerVectorDotProductIsInteger
    {x y : Fin n → ℝ}
    (hx : x ∈ integerVectors n)
    (hy : y ∈ integerVectors n) :
    ∃ k : ℤ, x ⬝ᵥ y = (k : ℝ) := by
  -- Choose integer representatives coordinatewise and sum their integer products.
  rcases mem_integerVectors_iff.mp hx with ⟨a, rfl⟩
  rcases mem_integerVectors_iff.mp hy with ⟨b, rfl⟩
  refine ⟨∑ i, a i * b i, ?_⟩
  simp [dotProduct, Function.comp_apply]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_26.lean
(Theorem 4.26).
Let `A x ≤ b` be a totally dual integral system and let `b` be an integral vector. Then
`P := {x : A x ≤ b}` is an integral polyhedron. -/
theorem totally_dual_integral_rational_matrix_polyhedron_is_integral
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℤ)
    (hTDI : totally_dual_integral A (Int.cast ∘ b)) :
    is_integral (rational_matrix_polyhedron A (Int.cast ∘ b)) := by
  -- Theorem 4.1 reduces integrality to proving that every attained integral-objective
  -- maximum is an integer.
  have hRational :
      is_rational_polyhedron (rational_matrix_polyhedron A (Int.cast ∘ b)) :=
    rationalMatrixPolyhedronIsRational A (Int.cast ∘ b)
  rw [rational_polyhedron_is_integral_iff_integral_linear_maxima_are_integer
    (rational_matrix_polyhedron A (Int.cast ∘ b)) hRational]
  intro c z hzGreatest
  rcases hzGreatest.1 with ⟨xStar, hxStar, hxStarValue⟩
  have hPrimalFinite : rational_primal_has_finite_optimum A (Int.cast ∘ b) c := by
    rw [rational_primal_has_finite_optimum_iff]
    refine ⟨xStar, hxStar, ?_⟩
    -- The supplied maximum is attained at the extracted feasible point.
    simpa only [Function.comp_apply, ← hxStarValue] using hzGreatest
  have hDual := hTDI c hPrimalFinite
  rw [rational_dual_has_integral_optimal_solution_iff] at hDual
  rcases hDual with ⟨yStar, hyStar, hyStarInteger, hyStarLeast⟩
  let AReal : Matrix (Fin m) (Fin n) ℝ := A.map (Rat.castHom ℝ)
  let bReal : Fin m → ℝ := fun i ↦ (((Int.cast ∘ b) i : ℚ) : ℝ)
  let cReal : Fin n → ℝ := Int.cast ∘ c
  have hzCanonical : IsGreatest (primal_objective_values AReal bReal cReal) z := by
    -- Normalize the rational presentation to the Chapter 3 primal feasible-region owner.
    simpa [AReal, bReal, cReal, primal_objective_values, primal_feasible_region,
      rational_matrix_polyhedron, polyhedron_le_set, Function.comp_apply] using hzGreatest
  have hyCanonical :
      IsLeast (dual_objective_values AReal bReal cReal) (yStar ⬝ᵥ bReal) := by
    -- Normalize the rational dual data to the Chapter 3 dual feasible-region owner.
    simpa [AReal, bReal, cReal, dual_objective_values, dual_feasible_region,
      rational_dual_feasible_region, Function.comp_apply] using hyStarLeast
  have hzDual : z = yStar ⬝ᵥ bReal :=
    primalDualOptimalValuesEq AReal bReal cReal hzCanonical hyCanonical
  have hbInteger : bReal ∈ integerVectors m := by
    -- The twice-cast rational right-hand side is still the original integral vector.
    rw [mem_integerVectors_iff]
    refine ⟨b, ?_⟩
    funext i
    simp [bReal, Function.comp_apply]
  rcases integerVectorDotProductIsInteger hyStarInteger hbInteger with ⟨k, hk⟩
  -- Strong duality identifies the primal maximum with this integral dot product.
  exact ⟨k, hzDual.trans hk⟩

end Theorem426

#print axioms totally_dual_integral_rational_matrix_polyhedron_is_integral
