import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic Lean search was unavailable in this session; this item uses the
-- standard ideal-span formulation of relative primality in `ℤ`.

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_20.lean: a Bézout relation
for the coefficients produces an integer point on every translated hyperplane
with the same normal vector. -/
theorem integer_points_on_hyperplane_of_bezout
    {n : ℕ} (a : Fin n → ℤ)
    (hbezout : ∃ u : Fin n → ℤ, Finset.univ.sum (fun i => a i * u i) = 1)
    (b : ℤ) :
    ∃ x : Fin n → ℤ, Finset.univ.sum (fun i => a i * x i) = b := by
  -- Scale the Bézout coefficients by the desired right-hand side.
  obtain ⟨u, hu⟩ := hbezout
  refine ⟨fun i ↦ u i * b, ?_⟩
  -- Associativity and distributivity turn the scaled sum into `1 * b`.
  calc
    Finset.univ.sum (fun i => a i * (u i * b)) =
        Finset.univ.sum (fun i => (a i * u i) * b) := by
      simp only [mul_assoc]
    _ = (Finset.univ.sum (fun i => a i * u i)) * b := by
      rw [Finset.sum_mul]
    _ = b := by rw [hu, one_mul]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_20.lean. Exercise 1.20.
If integers `a₁, ..., aₙ` are relatively prime, then for every `b : ℤ` the
hyperplane `a₁ x₁ + ... + aₙ xₙ = b` contains an integer point. Here relative
primality is expressed by the condition that the coefficients generate the unit
ideal in `ℤ`. -/
theorem integer_points_on_coprime_hyperplane
    {n : ℕ} (hn : 0 < n) (a : Fin n → ℤ)
    (hcoprime : (Ideal.span (Set.range a) : Ideal ℤ) = ⊤)
    (b : ℤ) :
    ∃ x : Fin n → ℤ, Finset.univ.sum (fun i => a i * x i) = b := by
  -- The positive dimension supplies an index, as required by the exercise's setup.
  cases Fin.pos_iff_nonempty.mp hn
  -- Unit-ideal generation says in particular that `1` lies in the span.
  have hone : (1 : ℤ) ∈ Ideal.span (Set.range a) := by
    rw [hcoprime]
    exact Submodule.mem_top
  -- The finite span characterization supplies Bézout coefficients.
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  refine integer_points_on_hyperplane_of_bezout a ?_ b
  -- Commute the products to match the coefficient order of the companion theorem.
  refine ⟨u, ?_⟩
  simpa only [mul_comm] using hu

#print axioms integer_points_on_coprime_hyperplane
