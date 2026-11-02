import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

open scoped Matrix

section Definition_4_6_extra_1

variable {m n : ℕ}

/-- Definition 4.6-extra-1. The dual feasible region of the rational system `A x ≤ b` for an
integral objective vector `c`, viewed in `ℝ^m`. -/
def rational_dual_feasible_region
    (A : Matrix (Fin m) (Fin n) ℚ) (c : Fin n → ℤ) : Set (Fin m → ℝ) :=
  {y | y ᵥ* (A.map (Rat.castHom ℝ)) = (fun j ↦ (c j : ℝ)) ∧ 0 ≤ y}

/-- Membership in the rational dual feasible region is exactly the system
`y A = c, y ≥ 0` after casting to `ℝ`. -/
theorem mem_rational_dual_feasible_region_iff
    {A : Matrix (Fin m) (Fin n) ℚ} {c : Fin n → ℤ} {y : Fin m → ℝ} :
    y ∈ rational_dual_feasible_region A c ↔
      y ᵥ* (A.map (Rat.castHom ℝ)) = (fun j ↦ (c j : ℝ)) ∧ 0 ≤ y :=
  Iff.rfl

/-- Definition 4.6-extra-1. The primal linear program `max {c x : A x ≤ b}` has a finite optimum
when some feasible point attains the greatest objective value. -/
def rational_primal_has_finite_optimum
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℤ) : Prop :=
  ∃ xStar ∈ rational_matrix_polyhedron A b,
    IsGreatest
      ((fun x : Fin n → ℝ ↦ (fun j ↦ (c j : ℝ)) ⬝ᵥ x) ''
        rational_matrix_polyhedron A b)
      ((fun j ↦ (c j : ℝ)) ⬝ᵥ xStar)

/-- Unfolding characterization of the existence of a finite primal optimum. -/
theorem rational_primal_has_finite_optimum_iff
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℤ) :
    rational_primal_has_finite_optimum A b c ↔
      ∃ xStar ∈ rational_matrix_polyhedron A b,
        IsGreatest
          ((fun x : Fin n → ℝ ↦ (fun j ↦ (c j : ℝ)) ⬝ᵥ x) ''
            rational_matrix_polyhedron A b)
          ((fun j ↦ (c j : ℝ)) ⬝ᵥ xStar) :=
  Iff.rfl

/-- Definition 4.6-extra-1. The dual linear program `min {y b : y A = c, y ≥ 0}` admits an
integral optimal solution when some feasible dual point in `integerVectors m` attains the least
dual objective value. -/
def rational_dual_has_integral_optimal_solution
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℤ) : Prop :=
  ∃ yStar ∈ rational_dual_feasible_region A c,
    yStar ∈ integerVectors m ∧
      IsLeast
        ((fun y : Fin m → ℝ ↦ y ⬝ᵥ fun i ↦ (b i : ℝ)) ''
          rational_dual_feasible_region A c)
        (yStar ⬝ᵥ fun i ↦ (b i : ℝ))

/-- Unfolding characterization of the existence of an integral dual optimal solution. -/
theorem rational_dual_has_integral_optimal_solution_iff
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℤ) :
    rational_dual_has_integral_optimal_solution A b c ↔
      ∃ yStar ∈ rational_dual_feasible_region A c,
        yStar ∈ integerVectors m ∧
          IsLeast
            ((fun y : Fin m → ℝ ↦ y ⬝ᵥ fun i ↦ (b i : ℝ)) ''
              rational_dual_feasible_region A c)
            (yStar ⬝ᵥ fun i ↦ (b i : ℝ)) :=
  Iff.rfl

/-- Definition 4.6-extra-1. A rational system `A x ≤ b` is totally dual integral if every
integral objective vector with finite primal optimum has an integral optimal dual solution. -/
def totally_dual_integral
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) : Prop :=
  ∀ c : Fin n → ℤ,
    rational_primal_has_finite_optimum A b c →
      rational_dual_has_integral_optimal_solution A b c

/-- Unfolding characterization of `totally_dual_integral`. -/
theorem totally_dual_integral_iff
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    totally_dual_integral A b ↔
      ∀ c : Fin n → ℤ,
        rational_primal_has_finite_optimum A b c →
          rational_dual_has_integral_optimal_solution A b c :=
  Iff.rfl

end Definition_4_6_extra_1
