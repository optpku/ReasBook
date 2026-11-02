import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2.ch5_sec5_2_definition_5_2_extra_2

open scoped Matrix

section Exercise516

variable {m n : ℕ}

/-- A restricted Chvátal multiplier is an admissible multiplier from the mixed-integer Chvátal
system with the additional pointwise strict bound `u_i < 1`. -/
def IsRestrictedChvatalMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (I : Finset (Fin n))
    (u : Fin m → ℝ) : Prop :=
  IsChvatalMultiplier A I u ∧ ∀ i : Fin m, u i < 1

namespace IsRestrictedChvatalMultiplier

/-- A restricted Chvátal multiplier is in particular a Chvátal multiplier. -/
theorem isChvatalMultiplier
    {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Finset (Fin n)}
    {u : Fin m → ℝ}
    (hu : IsRestrictedChvatalMultiplier A I u) :
    IsChvatalMultiplier A I u :=
  hu.1

/-- Every coordinate of a restricted Chvátal multiplier is strictly less than `1`. -/
theorem lt_one
    {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Finset (Fin n)}
    {u : Fin m → ℝ}
    (hu : IsRestrictedChvatalMultiplier A I u) (i : Fin m) :
    u i < 1 :=
  hu.2 i

end IsRestrictedChvatalMultiplier

/-- `IsRestrictedChvatalMultiplier A I u` means that `u` is a Chvátal multiplier and each
coordinate also satisfies the strict bound `u_i < 1`. -/
theorem isRestrictedChvatalMultiplier_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (I : Finset (Fin n))
    (u : Fin m → ℝ) :
    IsRestrictedChvatalMultiplier A I u ↔
      IsChvatalMultiplier A I u ∧
        ∀ i : Fin m, u i < 1 :=
  Iff.rfl

/-- Expanded companion form of `IsRestrictedChvatalMultiplier`, exposing the underlying
Chvátal-multiplier conditions together with the extra strict bound. -/
theorem isRestrictedChvatalMultiplier_expanded_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (I : Finset (Fin n))
    (u : Fin m → ℝ) :
    IsRestrictedChvatalMultiplier A I u ↔
      (∀ i : Fin m, 0 ≤ u i) ∧
        (∀ i : Fin m, u i < 1) ∧
          (∀ j : Fin n, j ∈ I → ∃ z : ℤ, (u ᵥ* A) j = (z : ℝ)) ∧
            ∀ j : Fin n, j ∉ I → (u ᵥ* A) j = 0 := by
  constructor
  · rintro ⟨hu, hu_lt_one⟩
    rcases (isChvatalMultiplier_iff A I u).1 hu with ⟨hu_nonneg, hu_int, hu_zero⟩
    exact ⟨hu_nonneg, hu_lt_one, hu_int, hu_zero⟩
  · rintro ⟨hu_nonneg, hu_lt_one, hu_int, hu_zero⟩
    exact ⟨(isChvatalMultiplier_iff A I u).2 ⟨hu_nonneg, hu_int, hu_zero⟩, hu_lt_one⟩

/-- The intersection of `P = {x : ℝ^n | A x ≤ b}` with all restricted Chvátal inequalities
defined by admissible multipliers `u` satisfying `u_i < 1` for every row index `i`. -/
def restrictedChvatalIntersection
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ |
    x ∈ polyhedron_le_set A b ∧
      ∀ u : Fin m → ℝ,
        IsRestrictedChvatalMultiplier A I u →
          (u ᵥ* A) ⬝ᵥ x ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ)}

/-- Membership in `restrictedChvatalIntersection A b I` means belonging to the original
polyhedron and satisfying every restricted Chvátal inequality. -/
theorem mem_restrictedChvatalIntersection_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (x : Fin n → ℝ) :
    x ∈ restrictedChvatalIntersection A b I ↔
      x ∈ polyhedron_le_set A b ∧
        ∀ u : Fin m → ℝ,
          IsRestrictedChvatalMultiplier A I u →
            (u ᵥ* A) ⬝ᵥ x ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ) :=
  Iff.rfl

/-- Expanded companion form of `mem_restrictedChvatalIntersection_iff`, exposing the
underlying Chvátal-multiplier conditions together with the extra bound `u_i < 1`. -/
theorem mem_restrictedChvatalIntersection_expanded_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (x : Fin n → ℝ) :
    x ∈ restrictedChvatalIntersection A b I ↔
      x ∈ polyhedron_le_set A b ∧
        ∀ u : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ u i) →
          (∀ i : Fin m, u i < 1) →
          (∀ j : Fin n, j ∈ I → ∃ z : ℤ, (u ᵥ* A) j = (z : ℝ)) →
          (∀ j : Fin n, j ∉ I → (u ᵥ* A) j = 0) →
          (u ᵥ* A) ⬝ᵥ x ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ) := by
  simp [restrictedChvatalIntersection, isRestrictedChvatalMultiplier_expanded_iff]

/-- The mixed-integer Chvátal closure is contained in the intersection obtained by restricting
to multipliers with `u_i < 1`, since every restricted multiplier is still admissible. -/
theorem chvatalClosure_subset_restrictedChvatalIntersection
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n)) :
    chvatalClosure A b I ⊆ restrictedChvatalIntersection A b I := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro u hu
  exact hx.2 u hu.isChvatalMultiplier

/-- The restricted Chvátal intersection is contained in the original polyhedron. -/
theorem restrictedChvatalIntersection_subset_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n)) :
    restrictedChvatalIntersection A b I ⊆ polyhedron_le_set A b := fun _ hx ↦ hx.1

/-- On a rational system `A x ≤ b`, the real restricted Chvátal intersection is exactly the
original rational polyhedron together with all restricted Chvátal inequalities. -/
theorem mem_restrictedChvatalIntersection_rat_iff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (I : Finset (Fin n))
    (x : Fin n → ℝ) :
    x ∈ restrictedChvatalIntersection (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) I ↔
      x ∈ rational_matrix_polyhedron A b ∧
        ∀ u : Fin m → ℝ,
          IsRestrictedChvatalMultiplier (A.map (Rat.castHom ℝ)) I u →
            (u ᵥ* (A.map (Rat.castHom ℝ))) ⬝ᵥ x ≤
              ((⌊u ⬝ᵥ fun i ↦ (b i : ℝ)⌋ : ℤ) : ℝ) := by
  simp [restrictedChvatalIntersection, rational_matrix_polyhedron]

/-- Helper for Exercise 5.16: for the `1 × 1` matrix `[1]`, the row product `(u ᵥ* A) 0`
reduces to the unique multiplier coordinate `u 0`. -/
private lemma exercise516CounterexampleVecMul_apply
    (u : Fin 1 → ℝ) :
    (u ᵥ* ![![(1 : ℝ)]]) 0 = u 0 := by
  -- Normalize the unique summand in the `1 × 1` row product.
  simp [Matrix.vecMul, dotProduct]

/-- Helper for Exercise 5.16: every restricted multiplier for the one-row system `x ≤ 1 / 2`
must vanish, because its unique coordinate is an integer in the interval `[0, 1)`. -/
private lemma exercise516RestrictedMultiplier_eq_zero
    (u : Fin 1 → ℝ)
    (hu : IsRestrictedChvatalMultiplier ![![(1 : ℝ)]] Finset.univ u) :
    u 0 = 0 := by
  have hzero_mem : (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1)) := by
    simp
  rcases
      (isRestrictedChvatalMultiplier_expanded_iff ![![(1 : ℝ)]] Finset.univ u).1 hu with
    ⟨hu_nonneg, hu_lt_one, hu_int, _⟩
  rcases hu_int 0 hzero_mem with ⟨z, hz⟩
  have hu0_eq_z : u 0 = (z : ℝ) := by
    simpa [exercise516CounterexampleVecMul_apply] using hz
  -- Convert the real inequalities on `u 0` into integer bounds on `z`.
  have hz_nonneg : 0 ≤ z := by
    have h : 0 ≤ (z : ℝ) := by
      simpa [hu0_eq_z] using hu_nonneg 0
    exact_mod_cast h
  have hz_lt_one : z < 1 := by
    have h : (z : ℝ) < 1 := by
      simpa [hu0_eq_z] using hu_lt_one 0
    exact_mod_cast h
  -- An integer lying in `[0, 1)` can only be `0`.
  have hz_zero : z = 0 := by
    omega
  calc
    u 0 = (u ᵥ* ![![(1 : ℝ)]]) 0 := by
      symm
      exact exercise516CounterexampleVecMul_apply u
    _ = (z : ℝ) := hz
    _ = 0 := by
      simp [hz_zero]

/-- Helper for Exercise 5.16: the witness `x = 1 / 2` belongs to the restricted Chvátal
intersection for the one-row system `x ≤ 1 / 2`, because every restricted multiplier is zero. -/
private lemma exercise516Witness_mem_restrictedChvatalIntersection :
    (fun _ : Fin 1 ↦ ((1 : ℚ) / 2 : ℝ)) ∈
      restrictedChvatalIntersection
        ![![(1 : ℝ)]]
        (fun _ : Fin 1 ↦ ((1 : ℚ) / 2 : ℝ))
        Finset.univ := by
  rw [mem_restrictedChvatalIntersection_iff]
  constructor
  · -- First verify that the witness lies in the original polyhedron `x ≤ 1 / 2`.
    rw [mem_polyhedron_le_set_iff]
    intro i
    fin_cases i
    norm_num [Matrix.mulVec, dotProduct]
  · intro u hu
    -- Every restricted multiplier collapses to the zero multiplier in this example.
    have hu_zero : u 0 = 0 := exercise516RestrictedMultiplier_eq_zero u hu
    simp [Matrix.vecMul, dotProduct, hu_zero]

/-- Helper for Exercise 5.16: the unrestricted multiplier `u = 1` yields the cut `x ≤ 0`, so
the witness `x = 1 / 2` is not in the full Chvátal closure of the same one-row system. -/
private lemma exercise516Witness_not_mem_chvatalClosure :
    (fun _ : Fin 1 ↦ ((1 : ℚ) / 2 : ℝ)) ∉
      chvatalClosure
        ![![(1 : ℝ)]]
        (fun _ : Fin 1 ↦ ((1 : ℚ) / 2 : ℝ))
        Finset.univ := by
  intro hx
  rw [mem_chvatalClosure_iff] at hx
  -- The constant multiplier `u = 1` is admissible for the unrestricted closure.
  have hu_one : IsChvatalMultiplier ![![(1 : ℝ)]] Finset.univ (fun _ : Fin 1 ↦ (1 : ℝ)) := by
    rw [isChvatalMultiplier_iff]
    constructor
    · intro i
      fin_cases i
      norm_num
    constructor
    · intro j hj
      refine ⟨1, ?_⟩
      fin_cases j
      simp [Matrix.vecMul, dotProduct]
    · intro j hj
      fin_cases j
      simp at hj
  have hcut := hx.2 (fun _ : Fin 1 ↦ (1 : ℝ)) hu_one
  -- The resulting Chvátal inequality simplifies to the contradiction `1 / 2 ≤ 0`.
  norm_num [Matrix.vecMul, dotProduct] at hcut

/-- Exercise 5.16. The statement is false: there exists a rational polyhedron
`P = {x : ℝ^n | A x ≤ b}` and a mixed-integer set `S = P ∩ (ℤ^I × ℝ^C)` for which the Chvátal
closure `P^Ch` is not the intersection of `P` with all restricted Chvátal inequalities, where
"restricted" means that the Chvátal multipliers satisfy `u_i < 1` for every row index `i`. -/
theorem exists_counterexample_to_chvatalClosure_eq_restrictedChvatalIntersection :
    ∃ m n : ℕ,
      ∃ A : Matrix (Fin m) (Fin n) ℚ,
      ∃ b : Fin m → ℚ,
      ∃ I : Finset (Fin n),
        chvatalClosure (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) I ≠
          restrictedChvatalIntersection (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) I := by
  -- Use the one-dimensional rational system `x ≤ 1 / 2` as the counterexample.
  let A : Matrix (Fin 1) (Fin 1) ℚ := ![![(1 : ℚ)]]
  let b : Fin 1 → ℚ := fun _ ↦ (1 : ℚ) / 2
  have hA :
      A.map (Rat.castHom ℝ) = ![![(1 : ℝ)]] := by
    -- The chosen rational matrix becomes the real `1 × 1` matrix `[1]` after coercion.
    ext i j
    fin_cases i
    fin_cases j
    simp [A]
  have hb :
      (fun i ↦ (b i : ℝ)) = (fun _ : Fin 1 ↦ ((1 : ℚ) / 2 : ℝ)) := by
    -- The right-hand side is the constant vector with unique entry `1 / 2`.
    funext i
    fin_cases i
    simp [b]
  refine ⟨1, 1, A, b, Finset.univ, ?_⟩
  have hwitness_mem_restricted :
      (fun _ : Fin 1 ↦ ((1 : ℚ) / 2 : ℝ)) ∈
        restrictedChvatalIntersection
          (A.map (Rat.castHom ℝ))
          (fun i ↦ (b i : ℝ))
          Finset.univ := by
    -- The witness survives every restricted cut because the restricted multipliers are zero.
    rw [hA, hb]
    exact exercise516Witness_mem_restrictedChvatalIntersection
  have hwitness_not_mem_closure :
      (fun _ : Fin 1 ↦ ((1 : ℚ) / 2 : ℝ)) ∉
        chvatalClosure
          (A.map (Rat.castHom ℝ))
          (fun i ↦ (b i : ℝ))
          Finset.univ := by
    -- The unrestricted multiplier `u = 1` cuts off the same witness from the closure.
    rw [hA, hb]
    exact exercise516Witness_not_mem_chvatalClosure
  intro hEq
  have hwitness_mem_closure :
      (fun _ : Fin 1 ↦ ((1 : ℚ) / 2 : ℝ)) ∈
        chvatalClosure
          (A.map (Rat.castHom ℝ))
          (fun i ↦ (b i : ℝ))
          Finset.univ := by
    -- Equality of the two sets would force the witness into the Chvátal closure.
    rw [hEq]
    exact hwitness_mem_restricted
  exact hwitness_not_mem_closure hwitness_mem_closure

end Exercise516
