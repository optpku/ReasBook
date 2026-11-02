import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_6.ch4_sec4_6_definition_4_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2.ch5_sec5_2_definition_5_2_extra_2

open scoped BigOperators Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: pure-integer Chvátal closures of integral TDI systems with rational
--   right-hand side
-- * sampled owner declarations: Chapter 4 `polyhedron_le_set`, `rational_matrix_polyhedron`,
--   and Chapter 4.6
--   `totally_dual_integral`, Theorem 4.27's integral-matrix TDI presentation, and Chapter 5
--   `chvatalClosure` / `mem_chvatalClosure_expanded_iff`
-- * owner abstraction: the Chapter 5 mixed-integer owner `chvatalClosure A b I`, specialized to
--   `I = Finset.univ`, with the floor-rounded system stated source-faithfully as
--   `polyhedron_le_set` and bridged to the Chapter 4 owner `rational_matrix_polyhedron`
-- * source/core/bridge triage: Exercise 5.17 is source-facing; the main theorem keeps the
--   floor-rounded inequality system, while companions expose the canonical Chapter 4 view
-- * primitive data: an integral constraint matrix `A`, a rational right-hand side `b`, and the
--   TDI hypothesis on the induced rational system
-- * derived API: the pure-integer closure, the floor-rounded polyhedron, and the canonical
--   rational-polyhedron bridge

section Exercise517

variable {m n : ℕ}

/-- Helper for Exercise 5.17: selecting a single row of an integral system gives a pure-integer
Chvátal multiplier. -/
private theorem singleRowIsChvatalMultiplier
    (A : Matrix (Fin m) (Fin n) ℤ)
    (i : Fin m) :
    IsChvatalMultiplier
      (A.map (Int.castRingHom ℝ))
      Finset.univ
      (Pi.single i (1 : ℝ)) := by
  -- Unfold the pure-integer multiplier conditions and check the selected row directly.
  rw [isChvatalMultiplier_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hk]
  · intro j _
    refine ⟨A i j, ?_⟩
    simp
  · intro j hj
    exact False.elim (hj (Finset.mem_univ j))

/-- Helper for Exercise 5.17: a primal feasible point together with a feasible dual witness gives
the finite-optimum hypothesis needed by total dual integrality. -/
private theorem rationalPrimalFiniteOfDualWitness
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    {x : Fin n → ℝ}
    {u : Fin m → ℝ}
    (hx : x ∈ polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)))
    (hu : u ∈ rational_dual_feasible_region (A.map (Int.castRingHom ℚ)) c) :
    rational_primal_has_finite_optimum (A.map (Int.castRingHom ℚ)) b c := by
  let AReal : Matrix (Fin m) (Fin n) ℝ := (A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)
  let bReal : Fin m → ℝ := fun i ↦ (b i : ℝ)
  let cReal : Fin n → ℝ := fun j ↦ (c j : ℝ)
  have hxPrimal : x ∈ primal_feasible_region AReal bReal := by
    -- Repackage the matrix polyhedron membership as primal feasibility.
    simpa [AReal, bReal, primal_feasible_region, mem_polyhedron_le_set_iff] using hx
  have huDual : u ∈ dual_feasible_region AReal cReal := by
    -- The rational dual owner is definitionally the same dual system after casting to `ℝ`.
    rcases (mem_rational_dual_feasible_region_iff.mp hu) with ⟨huRow, huNonneg⟩
    rw [mem_dual_feasible_region_iff]
    refine ⟨?_, huNonneg⟩
    simpa [AReal, cReal] using huRow
  rcases linear_programming_duality_primal_optimum_exists
      AReal bReal cReal ⟨x, hxPrimal⟩ ⟨u, huDual⟩ with
    ⟨xStar, hxStar, hxGreatest⟩
  rw [rational_primal_has_finite_optimum_iff]
  refine ⟨xStar, ?_, ?_⟩
  · -- Transport the primal optimizer back to the rational owner.
    simpa [AReal, bReal, primal_feasible_region, rational_matrix_polyhedron] using hxStar
  · -- The objective-value set is the same set after unfolding the rational owner.
    simpa [AReal, bReal, cReal, primal_objective_values, primal_feasible_region,
      rational_matrix_polyhedron] using hxGreatest

/-- Helper for Exercise 5.17: a nonnegative integral combination of coordinatewise floors is at
most the floor of the corresponding weighted sum. -/
private theorem nonnegativeIntDotProductFloor_le_floorDotProduct
    (z : Fin m → ℤ)
    (hzNonneg : ∀ i, 0 ≤ z i)
    (b : Fin m → ℚ) :
    ((∑ i, z i * Int.floor (b i) : ℤ) : ℝ) ≤
      (((Int.floor ((fun i ↦ (z i : ℝ)) ⬝ᵥ fun i ↦ (b i : ℝ))) : ℤ) : ℝ) := by
  have hsumLe :
      (((∑ i, z i * Int.floor (b i) : ℤ) : ℝ)) ≤
        (fun i ↦ (z i : ℝ)) ⬝ᵥ fun i ↦ (b i : ℝ) := by
    -- Compare the integer floor sum termwise with the original weighted sum.
    calc
      (((∑ i, z i * Int.floor (b i) : ℤ) : ℝ))
          = ∑ i, (((z i * Int.floor (b i) : ℤ) : ℝ)) := by
              simp
      _ = ∑ i, ((z i : ℝ) * ((Int.floor (b i) : ℤ) : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [Int.cast_mul]
      _ ≤ ∑ i, ((z i : ℝ) * (b i : ℝ)) := by
            refine Finset.sum_le_sum ?_
            intro i _
            exact mul_le_mul_of_nonneg_left
              (show (((Int.floor (b i) : ℤ) : ℝ) ≤ (b i : ℝ)) by
                exact_mod_cast Int.floor_le (b i))
              (show (0 : ℝ) ≤ (z i : ℝ) by exact_mod_cast hzNonneg i)
      _ = (fun i ↦ (z i : ℝ)) ⬝ᵥ fun i ↦ (b i : ℝ) := by
            rfl
  have hsInt :
      (∑ i, z i * Int.floor (b i) : ℤ) ≤
        Int.floor ((fun i ↦ (z i : ℝ)) ⬝ᵥ fun i ↦ (b i : ℝ)) := by
    -- Once the left-hand side is known to lie below the real sum, `Int.le_floor` closes it.
    exact Int.le_floor.mpr hsumLe
  exact_mod_cast hsInt

/-- Helper for Exercise 5.17: the floor-rounded system already satisfies every Chvátal inequality
of a totally dual integral presentation. -/
private theorem floorPolyhedron_subset_chvatalClosure_of_tdi
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ)
    (hTDI : totally_dual_integral (A.map (Int.castRingHom ℚ)) b)
    {x : Fin n → ℝ}
    (hx : x ∈ polyhedron_le_set
      (A.map (Int.castRingHom ℝ))
      (fun i ↦ (Int.floor (b i) : ℝ))) :
    x ∈ chvatalClosure (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) Finset.univ := by
  classical
  let AReal : Matrix (Fin m) (Fin n) ℝ := A.map (Int.castRingHom ℝ)
  let AQ : Matrix (Fin m) (Fin n) ℚ := A.map (Int.castRingHom ℚ)
  let bReal : Fin m → ℝ := fun i ↦ (b i : ℝ)
  let floorB : Fin m → ℝ := fun i ↦ (Int.floor (b i) : ℝ)
  have hfloorLe : ∀ i, floorB i ≤ bReal i := by
    intro i
    dsimp [floorB, bReal]
    exact_mod_cast Int.floor_le (b i : ℝ)
  have hxFloor : AReal *ᵥ x ≤ floorB := by
    simpa [AReal, floorB, mem_polyhedron_le_set_iff] using hx
  have hxBase : x ∈ polyhedron_le_set AReal bReal := by
    -- The floor-rounded system is a subsystem of the original one.
    rw [mem_polyhedron_le_set_iff]
    intro i
    exact (hxFloor i).trans (hfloorLe i)
  rw [mem_chvatalClosure_iff]
  refine ⟨hxBase, ?_⟩
  intro u hu
  let c : Fin n → ℤ := fun j ↦ Classical.choose (hu.exists_int (Finset.mem_univ j))
  have hcEq : (fun j ↦ (c j : ℝ)) = u ᵥ* AReal := by
    -- Record the integral objective induced by the Chvátal multiplier once.
    funext j
    exact (Classical.choose_spec (hu.exists_int (Finset.mem_univ j))).symm
  have huRat : u ∈ rational_dual_feasible_region AQ c := by
    -- The multiplier is a feasible dual point for the induced integral objective.
    rw [mem_rational_dual_feasible_region_iff]
    refine ⟨?_, fun i ↦ hu.nonneg i⟩
    simpa [AQ, AReal, c] using hcEq.symm
  have hFinite : rational_primal_has_finite_optimum AQ b c :=
    rationalPrimalFiniteOfDualWitness A b c hxBase huRat
  have hDual := hTDI c hFinite
  rw [rational_dual_has_integral_optimal_solution_iff] at hDual
  rcases hDual with ⟨yStar, hyStar, hyInt, hyLeast⟩
  rcases (mem_rational_dual_feasible_region_iff.mp hyStar) with ⟨hyRow, hyNonneg⟩
  rcases (mem_integerVectors_iff.mp hyInt) with ⟨z, hzCast⟩
  have hzEq : yStar = Int.cast ∘ z := hzCast
  have hzNonneg : ∀ i, 0 ≤ z i := by
    -- Integrality plus nonnegativity upgrades the dual optimum to an `ℤ`-valued nonnegative row.
    intro i
    have hyi : 0 ≤ yStar i := hyNonneg i
    have hzVal : yStar i = (z i : ℝ) := by
      simp [hzEq]
    rw [hzVal] at hyi
    exact_mod_cast hyi
  have hyRowEq : yStar ᵥ* AReal = u ᵥ* AReal := by
    -- Both dual points realize the same integral objective `c`.
    calc
      yStar ᵥ* AReal = (fun j ↦ (c j : ℝ)) := by
        simpa [AQ, AReal, c] using hyRow
      _ = u ᵥ* AReal := hcEq
  have hyFloorLe :
      yStar ⬝ᵥ floorB ≤
        (((Int.floor (yStar ⬝ᵥ bReal) : ℤ) : ℝ)) := by
    -- Bound the floored right-hand side by the floor of the dual optimum value.
    have hyFloorEq :
        yStar ⬝ᵥ floorB = ((∑ i, z i * Int.floor (b i) : ℤ) : ℝ) := by
      calc
        yStar ⬝ᵥ floorB = ∑ i, yStar i * floorB i := rfl
        _ = ∑ i, ((z i : ℝ) * floorB i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [floorB, hzEq]
        _ = ∑ i, (((z i * Int.floor (b i) : ℤ) : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [floorB, Int.cast_mul]
        _ = ((∑ i, z i * Int.floor (b i) : ℤ) : ℝ) := by
              simp
    have hyDotEq :
        (fun i ↦ (z i : ℝ)) ⬝ᵥ (fun i ↦ (b i : ℝ)) = yStar ⬝ᵥ bReal := by
      calc
        (fun i ↦ (z i : ℝ)) ⬝ᵥ (fun i ↦ (b i : ℝ))
            = ∑ i, (z i : ℝ) * (b i : ℝ) := rfl
        _ = ∑ i, yStar i * bReal i := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [bReal, hzEq]
        _ = yStar ⬝ᵥ bReal := rfl
    calc
      yStar ⬝ᵥ floorB = ((∑ i, z i * Int.floor (b i) : ℤ) : ℝ) := hyFloorEq
      _ ≤ (((Int.floor ((fun i ↦ (z i : ℝ)) ⬝ᵥ fun i ↦ (b i : ℝ))) : ℤ) : ℝ) :=
        nonnegativeIntDotProductFloor_le_floorDotProduct z hzNonneg b
      _ = (((Int.floor (yStar ⬝ᵥ bReal) : ℤ) : ℝ)) := by rw [hyDotEq]
  have hyOptLe : yStar ⬝ᵥ bReal ≤ u ⬝ᵥ bReal := by
    -- The integral dual optimum is least among all feasible dual points, including `u`.
    exact hyLeast.2 ⟨u, huRat, rfl⟩
  have hyFloorOptLe :
      (((Int.floor (yStar ⬝ᵥ bReal) : ℤ) : ℝ)) ≤
        (((Int.floor (u ⬝ᵥ bReal) : ℤ) : ℝ)) := by
    exact_mod_cast Int.floor_le_floor hyOptLe
  -- Compare against the integral optimal dual solution and then transfer back to `u`.
  calc
    (u ᵥ* AReal) ⬝ᵥ x = (yStar ᵥ* AReal) ⬝ᵥ x := by rw [hyRowEq]
    _ = yStar ⬝ᵥ (AReal *ᵥ x) := by rw [Matrix.dotProduct_mulVec]
    _ ≤ yStar ⬝ᵥ floorB := dotProduct_le_dotProduct_of_nonneg_left hxFloor hyNonneg
    _ ≤ (((Int.floor (yStar ⬝ᵥ bReal) : ℤ) : ℝ)) := hyFloorLe
    _ ≤ (((Int.floor (u ⬝ᵥ bReal) : ℤ) : ℝ)) := hyFloorOptLe

/-- Exercise 5.17. Let `P = {x ∈ ℝ^n | A x ≤ b}` where `A x ≤ b` is a totally dual integral
system with integral matrix `A`, and let `S = P ∩ ℤ^n`. Then the pure-integer Chvátal closure of
this system is exactly `{x ∈ ℝ^n | A x ≤ ⌊b⌋}`. -/
theorem exercise_5_17_chvatalClosure_eq_floor_polyhedron
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ)
    (hTDI : totally_dual_integral (A.map (Int.castRingHom ℚ)) b) :
    chvatalClosure (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) Finset.univ =
      polyhedron_le_set
        (A.map (Int.castRingHom ℝ))
        (fun i ↦ (Int.floor (b i) : ℝ)) := by
  ext x
  constructor
  · intro hx
    rw [mem_chvatalClosure_iff] at hx
    rw [mem_polyhedron_le_set_iff]
    intro i
    have hRowCut := hx.2 (Pi.single i (1 : ℝ)) (singleRowIsChvatalMultiplier A i)
    -- The unit row multiplier recovers exactly the floored `i`th row inequality.
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using hRowCut
  · intro hx
    -- Route correction: use total dual integrality to prove every Chvátal inequality on the
    -- floor-rounded system instead of rebuilding the closure through the generic integer hull.
    exact floorPolyhedron_subset_chvatalClosure_of_tdi A b hTDI hx

/-- The floor-rounded polyhedron from Exercise 5.17 is canonically the Chapter 4 owner
`rational_matrix_polyhedron` on the integral matrix `A` and the floored right-hand side `⌊b⌋`. -/
theorem exercise_5_17_chvatalClosure_eq_floor_rational_matrix_polyhedron
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ)
    (hTDI : totally_dual_integral (A.map (Int.castRingHom ℚ)) b) :
    chvatalClosure (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) Finset.univ =
      rational_matrix_polyhedron
        (A.map (Int.castRingHom ℚ))
        (fun i ↦ (Int.floor (b i) : ℚ)) := by
  simpa [rational_matrix_polyhedron] using
    exercise_5_17_chvatalClosure_eq_floor_polyhedron A b hTDI

/-- A point lies in the Exercise 5.17 pure-integer Chvátal closure exactly when it satisfies the
floor-rounded system `A x ≤ ⌊b⌋`. -/
theorem mem_exercise_5_17_chvatalClosure_iff
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ)
    (hTDI : totally_dual_integral (A.map (Int.castRingHom ℚ)) b)
    (x : Fin n → ℝ) :
    x ∈ chvatalClosure (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) Finset.univ ↔
      (A.map (Int.castRingHom ℝ)) *ᵥ x ≤ fun i ↦ (Int.floor (b i) : ℝ) := by
  rw [exercise_5_17_chvatalClosure_eq_floor_polyhedron A b hTDI, mem_polyhedron_le_set_iff]

end Exercise517
