/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_proposition_3_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1

open scoped Matrix

section Lemma515

variable {n : ℕ}

/-- Helper for Lemma 5.15: the common denominator of a rational vector is nonzero. -/
lemma rationalVectorCommonDenominator_ne_zero
    {k : ℕ} (v : Fin k → ℚ) :
    rational_vector_common_denominator v ≠ 0 := by
  -- Every coordinate denominator is positive, so their least common multiple is nonzero.
  have hden :
      ∀ i ∈ (Finset.univ : Finset (Fin k)), (v i).den ≠ 0 := by
    intro i hi
    exact Nat.ne_of_gt (Rat.den_pos (v i))
  rw [rational_vector_common_denominator]
  exact Finset.lcm_ne_zero_iff.2 hden

/-- Helper for Lemma 5.15: clearing denominators in a rational vector agrees with scaling by the
common denominator after casting to `ℝ`. -/
lemma commonDenominatorScaledVector_eq_smul_real
    {k : ℕ} (v : Fin k → ℚ) :
    (fun i ↦ (common_denominator_scaled_vector v i : ℝ)) =
      (rational_vector_common_denominator v : ℝ) • (fun i ↦ (v i : ℝ)) := by
  ext i
  change ((common_denominator_scaled_vector v i : ℤ) : ℝ) =
      (rational_vector_common_denominator v : ℝ) * (v i : ℝ)
  have hi :
      ((common_denominator_scaled_vector v i : ℤ) : ℚ) =
        (rational_vector_common_denominator v : ℚ) * v i := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      congrFun (common_denominator_scaled_vector_eq_smul v) i
  -- Cast the rational identity to `ℝ`.
  exact_mod_cast hi

/-- Helper for Lemma 5.15: clearing denominators raywise preserves the finitely generated real
cone. -/
lemma commonDenominatorScaledRays_eq_finitely_generated_cone
    {k q : ℕ} (r : Fin q → Fin k → ℚ) :
    finitely_generated_cone
        (fun j : Fin q ↦ fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) =
      finitely_generated_cone
        (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, hrepr⟩
    have hD_nonneg :
        ∀ j : Fin q, 0 ≤ (rational_vector_common_denominator (r j) : ℝ) := by
      intro j
      exact_mod_cast Nat.zero_le (rational_vector_common_denominator (r j))
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j * (rational_vector_common_denominator (r j) : ℝ), ?_, ?_⟩
    · -- Multiplying by a nonnegative common denominator preserves cone coefficients.
      intro j
      exact mul_nonneg (hμ_nonneg j) (hD_nonneg j)
    · -- Rewrite each cleared ray as the corresponding rational ray scaled by its denominator.
      calc
        x = ∑ j : Fin q, μ j • (fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) :=
              hrepr
        _ = ∑ j : Fin q,
              (μ j * (rational_vector_common_denominator (r j) : ℝ)) •
                (fun i : Fin k ↦ (r j i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [commonDenominatorScaledVector_eq_smul_real (v := r j), smul_smul]
  · intro x hx
    rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, hrepr⟩
    have hD_nonneg :
        ∀ j : Fin q, 0 ≤ (rational_vector_common_denominator (r j) : ℝ) := by
      intro j
      exact_mod_cast Nat.zero_le (rational_vector_common_denominator (r j))
    have hD_ne_zero :
        ∀ j : Fin q, (rational_vector_common_denominator (r j) : ℝ) ≠ 0 := by
      intro j
      exact_mod_cast rationalVectorCommonDenominator_ne_zero (v := r j)
    refine (mem_finitely_generated_cone_iff).2 ?_
    refine ⟨fun j ↦ μ j / (rational_vector_common_denominator (r j) : ℝ), ?_, ?_⟩
    · -- Dividing by a positive common denominator keeps coefficients nonnegative.
      intro j
      exact div_nonneg (hμ_nonneg j) (hD_nonneg j)
    · -- Undo denominator clearing by dividing each coefficient by the same positive scalar.
      calc
        x = ∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ)) := hrepr
        _ = ∑ j : Fin q,
              (μ j / (rational_vector_common_denominator (r j) : ℝ)) •
                (fun i : Fin k ↦ ((common_denominator_scaled_vector (r j)) i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [commonDenominatorScaledVector_eq_smul_real (v := r j), smul_smul,
                div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (hD_ne_zero j), mul_one]

/-- Helper for Lemma 5.15: a nonempty rational polyhedron has finitely many integral recession
generators after clearing denominators once. -/
lemma existsIntegralRecessionGeneratorsOfRationalPolyhedron
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P) :
    ∃ q : ℕ, ∃ rays : Fin q → Fin n → ℤ,
      recessionCone P =
        finitely_generated_cone (fun j : Fin q ↦ fun i : Fin n ↦ (rays j i : ℝ)) := by
  rcases hP_rational with ⟨m, A, b, hP_eq⟩
  rcases exists_rational_matrix_cone_of_rational_matrix_polyhedral_cone A with ⟨q, R, hR⟩
  let raysQ : Fin q → Fin n → ℚ := fun j i ↦ R i j
  let raysInt : Fin q → Fin n → ℤ := fun j ↦ common_denominator_scaled_vector (raysQ j)
  refine ⟨q, raysInt, ?_⟩
  have hrec_hom :
      recessionCone P = {r : Fin n → ℝ | (A.map (Rat.castHom ℝ)) *ᵥ r ≤ 0} := by
    -- Normalize the recession cone to the homogeneous linear system of the rational presentation.
    rw [hP_eq]
    exact
      polyhedron_recessionCone_eq_homogeneous_solution_set
        (A.map (Rat.castHom ℝ))
        (fun i ↦ (b i : ℝ))
        (by simpa [hP_eq] using hP_nonempty)
  -- Rewrite the homogeneous cone as a rational matrix cone and then clear denominators raywise.
  calc
    recessionCone P = matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) := by
      simpa [matrix_polyhedral_cone] using hrec_hom
    _ = (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin n → ℝ)) := hR
    _ = finitely_generated_cone (fun j : Fin q ↦ fun i : Fin n ↦ (raysQ j i : ℝ)) := by
          simpa [raysQ] using
            (finitely_generated_cone_eq_matrix_cone
              (fun j : Fin q ↦ fun i : Fin n ↦ (raysQ j i : ℝ))).symm
    _ = finitely_generated_cone (fun j : Fin q ↦ fun i : Fin n ↦ (raysInt j i : ℝ)) := by
          simpa [raysInt, raysQ] using
            (commonDenominatorScaledRays_eq_finitely_generated_cone (r := raysQ)).symm

/-- Helper for Lemma 5.15: the linear span of a finitely generated cone is already the span of its
listed generators. -/
lemma span_finitelyGeneratedCone_eq_span_range
    {q : ℕ} (rays : Fin q → Fin n → ℝ) :
    Submodule.span ℝ (finitely_generated_cone rays) = Submodule.span ℝ (Set.range rays) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    rcases mem_finitely_generated_cone_iff.mp hx with ⟨μ, -, rfl⟩
    -- Expand a cone element as a finite nonnegative combination of the listed generators.
    exact
      Submodule.sum_mem (Submodule.span ℝ (Set.range rays))
        (fun j _ ↦
          Submodule.smul_mem _ _ <|
            Submodule.subset_span ⟨j, rfl⟩)
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨j, rfl⟩
    -- Each listed generator is itself a one-term element of the finitely generated cone.
    exact Submodule.subset_span <|
      mem_finitely_generated_cone_iff.mpr <|
        ⟨Pi.single j 1, by
          intro t
          by_cases ht : t = j
          · subst ht
            simp
          · simp [Pi.single, ht], by
          ext i
          rw [Finset.sum_eq_single j]
          · simp [Pi.single]
          · intro t _ ht
            simp [Pi.single, ht]
          · simp [Pi.single]⟩

/-- Helper for Lemma 5.15: once the recession dimension is not smaller than the polyhedron
dimension, the recession span fills the affine direction. -/
lemma recessionSpan_eq_affineSpanDirection_of_not_dim_lt
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (h_not_lt : ¬ recessionConeDim P < polyhedronDim P) :
    Submodule.span ℝ (recessionCone P) = (affineSpan ℝ P).direction := by
  rcases hP_rational with ⟨m, A, b, hP_eq⟩
  have hle :
      Submodule.span ℝ (recessionCone P) ≤ (affineSpan ℝ P).direction := by
    rw [Submodule.span_le]
    intro r hr
    have hr' :
        r ∈ recessionCone
          (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) := by
      simpa [hP_eq] using hr
    have hdir' :
        r ∈
          (affineSpan ℝ
            (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)))).direction :=
      recessionCone_subset_affineSpan_direction
        (A.map (Rat.castHom ℝ))
        (fun i ↦ (b i : ℝ))
        (by simpa [hP_eq] using hP_nonempty)
        hr'
    -- The Chapter 3 inclusion converts pointwise recession membership into a span inclusion.
    simpa [hP_eq] using hdir'
  have hrec_le_poly : recessionConeDim P ≤ polyhedronDim P := by
    simpa [recessionConeDim, polyhedronDim] using (Submodule.finrank_mono hle)
  have hpoly_le_rec : polyhedronDim P ≤ recessionConeDim P :=
    Nat.not_lt.mp h_not_lt
  have hdim_eq : recessionConeDim P = polyhedronDim P :=
    le_antisymm hrec_le_poly hpoly_le_rec
  -- Equal finite-dimensional subspaces coincide once the recession span is known to be contained.
  exact
    Submodule.eq_of_le_of_finrank_eq hle <|
      by simpa [recessionConeDim, polyhedronDim] using hdim_eq

/-- Helper for Lemma 5.15: subtracting an integral linear combination of integral rays from an
integer vector stays in `integerVectors n`. -/
lemma integerVectors_sub_intLinearCombination_of_mem
    {q : ℕ}
    {y : Fin n → ℝ}
    (hy : y ∈ integerVectors n)
    (rays : Fin q → Fin n → ℤ)
    (a : Fin q → ℤ) :
    (fun i ↦ y i - ∑ j, (a j : ℝ) * (rays j i : ℝ)) ∈ integerVectors n := by
  rcases (mem_integerVectors_iff (x := y)).1 hy with ⟨z, hz⟩
  refine
    (mem_integerVectors_iff
      (x := fun i ↦ y i - ∑ j, (a j : ℝ) * (rays j i : ℝ))).2 ?_
  refine ⟨fun i ↦ z i - ∑ j, a j * rays j i, ?_⟩
  -- Rewrite both sides coordinatewise using the integer witness for `y`.
  ext i
  simp [hz, sub_eq_add_neg, mul_comm]

/-- Helper for Lemma 5.15: subtracting the floor part of a ray combination leaves the base point
plus the `Int.fract` ray combination. -/
lemma sub_floorRayCombination_eq_add_fractCombination
    {q : ℕ}
    {z y : Fin n → ℝ}
    (rays : Fin q → Fin n → ℤ)
    (μ : Fin q → ℝ)
    (hy_repr : y = z + ∑ j, μ j • (fun i ↦ (rays j i : ℝ))) :
    (fun i ↦ y i - ∑ j, (Int.floor (μ j) : ℝ) * (rays j i : ℝ)) =
      z + ∑ j, Int.fract (μ j) • (fun i ↦ (rays j i : ℝ)) := by
  ext i
  have hyi :
      y i = z i + ∑ j, μ j * (rays j i : ℝ) := by
    -- Rewrite the vector identity coordinatewise before separating floor and fractional parts.
    have hyi' := congrFun hy_repr i
    simpa [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using hyi'
  have hsplit :
      (∑ j, μ j * (rays j i : ℝ)) -
          ∑ j, (Int.floor (μ j) : ℝ) * (rays j i : ℝ) =
        ∑ j, Int.fract (μ j) * (rays j i : ℝ) := by
    -- Split each coefficient into its integer floor and fractional remainder.
    calc
      (∑ j, μ j * (rays j i : ℝ)) -
          ∑ j, (Int.floor (μ j) : ℝ) * (rays j i : ℝ) =
        ∑ j, (μ j * (rays j i : ℝ) - (Int.floor (μ j) : ℝ) * (rays j i : ℝ)) := by
          rw [← Finset.sum_sub_distrib]
      _ = ∑ j, ((μ j - (Int.floor (μ j) : ℝ)) * (rays j i : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
      _ = ∑ j, Int.fract (μ j) * (rays j i : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Int.self_sub_floor]
  -- Route correction: normalize the floor-corrected point once in `Int.fract` form before
  -- returning to recession-cone membership.
  calc
    y i - ∑ j, (Int.floor (μ j) : ℝ) * (rays j i : ℝ) =
        z i + ((∑ j, μ j * (rays j i : ℝ)) -
          ∑ j, (Int.floor (μ j) : ℝ) * (rays j i : ℝ)) := by
          rw [hyi]
          ring
    _ = z i + ∑ j, Int.fract (μ j) * (rays j i : ℝ) := by rw [hsplit]
    _ = (z + ∑ j, Int.fract (μ j) • (fun k ↦ (rays j k : ℝ))) i := by
          simp [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

/-- Helper for Lemma 5.15: the `Int.fract` combination of integral recession generators still lies
in the recession cone once the cone is identified with their finitely generated cone. -/
lemma fractCombination_mem_recessionCone_of_eq_finitelyGeneratedCone
    {q : ℕ}
    {P : Set (Fin n → ℝ)}
    (rays : Fin q → Fin n → ℤ)
    (μ : Fin q → ℝ)
    (hrec :
      recessionCone P =
        finitely_generated_cone (fun j : Fin q ↦ fun i : Fin n ↦ (rays j i : ℝ))) :
    (∑ j, Int.fract (μ j) • (fun i ↦ (rays j i : ℝ))) ∈ recessionCone P := by
  -- Cross the cone equality once, then use the canonical coefficient witness `Int.fract ∘ μ`.
  rw [hrec]
  refine (mem_finitely_generated_cone_iff).2 ?_
  refine ⟨fun j ↦ Int.fract (μ j), ?_, rfl⟩
  intro j
  exact Int.fract_nonneg (μ j)

/-- Helper for Lemma 5.15: the floor-corrected affine witness remains feasible because its
fractional remainder is a recession direction. -/
lemma floorCorrectedPoint_mem_of_mem_recessionGenerators
    {q : ℕ}
    {P : Set (Fin n → ℝ)}
    {z y : Fin n → ℝ}
    (hz : z ∈ P)
    (rays : Fin q → Fin n → ℤ)
    (μ : Fin q → ℝ)
    (hrec :
      recessionCone P =
        finitely_generated_cone (fun j : Fin q ↦ fun i : Fin n ↦ (rays j i : ℝ)))
    (hy_repr : y = z + ∑ j, μ j • (fun i ↦ (rays j i : ℝ))) :
    (fun i ↦ y i - ∑ j, (Int.floor (μ j) : ℝ) * (rays j i : ℝ)) ∈ P := by
  have hfract_mem :
      (∑ j, Int.fract (μ j) • (fun i ↦ (rays j i : ℝ))) ∈ recessionCone P :=
    fractCombination_mem_recessionCone_of_eq_finitelyGeneratedCone rays μ hrec
  rw [mem_recessionCone_iff] at hfract_mem
  -- The normalized floor-corrected point is exactly one nonnegative step along a recession ray.
  rw [sub_floorRayCombination_eq_add_fractCombination rays μ hy_repr]
  simpa using hfract_mem hz 1 zero_le_one

/-- Helper for Lemma 5.15: if `aff(P)` contains an integer point and
`recessionConeDim P` is not smaller than `polyhedronDim P`, then `pure_integer_hull P`
already contains a point. -/
lemma pureIntegerHull_nonempty_of_not_recessionConeDim_lt_polyhedronDim
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (h_affine_integer :
      ((affineSpan ℝ P : Set (Fin n → ℝ)) ∩ integerVectors n).Nonempty)
    (h_not_lt : ¬ recessionConeDim P < polyhedronDim P) :
    (pure_integer_hull P).Nonempty := by
  rcases hP_nonempty with ⟨z, hzP⟩
  have hP_nonempty' : P.Nonempty := ⟨z, hzP⟩
  rcases h_affine_integer with ⟨y, hy_aff, hy_int⟩
  rcases existsIntegralRecessionGeneratorsOfRationalPolyhedron P hP_nonempty' hP_rational with
    ⟨q, rays, hrec⟩
  let rayReal : Fin q → Fin n → ℝ := fun j i ↦ (rays j i : ℝ)
  have hspan_eq :
      Submodule.span ℝ (recessionCone P) = (affineSpan ℝ P).direction :=
    recessionSpan_eq_affineSpanDirection_of_not_dim_lt P hP_nonempty' hP_rational h_not_lt
  have hz_aff : z ∈ affineSpan ℝ P := mem_affineSpan ℝ hzP
  have hy_dir : y - z ∈ (affineSpan ℝ P).direction :=
    AffineSubspace.vsub_mem_direction hy_aff hz_aff
  have hdir_span :
      (affineSpan ℝ P).direction = Submodule.span ℝ (Set.range rayReal) := by
    -- Replace the affine direction by the span of the integral recession generators.
    calc
      (affineSpan ℝ P).direction = Submodule.span ℝ (recessionCone P) := hspan_eq.symm
      _ = Submodule.span ℝ (finitely_generated_cone rayReal) := by
            rw [hrec]
      _ = Submodule.span ℝ (Set.range rayReal) := span_finitelyGeneratedCone_eq_span_range rayReal
  have hy_span : y - z ∈ Submodule.span ℝ (Set.range rayReal) := by
    rw [← hdir_span]
    exact hy_dir
  obtain ⟨μ, hμ_repr⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hy_span
  have hy_repr : y = z + ∑ j, μ j • rayReal j := by
    -- Rewrite the affine-span witness into the single stable spelling used by the floor helper.
    have hμ_repr' : y - z = ∑ j, μ j • rayReal j := by
      simpa using hμ_repr.symm
    have hy_add : y = (∑ j, μ j • rayReal j) + z := (sub_eq_iff_eq_add).1 hμ_repr'
    calc
      y = (∑ j, μ j • rayReal j) + z := hy_add
      _ = z + ∑ j, μ j • rayReal j := by
            rw [add_comm]
  let xFloor : Fin n → ℝ :=
    fun i ↦ y i - ∑ j, (Int.floor (μ j) : ℝ) * (rays j i : ℝ)
  have hxFloor_mem_P : xFloor ∈ P := by
    -- The floor-corrected point is feasible because only the fractional ray combination remains.
    exact floorCorrectedPoint_mem_of_mem_recessionGenerators hzP rays μ hrec hy_repr
  have hxFloor_mem_int : xFloor ∈ integerVectors n := by
    -- Integrality is preserved after subtracting the integer floor combination of integral rays.
    exact integerVectors_sub_intLinearCombination_of_mem hy_int rays (fun j ↦ Int.floor (μ j))
  have hxFloor_mem_pure : xFloor ∈ pure_integer_points P := by
    -- Feasibility and integrality combine into membership in the pure-integer point set.
    rw [mem_pure_integer_points_iff]
    exact ⟨hxFloor_mem_P, hxFloor_mem_int⟩
  have hxFloor_mem_hull : xFloor ∈ pure_integer_hull P := by
    -- Any pure-integer point belongs to the convex hull of all pure-integer points.
    change xFloor ∈ convexHull ℝ (pure_integer_points P)
    exact subset_convexHull ℝ (pure_integer_points P) hxFloor_mem_pure
  exact ⟨xFloor, hxFloor_mem_hull⟩

/-- Lemma 5.15. Let `P ⊆ ℝ^n` be a nonempty rational polyhedron such that
`aff(P) ∩ ℤ^n ≠ ∅`. If `P_I = ∅`, represented here by `pure_integer_hull P = ∅`, then
`dim(rec(P)) < dim(P)`. On the chapter-level canonical owners these dimensions are
`recessionConeDim P` and `polyhedronDim P`. -/
theorem recessionConeDim_lt_polyhedronDim_of_pure_integer_hull_eq_empty
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (h_affine_integer :
      ((affineSpan ℝ P : Set (Fin n → ℝ)) ∩ integerVectors n).Nonempty)
    (hPI_empty : pure_integer_hull P = ∅) :
    recessionConeDim P < polyhedronDim P := by
  by_contra h_not_lt
  rcases pureIntegerHull_nonempty_of_not_recessionConeDim_lt_polyhedronDim
      P hP_nonempty hP_rational h_affine_integer h_not_lt with
    ⟨x, hx⟩
  rw [hPI_empty] at hx
  exact hx

/-- Expanded bridge form of Lemma 5.15 using the raw affine-span and recession-cone finrank
expressions. -/
theorem finrank_span_recessionCone_lt_finrank_direction_affineSpan_of_pure_integer_hull_eq_empty
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (h_affine_integer :
      ((affineSpan ℝ P : Set (Fin n → ℝ)) ∩ integerVectors n).Nonempty)
    (hPI_empty : pure_integer_hull P = ∅) :
    Module.finrank ℝ (Submodule.span ℝ (recessionCone P)) <
      Module.finrank ℝ (affineSpan ℝ P).direction := by
  change recessionConeDim P < polyhedronDim P
  exact recessionConeDim_lt_polyhedronDim_of_pure_integer_hull_eq_empty
    P hP_nonempty hP_rational h_affine_integer hPI_empty

end Lemma515
