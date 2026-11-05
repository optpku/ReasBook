/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectionalWidthNotation Matrix

section Exercise97

variable {n : ℕ}

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap09/section_9_5/ch9_sec9_5_exercise_9_7.lean:
a full-dimensional convex body contains a scalar direct affine Euclidean ball. -/
lemma existsScalarDirectAffineBall_subset
    (K : ConvexBody (Fin n → ℝ))
    (hfull : K.FullDimensional) :
    ∃ (δ : ℝ) (a : Fin n → ℝ),
      0 < δ ∧
        FlatnessSupport.directAffineEuclideanBall
          (δ • (1 : Matrix (Fin n) (Fin n) ℝ)) a ⊆
        (K : Set (Fin n → ℝ)) := by
  rcases ConvexBody.fullDimensional_iff.mp hfull with ⟨a, ha⟩
  have hK_nhds : (K : Set (Fin n → ℝ)) ∈ nhds a :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds ha) interior_subset
  rcases Metric.mem_nhds_iff.mp hK_nhds with ⟨ε, hε, hball⟩
  let δ : ℝ := ε / 2
  -- Reuse the interior ball around `a` and rewrite it as the scalar direct affine ball.
  refine ⟨δ, a, by simpa [δ] using half_pos hε, ?_⟩
  rintro x ⟨u, hu, rfl⟩
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  have hu_sup : ‖u‖ ≤ 1 := (FlatnessSupport.norm_le_euclideanNorm u).trans hu
  have hδ_pos : 0 < δ := by
    simpa [δ] using half_pos hε
  calc
    ‖a + ((δ • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u) - a‖ = ‖δ • u‖ := by
      congr 1
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      abel
    _ = δ * ‖u‖ := by
      simp [norm_smul, abs_of_pos hδ_pos]
    _ ≤ δ := by
      nlinarith
    _ < ε := by
      simp [δ, hε]

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap09/section_9_5/ch9_sec9_5_exercise_9_7.lean:
the width of a scalar direct affine Euclidean ball is exactly the scalar multiple of the Euclidean
norm of the direction. -/
lemma directionalWidth_scalarDirectAffineBall
    {δ : ℝ} {a : Fin n → ℝ} {d : Fin n → ℤ}
    (hδ : 0 < δ) :
    directional_width
        (FlatnessSupport.directAffineEuclideanBall
          (δ • (1 : Matrix (Fin n) (Fin n) ℝ)) a) d =
      2 * δ * FlatnessSupport.euclideanNorm (Int.cast ∘ d) := by
  have hdet : IsUnit ((δ • (1 : Matrix (Fin n) (Fin n) ℝ)).det) := by
    apply isUnit_iff_ne_zero.mpr
    simp [hδ.ne']
  have htranspose_unit :
      IsUnit (((δ • (1 : Matrix (Fin n) (Fin n) ℝ)).transpose).det) :=
    Matrix.isUnit_det_transpose _ hdet
  -- Rewrite the direct affine ball through the inverse ellipsoid presentation and simplify the
  -- transformed direction explicitly for the scalar identity matrix.
  rw [FlatnessSupport.directAffineEuclideanBall_eq_euclideanEllipsoid_inv _ _ hdet]
  calc
    directional_width
        (FlatnessSupport.euclideanEllipsoid ((δ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹) a) d
      = 2 *
          FlatnessSupport.euclideanNorm
            ((((δ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).transpose)⁻¹ *ᵥ
              (Int.cast ∘ d)) := by
        simpa using
          FlatnessSupport.directionalWidth_euclideanEllipsoid_eq_two_mul_dualNorm
            ((δ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹) a
            (Matrix.isUnit_nonsing_inv_det
              (A := (δ • (1 : Matrix (Fin n) (Fin n) ℝ))) hdet) d
    _ = 2 *
          FlatnessSupport.euclideanNorm
            (((δ • (1 : Matrix (Fin n) (Fin n) ℝ)).transpose) *ᵥ (Int.cast ∘ d)) := by
        congr 1
        rw [Matrix.transpose_nonsing_inv]
        have hmulVec :
            (((δ • (1 : Matrix (Fin n) (Fin n) ℝ)).transpose)⁻¹⁻¹) *ᵥ (Int.cast ∘ d) =
              ((δ • (1 : Matrix (Fin n) (Fin n) ℝ)).transpose) *ᵥ (Int.cast ∘ d) := by
          rw [Matrix.nonsing_inv_nonsing_inv
            (A := (δ • (1 : Matrix (Fin n) (Fin n) ℝ)).transpose) htranspose_unit]
        exact congrArg FlatnessSupport.euclideanNorm hmulVec
    _ = 2 *
          FlatnessSupport.euclideanNorm
            (((δ • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ (Int.cast ∘ d))) := by
        simp
    _ = 2 * FlatnessSupport.euclideanNorm (δ • (Int.cast ∘ d)) := by
        simp [Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = 2 * (δ * FlatnessSupport.euclideanNorm (Int.cast ∘ d)) := by
        rw [FlatnessSupport.euclideanNorm_smul, abs_of_pos hδ]
    _ = 2 * δ * FlatnessSupport.euclideanNorm (Int.cast ∘ d) := by
        ring

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap09/section_9_5/ch9_sec9_5_exercise_9_7.lean:
only finitely many nonzero integral directions can have width bounded by a fixed constant once `K`
contains a positive scalar Euclidean ball. -/
lemma finiteNonzeroIntegralDirections_of_width_le
    (K : ConvexBody (Fin n → ℝ))
    {δ : ℝ} {a : Fin n → ℝ}
    (hδ : 0 < δ)
    (hball :
      FlatnessSupport.directAffineEuclideanBall
          (δ • (1 : Matrix (Fin n) (Fin n) ℝ)) a ⊆
        (K : Set (Fin n → ℝ)))
    {B : ℝ}
    (_hB : 0 ≤ B) :
    Set.Finite {d : {d : Fin n → ℤ // d ≠ 0} |
      w_{d.1}((K : Set (Fin n → ℝ))) ≤ B} := by
  let radius : ℝ := B / (2 * δ)
  have hfinite_target :
      Set.Finite
        (Metric.closedBall (0 : Fin n → ℝ) radius ∩
          (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) :
            Set (Fin n → ℝ))) := by
    simpa [radius] using
      (ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin n))
        (s := Metric.closedBall (0 : Fin n → ℝ) radius)
        (Metric.isBounded_closedBall :
          Bornology.IsBounded (Metric.closedBall (0 : Fin n → ℝ) radius)))
  -- Embed every bounded-width direction into the finite closed-ball slice of the standard lattice.
  refine Set.Finite.of_injOn
    (f := fun d : {d : Fin n → ℤ // d ≠ 0} ↦ (Int.cast ∘ d.1 : Fin n → ℝ))
    ?_ ?_ hfinite_target
  · intro d hd
    have hball_width_le :
        directional_width
            (FlatnessSupport.directAffineEuclideanBall
              (δ • (1 : Matrix (Fin n) (Fin n) ℝ)) a) d.1 ≤ B := by
      calc
        directional_width
            (FlatnessSupport.directAffineEuclideanBall
              (δ • (1 : Matrix (Fin n) (Fin n) ℝ)) a) d.1
            ≤ directional_width (K : Set (Fin n → ℝ)) d.1 :=
          directionalWidth_mono
            ⟨a, FlatnessSupport.center_mem_directAffineEuclideanBall _ _⟩ K.isCompact hball
        _ ≤ B := hd
    have hnorm_le :
        FlatnessSupport.euclideanNorm (Int.cast ∘ d.1) ≤ radius := by
      rw [directionalWidth_scalarDirectAffineBall (a := a) (d := d.1) hδ] at hball_width_le
      have htwodelta_pos : 0 < 2 * δ := by
        positivity
      have hnorm_le' :
          FlatnessSupport.euclideanNorm (Int.cast ∘ d.1) ≤ B / (2 * δ) := by
        rw [le_div_iff₀ htwodelta_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hball_width_le
      simpa [radius] using hnorm_le'
    refine ⟨?_, ?_⟩
    · have hnorm_bound : ‖(Int.cast ∘ d.1 : Fin n → ℝ)‖ ≤ radius := by
        exact le_trans (FlatnessSupport.norm_le_euclideanNorm _) hnorm_le
      simpa [Metric.mem_closedBall, dist_zero_right, radius] using hnorm_bound
    · have hspan_mem :
          (∑ i, (d.1 i : ℤ) • Pi.basisFun ℝ (Fin n) i) ∈
            Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) := by
        exact Submodule.sum_mem _ fun i hi =>
          zsmul_mem
            (Submodule.subset_span
              (show Pi.basisFun ℝ (Fin n) i ∈ Set.range (Pi.basisFun ℝ (Fin n)) from
                ⟨i, rfl⟩))
            _
      have hcast_eq :
          (Int.cast ∘ d.1 : Fin n → ℝ) =
            ∑ i, (d.1 i : ℤ) • Pi.basisFun ℝ (Fin n) i := by
        simpa [zsmul_eq_mul] using
          ((Pi.basisFun ℝ (Fin n)).sum_repr (Int.cast ∘ d.1)).symm
      change (Int.cast ∘ d.1 : Fin n → ℝ) ∈
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
      rw [hcast_eq]
      exact hspan_mem
  · intro d₁ hd₁ d₂ hd₂ hcast
    apply Subtype.ext
    funext i
    exact Int.cast_injective (congrFun hcast i)

/-- remote integer-programming sorr<!-- -->y cleanup Integer/Chapters/Chap09/section_9_5/ch9_sec9_5_exercise_9_7.lean

Exercise 9.7. For a full-dimensional convex body `K ⊆ ℝ^n` in positive dimension, the
infimum defining the widths `w_d(K)` over nonzero integral directions is attained by some
nonzero integral direction. -/
theorem exists_nonzero_integral_direction_realizing_lattice_width
    (hn : 0 < n)
    (K : ConvexBody (Fin n → ℝ))
    (hfull : K.FullDimensional) :
    ∃ d : {d : Fin n → ℤ // d ≠ 0},
      lattice_width K = w_{d}((K : Set (Fin n → ℝ))) := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let d0 : Fin n → ℤ := Pi.single i0 1
  have hd0_ne : d0 ≠ 0 := by
    intro hd0
    have hvalue : d0 i0 = 0 := by
      simp [hd0]
    simp [d0] at hvalue
  let B : ℝ := w_{d0}((K : Set (Fin n → ℝ)))
  let widthSet : Set ℝ :=
    (fun d : {d : Fin n → ℤ // d ≠ 0} ↦ w_{d.1}((K : Set (Fin n → ℝ)))) '' Set.univ
  have hB_nonneg : 0 ≤ B := by
    simpa [B] using directionalWidth_nonneg K d0
  have hwidthSet_bddBelow : BddBelow widthSet := by
    refine ⟨0, ?_⟩
    rintro x ⟨d, -, rfl⟩
    exact directionalWidth_nonneg K d.1
  have hd0_mem_widthSet : B ∈ widthSet := by
    refine ⟨⟨d0, hd0_ne⟩, Set.mem_univ _, ?_⟩
    simp [B]
  have hlattice_le_B : lattice_width K ≤ B := by
    -- Insert the explicit direction `d0` into the defining infimum.
    simpa [lattice_width, widthSet] using csInf_le hwidthSet_bddBelow hd0_mem_widthSet
  rcases existsScalarDirectAffineBall_subset K hfull with ⟨δ, a, hδ, hball⟩
  let slice : Set {d : Fin n → ℤ // d ≠ 0} :=
    {d | w_{d.1}((K : Set (Fin n → ℝ))) ≤ B}
  have hd0_in_slice : ⟨d0, hd0_ne⟩ ∈ slice := by
    simp [slice, B]
  have hslice_nonempty : slice.Nonempty := ⟨⟨d0, hd0_ne⟩, hd0_in_slice⟩
  have hslice_finite : Set.Finite slice :=
    finiteNonzeroIntegralDirections_of_width_le (a := a) K hδ hball hB_nonneg
  obtain ⟨dmin, hdmin_mem, hdmin_min⟩ :=
    Set.exists_min_image slice
      (fun d : {d : Fin n → ℤ // d ≠ 0} ↦ w_{d.1}((K : Set (Fin n → ℝ))))
      hslice_finite hslice_nonempty
  have hdmin_mem_widthSet : w_{dmin.1}((K : Set (Fin n → ℝ))) ∈ widthSet := by
    refine ⟨dmin, Set.mem_univ _, rfl⟩
  have hdmin_le_B : w_{dmin.1}((K : Set (Fin n → ℝ))) ≤ B := hdmin_mem
  refine ⟨dmin, le_antisymm ?_ ?_⟩
  · -- The lattice width is below every realized competitor, in particular the minimizer.
    simpa [lattice_width, widthSet] using csInf_le hwidthSet_bddBelow hdmin_mem_widthSet
  · -- Conversely, every competitor is at least as large as the minimizer on the bounded slice.
    rw [lattice_width]
    refine le_csInf ?_ ?_
    · refine ⟨B, ?_⟩
      refine ⟨⟨d0, hd0_ne⟩, Set.mem_univ _, ?_⟩
      simp [B]
    · intro y hy
      rcases hy with ⟨d, -, rfl⟩
      by_cases hd_le_B : w_{d.1}((K : Set (Fin n → ℝ))) ≤ B
      · exact hdmin_min d (by simpa [slice] using hd_le_B)
      · have hB_lt_d : B < w_{d.1}((K : Set (Fin n → ℝ))) := lt_of_not_ge hd_le_B
        linarith

/-- Companion form of Exercise 9.7: the minimizing direction can be exposed as an ordinary
integral vector together with its nonzeroness proof. -/
theorem exists_integral_direction_ne_zero_realizing_lattice_width
    (hn : 0 < n)
    (K : ConvexBody (Fin n → ℝ))
    (hfull : K.FullDimensional) :
    ∃ d : Fin n → ℤ,
      d ≠ 0 ∧ lattice_width K = w_{d}((K : Set (Fin n → ℝ))) := by
  obtain ⟨d, hd⟩ := exists_nonzero_integral_direction_realizing_lattice_width hn K hfull
  exact ⟨d, d.2, hd⟩

end Exercise97
