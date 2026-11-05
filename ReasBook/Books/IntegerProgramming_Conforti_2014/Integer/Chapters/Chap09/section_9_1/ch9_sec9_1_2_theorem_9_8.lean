/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_remark_9_9.Ellipsoid
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section Theorem98

variable {n : ℕ}

/-- The ellipsoid in `ℝ^n` with center `a` and shape matrix `C`, written as
`{x | ‖C (x - a)‖₂ ≤ 1}` in the local `Fin n → ℝ` coordinate model, encoded by the equivalent
quadratic inequality `(C *ᵥ (x - a)) ⬝ᵥ (C *ᵥ (x - a)) ≤ 1`. -/
def euclidean_ellipsoid
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | (C *ᵥ (x - a)) ⬝ᵥ (C *ᵥ (x - a)) ≤ 1}

/-- Membership in `euclidean_ellipsoid C a` is exactly the defining quadratic inequality. -/
theorem mem_euclidean_ellipsoid_iff
    {C : Matrix (Fin n) (Fin n) ℝ} {a x : Fin n → ℝ} :
    x ∈ euclidean_ellipsoid C a ↔
      (C *ᵥ (x - a)) ⬝ᵥ (C *ᵥ (x - a)) ≤ 1 := by
  rfl

/-- Helper for theorem 9.8 file
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean`: the local quadratic
ellipsoid agrees with the Chapter 9 support-side Euclidean ellipsoid. -/
theorem euclideanEllipsoid_eq_supportEuclideanEllipsoid
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    euclidean_ellipsoid C a = FlatnessSupport.euclideanEllipsoid C a := by
  ext x
  constructor
  · intro hx
    -- Rewrite the quadratic inequality as the square of the Euclidean norm.
    rw [mem_euclidean_ellipsoid_iff] at hx
    change FlatnessSupport.euclideanNorm (C *ᵥ (x - a)) ≤ 1
    rw [FlatnessSupport.dotProduct_self_eq_euclideanNorm_sq] at hx
    have hnorm_nonneg : 0 ≤ FlatnessSupport.euclideanNorm (C *ᵥ (x - a)) :=
      FlatnessSupport.euclideanNorm_nonneg _
    nlinarith
  · intro hx
    -- Square the support-side norm bound to recover the quadratic presentation.
    change FlatnessSupport.euclideanNorm (C *ᵥ (x - a)) ≤ 1 at hx
    rw [mem_euclidean_ellipsoid_iff]
    rw [FlatnessSupport.dotProduct_self_eq_euclideanNorm_sq]
    have hnorm_nonneg : 0 ≤ FlatnessSupport.euclideanNorm (C *ᵥ (x - a)) :=
      FlatnessSupport.euclideanNorm_nonneg _
    nlinarith

/-- Helper for theorem 9.8 file
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean`: a nonsingular local
ellipsoid is the direct affine image of the Euclidean unit ball under the inverse shape matrix. -/
theorem euclideanEllipsoid_eq_directAffineEuclideanBallInv
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hC : IsUnit C.det) :
    euclidean_ellipsoid C a = FlatnessSupport.directAffineEuclideanBall C⁻¹ a := by
  -- Normalize to the support-side ellipsoid and then invoke the inverse-matrix direct-ball API.
  calc
    euclidean_ellipsoid C a = FlatnessSupport.euclideanEllipsoid C a :=
      euclideanEllipsoid_eq_supportEuclideanEllipsoid C a
    _ = FlatnessSupport.directAffineEuclideanBall C⁻¹ a := by
      symm
      rw [FlatnessSupport.directAffineEuclideanBall_eq_euclideanEllipsoid_inv
        C⁻¹ a (Matrix.isUnit_nonsing_inv_det C hC)]
      simpa using congrArg
        (fun M : Matrix (Fin n) (Fin n) ℝ ↦ FlatnessSupport.euclideanEllipsoid M a)
        (Matrix.nonsing_inv_nonsing_inv C hC)

/-- Helper for theorem 9.8 file
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean`: the center point belongs to
the local ellipsoid. -/
theorem center_mem_euclidean_ellipsoid
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    a ∈ euclidean_ellipsoid C a := by
  -- Transport the canonical center-membership fact across the normalization bridge.
  rw [euclideanEllipsoid_eq_supportEuclideanEllipsoid]
  exact FlatnessSupport.center_mem_euclideanEllipsoid C a

/-- Helper for theorem 9.8 file
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean`: a nonsingular local
ellipsoid is convex. -/
theorem convex_euclidean_ellipsoid
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hC : IsUnit C.det) :
    Convex ℝ (euclidean_ellipsoid C a) := by
  -- Use the direct-affine-ball model instead of unfolding the quadratic inequality.
  rw [euclideanEllipsoid_eq_directAffineEuclideanBallInv C a hC]
  exact FlatnessSupport.convex_directAffineEuclideanBall C⁻¹ a

/-- Helper for theorem 9.8 file
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean`: a nonsingular local
ellipsoid is compact. -/
theorem isCompact_euclidean_ellipsoid
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hC : IsUnit C.det) :
    IsCompact (euclidean_ellipsoid C a) := by
  -- Reuse compactness of the direct affine Euclidean ball after normalization.
  rw [euclideanEllipsoid_eq_directAffineEuclideanBallInv C a hC]
  exact FlatnessSupport.isCompact_directAffineEuclideanBall C⁻¹ a

/-- Helper for theorem 9.8 file
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean`: inserting any nonzero
integral direction into the defining infimum bounds the lattice width. -/
theorem latticeWidth_le_of_directionalWidth_le
    {K : ConvexBody (Fin n → ℝ)}
    {d : Fin n → ℤ}
    {B : ℝ}
    (hd : d ≠ 0)
    (hwidth : directional_width (K : Set (Fin n → ℝ)) d ≤ B) :
    lattice_width K ≤ B := by
  have hBddBelow :
      BddBelow
        ((fun e : {e : Fin n → ℤ // e ≠ 0} ↦
            directional_width (K : Set (Fin n → ℝ)) e.1) '' Set.univ) := by
    -- Every directional width in the infimum is nonnegative.
    refine ⟨0, ?_⟩
    rintro x ⟨e, -, rfl⟩
    exact directionalWidth_nonneg K e.1
  have hmem :
      directional_width (K : Set (Fin n → ℝ)) d ∈
        ((fun e : {e : Fin n → ℤ // e ≠ 0} ↦
            directional_width (K : Set (Fin n → ℝ)) e.1) '' Set.univ) := by
    -- The chosen direction is one of the admissible nonzero integral directions.
    refine ⟨⟨d, hd⟩, Set.mem_univ _, rfl⟩
  -- Compare the infimum to the chosen width and then apply the hypothesis.
  exact le_trans (csInf_le hBddBelow hmem) hwidth

/-- Helper for theorem 9.8 file
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean`: a lattice-free nonsingular
direct affine ball contains only finitely many integral points in its doubled copy. -/
theorem finiteIntegralPointsInDoubleDirectAffineBall
    (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Set.Finite {z : Fin n → ℤ |
      (Int.cast ∘ z : Fin n → ℝ) ∈
        FlatnessSupport.directAffineEuclideanBall (2 • A) a} := by
  let S : Set (Fin n → ℝ) := FlatnessSupport.directAffineEuclideanBall (2 • A) a
  have hfinite_target :
      Set.Finite
        (S ∩
          (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) :
            Set (Fin n → ℝ))) := by
    -- Intersect the compact doubled ball with the standard integer lattice span.
    exact
      ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin n))
        (by
          dsimp [S]
          exact (FlatnessSupport.isCompact_directAffineEuclideanBall (2 • A) a).isBounded)
  have hmapsTo :
      Set.MapsTo
        (fun z : Fin n → ℤ ↦ (Int.cast ∘ z : Fin n → ℝ))
        {z : Fin n → ℤ |
          (Int.cast ∘ z : Fin n → ℝ) ∈
            FlatnessSupport.directAffineEuclideanBall (2 • A) a}
        (S ∩
          (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) :
            Set (Fin n → ℝ))) := by
    intro z hz
    refine ⟨hz, ?_⟩
    -- Rewrite the integer vector in the standard `ℤ`-span generated by the coordinate basis.
    have hspan_mem :
        (∑ i, (z i : ℤ) • Pi.basisFun ℝ (Fin n) i) ∈
          Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) := by
      exact Submodule.sum_mem _ fun i _ ↦
        zsmul_mem
          (Submodule.subset_span
            (show Pi.basisFun ℝ (Fin n) i ∈ Set.range (Pi.basisFun ℝ (Fin n)) from
              ⟨i, rfl⟩))
          _
    have hcast_eq :
        (Int.cast ∘ z : Fin n → ℝ) =
          ∑ i, (z i : ℤ) • Pi.basisFun ℝ (Fin n) i := by
      simpa [zsmul_eq_mul] using
        ((Pi.basisFun ℝ (Fin n)).sum_repr (Int.cast ∘ z)).symm
    change (Int.cast ∘ z : Fin n → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
    rw [hcast_eq]
    exact hspan_mem
  have hinj :
      Set.InjOn
        (fun z : Fin n → ℤ ↦ (Int.cast ∘ z : Fin n → ℝ))
        {z : Fin n → ℤ |
          (Int.cast ∘ z : Fin n → ℝ) ∈
            FlatnessSupport.directAffineEuclideanBall (2 • A) a} := by
    intro z₁ hz₁ z₂ hz₂ hcast
    -- Integer casts are injective coordinatewise.
    funext i
    exact Int.cast_injective (congrFun hcast i)
  exact Set.Finite.of_injOn hmapsTo hinj hfinite_target

/-- Helper for theorem 9.8 file
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean`: a lattice-free nonsingular
direct affine ball can be dilated slightly while remaining lattice-free. -/
theorem existsLatticeFreeExpansion_directAffineEuclideanBall
    (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hA : IsUnit A.det)
    (hfree : ¬ contains_integral_point (FlatnessSupport.directAffineEuclideanBall A a)) :
    ∃ τ : ℝ,
      1 < τ ∧
        τ < 2 ∧
          ¬ contains_integral_point (FlatnessSupport.directAffineEuclideanBall (τ • A) a) := by
  classical
  let ν : (Fin n → ℤ) → ℝ := fun z ↦
    FlatnessSupport.euclideanNorm (A⁻¹ *ᵥ ((Int.cast ∘ z : Fin n → ℝ) - a))
  have hfreeEllipsoid :
      ¬ contains_integral_point (FlatnessSupport.euclideanEllipsoid A⁻¹ a) := by
    -- Normalize the direct ball to the inverse-shape ellipsoid model.
    simpa [FlatnessSupport.directAffineEuclideanBall_eq_euclideanEllipsoid_inv A a hA] using hfree
  have hν_gt_one : ∀ z : Fin n → ℤ, 1 < ν z := by
    intro z
    -- Lattice-freeness means every translated inverse-shape norm is strictly larger than `1`.
    have havoid :=
      (FlatnessSupport.not_containsIntegralPoint_iff_translateAvoidsClosedUnitBall A⁻¹ a).mp
        hfreeEllipsoid z
    simpa [ν, Matrix.mulVec_sub] using havoid
  have hν_le_of_mem_scaledBall :
      ∀ {τ : ℝ},
        0 ≤ τ →
          ∀ {z : Fin n → ℤ},
            (Int.cast ∘ z : Fin n → ℝ) ∈
                FlatnessSupport.directAffineEuclideanBall (τ • A) a →
              ν z ≤ τ := by
    intro τ hτ_nonneg z hz
    rcases hz with ⟨u, hu, huz⟩
    have hu_norm : FlatnessSupport.euclideanNorm u ≤ 1 := by
      simpa using hu
    have hz_sub :
        ((Int.cast ∘ z : Fin n → ℝ) - a) = (τ • A) *ᵥ u := by
      rw [← huz]
      ext i
      simp [sub_eq_add_neg]
    have hcancel :
        A⁻¹ *ᵥ ((Int.cast ∘ z : Fin n → ℝ) - a) = τ • u := by
      -- Cancel the inverse matrix against the direct-shape witness.
      calc
        A⁻¹ *ᵥ ((Int.cast ∘ z : Fin n → ℝ) - a)
            = A⁻¹ *ᵥ ((τ • A) *ᵥ u) := by rw [hz_sub]
        _ = A⁻¹ *ᵥ (τ • (A *ᵥ u)) := by
              rw [Matrix.smul_mulVec]
        _ = τ • (A⁻¹ *ᵥ (A *ᵥ u)) := by
              rw [Matrix.mulVec_smul]
        _ = τ • ((A⁻¹ * A) *ᵥ u) := by
              rw [← Matrix.mulVec_mulVec]
        _ = τ • u := by
              simp [Matrix.nonsing_inv_mul _ hA]
    -- The scaled witness bounds the inverse-shape norm by `τ`.
    calc
      ν z = FlatnessSupport.euclideanNorm (τ • u) := by
        simpa [ν] using congrArg FlatnessSupport.euclideanNorm hcancel
      _ = |τ| * FlatnessSupport.euclideanNorm u := FlatnessSupport.euclideanNorm_smul _ _
      _ = τ * FlatnessSupport.euclideanNorm u := by
            rw [abs_of_nonneg hτ_nonneg]
      _ ≤ τ := by
            nlinarith
  have hsubset_double_of_lt_two :
      ∀ {τ : ℝ},
        0 ≤ τ →
          τ ≤ 2 →
            FlatnessSupport.directAffineEuclideanBall (τ • A) a ⊆
              FlatnessSupport.directAffineEuclideanBall (2 • A) a := by
    intro τ hτ_nonneg hτ_le_two x hx
    rcases hx with ⟨u, hu, rfl⟩
    have hhalf_nonneg : 0 ≤ τ / 2 := by positivity
    have hhalf_le_one : τ / 2 ≤ 1 := by
      nlinarith
    refine ⟨(τ / 2) • u, ?_, ?_⟩
    · -- Scaling the witness by `τ / 2 ≤ 1` keeps it in the unit ball.
      have hu_norm : FlatnessSupport.euclideanNorm u ≤ 1 := by
        simpa using hu
      calc
        FlatnessSupport.euclideanNorm ((τ / 2) • u)
            = |τ / 2| * FlatnessSupport.euclideanNorm u := FlatnessSupport.euclideanNorm_smul _ _
        _ = (τ / 2) * FlatnessSupport.euclideanNorm u := by
              rw [abs_of_nonneg hhalf_nonneg]
        _ ≤ 1 := by
              nlinarith
    · -- Reassociate the scalar between the matrix and the witness.
      ext i
      dsimp
      rw [two_nsmul, Matrix.add_mulVec]
      simp [Matrix.smul_mulVec, Matrix.mulVec_smul]
      ring
  let candidates : Set (Fin n → ℤ) := {z : Fin n → ℤ |
    (Int.cast ∘ z : Fin n → ℝ) ∈ FlatnessSupport.directAffineEuclideanBall (2 • A) a}
  have hcandidates_finite : candidates.Finite := finiteIntegralPointsInDoubleDirectAffineBall A a
  by_cases hnonempty : candidates.Nonempty
  · let F : Finset (Fin n → ℤ) := hcandidates_finite.toFinset
    rcases hnonempty with ⟨z₀, hz₀⟩
    have hF_nonempty : F.Nonempty := by
      refine ⟨z₀, ?_⟩
      change z₀ ∈ hcandidates_finite.toFinset
      exact hcandidates_finite.mem_toFinset.mpr hz₀
    let m : ℝ := F.inf' hF_nonempty ν
    let b : ℝ := min m 2
    let τ : ℝ := (1 + b) / 2
    have hOne_lt_m : 1 < m := by
      -- Every doubled-ball candidate still satisfies the original strict lattice-free gap.
      refine (Finset.lt_inf'_iff hF_nonempty).2 ?_
      intro z hzF
      exact hν_gt_one z
    have hOne_lt_b : 1 < b := by
      dsimp [b]
      exact lt_min hOne_lt_m (by norm_num)
    have hτ_gt_one : 1 < τ := by
      dsimp [τ]
      nlinarith
    have hτ_lt_b : τ < b := by
      dsimp [τ]
      nlinarith
    have hb_le_two : b ≤ 2 := by
      dsimp [b]
      exact min_le_right _ _
    have hb_le_m : b ≤ m := by
      dsimp [b]
      exact min_le_left _ _
    have hτ_lt_two : τ < 2 := by
      dsimp [τ]
      nlinarith
    have hτ_nonneg : 0 ≤ τ := by
      linarith
    refine ⟨τ, hτ_gt_one, hτ_lt_two, ?_⟩
    intro hcontains
    rcases contains_integral_point_iff.mp hcontains with ⟨z, hz⟩
    have hz_double :
        (Int.cast ∘ z : Fin n → ℝ) ∈ FlatnessSupport.directAffineEuclideanBall (2 • A) a := by
      exact hsubset_double_of_lt_two hτ_nonneg hτ_lt_two.le hz
    have hzF : z ∈ F := by
      change z ∈ hcandidates_finite.toFinset
      exact hcandidates_finite.mem_toFinset.mpr hz_double
    have hm_le : m ≤ ν z := by
      simpa [m] using (Finset.inf'_le ν hzF)
    have hτ_lt_m : τ < m := lt_of_lt_of_le hτ_lt_b hb_le_m
    have hν_le_τ : ν z ≤ τ := hν_le_of_mem_scaledBall hτ_nonneg hz
    exact (not_lt_of_ge hν_le_τ) (lt_of_lt_of_le hτ_lt_m hm_le)
  · refine ⟨3 / 2, by norm_num, by norm_num, ?_⟩
    -- If the doubled ball is lattice-free on integers, then so is the `3/2`-dilation.
    intro hcontains
    rcases contains_integral_point_iff.mp hcontains with ⟨z, hz⟩
    have hz_double :
        (Int.cast ∘ z : Fin n → ℝ) ∈ FlatnessSupport.directAffineEuclideanBall (2 • A) a :=
      hsubset_double_of_lt_two (by positivity) (by norm_num) hz
    exact hnonempty ⟨z, hz_double⟩

/-- Helper for theorem 9.8 file
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean`: a nonsingular direct affine
ball has a rational outer support ellipsoid inside any strict dilation. -/
theorem existsRationalOuterSupportEllipsoid_of_directAffineBall
    (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hA_unit : IsUnit A.det)
    {τ : ℝ}
    (hτ : 1 < τ) :
    ∃ Q : Matrix (Fin n) (Fin n) ℚ,
      IsUnit Q.det ∧
        FlatnessSupport.directAffineEuclideanBall A a ⊆
          FlatnessSupport.euclideanEllipsoid (Q.map (Rat.castHom ℝ)) a ∧
        FlatnessSupport.euclideanEllipsoid (Q.map (Rat.castHom ℝ)) a ⊆
          FlatnessSupport.directAffineEuclideanBall (τ • A) a := by
  let σ : ℝ := τ⁻¹
  let ρ : ℝ := (σ + 1) / 2
  have hτ_pos : 0 < τ := lt_trans zero_lt_one hτ
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    simpa using inv_pos.mpr hτ_pos
  have hσ_lt_one : σ < 1 := by
    dsimp [σ]
    simpa [one_div] using one_div_lt_one_div_of_lt zero_lt_one hτ
  have hσ_lt_ρ : σ < ρ := by
    dsimp [ρ]
    nlinarith
  have hρ_lt_one : ρ < 1 := by
    dsimp [ρ]
    nlinarith
  have hτA_unit : IsUnit ((τ • A).det) := by
    -- Rescaling a nonsingular shape by a nonzero scalar preserves nonsingularity.
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hτ_pos.ne') (isUnit_iff_ne_zero.mp hA_unit)
  rcases FlatnessSupport.existsRationalEllipsoid_between_scaledDirectBalls
      (τ • A) a hτA_unit hσ_pos hσ_lt_ρ hρ_lt_one with
    ⟨Q, hQ_unit, hleft, hright⟩
  refine ⟨Q, hQ_unit, ?_, ?_⟩
  · -- The imported bridge starts at `(τ⁻¹ • (τ • A))`, which is exactly `A`.
    simpa [σ, smul_smul, hτ_pos.ne', div_eq_mul_inv] using hleft
  · -- The imported outer ellipsoid sits in a smaller dilation of `τ • A`, hence inside `τ • A`.
    exact Set.Subset.trans hright
      (FlatnessSupport.directAffineEuclideanBall_smul_subset_of_le_one (τ • A) a
        (by
          dsimp [ρ]
          positivity)
        (by
          dsimp [ρ]
          nlinarith [hσ_lt_one]))

/-- Helper for theorem 9.8 file
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean`: a lattice-free nonsingular
real ellipsoid yields a nonzero integral direction whose width is bounded by the sharp
ellipsoid flatness constant. -/
theorem existsSharpDirection_euclideanEllipsoid
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : IsUnit C.det)
    (hfree : ¬ contains_integral_point (euclidean_ellipsoid C a)) :
    ∃ d : Fin n → ℤ,
      d ≠ 0 ∧
        directional_width (euclidean_ellipsoid C a) d ≤ ellipsoid_flatness_bound n := by
  let A : Matrix (Fin n) (Fin n) ℝ := C⁻¹
  have hA : IsUnit A.det := by
    -- The inverse shape remains nonsingular.
    simpa [A] using Matrix.isUnit_nonsing_inv_det C hC
  have hfreeBall :
      ¬ contains_integral_point (FlatnessSupport.directAffineEuclideanBall A a) := by
    -- Rewrite the source-facing ellipsoid into the direct-ball model used by Theorem 9.7.
    simpa [A, euclideanEllipsoid_eq_directAffineEuclideanBallInv C a hC] using hfree
  rcases existsLatticeFreeExpansion_directAffineEuclideanBall A a hA hfreeBall with
    ⟨τ, hτ_gt_one, hτ_lt_two, hτ_free⟩
  rcases existsRationalOuterSupportEllipsoid_of_directAffineBall A a hA hτ_gt_one with
    ⟨Q, hQ_unit, hsubsetOuter, houterSubset⟩
  have hQ_free :
      ¬ contains_integral_point (FlatnessSupport.euclideanEllipsoid (Q.map (Rat.castHom ℝ)) a) := by
    -- Lattice-freeness descends from the enlarged direct ball to the containing rational ellipsoid.
    exact not_contains_integral_point_of_subset houterSubset hτ_free
  rcases
      FlatnessSupport.existsFlatDirection_of_latticeFreeEuclideanEllipsoid
        Q a hQ_unit hQ_free with
    ⟨d, hd_ne, hd_width⟩
  have hbound_eq :
      FlatnessSupport.ellipsoidFlatnessBound n = ellipsoid_flatness_bound n := by
    -- Align the Theorem 9.7 constant with the public theorem-side notation.
    cases n with
    | zero =>
        simp [FlatnessSupport.ellipsoidFlatnessBound, ellipsoid_flatness_bound]
    | succ k =>
        simp [FlatnessSupport.ellipsoidFlatnessBound, ellipsoid_flatness_bound]
  have hQ_width :
      directional_width
        (FlatnessSupport.euclideanEllipsoid (Q.map (Rat.castHom ℝ)) a) d ≤
          ellipsoid_flatness_bound n := by
    rw [← hbound_eq]
    exact hd_width
  have hQ_compact :
      IsCompact (FlatnessSupport.euclideanEllipsoid (Q.map (Rat.castHom ℝ)) a) := by
    -- The rational support ellipsoid is closed and sits inside the compact enlarged direct ball.
    exact IsCompact.of_isClosed_subset
      (FlatnessSupport.isCompact_directAffineEuclideanBall (τ • A) a)
      (FlatnessSupport.isClosed_euclideanEllipsoid _ _)
      houterSubset
  have hsubset :
      euclidean_ellipsoid C a ⊆ FlatnessSupport.euclideanEllipsoid (Q.map (Rat.castHom ℝ)) a := by
    -- Re-express the original ellipsoid as the undilated direct ball before applying the bridge.
    simpa [A, euclideanEllipsoid_eq_directAffineEuclideanBallInv C a hC] using hsubsetOuter
  have hmono :
      directional_width (euclidean_ellipsoid C a) d ≤
        directional_width (FlatnessSupport.euclideanEllipsoid (Q.map (Rat.castHom ℝ)) a) d := by
    -- Width is monotone from the original ellipsoid to its containing rational support ellipsoid.
    exact directionalWidth_mono
      ⟨a, center_mem_euclidean_ellipsoid C a⟩
      hQ_compact
      hsubset
  refine ⟨d, hd_ne, ?_⟩
  -- Transfer the sharp rational ellipsoid bound back along the containment.
  exact le_trans hmono hQ_width

/-- For a nonsingular matrix `C`, the ellipsoid `euclidean_ellipsoid C a` defines a convex body,
so the Chapter 9 lattice-width API applies directly to it. -/
def euclidean_ellipsoid_convex_body
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hC : IsUnit C.det) :
    ConvexBody (Fin n → ℝ) where
  carrier := euclidean_ellipsoid C a
  convex' := convex_euclidean_ellipsoid C a hC
  isCompact' := isCompact_euclidean_ellipsoid C a hC
  nonempty' := ⟨a, center_mem_euclidean_ellipsoid C a⟩

@[simp] theorem coe_euclidean_ellipsoid_convex_body
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hC : IsUnit C.det) :
    (euclidean_ellipsoid_convex_body C a hC : Set (Fin n → ℝ)) = euclidean_ellipsoid C a :=
  rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_8.lean
Theorem 9.8 (Flatness Theorem for Ellipsoids). Let `E ⊆ ℝ^n` be the ellipsoid
`euclidean_ellipsoid C a` for a nonsingular matrix `C`. If `E` does not contain any integral
point, then its lattice width is at most `ellipsoid_flatness_bound n`. The lattice width is taken
for the canonical convex-body owner associated to the nonsingular ellipsoid. -/
theorem euclidean_ellipsoid_lattice_width_le_flatness_bound
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : IsUnit C.det)
    (hfree : ¬ contains_integral_point (euclidean_ellipsoid C a)) :
    lattice_width (euclidean_ellipsoid_convex_body C a hC) ≤ ellipsoid_flatness_bound n := by
  -- Reduce the theorem to the sharp-width witness and a single infimum-insertion step.
  rcases existsSharpDirection_euclideanEllipsoid C a hC hfree with ⟨d, hd, hwidth⟩
  have hbodyWidth :
      directional_width
          ((euclidean_ellipsoid_convex_body C a hC : ConvexBody (Fin n → ℝ)) :
            Set (Fin n → ℝ))
          d ≤
        ellipsoid_flatness_bound n := by
    -- The convex-body owner has the same underlying set as the source-facing ellipsoid.
    simpa [coe_euclidean_ellipsoid_convex_body] using hwidth
  exact latticeWidth_le_of_directionalWidth_le hd hbodyWidth

end Theorem98
