/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Objective
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Polyhedron
import Mathlib.LinearAlgebra.Matrix.DotProduct

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators IntegerVectorNotation Matrix MixedIntegerNotation Pointwise

-- Semantic recall note: `lean_leansearch` was unavailable in this runner, and `tool_search`
-- exposed no deferred Lean semantic-search tools. The declarations below follow the local
-- Chapter 4 product-space and convex-hull conventions for mixed-integer polyhedra.

section Theorem43

variable {m n p : ℕ}

/-- The rational mixed polyhedron
`{(x, y) : ℝ^n × ℝ^p | A x + G y ≤ b}` attached to rational data `A`, `G`, and `b`. -/
def rational_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) :
    Set (MixedRealPoint n p) :=
  {xy |
    (A.map (Rat.castHom ℝ)) *ᵥ xy.1 + (G.map (Rat.castHom ℝ)) *ᵥ xy.2 ≤ fun i ↦ (b i : ℝ)}

/-- Membership in `rational_mixed_polyhedron A G b` is exactly the inequality system
`A x + G y ≤ b` after coercing the rational data to `ℝ`. -/
theorem mem_rational_mixed_polyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ}
    {xy : MixedRealPoint n p} :
    xy ∈ rational_mixed_polyhedron A G b ↔
      (A.map (Rat.castHom ℝ)) *ᵥ xy.1 + (G.map (Rat.castHom ℝ)) *ᵥ xy.2 ≤
        fun i ↦ (b i : ℝ) :=
  Iff.rfl

/-- The mixed-integer points of `P` are the members of `P` whose `x`-block is integral. -/
def mixed_integer_points (P : Set (MixedRealPoint n p)) : Set (MixedRealPoint n p) :=
  P ∩ (ℤ^n×ℝ^p)

/-- Membership in `mixed_integer_points P` means membership in `P` together with integrality of
the `x`-block. -/
theorem mem_mixed_integer_points_iff
    {P : Set (MixedRealPoint n p)}
    {xy : MixedRealPoint n p} :
    xy ∈ mixed_integer_points P ↔ xy ∈ P ∧ xy ∈ (ℤ^n×ℝ^p) :=
  Iff.rfl

/-- Source-facing bridge/view: a subset of `ℝ^n × ℝ^p` is a rational mixed polyhedron when its
canonical flattening in `ℝ^(n + p)` is a rational polyhedron. -/
def is_rational_mixed_polyhedron (P : Set (MixedRealPoint n p)) : Prop :=
  is_rational_polyhedron ((Fin.appendEquiv n p) '' P)

/-- Source-facing expansion of `is_rational_mixed_polyhedron` into a rational mixed-system
presentation. -/
theorem is_rational_mixed_polyhedron_iff
    {P : Set (MixedRealPoint n p)} :
    is_rational_mixed_polyhedron P ↔
      ∃ m : ℕ,
        ∃ A : Matrix (Fin m) (Fin n) ℚ,
          ∃ G : Matrix (Fin m) (Fin p) ℚ,
            ∃ b : Fin m → ℚ,
              P = rational_mixed_polyhedron A G b := by
  constructor
  · rintro ⟨m, M, b, hP⟩
    -- Split every flat rational row into its integer and continuous coordinate blocks.
    let A : Matrix (Fin m) (Fin n) ℚ := fun i j ↦ M i (Fin.castAdd p j)
    let G : Matrix (Fin m) (Fin p) ℚ := fun i j ↦ M i (Fin.natAdd n j)
    refine ⟨m, A, G, b, Set.ext fun xy ↦ ?_⟩
    have hmatrix :
        mixedConstraintMatrix (A.map (Rat.castHom ℝ)) (G.map (Rat.castHom ℝ)) =
          M.map (Rat.castHom ℝ) := by
      ext i j
      refine Fin.addCases ?_ ?_ j
      · intro k
        simp [mixedConstraintMatrix, A]
      · intro k
        simp [mixedConstraintMatrix, G]
    constructor
    · intro hxy
      have hflat : Fin.appendEquiv n p xy ∈ (Fin.appendEquiv n p) '' P :=
        ⟨xy, hxy, rfl⟩
      rw [hP, mem_polyhedron_le_set_iff] at hflat
      rw [mem_rational_mixed_polyhedron_iff, ← mixedConstraintMatrix_mulVec_append,
        hmatrix]
      simpa [Fin.appendEquiv] using hflat
    · intro hxy
      have hflat : Fin.appendEquiv n p xy ∈ (Fin.appendEquiv n p) '' P := by
        rw [hP]
        rw [mem_polyhedron_le_set_iff]
        rw [mem_rational_mixed_polyhedron_iff] at hxy
        have hxy' := hxy
        rw [← mixedConstraintMatrix_mulVec_append] at hxy'
        rw [← hmatrix]
        simpa [Fin.appendEquiv] using hxy'
      rcases hflat with ⟨xy', hxy'P, heq⟩
      exact (Fin.appendEquiv n p).injective heq ▸ hxy'P
  · rintro ⟨m, A, G, b, rfl⟩
    -- Join the two rational blocks to obtain the canonical flat presentation.
    let M : Matrix (Fin m) (Fin (n + p)) ℚ := fun i ↦ Fin.addCases (A i) (G i)
    refine ⟨m, M, b, ?_⟩
    have hmatrix :
        M.map (Rat.castHom ℝ) =
          mixedConstraintMatrix (A.map (Rat.castHom ℝ)) (G.map (Rat.castHom ℝ)) := by
      ext i j
      refine Fin.addCases ?_ ?_ j
      · intro k
        simp [M, mixedConstraintMatrix]
      · intro k
        simp [M, mixedConstraintMatrix]
    have hreal :
        rational_mixed_polyhedron A G b =
          real_mixed_polyhedron (A.map (Rat.castHom ℝ)) (G.map (Rat.castHom ℝ))
            (fun i ↦ (b i : ℝ)) := by
      ext xy
      rw [mem_rational_mixed_polyhedron_iff, mem_real_mixed_polyhedron_iff]
    rw [hreal, image_real_mixed_polyhedron_eq_polyhedron_le_set, hmatrix]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: flattening the mixed ambient
space is linear. -/
private lemma mixedPointFlattening_isLinearMap :
    IsLinearMap ℝ (Fin.appendEquiv (α := ℝ) n p) := by
  refine ⟨?_, ?_⟩
  · intro x y
    -- Addition is preserved separately on the two coordinate blocks.
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]
  · intro a x
    -- Scalar multiplication is preserved by the same blockwise calculation.
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: a flattened mixed point is
mixed-integer exactly when it is feasible and its leading block is integral. -/
private lemma mem_flattenedMixedIntegerPoints_iff
    {P : Set (MixedRealPoint n p)} {u : Fin (n + p) → ℝ} :
    u ∈ (Fin.appendEquiv n p) '' mixed_integer_points P ↔
      u ∈ (Fin.appendEquiv n p) '' P ∧
        (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ ℤ^n := by
  -- Unflatten witnesses in both directions and retain exactly the leading lattice condition.
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    rcases mem_mixed_integer_points_iff.mp hxy with ⟨hxyP, hxyZ⟩
    have hxInteger : (fun i : Fin n ↦ Fin.appendEquiv n p xy (Fin.castAdd p i)) ∈ ℤ^n := by
      rw [mem_mixed_integer_lattice_iff] at hxyZ
      simpa [Fin.appendEquiv] using hxyZ
    exact ⟨⟨xy, hxyP, rfl⟩, hxInteger⟩
  · rintro ⟨⟨xy, hxyP, rfl⟩, hxZ⟩
    refine ⟨xy, mem_mixed_integer_points_iff.mpr ⟨hxyP, ?_⟩, rfl⟩
    rw [mem_mixed_integer_lattice_iff]
    simpa [Fin.appendEquiv] using hxZ

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: the mixed objective is the
ordinary dot product after flattening. -/
private lemma mixedLinearObjective_eq_flatDotProduct
    (c : Fin n → ℝ) (h : Fin p → ℝ) (xy : MixedRealPoint n p) :
    mixed_linear_objective c h xy = Fin.append c h ⬝ᵥ Fin.appendEquiv n p xy := by
  -- Split the flat dot product into its two coordinate blocks.
  simp [mixed_linear_objective, dotProduct, Fin.sum_univ_add, Fin.appendEquiv]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: a linear equivalence transports
extreme subsets exactly. -/
private lemma isExtreme_image_linearEquiv_iff
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) (A B : Set E) :
    IsExtreme ℝ (e '' A) (e '' B) ↔ IsExtreme ℝ A B := by
  -- A linear equivalence identifies the corresponding open segments and memberships.
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hxB
      rcases h.subset ⟨x, hxB, rfl⟩ with ⟨y, hyA, hy⟩
      exact e.injective hy ▸ hyA
    · intro x hxA y hyA z hzB hzSegment
      have hzImage : e z ∈ openSegment ℝ (e x) (e y) := by
        have hzImagePrime : e z ∈ e.toAffineMap '' openSegment ℝ x y :=
          ⟨z, hzSegment, rfl⟩
        rw [image_openSegment] at hzImagePrime
        simpa using hzImagePrime
      rcases h.left_mem_of_mem_openSegment
          ⟨x, hxA, rfl⟩ ⟨y, hyA, rfl⟩ ⟨z, hzB, rfl⟩ hzImage with
        ⟨w, hwB, hw⟩
      exact e.injective hw ▸ hwB
  · intro h
    refine ⟨Set.image_mono h.subset, ?_⟩
    rintro _ ⟨x, hxA, rfl⟩ _ ⟨y, hyA, rfl⟩ _ ⟨z, hzB, rfl⟩ hzSegment
    have hzPreimage : z ∈ openSegment ℝ x y := by
      have hzImage : e z ∈ e.toAffineMap '' openSegment ℝ x y := by
        rw [image_openSegment]
        simpa using hzSegment
      rcases hzImage with ⟨w, hwSegment, hw⟩
      exact e.injective hw ▸ hwSegment
    exact ⟨x, h.left_mem_of_mem_openSegment hxA hyA hzB hzPreimage, rfl⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: minimal faces are preserved and
reflected by a linear equivalence. -/
private lemma isMinimalFaceOf_image_linearEquiv_iff
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) (A B : Set E) :
    IsMinimalFaceOf ℝ (e '' A) (e '' B) ↔ IsMinimalFaceOf ℝ A B := by
  -- Transport nonemptiness, extremality, and inclusion-minimality through the equivalence.
  rw [isMinimalFaceOf_iff, isMinimalFaceOf_iff]
  constructor
  · rintro ⟨hBne, hBextreme, hminimal⟩
    refine ⟨?_, (isExtreme_image_linearEquiv_iff e A B).mp hBextreme, ?_⟩
    · rcases hBne with ⟨_, x, hxB, rfl⟩
      exact ⟨x, hxB⟩
    · intro G hGne hGextreme hGB x hxB
      have hImageGne : (e '' G).Nonempty := hGne.image e
      have hImageGextreme : IsExtreme ℝ (e '' A) (e '' G) :=
        (isExtreme_image_linearEquiv_iff e A G).mpr hGextreme
      have hImageSubset : e '' G ⊆ e '' B := Set.image_mono hGB
      rcases hminimal hImageGne hImageGextreme hImageSubset ⟨x, hxB, rfl⟩ with
        ⟨y, hyG, hy⟩
      exact e.injective hy ▸ hyG
  · rintro ⟨hBne, hBextreme, hminimal⟩
    refine ⟨hBne.image e, (isExtreme_image_linearEquiv_iff e A B).mpr hBextreme, ?_⟩
    intro G hGne hGextreme hGsub
    let H : Set E := e.symm '' G
    have hImageH : e '' H = G := by
      ext y
      simp [H]
    have hHne : H.Nonempty := hGne.image e.symm
    have hHextreme : IsExtreme ℝ A H := by
      apply (isExtreme_image_linearEquiv_iff e A H).mp
      rwa [hImageH]
    have hHsub : H ⊆ B := by
      rintro x ⟨y, hyG, rfl⟩
      have hyImage : y ∈ e '' B := hGsub hyG
      rcases hyImage with ⟨z, hzB, hz⟩
      have hzy : e.symm y = z := by
        rw [← hz, e.symm_apply_apply]
      rwa [hzy]
    have hBsubH : B ⊆ H := hminimal hHne hHextreme hHsub
    rw [← hImageH]
    exact Set.image_mono hBsubH

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: closure under all natural
translates by a direction puts that direction in the recession cone of the convex hull. -/
private lemma natTranslate_mem_recessionCone_convexHull
    {k : ℕ} (X : Set (Fin k → ℝ)) {r : Fin k → ℝ}
    (htranslate : ∀ x ∈ X, ∀ a : ℕ, x + (a : ℝ) • r ∈ X) :
    r ∈ recessionCone (convexHull ℝ X) := by
  rw [mem_recessionCone_iff]
  intro x hx a ha
  obtain ⟨m, hm⟩ := exists_nat_gt a
  have hmCast : a < (m : ℝ) := by exact_mod_cast hm
  have hmPos : 0 < (m : ℝ) := lt_of_le_of_lt ha hmCast
  have hshiftSubset : (m : ℝ) • r +ᵥ X ⊆ X := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [add_comm] using htranslate z hz m
  have hshift : x + (m : ℝ) • r ∈ convexHull ℝ X := by
    have hvadd : (m : ℝ) • r +ᵥ x ∈ (m : ℝ) • r +ᵥ convexHull ℝ X :=
      ⟨x, hx, rfl⟩
    rw [← convexHull_vadd] at hvadd
    have hmono := convexHull_mono hshiftSubset hvadd
    simpa [add_comm] using hmono
  have hratio : a / (m : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ha hmPos.le, (div_le_one hmPos).2 hmCast.le⟩
  have hinterp := (convex_convexHull ℝ X).add_smul_mem hx hshift hratio
  have hscale : (a / (m : ℝ)) * (m : ℝ) = a := by field_simp
  -- Interpolation with a sufficiently distant natural translate gives the real translate.
  simpa [smul_smul, hscale] using hinterp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: the common denominator of a
rational vector is nonzero. -/
private lemma mixedRationalVectorCommonDenominator_ne_zero
    {k : ℕ} (v : Fin k → ℚ) : rational_vector_common_denominator v ≠ 0 := by
  -- Every coordinate denominator is positive, including in the empty-dimensional case.
  have hden : ∀ i ∈ (Finset.univ : Finset (Fin k)), (v i).den ≠ 0 := by
    intro i _
    exact Nat.ne_of_gt (Rat.den_pos (v i))
  rw [rational_vector_common_denominator, Finset.lcm_ne_zero_iff]
  exact hden

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: clearing a rational vector's
common denominator commutes with its cast to `ℝ`. -/
private lemma mixedCommonDenominatorScaledVector_eq_smul_real
    {k : ℕ} (v : Fin k → ℚ) :
    (fun i ↦ (common_denominator_scaled_vector v i : ℝ)) =
      (rational_vector_common_denominator v : ℝ) • (fun i ↦ (v i : ℝ)) := by
  -- Cast the coordinatewise rational clearing-denominators identity to the reals.
  ext i
  have hi := congrFun (common_denominator_scaled_vector_eq_smul v) i
  change ((common_denominator_scaled_vector v i : ℤ) : ℝ) =
    (rational_vector_common_denominator v : ℝ) * (v i : ℝ)
  exact_mod_cast hi

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: clearing denominators does not
change the real cone generated by a finite rational family. -/
private lemma mixedCommonDenominatorScaledRays_eq_finitelyGeneratedCone
    {k q : ℕ} (rays : Fin q → Fin k → ℚ) :
    finitely_generated_cone
        (fun j i ↦ (common_denominator_scaled_vector (rays j) i : ℝ)) =
      finitely_generated_cone (fun j i ↦ (rays j i : ℝ)) := by
  -- Rescale coefficients in each direction to pass between rational and integral rays.
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_finitely_generated_cone_iff.mp hx with ⟨μ, hμ, hrepr⟩
    refine mem_finitely_generated_cone_iff.mpr
      ⟨fun j ↦ μ j * (rational_vector_common_denominator (rays j) : ℝ), ?_, ?_⟩
    · intro j
      exact mul_nonneg (hμ j) (Nat.cast_nonneg _)
    · calc
        x = ∑ j, μ j •
            (fun i ↦ (common_denominator_scaled_vector (rays j) i : ℝ)) := hrepr
        _ = ∑ j, (μ j * (rational_vector_common_denominator (rays j) : ℝ)) •
            (fun i ↦ (rays j i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [mixedCommonDenominatorScaledVector_eq_smul_real, smul_smul]
  · intro x hx
    rcases mem_finitely_generated_cone_iff.mp hx with ⟨μ, hμ, hrepr⟩
    have hD : ∀ j, (rational_vector_common_denominator (rays j) : ℝ) ≠ 0 := by
      intro j
      exact_mod_cast mixedRationalVectorCommonDenominator_ne_zero (rays j)
    refine mem_finitely_generated_cone_iff.mpr
      ⟨fun j ↦ μ j / (rational_vector_common_denominator (rays j) : ℝ), ?_, ?_⟩
    · intro j
      exact div_nonneg (hμ j) (Nat.cast_nonneg _)
    · calc
        x = ∑ j, μ j • (fun i ↦ (rays j i : ℝ)) := hrepr
        _ = ∑ j, (μ j / (rational_vector_common_denominator (rays j) : ℝ)) •
            (fun i ↦ (common_denominator_scaled_vector (rays j) i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [mixedCommonDenominatorScaledVector_eq_smul_real, smul_smul, div_eq_mul_inv,
                mul_assoc, inv_mul_cancel₀ (hD j), mul_one]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: a nonempty rational
polyhedron has finitely many integral recession generators. -/
private lemma existsMixedIntegralRecessionGenerators
    {k : ℕ} (Q : Set (Fin k → ℝ)) (hQ : is_rational_polyhedron Q) (hQne : Q.Nonempty) :
    ∃ q : ℕ, ∃ rays : Fin q → Fin k → ℤ,
      recessionCone Q = finitely_generated_cone (fun j i ↦ (rays j i : ℝ)) := by
  rcases hQ with ⟨m, A, b, rfl⟩
  have hrec :=
    polyhedron_recessionCone_eq_homogeneous_solution_set
      (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) hQne
  rcases exists_rational_matrix_cone_of_rational_matrix_polyhedral_cone A with ⟨q, R, hR⟩
  let raysQ : Fin q → Fin k → ℚ := fun j i ↦ R i j
  let rays : Fin q → Fin k → ℤ := fun j ↦ common_denominator_scaled_vector (raysQ j)
  refine ⟨q, rays, ?_⟩
  -- First obtain rational rays, then clear their common denominators.
  calc
    recessionCone
        (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) =
        matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) := by
          simpa [matrix_polyhedral_cone] using hrec
    _ = (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin k → ℝ)) := hR
    _ = finitely_generated_cone (fun j i ↦ (raysQ j i : ℝ)) := by
          simpa [raysQ] using
            (finitely_generated_cone_eq_matrix_cone
              (fun j : Fin q ↦ fun i : Fin k ↦ (raysQ j i : ℝ))).symm
    _ = finitely_generated_cone (fun j i ↦ (rays j i : ℝ)) := by
          simpa [rays] using
            (mixedCommonDenominatorScaledRays_eq_finitelyGeneratedCone raysQ).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: a cone generated by recession
directions is contained in the recession cone. -/
private lemma mixedFinitelyGeneratedCone_subset_recessionCone
    {k q : ℕ} {Q : Set (Fin k → ℝ)} {rays : Fin q → Fin k → ℝ}
    (hgen : ∀ j, rays j ∈ recessionCone Q) :
    finitely_generated_cone rays ⊆ recessionCone Q := by
  -- The recession pointed cone absorbs nonnegative finite linear combinations.
  intro x hx
  rcases mem_finitely_generated_cone_iff.mp hx with ⟨μ, hμ, rfl⟩
  change (∑ j, μ j • rays j) ∈ recessionPointedCone ℝ Q
  exact Submodule.sum_mem _ fun j _ ↦ smul_mem_recessionCone (hgen j) (hμ j)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: integral-translation stability
of `X` transfers all rational-polyhedral recession directions to `convexHull ℝ X`. -/
private lemma rationalPolyhedronRecessionDirections_mem_hullRecessionCone
    {k : ℕ} (Q X : Set (Fin k → ℝ))
    (hQ : is_rational_polyhedron Q) (hXne : X.Nonempty) (hXQ : X ⊆ Q)
    (htranslate : ∀ x ∈ X, ∀ z : Fin k → ℤ,
      (fun i ↦ (z i : ℝ)) ∈ recessionCone Q →
        ∀ a : ℕ, x + (a : ℝ) • (fun i ↦ (z i : ℝ)) ∈ X) :
    recessionCone Q ⊆ recessionCone (convexHull ℝ X) := by
  -- Generate the rational recession cone by integral rays and treat each ray separately.
  have hQne : Q.Nonempty := by
    rcases hXne with ⟨x, hx⟩
    exact ⟨x, hXQ hx⟩
  rcases existsMixedIntegralRecessionGenerators Q hQ hQne with ⟨q, rays, hrec⟩
  rw [hrec]
  refine mixedFinitelyGeneratedCone_subset_recessionCone ?_
  intro j
  have hjQ : (fun i ↦ (rays j i : ℝ)) ∈ recessionCone Q := by
    rw [hrec]
    exact subset_cone (Set.range fun j i ↦ (rays j i : ℝ)) (Set.mem_range_self j)
  exact natTranslate_mem_recessionCone_convexHull X (htranslate · · (rays j) hjQ)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: conic combinations of a set of
recession directions are recession directions. -/
private lemma mixedCone_subset_recessionCone_of_subset
    {k : ℕ} (Q Y : Set (Fin k → ℝ)) (hY : Y ⊆ recessionCone Q) :
    cone Y ⊆ recessionCone Q := by
  -- Interpret the finite conic combination inside the recession pointed cone.
  intro d hd
  rcases mem_cone_iff.mp hd with ⟨q, rays, hrays, hcomb⟩
  change d ∈ (recessionPointedCone ℝ Q : Set (Fin k → ℝ))
  exact PointedCone.conicCombination_mem (fun j ↦ hY (hrays j)) hcomb

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: every lineality direction is a
recession direction. -/
private lemma mixedLinealitySpace_subset_recessionCone
    {k : ℕ} (Q : Set (Fin k → ℝ)) : linealitySpace Q ⊆ recessionCone Q := by
  -- Forget the negative-time half of the lineality condition.
  intro d hd
  rw [mem_linealitySpace_iff] at hd
  rw [mem_recessionCone_iff]
  intro x hx a _
  exact hd hx a

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: adding two recession directions
to a point preserves membership. -/
private lemma mixedAddAdd_mem_of_mem_recessionCone
    {k : ℕ} (Q : Set (Fin k → ℝ)) {q d l : Fin k → ℝ}
    (hq : q ∈ Q) (hd : d ∈ recessionCone Q) (hl : l ∈ recessionCone Q) :
    q + d + l ∈ Q := by
  -- Apply the two recession directions successively at scalar one.
  have hqd : q + d ∈ Q := by
    have hstep := (mem_recessionCone_iff.mp hd) hq 1 zero_le_one
    simpa using hstep
  have hqdl := (mem_recessionCone_iff.mp hl) hqd 1 zero_le_one
  simpa using hqdl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: the rank of the lineality space
used by the quotient decomposition. -/
private noncomputable abbrev mixedLinealityRank
    {k : ℕ} (Q : Set (Fin k → ℝ)) : ℕ :=
  Module.finrank ℝ (linealitySubmodule Q)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: a set meets every minimal face
of a polyhedron. -/
private def mixedMeetsEveryMinimalFace
    {k : ℕ} (Q X : Set (Fin k → ℝ)) : Prop :=
  ∀ F, IsMinimalFaceOf ℝ Q F → ∃ x, x ∈ X ∧ x ∈ F

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: a set meets every relevant
one-dimensional enlargement of lineality in the recession cone. -/
private def mixedMeetsEverySuccessorRecessionFace
    {k : ℕ} (Q Y : Set (Fin k → ℝ)) : Prop :=
  ∀ R, IsExposed ℝ (recessionCone Q) R →
    Module.finrank ℝ (affineSpan ℝ R).direction = mixedLinealityRank Q + 1 →
      ∃ y, y ∈ Y ∧ y ∈ R ∧ y ∉ linealitySpace Q

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: a recession face one dimension
larger than lineality contains a nonlineality direction. -/
private lemma mixedExposedRecessionFace_exists_not_mem_lineality
    {k : ℕ} (Q R : Set (Fin k → ℝ))
    (hdim : Module.finrank ℝ (affineSpan ℝ R).direction = mixedLinealityRank Q + 1) :
    ∃ z, z ∈ R ∧ z ∉ linealitySpace Q := by
  -- Containment in lineality would contradict the strict one-dimensional rank increase.
  have hRne : R.Nonempty := by
    by_contra hempty
    have hzero : Module.finrank ℝ (affineSpan ℝ R).direction = 0 := by
      simp [Set.not_nonempty_iff_eq_empty.mp hempty]
    omega
  by_contra hnone
  have hsubset : R ⊆ linealitySpace Q := by
    intro z hz
    by_contra hznot
    exact hnone ⟨z, hz, hznot⟩
  have haffine : affineSpan ℝ R ≤ affineSpan ℝ (linealitySpace Q) :=
    affineSpan_mono ℝ hsubset
  have hdir : (affineSpan ℝ R).direction ≤ linealitySubmodule Q := by
    have hdirBridge := AffineSubspace.direction_le haffine
    have haffineLineality :
        affineSpan ℝ (linealitySpace Q) = (linealitySubmodule Q).toAffineSubspace := by
      rw [show linealitySpace Q = (linealitySubmodule Q : Set (Fin k → ℝ)) from
        (coe_linealitySubmodule Q).symm]
      exact AffineSubspace.affineSpan_coe (k := ℝ) (linealitySubmodule Q).toAffineSubspace
    rw [haffineLineality, Submodule.toAffineSubspace_direction] at hdirBridge
    exact hdirBridge
  have hrank :
      Module.finrank ℝ (affineSpan ℝ R).direction ≤ mixedLinealityRank Q := by
    simpa [mixedLinealityRank] using Submodule.finrank_mono hdir
  omega

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: after quotienting by
lineality, minimal-face and recession-face coverage control the pointed image. -/
private lemma mixedLinealityQuotientImage_subset_of_generatorCoverage
    {k : ℕ} (Q X Y : Set (Fin k → ℝ))
    (hQpoly : is_polyhedron Q) (hQne : Q.Nonempty)
    (hXfaces : mixedMeetsEveryMinimalFace Q X)
    (hYfaces : mixedMeetsEverySuccessorRecessionFace Q Y) :
    linealityQuotientCoordinateMap Q '' Q ⊆
      convexHull ℝ (linealityQuotientCoordinateMap Q '' X) +
        cone (linealityQuotientCoordinateMap Q '' Y) := by
  -- Quotient by lineality, then cover vertices and extreme rays by the chosen generators.
  let π := linealityQuotientCoordinateMap Q
  let Qbar : Set (Fin (Module.finrank ℝ ((Fin k → ℝ) ⧸ linealitySubmodule Q)) → ℝ) :=
    π '' Q
  have hQbarne : Qbar.Nonempty := hQne.image π
  have hQbarpoly : is_polyhedron Qbar :=
    linearImage_isPolyhedron_of_polyhedron π Q hQpoly
  have hQbarrec : recessionCone Qbar = π '' recessionCone Q :=
    recessionCone_linearImage_eq_image_recessionCone_of_polyhedron π Q hQpoly hQne
  have hImagePointed : is_pointed (π '' recessionCone Q) :=
    linealityQuotientCoordinateImage_recessionCone_pointed Q
  have hQbarpointed : is_pointed Qbar := by
    rw [is_pointed_iff_eq_zero_of_mem_linealitySpace] at hImagePointed ⊢
    intro d hd
    apply hImagePointed d
    rw [← hQbarrec, linealitySpace_recessionCone_eq]
    exact hd
  have hImagePolyhedral : is_polyhedral_cone (π '' recessionCone Q) := by
    have hrecPolyhedral :=
      recessionCone_isPolyhedral_of_polyhedron_nonempty Qbar hQbarpoly hQbarne
    rwa [hQbarrec] at hrecPolyhedral
  have hdecomp :=
    pointedPolyhedron_subset_convexHull_extremePoints_add_cone_extremeRays
      Qbar hQbarne hQbarpoly hQbarpointed
  have hvertices : Qbar.extremePoints ℝ ⊆ π '' X := by
    intro q hq
    let F : Set (Fin k → ℝ) := Q ∩ π ⁻¹' ({q} : Set _)
    have hF : IsMinimalFaceOf ℝ Q F :=
      linealityQuotientExtremePointFiber_isMinimalFace Q hq
    obtain ⟨x, hxX, hxF⟩ := hXfaces F hF
    have hπx : π x = q := by simpa [F, π] using hxF.2
    exact ⟨x, hxX, hπx⟩
  have hrays : {d | IsExtremeRayOfCone (recessionCone Qbar) d} ⊆ cone (π '' Y) := by
    intro d hd
    have hdImage : IsExtremeRayOfCone (π '' recessionCone Q) d := by
      rwa [← hQbarrec]
    have hfiber :=
      linealityQuotientExtremeRayFiber_isExposed_finrank
        Q hImagePolyhedral hImagePointed hdImage
    have hfiberDim :
        Module.finrank ℝ (affineSpan ℝ (recessionCone Q ∩ π ⁻¹' ray d)).direction =
          mixedLinealityRank Q + 1 := by
      simpa [mixedLinealityRank] using hfiber.2
    obtain ⟨y, hyY, hyFiber, hyNot⟩ :=
      hYfaces (recessionCone Q ∩ π ⁻¹' ray d) hfiber.1 hfiberDim
    rcases mem_ray_iff.mp hyFiber.2 with ⟨μ, hμ, hπy⟩
    have hμpos : 0 < μ := by
      apply lt_of_le_of_ne hμ
      intro hμzero
      have hπyzero : π y = 0 := by rw [hπy, ← hμzero, zero_smul]
      apply hyNot
      apply mem_linealitySubmodule_iff.mp
      rw [← linealityQuotientCoordinateMap_ker Q, LinearMap.mem_ker]
      exact hπyzero
    have hπycone : π y ∈ cone (π '' Y) := subset_cone _ ⟨y, hyY, rfl⟩
    have hscaled : μ⁻¹ • π y ∈ cone (π '' Y) :=
      cone_smul_mem hπycone (inv_nonneg.mpr hμpos.le)
    have hscale : μ⁻¹ • π y = d := by
      rw [hπy, smul_smul, inv_mul_cancel₀ hμpos.ne', one_smul]
    rwa [hscale] at hscaled
  intro q hq
  rcases hdecomp hq with ⟨u, hu, v, hv, huv⟩
  exact Set.mem_add.mpr
    ⟨u, convexHull_mono hvertices hu, v, cone_min hrays hv, huv⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: covered point and recession
generators give the required Minkowski decomposition inclusion. -/
private lemma mixedPolyhedron_subset_convexHull_add_cone_add_lineality
    {k : ℕ} (Q X Y : Set (Fin k → ℝ))
    (hQpoly : is_polyhedron Q) (hQne : Q.Nonempty)
    (hYrec : Y ⊆ recessionCone Q)
    (hXfaces : mixedMeetsEveryMinimalFace Q X)
    (hYfaces : mixedMeetsEverySuccessorRecessionFace Q Y) :
    Q ⊆ convexHull ℝ X + cone Y + linealitySpace Q := by
  -- Lift the pointed quotient decomposition and record the lost kernel as lineality.
  rcases hQpoly with ⟨m, A, b, rfl⟩
  intro x hx
  let π := linealityQuotientCoordinateMap (polyhedron_le_set A b)
  have hxq : π x ∈ convexHull ℝ (π '' X) + cone (π '' Y) :=
    mixedLinealityQuotientImage_subset_of_generatorCoverage
      (polyhedron_le_set A b) X Y ⟨m, A, b, rfl⟩ hQne hXfaces hYfaces
      ⟨x, hx, rfl⟩
  rcases Set.mem_add.mp hxq with ⟨u, hu, v, hv, huv⟩
  have hvImage : v ∈ π '' recessionCone (polyhedron_le_set A b) :=
    mem_linealityQuotientCoordinateImage_recessionCone_of_mem_coneImage
      (polyhedron_le_set A b) Y hYrec hv
  rcases hvImage with ⟨d, hdrec, hdmap⟩
  have hxdMap : π (x - d) ∈ convexHull ℝ (π '' X) := by
    have hmap : π (x - d) = u := by
      calc
        π (x - d) = π x - π d := by simp [π]
        _ = (u + v) - v := by rw [← huv, hdmap]
        _ = u := by abel
    simpa [hmap] using hu
  have hxd : x - d ∈ convexHull ℝ X + linealitySpace (polyhedron_le_set A b) :=
    mem_convexHull_add_lineality_of_linealityQuotientCoordinateMap_mem_convexHullImage
      (polyhedron_le_set A b) X hxdMap
  have hd : d ∈ cone Y + linealitySpace (polyhedron_le_set A b) := by
    have hdCone :
        linealityQuotientCoordinateMap (polyhedron_le_set A b) d ∈
          cone (linealityQuotientCoordinateMap (polyhedron_le_set A b) '' Y) := by
      rw [hdmap]
      exact hv
    exact mem_cone_add_lineality_of_linealityQuotientCoordinateMap_mem_coneImage
      (polyhedron_le_set A b) Y hdrec hdCone
  rcases Set.mem_add.mp hxd with ⟨c, hc, l₁, hl₁, hxdEq⟩
  rcases Set.mem_add.mp hd with ⟨r, hr, l₂, hl₂, hdEq⟩
  have hl : l₁ + l₂ ∈ linealitySpace (polyhedron_le_set A b) := by
    rw [← mem_linealitySubmodule_iff] at hl₁ hl₂ ⊢
    exact add_mem hl₁ hl₂
  refine Set.mem_add.mpr ⟨c + r, Set.mem_add.mpr ⟨c, hc, r, hr, rfl⟩,
    l₁ + l₂, hl, ?_⟩
  calc
    (c + r) + (l₁ + l₂) = (c + l₁) + (r + l₂) := by abel
    _ = (x - d) + d := by rw [← hxdEq, ← hdEq]
    _ = x := by abel

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: every finite system of linear
inequalities defines a convex set. -/
private lemma mixedPolyhedronConvex
    {k m : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  -- Verify convexity row by row using the two endpoint inequalities.
  intro x hx y hy a₁ a₂ ha₁ ha₂ haSum i
  have hxi : (Matrix.mulVec A x) i ≤ b i := hx i
  have hyi : (Matrix.mulVec A y) i ≤ b i := hy i
  calc
    (Matrix.mulVec A (a₁ • x + a₂ • y)) i =
        a₁ * (Matrix.mulVec A x) i + a₂ * (Matrix.mulVec A y) i := by
          calc
            ∑ j, A i j * (a₁ * x j + a₂ * y j) =
                ∑ j, (a₁ * (A i j * x j) + a₂ * (A i j * y j)) := by
                  refine Finset.sum_congr rfl ?_
                  intro j _
                  ring
            _ = a₁ * ∑ j, A i j * x j + a₂ * ∑ j, A i j * y j := by
                  simp [Finset.mul_sum, Finset.sum_add_distrib]
            _ = a₁ * (Matrix.mulVec A x) i + a₂ * (Matrix.mulVec A y) i := by
                  simp [Matrix.mulVec, dotProduct]
    _ ≤ a₁ * b i + a₂ * b i :=
      add_le_add (mul_le_mul_of_nonneg_left hxi ha₁) (mul_le_mul_of_nonneg_left hyi ha₂)
    _ = (a₁ + a₂) * b i := by ring
    _ = b i := by rw [haSum, one_mul]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean`: a rational polyhedron whose
minimal faces meet a recession-stable generator set is its convex hull. -/
private lemma rationalPolyhedron_eq_convexHull_of_meetsMinimalFaces_of_integerTranslations
    {k : ℕ} (Q X : Set (Fin k → ℝ))
    (hQ : is_rational_polyhedron Q) (hXQ : X ⊆ Q)
    (hfaces : mixedMeetsEveryMinimalFace Q X)
    (htranslate : ∀ x ∈ X, ∀ z : Fin k → ℤ,
      (fun i ↦ (z i : ℝ)) ∈ recessionCone Q →
        ∀ a : ℕ, x + (a : ℝ) • (fun i ↦ (z i : ℝ)) ∈ X) :
    Q = convexHull ℝ X := by
  -- The nonempty case combines generator coverage with integral recession stability.
  by_cases hQne : Q.Nonempty
  · rcases hQ with ⟨m, A, b, hQeq⟩
    have hQpoly : is_polyhedron Q :=
      ⟨m, A.map (Rat.castHom ℝ), (fun i ↦ (b i : ℝ)), hQeq⟩
    have hQconvex : Convex ℝ Q := by
      rw [hQeq]
      exact mixedPolyhedronConvex _ _
    have hrecessionFaces : mixedMeetsEverySuccessorRecessionFace Q (recessionCone Q) := by
      intro R hR hdim
      obtain ⟨y, hyR, hyNot⟩ :=
        mixedExposedRecessionFace_exists_not_mem_lineality Q R hdim
      exact ⟨y, hR.subset hyR, hyR, hyNot⟩
    have hdecomp :
        Q ⊆ convexHull ℝ X + cone (recessionCone Q) + linealitySpace Q :=
      mixedPolyhedron_subset_convexHull_add_cone_add_lineality
        Q X (recessionCone Q) hQpoly hQne (fun _ h ↦ h) hfaces hrecessionFaces
    obtain ⟨q, hqQ⟩ := hQne
    have hqDecomp : q ∈ convexHull ℝ X + cone (recessionCone Q) + linealitySpace Q :=
      hdecomp hqQ
    rcases Set.mem_add.mp hqDecomp with ⟨u, hu, _, _, _⟩
    rcases Set.mem_add.mp hu with ⟨x, hxHull, _, _, _⟩
    have hXne : X.Nonempty := convexHull_nonempty_iff.mp ⟨x, hxHull⟩
    have hrec : recessionCone Q ⊆ recessionCone (convexHull ℝ X) :=
      rationalPolyhedronRecessionDirections_mem_hullRecessionCone
        Q X ⟨m, A, b, hQeq⟩ hXne hXQ htranslate
    have hconeRec : cone (recessionCone Q) ⊆ recessionCone (convexHull ℝ X) :=
      mixedCone_subset_recessionCone_of_subset _ _ hrec
    have hlinealityRec : linealitySpace Q ⊆ recessionCone (convexHull ℝ X) :=
      fun _ hl ↦ hrec (mixedLinealitySpace_subset_recessionCone Q hl)
    apply Set.Subset.antisymm
    · intro x hxQ
      rcases Set.mem_add.mp (hdecomp hxQ) with ⟨u, hu, l, hl, rfl⟩
      rcases Set.mem_add.mp hu with ⟨q, hq, d, hd, rfl⟩
      exact mixedAddAdd_mem_of_mem_recessionCone
        (convexHull ℝ X) hq (hconeRec hd) (hlinealityRec hl)
    · exact convexHull_min hXQ hQconvex
  · have hQempty : Q = ∅ := Set.not_nonempty_iff_eq_empty.mp hQne
    have hXnot : ¬ X.Nonempty := by
      intro hXne
      rcases hXne with ⟨x, hx⟩
      exact hQne ⟨x, hXQ hx⟩
    have hXempty : X = ∅ := Set.not_nonempty_iff_eq_empty.mp hXnot
    simp [hQempty, hXempty]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_3.lean.
Theorem 4.3 (1). Let `P ⊆ ℝ^n × ℝ^p` be a rational polyhedron, and let
`S := mixed_integer_points P`. Then `P = conv(S)` if and only if every minimal face of `P`
contains a point of `S`. -/
theorem mixed_integer_hull_eq_iff_minimal_faces_contain_mixed_integer_point
    (P : Set (MixedRealPoint n p))
    (hP : is_rational_mixed_polyhedron P) :
    P = convexHull ℝ (mixed_integer_points P) ↔
      ∀ F : Set (MixedRealPoint n p), IsMinimalFaceOf ℝ P F →
        ∃ xy : MixedRealPoint n p, xy ∈ F ∧ xy ∈ mixed_integer_points P := by
  constructor
  · intro hHull F hF
    -- Extremality prevents a convex combination of generators outside `F` from entering `F`.
    obtain ⟨q, hqF⟩ := hF.nonempty
    have hqHull : q ∈ convexHull ℝ (mixed_integer_points P) := by
      rw [← hHull]
      exact hF.isExtreme.subset hqF
    by_contra hNoPoint
    have hgeneratorsOutside : mixed_integer_points P ⊆ P \ F := by
      intro xy hxy
      refine ⟨(mem_mixed_integer_points_iff.mp hxy).1, ?_⟩
      intro hxyF
      exact hNoPoint ⟨xy, hxyF, hxy⟩
    have hPconvex : Convex ℝ P := by
      rw [hHull]
      exact convex_convexHull ℝ (mixed_integer_points P)
    have houtside : q ∈ P \ F :=
      convexHull_min hgeneratorsOutside (hF.isExtreme.convex_diff hPconvex) hqHull
    exact houtside.2 hqF
  · intro hfaces
    let e : MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
      (Fin.appendEquiv n p).toLinearEquiv mixedPointFlattening_isLinearMap
    let Q : Set (Fin (n + p) → ℝ) := e '' P
    let X : Set (Fin (n + p) → ℝ) := e '' mixed_integer_points P
    have hXQ : X ⊆ Q := by
      rintro _ ⟨xy, hxy, rfl⟩
      exact ⟨xy, (mem_mixed_integer_points_iff.mp hxy).1, rfl⟩
    have hfaceCoverage : mixedMeetsEveryMinimalFace Q X := by
      intro F hF
      let G : Set (MixedRealPoint n p) := e.symm '' F
      have hImageG : e '' G = F := by
        ext u
        simp [G]
      have hG : IsMinimalFaceOf ℝ P G := by
        apply (isMinimalFaceOf_image_linearEquiv_iff e P G).mp
        rwa [hImageG]
      obtain ⟨xy, hxyG, hxyMixed⟩ := hfaces G hG
      have hexyF : e xy ∈ F := by
        rw [← hImageG]
        exact ⟨xy, hxyG, rfl⟩
      exact ⟨e xy, ⟨xy, hxyMixed, rfl⟩, hexyF⟩
    have htranslate : ∀ x ∈ X, ∀ z : Fin (n + p) → ℤ,
        (fun i ↦ (z i : ℝ)) ∈ recessionCone Q →
          ∀ a : ℕ, x + (a : ℝ) • (fun i ↦ (z i : ℝ)) ∈ X := by
      intro x hx z hz a
      have hxDescription :
          x ∈ (Fin.appendEquiv n p) '' P ∧
            (fun i : Fin n ↦ x (Fin.castAdd p i)) ∈ ℤ^n := by
        exact mem_flattenedMixedIntegerPoints_iff.mp hx
      apply mem_flattenedMixedIntegerPoints_iff.mpr
      constructor
      · exact (mem_recessionCone_iff.mp hz) hxDescription.1 a (Nat.cast_nonneg _)
      · rcases mem_integerVectors_iff.mp hxDescription.2 with ⟨u, hu⟩
        refine mem_integerVectors_iff.mpr
          ⟨fun i ↦ u i + (a : ℤ) * z (Fin.castAdd p i), ?_⟩
        funext i
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hu i
    have hQeq : Q = convexHull ℝ X :=
      rationalPolyhedron_eq_convexHull_of_meetsMinimalFaces_of_integerTranslations
        Q X hP hXQ hfaceCoverage htranslate
    -- Injectivity of flattening transports the flat convex-hull equality back to the product.
    apply e.injective.image_injective
    have hImageHull := mixedPointFlattening_isLinearMap.image_convexHull
      (mixed_integer_points P)
    simpa [Q, X, e] using hQeq.trans hImageHull.symm

/-- Theorem 4.3 (2). Let `P ⊆ ℝ^n × ℝ^p` be a rational polyhedron, and let
`S := mixed_integer_points P`. Then `P = conv(S)` if and only if every finite maximum of a linear
objective `(x, y) ↦ c x + h y` over `P` is attained at a point of `S`. -/
theorem mixed_integer_hull_eq_iff_linear_maxima_attained_by_mixed_integer_points
    (P : Set (MixedRealPoint n p))
    (hP : is_rational_mixed_polyhedron P) :
    P = convexHull ℝ (mixed_integer_points P) ↔
      ∀ (c : Fin n → ℝ) (h : Fin p → ℝ) (z : ℝ),
        IsGreatest (mixed_linear_objective c h '' P) z →
          ∃ xy : MixedRealPoint n p,
            xy ∈ mixed_integer_points P ∧ mixed_linear_objective c h xy = z := by
  constructor
  · intro hHull c h z hz
    -- Flatten the objective and transfer greatest-element attainment from a convex hull.
    let e : MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
      (Fin.appendEquiv n p).toLinearEquiv mixedPointFlattening_isLinearMap
    let a : Fin (n + p) → ℝ := Fin.append c h
    have hObjectiveImage (T : Set (MixedRealPoint n p)) :
        mixed_linear_objective c h '' T = (fun u ↦ a ⬝ᵥ u) '' (e '' T) := by
      ext z'
      constructor
      · rintro ⟨xy, hxyT, rfl⟩
        refine ⟨e xy, ⟨xy, hxyT, rfl⟩, ?_⟩
        exact (mixedLinearObjective_eq_flatDotProduct c h xy).symm
      · rintro ⟨_, ⟨xy, hxyT, rfl⟩, rfl⟩
        exact ⟨xy, hxyT, mixedLinearObjective_eq_flatDotProduct c h xy⟩
    have hzHull :
        IsGreatest (mixed_linear_objective c h '' convexHull ℝ (mixed_integer_points P)) z := by
      rwa [← hHull]
    have hFlatHull :
        e '' convexHull ℝ (mixed_integer_points P) =
          convexHull ℝ (e '' mixed_integer_points P) := by
      simpa [e] using
        mixedPointFlattening_isLinearMap.image_convexHull (mixed_integer_points P)
    have hzFlatHull :
        IsGreatest ((fun u ↦ a ⬝ᵥ u) '' convexHull ℝ (e '' mixed_integer_points P)) z := by
      rw [← hFlatHull, ← hObjectiveImage]
      exact hzHull
    have hzFlatPoints :
        IsGreatest ((fun u ↦ a ⬝ᵥ u) '' (e '' mixed_integer_points P)) z :=
      (dotProduct_isGreatest_image_convexHull_iff z).mpr hzFlatHull
    have hzMixedPoints : IsGreatest (mixed_linear_objective c h '' mixed_integer_points P) z := by
      rwa [hObjectiveImage]
    rcases hzMixedPoints.1 with ⟨xy, hxy, hxyValue⟩
    exact ⟨xy, hxy, hxyValue⟩
  · intro hmaxima
    -- It suffices to meet each minimal face; flattening exposes it by an ordinary dot product.
    apply
      (mixed_integer_hull_eq_iff_minimal_faces_contain_mixed_integer_point P hP).mpr
    intro F hF
    let e : MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
      (Fin.appendEquiv n p).toLinearEquiv mixedPointFlattening_isLinearMap
    let Q : Set (Fin (n + p) → ℝ) := e '' P
    let Fflat : Set (Fin (n + p) → ℝ) := e '' F
    have hFflat : IsMinimalFaceOf ℝ Q Fflat := by
      exact (isMinimalFaceOf_image_linearEquiv_iff e P F).mpr hF
    have hQ : is_rational_polyhedron Q := by
      simpa [Q, e, is_rational_mixed_polyhedron] using hP
    rcases hQ with ⟨m, A, b, hQeq⟩
    have hFflatPoly :
        IsMinimalFaceOf ℝ
          (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) Fflat := by
      rwa [← hQeq]
    have hFexposed : IsExposed ℝ Q Fflat := by
      rw [hQeq]
      exact minimal_face_isExposed_of_polyhedron
        (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) Fflat hFflatPoly
    obtain ⟨xyF, hxyF⟩ := hF.nonempty
    have hexyF : e xyF ∈ Fflat := ⟨xyF, hxyF, rfl⟩
    obtain ⟨l, hFflatEq⟩ := hFexposed ⟨e xyF, hexyF⟩
    obtain ⟨a, ha⟩ := strongDual_eq_dotProduct_fin l
    let c : Fin n → ℝ := fun i ↦ a (Fin.castAdd p i)
    let h : Fin p → ℝ := fun i ↦ a (Fin.natAdd n i)
    have hAppend : Fin.append c h = a := by
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [c]
      · intro j
        simp [h]
    have hObjective (xy : MixedRealPoint n p) :
        mixed_linear_objective c h xy = a ⬝ᵥ e xy := by
      rw [mixedLinearObjective_eq_flatDotProduct, hAppend]
      rfl
    have hexyFDescription :
        e xyF ∈ {u : Fin (n + p) → ℝ | u ∈ Q ∧ ∀ v ∈ Q, l v ≤ l u} := by
      rw [← hFflatEq]
      exact hexyF
    have hxFmax :
        IsGreatest (mixed_linear_objective c h '' P)
          (mixed_linear_objective c h xyF) := by
      refine ⟨⟨xyF, hF.isExtreme.subset hxyF, rfl⟩, ?_⟩
      rintro _ ⟨xy, hxyP, rfl⟩
      calc
        mixed_linear_objective c h xy = a ⬝ᵥ e xy := hObjective xy
        _ = l (e xy) := (ha (e xy)).symm
        _ ≤ l (e xyF) := hexyFDescription.2 (e xy) ⟨xy, hxyP, rfl⟩
        _ = a ⬝ᵥ e xyF := ha (e xyF)
        _ = mixed_linear_objective c h xyF := (hObjective xyF).symm
    obtain ⟨xy, hxyMixed, hxyValue⟩ :=
      hmaxima c h (mixed_linear_objective c h xyF) hxFmax
    have hexyQ : e xy ∈ Q :=
      ⟨xy, (mem_mixed_integer_points_iff.mp hxyMixed).1, rfl⟩
    have hexyBound : ∀ v ∈ Q, l v ≤ l (e xy) := by
      intro v hvQ
      rcases hvQ with ⟨y, hyP, rfl⟩
      have hyBound := hxFmax.2
        ⟨y, hyP, rfl⟩
      calc
        l (e y) = a ⬝ᵥ e y := ha (e y)
        _ = mixed_linear_objective c h y := (hObjective y).symm
        _ ≤ mixed_linear_objective c h xyF := hyBound
        _ = mixed_linear_objective c h xy := hxyValue.symm
        _ = a ⬝ᵥ e xy := hObjective xy
        _ = l (e xy) := (ha (e xy)).symm
    have hexyFlat : e xy ∈ Fflat := by
      rw [hFflatEq]
      exact ⟨hexyQ, hexyBound⟩
    rcases hexyFlat with ⟨xy', hxy'F, hxy'⟩
    have hxyEq : xy' = xy := e.injective hxy'
    exact ⟨xy, hxyEq ▸ hxy'F, hxyMixed⟩

end Theorem43

#print axioms is_rational_mixed_polyhedron_iff
#print axioms mixed_integer_hull_eq_iff_minimal_faces_contain_mixed_integer_point
#print axioms mixed_integer_hull_eq_iff_linear_maxima_attained_by_mixed_integer_points
