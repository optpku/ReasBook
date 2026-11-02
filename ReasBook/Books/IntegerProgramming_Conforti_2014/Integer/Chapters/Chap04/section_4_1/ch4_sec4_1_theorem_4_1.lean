import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1.Polyhedron
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1.Integral
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_lemma_1_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_definition_1_37
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_theorem_1_10
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_proposition_3_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_33
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.PointedCore
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.Recession
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.QuotientFaces

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators IntegerVectorNotation Matrix Pointwise

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the declarations
-- below follow the local Chapter 3/4 `Fin n → ℝ` conventions, with `IsGreatest` on the objective
-- image to express the finite attained maximum.

section Theorem41

variable {n : ℕ}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: the common denominator of a
rational vector is nonzero. -/
private lemma rationalVectorCommonDenominator_ne_zero (v : Fin n → ℚ) :
    rational_vector_common_denominator v ≠ 0 := by
  -- Every rational denominator is positive, including in the empty-dimensional case.
  have hden : ∀ i ∈ (Finset.univ : Finset (Fin n)), (v i).den ≠ 0 := by
    intro i _
    exact Nat.ne_of_gt (Rat.den_pos (v i))
  rw [rational_vector_common_denominator, Finset.lcm_ne_zero_iff]
  exact hden

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: clearing the common denominator
commutes with the cast from `ℚ` to `ℝ`. -/
private lemma commonDenominatorScaledVector_eq_smul_real (v : Fin n → ℚ) :
    (fun i ↦ (common_denominator_scaled_vector v i : ℝ)) =
      (rational_vector_common_denominator v : ℝ) • (fun i ↦ (v i : ℝ)) := by
  -- Cast the coordinatewise rational identity supplied by the common-denominator API.
  ext i
  have hi := congrFun (common_denominator_scaled_vector_eq_smul v) i
  change ((common_denominator_scaled_vector v i : ℤ) : ℝ) =
    (rational_vector_common_denominator v : ℝ) * (v i : ℝ)
  exact_mod_cast hi

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: a column-reindexed block
matrix acts only through its leading coordinates. -/
private lemma reindexedBlock_mulVec
    {R ι κ κ₁ κ₂ : Type*}
    [Fintype κ] [Fintype κ₁] [Finite κ₂] [Semiring R]
    (e : κ ≃ κ₁ ⊕ κ₂) (M : Matrix ι κ R) (D : Matrix ι κ₁ R)
    (hblock : Matrix.reindex (Equiv.refl _) e M = Matrix.fromCols D 0)
    (z : κ → R) :
    M *ᵥ z = D *ᵥ (fun i ↦ z (e.symm (Sum.inl i))) := by
  classical
  -- Pull the vector through the column equivalence and then discard the zero block.
  letI : Fintype κ₂ := Fintype.ofFinite κ₂
  have hreindex :=
    Matrix.submatrix_mulVec_equiv M (z ∘ e.symm) (Equiv.refl ι).symm e.symm
  have hcoordinates : (z ∘ e.symm) ∘ e = z := by
    funext j
    exact congrArg z (e.symm_apply_apply j)
  calc
    M *ᵥ z = Matrix.reindex (Equiv.refl _) e M *ᵥ (z ∘ e.symm) := by
      rw [Matrix.reindex_apply, hreindex, Equiv.symm_symm, hcoordinates,
        Equiv.refl_symm]
      rfl
    _ = Matrix.fromCols D 0 *ᵥ (z ∘ e.symm) := by rw [hblock]
    _ = D *ᵥ (fun i ↦ z (e.symm (Sum.inl i))) := by
      simp only [Matrix.fromCols_mulVec, Matrix.zero_mulVec, add_zero]
      rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: a row of the inverse leading
block becomes the corresponding coordinate row after undoing a column reindexing. -/
private lemma inverseRow_vecMul_reindexedBlock
    {k r : ℕ} (e : Fin n ≃ Fin k ⊕ Fin r)
    (M : Matrix (Fin k) (Fin n) ℚ) (D : Matrix (Fin k) (Fin k) ℚ)
    (hblock : Matrix.reindex (Equiv.refl _) e M = Matrix.fromCols D 0)
    (hD : IsUnit D.det) (i : Fin k) :
    (D⁻¹ i) ᵥ* M = fun j ↦ if e j = Sum.inl i then 1 else 0 := by
  classical
  ext j
  have hentry : ∀ a, M a j = Matrix.fromCols D 0 a (e j) := by
    intro a
    have h := congrFun (congrFun hblock a) (e j)
    simpa [Matrix.reindex_apply] using h
  rw [Matrix.vecMul]
  simp_rw [hentry]
  rcases hj : e j with a | b
  · have hinverse := congrFun (congrFun (D.nonsing_inv_mul hD) i) a
    simpa [hj, Matrix.mul_apply, Matrix.one_apply, eq_comm] using hinverse
  · simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: adding a natural multiple of an
integral direction preserves the integer lattice. -/
private lemma integerVectors_add_nat_smul
    {x : Fin n → ℝ} (hx : x ∈ ℤ^n) (z : Fin n → ℤ) (m : ℕ) :
    (fun i ↦ x i + (m : ℝ) * (z i : ℝ)) ∈ ℤ^n := by
  -- Lift the operation to the witnessing integer-valued functions.
  rcases mem_integerVectors_iff.mp hx with ⟨a, ha⟩
  refine mem_integerVectors_iff.mpr ⟨fun i ↦ a i + (m : ℤ) * z i, ?_⟩
  ext i
  simp [ha, mul_comm]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: a direction which preserves all
generators under natural translations is a recession direction of their convex hull. -/
private lemma mem_recessionCone_convexHull_of_natTranslate
    (X : Set (Fin n → ℝ)) {r : Fin n → ℝ}
    (htranslate : ∀ x ∈ X, ∀ m : ℕ, x + (m : ℝ) • r ∈ X) :
    r ∈ recessionCone (convexHull ℝ X) := by
  rw [mem_recessionCone_iff]
  intro x hx a ha
  obtain ⟨m, hm⟩ := exists_nat_gt a
  have hm_cast : a < (m : ℝ) := by
    exact_mod_cast hm
  have hm_pos : 0 < (m : ℝ) := lt_of_le_of_lt ha hm_cast
  have hshift_subset : (m : ℝ) • r +ᵥ X ⊆ X := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    simpa [add_comm] using htranslate z hz m
  have hshift : x + (m : ℝ) • r ∈ convexHull ℝ X := by
    have hvadd : (m : ℝ) • r +ᵥ x ∈ (m : ℝ) • r +ᵥ convexHull ℝ X := by
      exact ⟨x, hx, rfl⟩
    rw [← convexHull_vadd] at hvadd
    have hmono := convexHull_mono hshift_subset hvadd
    simpa [add_comm] using hmono
  have hratio : a / (m : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg ha hm_pos.le
    · exact (div_le_one hm_pos).2 hm_cast.le
  have hinterp :=
    (convex_convexHull ℝ X).add_smul_mem hx hshift hratio
  have hratio_scale : (a / (m : ℝ)) * (m : ℝ) = a := by
    field_simp
  -- Interpolation between the original point and its integral translate gives the requested one.
  simpa [smul_smul, hratio_scale] using hinterp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: nonnegative combinations of
listed recession directions remain recession directions. -/
private lemma finitelyGeneratedCone_subset_recessionCone
    {q : ℕ} {Q : Set (Fin n → ℝ)} {rays : Fin q → Fin n → ℝ}
    (hgen : ∀ j, rays j ∈ recessionCone Q) :
    finitely_generated_cone rays ⊆ recessionCone Q := by
  intro x hx
  rcases mem_finitely_generated_cone_iff.mp hx with ⟨μ, hμ, rfl⟩
  -- Use the pointed-cone structure to sum the nonnegative scalar multiples.
  change (∑ j, μ j • rays j) ∈ recessionPointedCone ℝ Q
  exact Submodule.sum_mem _ fun j _ ↦ smul_mem_recessionCone (hgen j) (hμ j)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: clearing denominators of every
listed rational ray does not change the real cone they generate. -/
private lemma commonDenominatorScaledRays_eq_finitelyGeneratedCone
    {q : ℕ} (rays : Fin q → Fin n → ℚ) :
    finitely_generated_cone
        (fun j i ↦ (common_denominator_scaled_vector (rays j) i : ℝ)) =
      finitely_generated_cone (fun j i ↦ (rays j i : ℝ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_finitely_generated_cone_iff.mp hx with ⟨μ, hμ, hrepr⟩
    refine mem_finitely_generated_cone_iff.mpr
      ⟨fun j ↦ μ j * (rational_vector_common_denominator (rays j) : ℝ), ?_, ?_⟩
    · intro j
      exact mul_nonneg (hμ j) (Nat.cast_nonneg _)
    · calc
        x = ∑ j, μ j • (fun i ↦ (common_denominator_scaled_vector (rays j) i : ℝ)) :=
          hrepr
        _ = ∑ j, (μ j * (rational_vector_common_denominator (rays j) : ℝ)) •
            (fun i ↦ (rays j i : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [commonDenominatorScaledVector_eq_smul_real, smul_smul]
  · intro x hx
    rcases mem_finitely_generated_cone_iff.mp hx with ⟨μ, hμ, hrepr⟩
    have hD : ∀ j, (rational_vector_common_denominator (rays j) : ℝ) ≠ 0 := by
      intro j
      exact_mod_cast rationalVectorCommonDenominator_ne_zero (rays j)
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
              rw [commonDenominatorScaledVector_eq_smul_real, smul_smul, div_eq_mul_inv,
                mul_assoc, inv_mul_cancel₀ (hD j), mul_one]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: the recession cone of a
nonempty rational polyhedron has a finite family of integral generators. -/
private lemma existsIntegralRecessionGenerators
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P) (hPne : P.Nonempty) :
    ∃ q : ℕ, ∃ rays : Fin q → Fin n → ℤ,
      recessionCone P =
        finitely_generated_cone (fun j i ↦ (rays j i : ℝ)) := by
  rcases hP with ⟨m, A, b, rfl⟩
  have hrec :=
    polyhedron_recessionCone_eq_homogeneous_solution_set
      (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) hPne
  rcases exists_rational_matrix_cone_of_rational_matrix_polyhedral_cone A with ⟨q, R, hR⟩
  let raysQ : Fin q → Fin n → ℚ := fun j i ↦ R i j
  let rays : Fin q → Fin n → ℤ := fun j ↦ common_denominator_scaled_vector (raysQ j)
  refine ⟨q, rays, ?_⟩
  -- Pass from the homogeneous inequality system to rational rays, then clear denominators.
  calc
    recessionCone
        (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) =
        matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) := by
          simpa [matrix_polyhedral_cone] using hrec
    _ = (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin n → ℝ)) := hR
    _ = finitely_generated_cone (fun j i ↦ (raysQ j i : ℝ)) := by
          simpa [raysQ] using
            (finitely_generated_cone_eq_matrix_cone
              (fun j : Fin q ↦ fun i : Fin n ↦ (raysQ j i : ℝ))).symm
    _ = finitely_generated_cone (fun j i ↦ (rays j i : ℝ)) := by
          simpa [rays] using
            (commonDenominatorScaledRays_eq_finitelyGeneratedCone raysQ).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: recession directions of a
nonempty rational polyhedron remain recession directions of its integer hull. -/
private lemma rationalPolyhedron_recessionCone_le_integerHullRecessionCone
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P) (hPne : P.Nonempty) :
    recessionCone P ⊆ recessionCone (convexHull ℝ (P ∩ ℤ^n)) := by
  rcases existsIntegralRecessionGenerators P hP hPne with ⟨q, rays, hrec⟩
  rw [hrec]
  refine finitelyGeneratedCone_subset_recessionCone ?_
  intro j
  have hjP : (fun i ↦ (rays j i : ℝ)) ∈ recessionCone P := by
    rw [hrec]
    exact subset_cone (Set.range fun j i ↦ (rays j i : ℝ)) (Set.mem_range_self j)
  apply mem_recessionCone_convexHull_of_natTranslate
  intro x hx m
  constructor
  · -- Feasibility follows from the original recession direction.
    exact (mem_recessionCone_iff.mp hjP) hx.1 m (Nat.cast_nonneg _)
  · -- Integrality is stable under a natural multiple of an integral ray.
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      integerVectors_add_nat_smul hx.2 (rays j) m

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: the rank of the lineality space
used in the quotient decomposition. -/
private noncomputable abbrev theorem41LinealityRank (P : Set (Fin n → ℝ)) : ℕ :=
  Module.finrank ℝ (linealitySubmodule P)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: a set meets every minimal face
of a polyhedron. -/
private def theorem41MeetsEveryMinimalFace
    (P X : Set (Fin n → ℝ)) : Prop :=
  ∀ F, IsMinimalFaceOf ℝ P F → ∃ x, x ∈ X ∧ x ∈ F

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: a set meets every relevant
one-dimensional enlargement of the lineality space in the recession cone. -/
private def theorem41MeetsEverySuccessorRecessionFace
    (P Y : Set (Fin n → ℝ)) : Prop :=
  ∀ R, IsExposed ℝ (recessionCone P) R →
    Module.finrank ℝ (affineSpan ℝ R).direction = theorem41LinealityRank P + 1 →
      ∃ y, y ∈ Y ∧ y ∈ R ∧ y ∉ linealitySpace P

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: a relevant exposed recession
face contains a direction outside the ambient lineality space. -/
private lemma exposedRecessionFace_exists_not_mem_lineality
    (P R : Set (Fin n → ℝ))
    (hdim : Module.finrank ℝ (affineSpan ℝ R).direction = theorem41LinealityRank P + 1) :
    ∃ z, z ∈ R ∧ z ∉ linealitySpace P := by
  -- A face contained in lineality cannot have dimension one larger than lineality.
  have hRne : R.Nonempty := by
    by_contra hempty
    have hzero : Module.finrank ℝ (affineSpan ℝ R).direction = 0 := by
      simp [Set.not_nonempty_iff_eq_empty.mp hempty]
    omega
  by_contra hnone
  have hsubset : R ⊆ linealitySpace P := by
    intro z hz
    by_contra hznot
    exact hnone ⟨z, hz, hznot⟩
  have haffine : affineSpan ℝ R ≤ affineSpan ℝ (linealitySpace P) :=
    affineSpan_mono ℝ hsubset
  have hdir : (affineSpan ℝ R).direction ≤ linealitySubmodule P := by
    have hdirBridge := AffineSubspace.direction_le haffine
    have haffineLineality :
        affineSpan ℝ (linealitySpace P) = (linealitySubmodule P).toAffineSubspace := by
      rw [show linealitySpace P = (linealitySubmodule P : Set (Fin n → ℝ)) from
        (coe_linealitySubmodule P).symm]
      exact AffineSubspace.affineSpan_coe (k := ℝ) (linealitySubmodule P).toAffineSubspace
    rw [haffineLineality, Submodule.toAffineSubspace_direction] at hdirBridge
    exact hdirBridge
  have hrank :
      Module.finrank ℝ (affineSpan ℝ R).direction ≤ theorem41LinealityRank P := by
    simpa [theorem41LinealityRank] using Submodule.finrank_mono hdir
  omega

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: after quotienting by lineality,
minimal-face and recession-face coverage control the pointed polyhedron. -/
private lemma linealityQuotientImage_subset_of_generatorCoverage
    (P X Y : Set (Fin n → ℝ))
    (hPpoly : is_polyhedron P) (hPne : P.Nonempty)
    (hXfaces : theorem41MeetsEveryMinimalFace P X)
    (hYfaces : theorem41MeetsEverySuccessorRecessionFace P Y) :
    linealityQuotientCoordinateMap P '' P ⊆
      convexHull ℝ (linealityQuotientCoordinateMap P '' X) +
        cone (linealityQuotientCoordinateMap P '' Y) := by
  -- Quotient by lineality, then cover the pointed quotient by its vertices and extreme rays.
  let π := linealityQuotientCoordinateMap P
  let Q : Set (Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ linealitySubmodule P)) → ℝ) := π '' P
  have hQne : Q.Nonempty := hPne.image π
  have hQpoly : is_polyhedron Q := linearImage_isPolyhedron_of_polyhedron π P hPpoly
  have hQrec : recessionCone Q = π '' recessionCone P :=
    recessionCone_linearImage_eq_image_recessionCone_of_polyhedron π P hPpoly hPne
  have hImagePointed : is_pointed (π '' recessionCone P) :=
    linealityQuotientCoordinateImage_recessionCone_pointed P
  have hQpointed : is_pointed Q := by
    rw [is_pointed_iff_eq_zero_of_mem_linealitySpace] at hImagePointed ⊢
    intro d hd
    apply hImagePointed d
    rw [← hQrec, linealitySpace_recessionCone_eq]
    exact hd
  have hImagePolyhedral : is_polyhedral_cone (π '' recessionCone P) := by
    have hrecPolyhedral := recessionCone_isPolyhedral_of_polyhedron_nonempty Q hQpoly hQne
    rwa [hQrec] at hrecPolyhedral
  have hdecomp :=
    pointedPolyhedron_subset_convexHull_extremePoints_add_cone_extremeRays
      Q hQne hQpoly hQpointed
  have hvertices : Q.extremePoints ℝ ⊆ π '' X := by
    intro q hq
    let F : Set (Fin n → ℝ) := P ∩ π ⁻¹' ({q} : Set _)
    have hF : IsMinimalFaceOf ℝ P F :=
      linealityQuotientExtremePointFiber_isMinimalFace P hq
    obtain ⟨x, hxX, hxF⟩ := hXfaces F hF
    have hπx : π x = q := by
      simpa [F, π] using hxF.2
    exact ⟨x, hxX, hπx⟩
  have hrays :
      {d | IsExtremeRayOfCone (recessionCone Q) d} ⊆ cone (π '' Y) := by
    intro d hd
    have hdImage : IsExtremeRayOfCone (π '' recessionCone P) d := by
      rwa [← hQrec]
    have hfiber :=
      linealityQuotientExtremeRayFiber_isExposed_finrank
        P hImagePolyhedral hImagePointed hdImage
    have hfiberDim :
        Module.finrank ℝ
            (affineSpan ℝ (recessionCone P ∩ π ⁻¹' ray d)).direction =
          theorem41LinealityRank P + 1 := by
      simpa [theorem41LinealityRank] using hfiber.2
    obtain ⟨y, hyY, hyFiber, hyNot⟩ :=
      hYfaces (recessionCone P ∩ π ⁻¹' ray d) hfiber.1 hfiberDim
    rcases mem_ray_iff.mp hyFiber.2 with ⟨μ, hμ, hπy⟩
    have hμpos : 0 < μ := by
      apply lt_of_le_of_ne hμ
      intro hμzero
      have hπyzero : π y = 0 := by
        rw [hπy, ← hμzero, zero_smul]
      apply hyNot
      apply mem_linealitySubmodule_iff.mp
      rw [← linealityQuotientCoordinateMap_ker P, LinearMap.mem_ker]
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
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: covered vertex and recession
generators give the required Minkowski decomposition inclusion. -/
private lemma polyhedron_subset_convexHull_add_cone_add_lineality
    (P X Y : Set (Fin n → ℝ))
    (hPpoly : is_polyhedron P) (hPne : P.Nonempty)
    (hYrec : Y ⊆ recessionCone P)
    (hXfaces : theorem41MeetsEveryMinimalFace P X)
    (hYfaces : theorem41MeetsEverySuccessorRecessionFace P Y) :
    P ⊆ convexHull ℝ X + cone Y + linealitySpace P := by
  -- Lift the quotient decomposition and record the lost kernel component as lineality.
  rcases hPpoly with ⟨m, A, b, rfl⟩
  intro x hx
  let π := linealityQuotientCoordinateMap (polyhedron_le_set A b)
  have hxq : π x ∈ convexHull ℝ (π '' X) + cone (π '' Y) :=
    linealityQuotientImage_subset_of_generatorCoverage
      (polyhedron_le_set A b) X Y ⟨m, A, b, rfl⟩ hPne hXfaces hYfaces
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
  rcases Set.mem_add.mp hd with ⟨k, hk, l₂, hl₂, hdEq⟩
  have hl : l₁ + l₂ ∈ linealitySpace (polyhedron_le_set A b) := by
    rw [← mem_linealitySubmodule_iff] at hl₁ hl₂ ⊢
    exact add_mem hl₁ hl₂
  refine Set.mem_add.mpr ⟨c + k, Set.mem_add.mpr ⟨c, hc, k, hk, rfl⟩,
    l₁ + l₂, hl, ?_⟩
  calc
    (c + k) + (l₁ + l₂) = (c + l₁) + (k + l₂) := by abel
    _ = (x - d) + d := by rw [← hxdEq, ← hdEq]
    _ = x := by abel

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: every set presented by finitely
many linear inequalities is convex. -/
private lemma theorem41PolyhedronConvex
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  intro x hx y hy a₁ a₂ ha₁ ha₂ ha_sum i
  -- Check convexity row by row and use the convex coefficients on each scalar inequality.
  have hx_i : (Matrix.mulVec A x) i ≤ b i := hx i
  have hy_i : (Matrix.mulVec A y) i ≤ b i := hy i
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
      add_le_add (mul_le_mul_of_nonneg_left hx_i ha₁) (mul_le_mul_of_nonneg_left hy_i ha₂)
    _ = (a₁ + a₂) * b i := by ring
    _ = b i := by rw [ha_sum, one_mul]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: taking conic combinations
preserves inclusion in a recession cone. -/
private lemma cone_subset_recessionCone_of_subset
    (Q Y : Set (Fin n → ℝ)) (hY : Y ⊆ recessionCone Q) :
    cone Y ⊆ recessionCone Q := by
  intro d hd
  rcases mem_cone_iff.mp hd with ⟨q, rays, hrays, hcomb⟩
  -- The recession cone's pointed-cone structure absorbs the finite conic combination.
  change d ∈ (recessionPointedCone ℝ Q : Set (Fin n → ℝ))
  exact PointedCone.conicCombination_mem (fun j ↦ hY (hrays j)) hcomb

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: lineality directions are
recession directions. -/
private lemma linealitySpace_subset_recessionCone
    (P : Set (Fin n → ℝ)) : linealitySpace P ⊆ recessionCone P := by
  -- Forget the negative-time half of the lineality condition.
  intro d hd
  rw [mem_linealitySpace_iff] at hd
  rw [mem_recessionCone_iff]
  intro x hx a _
  exact hd hx a

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: adding two recession
directions to a point preserves membership in the underlying set. -/
private lemma add_add_mem_of_mem_recessionCone
    (Q : Set (Fin n → ℝ)) {q d l : Fin n → ℝ}
    (hq : q ∈ Q) (hd : d ∈ recessionCone Q) (hl : l ∈ recessionCone Q) :
    q + d + l ∈ Q := by
  -- Apply the recession property successively to the two directions.
  have hqd : q + d ∈ Q := by
    have hstep := (mem_recessionCone_iff.mp hd) hq 1 zero_le_one
    simpa using hstep
  have hqdl := (mem_recessionCone_iff.mp hl) hqd 1 zero_le_one
  simpa using hqdl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: a rational polyhedron whose
minimal faces all meet its integer points equals the convex hull of those points. -/
private lemma rationalPolyhedron_eq_integerHull_of_meetsMinimalFaces
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P)
    (hfaces : ∀ F, IsMinimalFaceOf ℝ P F → ∃ x ∈ F, x ∈ ℤ^n) :
    P = convexHull ℝ (P ∩ ℤ^n) := by
  -- The nonempty case is controlled by the quotient decomposition and recession inclusion.
  by_cases hPne : P.Nonempty
  · rcases hP with ⟨m, A, b, hP_eq⟩
    have hPpoly : is_polyhedron P :=
      ⟨m, A.map (Rat.castHom ℝ), (fun i ↦ (b i : ℝ)), hP_eq⟩
    have hPconvex : Convex ℝ P := by
      rw [hP_eq]
      exact theorem41PolyhedronConvex _ _
    have hminimal : theorem41MeetsEveryMinimalFace P (P ∩ ℤ^n) := by
      intro F hF
      obtain ⟨x, hxF, hxZ⟩ := hfaces F hF
      exact ⟨x, ⟨hF.isExtreme.subset hxF, hxZ⟩, hxF⟩
    have hrecessionFaces :
        theorem41MeetsEverySuccessorRecessionFace P (recessionCone P) := by
      intro R hR hdim
      obtain ⟨y, hyR, hyNot⟩ := exposedRecessionFace_exists_not_mem_lineality P R hdim
      exact ⟨y, hR.subset hyR, hyR, hyNot⟩
    have hdecomp :
        P ⊆ convexHull ℝ (P ∩ ℤ^n) + cone (recessionCone P) + linealitySpace P :=
      polyhedron_subset_convexHull_add_cone_add_lineality
        P (P ∩ ℤ^n) (recessionCone P) hPpoly hPne (fun _ h ↦ h) hminimal hrecessionFaces
    have hrec := rationalPolyhedron_recessionCone_le_integerHullRecessionCone P
      ⟨m, A, b, hP_eq⟩ hPne
    have hconeRec :
        cone (recessionCone P) ⊆ recessionCone (convexHull ℝ (P ∩ ℤ^n)) :=
      cone_subset_recessionCone_of_subset _ _ hrec
    have hlinealityRec :
        linealitySpace P ⊆ recessionCone (convexHull ℝ (P ∩ ℤ^n)) :=
      fun _ hl ↦ hrec (linealitySpace_subset_recessionCone P hl)
    apply Set.Subset.antisymm
    · intro x hxP
      rcases Set.mem_add.mp (hdecomp hxP) with ⟨u, hu, l, hl, rfl⟩
      rcases Set.mem_add.mp hu with ⟨q, hq, d, hd, rfl⟩
      exact add_add_mem_of_mem_recessionCone _ hq (hconeRec hd) (hlinealityRec hl)
    · -- Convexity of `P` absorbs the convex hull of its integral subset.
      exact convexHull_min Set.inter_subset_left hPconvex
  · -- The empty polyhedron is already the convex hull of its empty integer-point set.
    have hPempty : P = ∅ := Set.not_nonempty_iff_eq_empty.mp hPne
    simp [hPempty]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean.
Theorem 4.1 (1). Let `P` be a rational polyhedron. Then `P` is an integral polyhedron if and only
if every minimal face of `P` contains an integral point. -/
theorem rational_polyhedron_is_integral_iff_minimal_faces_contain_integral_point
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P) :
    is_integral P ↔
      ∀ F, IsMinimalFaceOf ℝ P F → ∃ x ∈ F, x ∈ ℤ^n := by
  constructor
  · intro hIntegral F hF
    -- Extremality prevents a convex combination of outside generators from entering the face.
    obtain ⟨q, hqF⟩ := hF.nonempty
    have hIntegral' : P = convexHull ℝ (P ∩ ℤ^n) := by
      simpa [integerVectors] using (is_integral_iff.mp hIntegral)
    have hqHull : q ∈ convexHull ℝ (P ∩ ℤ^n) := by
      rw [← hIntegral']
      exact hF.isExtreme.subset hqF
    by_contra hNoIntegral
    have hgeneratorsOutside : P ∩ ℤ^n ⊆ P \ F := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      intro hxF
      exact hNoIntegral ⟨x, hxF, hx.2⟩
    rcases hP with ⟨m, A, b, hP_eq⟩
    have hPconvex : Convex ℝ P := by
      rw [hP_eq]
      exact theorem41PolyhedronConvex _ _
    have houtside : q ∈ P \ F :=
      convexHull_min hgeneratorsOutside (hF.isExtreme.convex_diff hPconvex) hqHull
    exact houtside.2 hqF
  · intro hfaces
    -- The decomposition inclusion and recession stability identify `P` with its integer hull.
    exact is_integral_iff.mpr
      (rationalPolyhedron_eq_integerHull_of_meetsMinimalFaces P hP hfaces)

/-- Theorem 4.1 (2). Let `P` be a rational polyhedron. Then `P` is an integral polyhedron if and
only if every finite maximum of a linear objective over `P` is attained at an integral point of
`P`. -/
theorem rational_polyhedron_is_integral_iff_linear_maxima_attained_by_integral_points
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P) :
    is_integral P ↔
      ∀ c z,
        IsGreatest ((c ⬝ᵥ ·) '' P) z →
          ∃ x ∈ P ∩ ℤ^n, c ⬝ᵥ x = z := by
  constructor
  · intro hIntegral c z hz
    have hIntegral' : P = convexHull ℝ (P ∩ ℤ^n) := by
      simpa [integerVectors] using (is_integral_iff.mp hIntegral)
    have hzHull :
        IsGreatest ((c ⬝ᵥ ·) '' convexHull ℝ (P ∩ ℤ^n)) z := by
      rw [← hIntegral']
      exact hz
    have hzIntegerPoints : IsGreatest ((c ⬝ᵥ ·) '' (P ∩ ℤ^n)) z :=
      (dotProduct_isGreatest_image_convexHull_iff z).mpr hzHull
    rcases hzIntegerPoints.1 with ⟨x, hx, hxValue⟩
    -- The generator attaining the hull maximum is the required integral feasible point.
    exact ⟨x, hx, hxValue⟩
  · intro hmaxima
    -- Expose each minimal face by a linear functional and apply the attainment hypothesis.
    apply (rational_polyhedron_is_integral_iff_minimal_faces_contain_integral_point P hP).mpr
    intro F hF
    rcases hP with ⟨m, A, b, hP_eq⟩
    have hFpoly :
        IsMinimalFaceOf ℝ
          (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) F := by
      rwa [← hP_eq]
    have hFexposed : IsExposed ℝ P F := by
      rw [hP_eq]
      exact minimal_face_isExposed_of_polyhedron
        (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) F hFpoly
    obtain ⟨xF, hxF⟩ := hF.nonempty
    obtain ⟨l, hF_eq⟩ := hFexposed ⟨xF, hxF⟩
    obtain ⟨c, hc⟩ := strongDual_eq_dotProduct_fin l
    have hxFmax : IsGreatest ((c ⬝ᵥ ·) '' P) (c ⬝ᵥ xF) := by
      refine ⟨⟨xF, hF.isExtreme.subset hxF, rfl⟩, ?_⟩
      rintro z ⟨y, hyP, rfl⟩
      have hxF' :
          xF ∈ {x : Fin n → ℝ | x ∈ P ∧ ∀ y ∈ P, l y ≤ l x} := by
        rw [← hF_eq]
        exact hxF
      calc
        c ⬝ᵥ y = l y := (hc y).symm
        _ ≤ l xF := hxF'.2 y hyP
        _ = c ⬝ᵥ xF := hc xF
    obtain ⟨x, hxInteger, hxValue⟩ := hmaxima c (c ⬝ᵥ xF) hxFmax
    refine ⟨x, ?_, hxInteger.2⟩
    rw [hF_eq]
    refine ⟨hxInteger.1, ?_⟩
    intro y hyP
    have hyBound : c ⬝ᵥ y ≤ c ⬝ᵥ xF := hxFmax.2 ⟨y, hyP, rfl⟩
    calc
      l y = c ⬝ᵥ y := hc y
      _ ≤ c ⬝ᵥ xF := hyBound
      _ = c ⬝ᵥ x := hxValue.symm
      _ = l x := (hc x).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: a minimal face of a rational
polyhedron is the solution set of rational rows which are valid inequalities on the polyhedron. -/
private lemma rationalMinimalFace_eq_validRationalSystem
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P)
    {F : Set (Fin n → ℝ)} (hF : IsMinimalFaceOf ℝ P F) :
    ∃ k : ℕ, ∃ B : Matrix (Fin k) (Fin n) ℚ, ∃ d : Fin k → ℚ,
      F = {x : Fin n → ℝ |
        B.map (Rat.castHom ℝ) *ᵥ x = fun i ↦ (d i : ℝ)} ∧
      (∀ x ∈ P, B.map (Rat.castHom ℝ) *ᵥ x ≤ fun i ↦ (d i : ℝ)) ∧
      B.rank = k := by
  classical
  -- Reindex the active rational rows by a finite standard type.
  rcases hP with ⟨m, A, b, hP_eq⟩
  have hFpoly :
      IsMinimalFaceOf ℝ
        (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) F := by
    rwa [← hP_eq]
  have hFexposed :=
    minimal_face_isExposed_of_polyhedron
      (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) F hFpoly
  obtain ⟨I, hFslice, -⟩ :=
    (isMinimalFaceOf_iff_exists_eq_submatrix_solution_set_and_rank
      (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) F hFexposed hF.nonempty).mp hFpoly
  let rows := {i : Fin m // i ∈ I}
  let C : Matrix rows (Fin n) ℚ := A.submatrix Subtype.val id
  obtain ⟨g, hg_mem, hg_span, hg_linear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range C.row)
  let k := Module.finrank ℚ (Submodule.span ℚ (Set.range C.row))
  have hg_mem_chosen : ∀ i : Fin k, ∃ j : rows, C.row j = g i := by
    intro i
    simpa [k] using hg_mem i
  let chosen : Fin k → rows := fun i ↦ Classical.choose (hg_mem_chosen i)
  have hchosen : ∀ i, C.row (chosen i) = g i := by
    intro i
    exact Classical.choose_spec (hg_mem_chosen i)
  let B : Matrix (Fin k) (Fin n) ℚ := fun i ↦ C (chosen i)
  let d : Fin k → ℚ := fun i ↦ b (chosen i).1
  have hBrow : B.row = g := by
    funext i
    simpa [B, Matrix.row] using hchosen i
  have hBrank : B.rank = k := by
    have hBlinear : LinearIndependent ℚ B.row := by
      rw [hBrow]
      exact hg_linear
    simpa using hBlinear.rank_matrix
  obtain ⟨x₀, hx₀F⟩ := hF.nonempty
  have hx₀Slice :
      (A.map (Rat.castHom ℝ)).submatrix
          (Subtype.val : rows → Fin m) id *ᵥ x₀ =
        (fun i ↦ (b i : ℝ)) ∘ (Subtype.val : rows → Fin m) := by
    rw [hFslice] at hx₀F
    exact hx₀F
  refine ⟨k, B, d, ?_, ?_, hBrank⟩
  · ext x
    constructor
    · intro hxF
      have hxSlice :
          (A.map (Rat.castHom ℝ)).submatrix
              (Subtype.val : rows → Fin m) id *ᵥ x =
            (fun i ↦ (b i : ℝ)) ∘ (Subtype.val : rows → Fin m) := by
        rw [hFslice] at hxF
        exact hxF
      funext i
      have hi := congrFun hxSlice (chosen i)
      simpa [B, d, C, rows, Matrix.mulVec] using hi
    · intro hx
      have hxSelected : ∀ i,
          (fun j ↦ (g i j : ℝ)) ⬝ᵥ x = (d i : ℝ) := by
        intro i
        have hi := congrFun hx i
        rw [← hchosen i]
        simpa [B, Matrix.row, Matrix.mulVec] using hi
      have hx₀Selected : ∀ i,
          (fun j ↦ (g i j : ℝ)) ⬝ᵥ x₀ = (d i : ℝ) := by
        intro i
        have hi := congrFun hx₀Slice (chosen i)
        rw [← hchosen i]
        simpa [d, C, B, rows, Matrix.row, Matrix.mulVec] using hi
      have hann : ∀ v ∈ Submodule.span ℚ (Set.range g),
          (fun j ↦ (v j : ℝ)) ⬝ᵥ (x - x₀) = 0 := by
        intro v hv
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
        · intro v hv
          rcases hv with ⟨i, rfl⟩
          rw [dotProduct_sub, hxSelected i, hx₀Selected i, sub_self]
        · simp
        · intro u v _ _ hu hv
          calc
            (fun j ↦ ((u + v) j : ℝ)) ⬝ᵥ (x - x₀) =
                (fun j ↦ (u j : ℝ)) ⬝ᵥ (x - x₀) +
                  (fun j ↦ (v j : ℝ)) ⬝ᵥ (x - x₀) := by
                    simp only [dotProduct, Pi.add_apply, Rat.cast_add, add_mul,
                      Finset.sum_add_distrib]
            _ = 0 := by rw [hu, hv, add_zero]
        · intro q v _ hv
          calc
            (fun j ↦ ((q • v) j : ℝ)) ⬝ᵥ (x - x₀) =
                (q : ℝ) * ((fun j ↦ (v j : ℝ)) ⬝ᵥ (x - x₀)) := by
                  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Rat.cast_mul,
                    Finset.mul_sum, mul_assoc]
            _ = 0 := by rw [hv, mul_zero]
      rw [hFslice]
      funext i
      have hrow : C.row i ∈ Submodule.span ℚ (Set.range g) := by
        rw [hg_span]
        exact Submodule.subset_span (Set.mem_range_self i)
      have hzero := hann (C.row i) hrow
      have heq :
          (fun j ↦ (C i j : ℝ)) ⬝ᵥ x =
            (fun j ↦ (C i j : ℝ)) ⬝ᵥ x₀ := by
        rw [dotProduct_sub] at hzero
        exact sub_eq_zero.mp hzero
      have hx₀i := congrFun hx₀Slice i
      simpa [C, rows, Matrix.mulVec] using heq.trans hx₀i
  · intro x hxP
    rw [hP_eq] at hxP
    intro i
    simpa [B, d, C, Matrix.mulVec] using hxP (chosen i).1

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: append the right-hand side to a
rational matrix row so one denominator clears both simultaneously. -/
private def augmentedRationalRow
    {k : ℕ} (B : Matrix (Fin k) (Fin n) ℚ) (d : Fin k → ℚ)
    (i : Fin k) : Fin (n + 1) → ℚ :=
  Fin.lastCases (d i) (B i)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: the cleared augmented row agrees
with denominator scaling on each coefficient. -/
private lemma scaledAugmentedRationalRow_castSucc
    {k : ℕ} (B : Matrix (Fin k) (Fin n) ℚ) (d : Fin k → ℚ)
    (i : Fin k) (j : Fin n) :
    ((common_denominator_scaled_vector (augmentedRationalRow B d i) j.castSucc : ℤ) : ℝ) =
      (rational_vector_common_denominator (augmentedRationalRow B d i) : ℝ) *
        (B i j : ℝ) := by
  -- Specialize the vector denominator identity to an ordinary matrix coordinate.
  have h := congrFun
    (commonDenominatorScaledVector_eq_smul_real (augmentedRationalRow B d i)) j.castSucc
  simpa [augmentedRationalRow] using h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: the last coordinate of a cleared
augmented row is the correspondingly scaled right-hand side. -/
private lemma scaledAugmentedRationalRow_last
    {k : ℕ} (B : Matrix (Fin k) (Fin n) ℚ) (d : Fin k → ℚ)
    (i : Fin k) :
    ((common_denominator_scaled_vector (augmentedRationalRow B d i) (Fin.last n) : ℤ) : ℝ) =
      (rational_vector_common_denominator (augmentedRationalRow B d i) : ℝ) *
        (d i : ℝ) := by
  -- Specialize the same identity to the appended right-hand-side coordinate.
  have h := congrFun
    (commonDenominatorScaledVector_eq_smul_real (augmentedRationalRow B d i)) (Fin.last n)
  simpa [augmentedRationalRow] using h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: an infeasible full-row-rank
rational equality system has an integral row certificate with a nonintegral right-hand side. -/
private lemma existsIntegralRowCertificate_of_fullRowRank
    {k : ℕ} (B : Matrix (Fin k) (Fin n) ℚ) (d : Fin k → ℚ)
    (hB : B.rank = k)
    (hno : ¬ RationalLinearSystem.hasIntegerSolution B d) :
    ∃ u : Fin k → ℝ,
      u ᵥ* (B.map (Rat.castHom ℝ)) ∈ ℤ^n ∧
        u ⬝ᵥ (fun i ↦ (d i : ℝ)) ∉ Set.range (Int.cast : ℤ → ℝ) := by
  classical
  obtain ⟨U, hU, hHNF⟩ :=
    Matrix.exists_unimodular_columnHermiteNormalForm_of_rank_eq B hB
  obtain ⟨r, hshape, D, hblock, htriangular, hpositive, -⟩ :=
    (Matrix.isColumnHermiteNormalForm_iff_exists_block
      (B * U.map (Int.castRingHom ℚ))).mp hHNF
  let e : Fin n ≃ Fin k ⊕ Fin r :=
    (finCongr hshape).trans finSumFinEquiv.symm
  have hDdet : D.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular D htriangular]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hpositive i).ne'
  have hDunit : IsUnit D.det := isUnit_iff_ne_zero.mpr hDdet
  let y : Fin k → ℚ := D⁻¹ *ᵥ d
  have hyNotIntegral : ¬ ∃ z : Fin k → ℤ, (fun i ↦ (z i : ℚ)) = y := by
    rintro ⟨z, hz⟩
    let v : Fin n → ℤ := fun j ↦ Sum.elim z (fun _ ↦ 0) (e j)
    let x : Fin n → ℤ := U *ᵥ v
    apply hno
    refine (RationalLinearSystem.hasIntegerSolution_iff B d).mpr ⟨x, ?_⟩
    have hxCast :
        (fun j ↦ (x j : ℚ)) =
          U.map (Int.castRingHom ℚ) *ᵥ (fun j ↦ (v j : ℚ)) := by
      funext j
      exact RingHom.map_mulVec (Int.castRingHom ℚ) U v j
    have hvHead :
        (fun i ↦ ((v (e.symm (Sum.inl i)) : ℤ) : ℚ)) = y := by
      funext i
      simpa [v, e] using congrFun hz i
    calc
      B *ᵥ (fun j ↦ (x j : ℚ)) =
          B *ᵥ (U.map (Int.castRingHom ℚ) *ᵥ (fun j ↦ (v j : ℚ))) := by
            rw [hxCast]
      _ = (B * U.map (Int.castRingHom ℚ)) *ᵥ (fun j ↦ (v j : ℚ)) := by
            rw [Matrix.mulVec_mulVec]
      _ = D *ᵥ y := by
            rw [reindexedBlock_mulVec e _ D hblock, hvHead]
      _ = d := by
            dsimp [y]
            rw [Matrix.mulVec_mulVec, D.mul_nonsing_inv hDunit, Matrix.one_mulVec]
  have hyCoordinate :
      ∃ i : Fin k, y i ∉ Set.range (Int.cast : ℤ → ℚ) := by
    by_contra h
    push Not at h
    choose z hz using h
    apply hyNotIntegral
    exact ⟨z, funext hz⟩
  obtain ⟨i, hiNonintegral⟩ := hyCoordinate
  let uℚ : Fin k → ℚ := D⁻¹ i
  let pℤ : Fin n → ℤ := fun j ↦ if e j = Sum.inl i then 1 else 0
  let c : Fin n → ℤ := pℤ ᵥ* U⁻¹
  have huBU :
      uℚ ᵥ* (B * U.map (Int.castRingHom ℚ)) =
        fun j ↦ if e j = Sum.inl i then 1 else 0 := by
    exact inverseRow_vecMul_reindexedBlock e _ D hblock hDunit i
  have hpCast :
      (fun j ↦ (pℤ j : ℚ)) = fun j ↦ if e j = Sum.inl i then 1 else 0 := by
    funext j
    by_cases hj : e j = Sum.inl i
    · simp only [pℤ, hj, if_pos]
      exact map_one (Int.castRingHom ℚ)
    · simp only [pℤ, hj]
      exact map_zero (Int.castRingHom ℚ)
  have hcastZero : (Int.castRingHom ℚ) 0 = 0 := map_zero (Int.castRingHom ℚ)
  have hcastOne : (Int.castRingHom ℚ) 1 = 1 := map_one (Int.castRingHom ℚ)
  have hrowRecover :
      uℚ ᵥ* B =
        (fun j ↦ (pℤ j : ℚ)) ᵥ* (U⁻¹.map (Int.castRingHom ℚ)) := by
    calc
      uℚ ᵥ* B = (uℚ ᵥ* B) ᵥ* (1 : Matrix (Fin n) (Fin n) ℚ) := by simp
      _ = (uℚ ᵥ* B) ᵥ*
          (U.map (Int.castRingHom ℚ) * U⁻¹.map (Int.castRingHom ℚ)) := by
            rw [← Matrix.map_mul, U.mul_nonsing_inv hU,
              Matrix.map_one (Int.castRingHom ℚ) hcastZero hcastOne]
      _ = uℚ ᵥ* (B *
          (U.map (Int.castRingHom ℚ) * U⁻¹.map (Int.castRingHom ℚ))) :=
            Matrix.vecMul_vecMul _ _ _
      _ = uℚ ᵥ* ((B * U.map (Int.castRingHom ℚ)) *
          U⁻¹.map (Int.castRingHom ℚ)) := by rw [Matrix.mul_assoc]
      _ = (uℚ ᵥ* (B * U.map (Int.castRingHom ℚ))) ᵥ*
          U⁻¹.map (Int.castRingHom ℚ) := (Matrix.vecMul_vecMul _ _ _).symm
      _ = (fun j ↦ (pℤ j : ℚ)) ᵥ* U⁻¹.map (Int.castRingHom ℚ) := by
            rw [huBU, hpCast]
  have hcCast : (fun j ↦ (c j : ℚ)) = uℚ ᵥ* B := by
    funext j
    rw [hrowRecover]
    simpa [c] using RingHom.map_vecMul (Int.castRingHom ℚ) U⁻¹ pℤ j
  let u : Fin k → ℝ := fun i ↦ (uℚ i : ℝ)
  refine ⟨u, ?_, ?_⟩
  · refine mem_integerVectors_iff.mpr ⟨c, ?_⟩
    funext j
    have hmap := RingHom.map_vecMul (Rat.castHom ℝ) B uℚ j
    calc
      (u ᵥ* B.map (Rat.castHom ℝ)) j = ((uℚ ᵥ* B) j : ℝ) := by
        simpa [u] using hmap.symm
      _ = (c j : ℝ) := by
        rw [← congrFun hcCast j]
        exact Rat.cast_intCast (c j)
      _ = (Int.cast ∘ c) j := rfl
  · rintro ⟨a, ha⟩
    apply hiNonintegral
    refine ⟨a, ?_⟩
    have hvalue : uℚ ⬝ᵥ d = y i := by
      rfl
    have hcast := RingHom.map_dotProduct (Rat.castHom ℝ) uℚ d
    have hreal : ((y i : ℚ) : ℝ) = (a : ℝ) := by
      calc
        ((y i : ℚ) : ℝ) = ((uℚ ⬝ᵥ d : ℚ) : ℝ) :=
          congrArg (Rat.castHom ℝ) hvalue.symm
        _ = u ⬝ᵥ (fun j ↦ (d j : ℝ)) := by simpa [u] using hcast
        _ = (a : ℝ) := ha.symm
    exact Rat.cast_injective hreal.symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: an infeasible integer equality
system made of valid inequalities yields an attained integral objective with nonintegral value. -/
private lemma existsIntegralObjectiveWithNonintegralMaximum_of_noIntegerSolution
    {k : ℕ} (P : Set (Fin n → ℝ))
    (B : Matrix (Fin k) (Fin n) ℚ) (d : Fin k → ℚ)
    (hB : B.rank = k)
    (hvalid : ∀ x ∈ P,
      B.map (Rat.castHom ℝ) *ᵥ x ≤ fun i ↦ (d i : ℝ))
    (hattain : ∃ x ∈ P,
      B.map (Rat.castHom ℝ) *ᵥ x = fun i ↦ (d i : ℝ))
    (hno : ¬ RationalLinearSystem.hasIntegerSolution B d) :
    ∃ c : Fin n → ℤ, ∃ β : ℝ,
      IsGreatest (((Int.cast ∘ c) ⬝ᵥ ·) '' P) β ∧
        β ∉ Set.range (Int.cast : ℤ → ℝ) := by
  classical
  -- Shift the Farkas multiplier by positive, denominator-cleared valid rows.
  obtain ⟨u, huInteger, huValueNotInteger⟩ :=
    existsIntegralRowCertificate_of_fullRowRank B d hB hno
  obtain ⟨cBase, hcBase⟩ := mem_integerVectors_iff.mp huInteger
  let D : Fin k → ℕ := fun i ↦
    rational_vector_common_denominator (augmentedRationalRow B d i)
  let N : Fin k → ℕ := fun i ↦ Classical.choose (exists_nat_gt (-u i))
  have hNgt : ∀ i, -u i < (N i : ℝ) := by
    intro i
    exact Classical.choose_spec (exists_nat_gt (-u i))
  let w : Fin k → ℝ := fun i ↦ u i + (N i : ℝ) * (D i : ℝ)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    have hDoneNat : 1 ≤ D i := Nat.one_le_iff_ne_zero.mpr
      (rationalVectorCommonDenominator_ne_zero (augmentedRationalRow B d i))
    have hDone : (1 : ℝ) ≤ D i := by
      exact_mod_cast hDoneNat
    have hNnonneg : 0 ≤ (N i : ℝ) := Nat.cast_nonneg _
    have hNle : (N i : ℝ) ≤ (N i : ℝ) * (D i : ℝ) := by
      nlinarith
    dsimp [w]
    linarith [hNgt i]
  let scaledRow : Fin k → Fin (n + 1) → ℤ := fun i ↦
    common_denominator_scaled_vector (augmentedRationalRow B d i)
  let c : Fin n → ℤ := fun j ↦
    cBase j + ∑ i, (N i : ℤ) * scaledRow i j.castSucc
  let shift : ℤ := ∑ i, (N i : ℤ) * scaledRow i (Fin.last n)
  have hscaledCoeff : ∀ i j,
      ((scaledRow i j.castSucc : ℤ) : ℝ) = (D i : ℝ) * (B i j : ℝ) := by
    intro i j
    simpa [scaledRow, D] using scaledAugmentedRationalRow_castSucc B d i j
  have hscaledRhs : ∀ i,
      ((scaledRow i (Fin.last n) : ℤ) : ℝ) = (D i : ℝ) * (d i : ℝ) := by
    intro i
    simpa [scaledRow, D] using scaledAugmentedRationalRow_last B d i
  have hc :
      (Int.cast ∘ c : Fin n → ℝ) = w ᵥ* (B.map (Rat.castHom ℝ)) := by
    funext j
    have hcBaseCoord : (cBase j : ℝ) = (u ᵥ* (B.map (Rat.castHom ℝ))) j := by
      exact (congrFun hcBase j).symm
    calc
      (Int.cast ∘ c : Fin n → ℝ) j =
          (cBase j : ℝ) + ∑ i, (N i : ℝ) * (scaledRow i j.castSucc : ℝ) := by
            simp [c]
      _ = (u ᵥ* (B.map (Rat.castHom ℝ))) j +
          ∑ i, (N i : ℝ) * (scaledRow i j.castSucc : ℝ) := by rw [hcBaseCoord]
      _ = ∑ i, (u i + (N i : ℝ) * (D i : ℝ)) * (B i j : ℝ) := by
            rw [Matrix.vecMul, dotProduct, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hscaledCoeff]
            simp only [Matrix.map_apply, Rat.coe_castHom]
            ring
      _ = (w ᵥ* (B.map (Rat.castHom ℝ))) j := by
            simp [w, Matrix.vecMul, dotProduct]
  let β : ℝ := w ⬝ᵥ (fun i ↦ (d i : ℝ))
  have hβ :
      β = u ⬝ᵥ (fun i ↦ (d i : ℝ)) + (shift : ℝ) := by
    calc
      β = ∑ i, (u i + (N i : ℝ) * (D i : ℝ)) * (d i : ℝ) := by
        simp [β, w, dotProduct]
      _ = (∑ i, u i * (d i : ℝ)) +
          ∑ i, (N i : ℝ) * ((scaledRow i (Fin.last n) : ℤ) : ℝ) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hscaledRhs]
            ring
      _ = u ⬝ᵥ (fun i ↦ (d i : ℝ)) + (shift : ℝ) := by
            simp [dotProduct, shift]
  have hβNotInteger : β ∉ Set.range (Int.cast : ℤ → ℝ) := by
    rintro ⟨a, ha⟩
    apply huValueNotInteger
    refine ⟨a - shift, ?_⟩
    have hvalue :
        u ⬝ᵥ (fun i ↦ (d i : ℝ)) = (a : ℝ) - (shift : ℝ) := by
      rw [hβ] at ha
      linarith
    calc
      ((a - shift : ℤ) : ℝ) = (a : ℝ) - (shift : ℝ) := by norm_num
      _ = u ⬝ᵥ (fun i ↦ (d i : ℝ)) := hvalue.symm
  obtain ⟨x₀, hx₀P, hx₀Eq⟩ := hattain
  refine ⟨c, β, ?_, hβNotInteger⟩
  constructor
  · refine ⟨x₀, hx₀P, ?_⟩
    calc
      (Int.cast ∘ c : Fin n → ℝ) ⬝ᵥ x₀ =
          w ⬝ᵥ (B.map (Rat.castHom ℝ) *ᵥ x₀) := by
            rw [hc, Matrix.dotProduct_mulVec]
      _ = β := by rw [hx₀Eq]
  · rintro z ⟨x, hxP, rfl⟩
    calc
      (Int.cast ∘ c : Fin n → ℝ) ⬝ᵥ x =
          w ⬝ᵥ (B.map (Rat.castHom ℝ) *ᵥ x) := by
            rw [hc, Matrix.dotProduct_mulVec]
      _ ≤ w ⬝ᵥ (fun i ↦ (d i : ℝ)) := by
            exact Finset.sum_le_sum fun i _ ↦
              mul_le_mul_of_nonneg_left (hvalid x hxP i) (hw i)
      _ = β := rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_1/ch4_sec4_1_theorem_4_1.lean`: integrality of all attained
integral-objective maxima forces every minimal face to contain an integral point. -/
private lemma rationalMinimalFace_containsIntegralPoint_of_integralMaxima
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P)
    {F : Set (Fin n → ℝ)} (hF : IsMinimalFaceOf ℝ P F)
    (hmaxima : ∀ c z,
      IsGreatest (((Int.cast ∘ c) ⬝ᵥ ·) '' P) z →
        ∃ a : ℤ, z = a) :
    ∃ x ∈ F, x ∈ ℤ^n := by
  classical
  -- If the face had no lattice point, its equality system would yield a forbidden maximum.
  by_contra hNoIntegralPoint
  obtain ⟨k, B, d, hF_eq, hvalid, hB⟩ :=
    rationalMinimalFace_eq_validRationalSystem P hP hF
  have hnoSolution : ¬ RationalLinearSystem.hasIntegerSolution B d := by
    intro hsolution
    obtain ⟨xInt, hxIntEq⟩ :=
      (RationalLinearSystem.hasIntegerSolution_iff B d).mp hsolution
    let x : Fin n → ℝ := fun j ↦ (xInt j : ℝ)
    have hxRealEq :
        B.map (Rat.castHom ℝ) *ᵥ x = fun i ↦ (d i : ℝ) := by
      funext i
      have hi := congrFun hxIntEq i
      calc
        (B.map (Rat.castHom ℝ) *ᵥ x) i =
            (Rat.castHom ℝ) ((B *ᵥ fun j ↦ (xInt j : ℚ)) i) := by
          simpa only [x, Function.comp_apply, Rat.cast_intCast] using
            (RingHom.map_mulVec (Rat.castHom ℝ) B (fun j ↦ (xInt j : ℚ)) i).symm
        _ = (d i : ℝ) := congrArg (Rat.castHom ℝ) hi
    have hxF : x ∈ F := by
      rw [hF_eq]
      exact hxRealEq
    have hxInteger : x ∈ ℤ^n := by
      exact mem_integerVectors_iff.mpr ⟨xInt, rfl⟩
    exact hNoIntegralPoint ⟨x, hxF, hxInteger⟩
  obtain ⟨x₀, hx₀F⟩ := hF.nonempty
  have hattain :
      ∃ x ∈ P, B.map (Rat.castHom ℝ) *ᵥ x = fun i ↦ (d i : ℝ) := by
    refine ⟨x₀, hF.isExtreme.subset hx₀F, ?_⟩
    rw [hF_eq] at hx₀F
    exact hx₀F
  obtain ⟨c, β, hgreatest, hβNotInteger⟩ :=
    existsIntegralObjectiveWithNonintegralMaximum_of_noIntegerSolution
      P B d hB hvalid hattain hnoSolution
  obtain ⟨a, hβInteger⟩ := hmaxima c β hgreatest
  -- The Farkas certificate made this same attained value nonintegral.
  exact hβNotInteger ⟨a, hβInteger.symm⟩

/-- Theorem 4.1 (3). Let `P` be a rational polyhedron. Then `P` is an integral polyhedron if and
only if every finite maximum of an integral linear objective over `P` is an integer. -/
theorem rational_polyhedron_is_integral_iff_integral_linear_maxima_are_integer
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P) :
    is_integral P ↔
      ∀ c z,
        IsGreatest (((Int.cast ∘ c) ⬝ᵥ ·) '' P) z →
          ∃ k : ℤ, z = k := by
  constructor
  · intro hIntegral c z hz
    obtain ⟨x, hxInteger, hxValue⟩ :=
      (rational_polyhedron_is_integral_iff_linear_maxima_attained_by_integral_points P hP).mp
        hIntegral (Int.cast ∘ c) z hz
    obtain ⟨xInt, hxCast⟩ := mem_integerVectors_iff.mp hxInteger.2
    refine ⟨∑ i, c i * xInt i, ?_⟩
    -- The objective at an integral point is the cast of the corresponding integer sum.
    rw [← hxValue]
    simp [hxCast, dotProduct]
  · intro hmaxima
    apply (rational_polyhedron_is_integral_iff_minimal_faces_contain_integral_point P hP).mpr
    intro F hF
    -- Integer Farkas supplies a forbidden nonintegral maximum if this face has no lattice point.
    exact rationalMinimalFace_containsIntegralPoint_of_integralMaxima P hP hF hmaxima

end Theorem41

#print axioms rational_polyhedron_is_integral_iff_minimal_faces_contain_integral_point
#print axioms rational_polyhedron_is_integral_iff_linear_maxima_attained_by_integral_points
#print axioms rational_polyhedron_is_integral_iff_integral_linear_maxima_are_integer
