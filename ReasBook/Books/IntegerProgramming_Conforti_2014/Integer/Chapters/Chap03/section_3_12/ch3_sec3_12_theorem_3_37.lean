import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_4.ch3_sec3_4_4_definition_3_4_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_33
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.PointedCore
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.Recession
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.QuotientFaces

open scoped Pointwise

-- Domain sampling for this theorem:
-- * primary domain: polyhedra, recession cones, and exposed faces in `ℝ^n`
-- * source-facing owners: `is_polyhedron`, `IsExposed`, `recessionCone`, `linealitySpace`,
--   `IsMinimalFaceOf`
-- * core/canonical finite-family owner: `cone (Set.range rays)`
-- * derived face API used below: `IsExposed.isExtreme`
-- * core/canonical derived owner for `dim (lin P)`: `PolyhedronDecomposition.linealityRank`

section Theorem337

variable {n : ℕ}

namespace PolyhedronDecomposition

/-- The dimension of the lineality space of `P`, packaged through the canonical submodule owner. -/
noncomputable abbrev linealityRank (P : Set (Fin n → ℝ)) : ℕ :=
  Module.finrank ℝ (linealitySubmodule P)

/-- A set `X` meets every minimal face of `P`. -/
def MeetsEveryMinimalFace (P X : Set (Fin n → ℝ)) : Prop :=
  ∀ F : Set (Fin n → ℝ), IsMinimalFaceOf ℝ P F → ∃ x, x ∈ X ∧ x ∈ F

/-- A set `X` meets every nonempty exposed face of `P` whose affine-span direction has the same
dimension as the lineality space of `P`. -/
def MeetsEveryLinealityDimensionFace (P X : Set (Fin n → ℝ)) : Prop :=
  ∀ F : Set (Fin n → ℝ),
    IsExposed ℝ P F →
    F.Nonempty →
    Module.finrank ℝ (affineSpan ℝ F).direction = linealityRank P →
    ∃ x, x ∈ X ∧ x ∈ F

/-- A set `Y` meets every exposed face of `recessionCone P` whose affine-span direction has
dimension `linealityRank P + 1`, with the chosen generator lying outside `linealitySpace P`. -/
def MeetsEveryLinealitySuccDimensionRecessionFace (P Y : Set (Fin n → ℝ)) : Prop :=
  ∀ R : Set (Fin n → ℝ),
    IsExposed ℝ (recessionCone P) R →
    Module.finrank ℝ (affineSpan ℝ R).direction = linealityRank P + 1 →
    ∃ y, y ∈ Y ∧ y ∈ R ∧ y ∉ linealitySpace P

/-- A set `Y` contains a generator whose whole ray lies in every exposed face of
`recessionCone P` whose affine-span direction has dimension `linealityRank P + 1`, with the
generator lying outside `linealitySpace P`. -/
def ContainsGeneratorRayInEveryLinealitySuccDimensionRecessionFace
    (P Y : Set (Fin n → ℝ)) : Prop :=
  ∀ R : Set (Fin n → ℝ),
    IsExposed ℝ (recessionCone P) R →
    Module.finrank ℝ (affineSpan ℝ R).direction = linealityRank P + 1 →
    ∃ y, y ∈ Y ∧ y ∉ linealitySpace P ∧ ray y ⊆ R

end PolyhedronDecomposition

/-- Helper for Theorem 3.37: once `X ⊆ P` and every `Y`-generator is a recession direction of `P`,
the full Minkowski sum `convexHull ℝ X + cone Y + linealitySpace P` stays inside `P`. -/
lemma convexHull_add_cone_add_linealitySpace_subset
    (P X Y : Set (Fin n → ℝ))
    (hP_convex : Convex ℝ P)
    (hX_subset : X ⊆ P)
    (hY_subset : Y ⊆ recessionCone P) :
    convexHull ℝ X + cone Y + linealitySpace P ⊆ P := by
  have hconvexHull_subset : convexHull ℝ X ⊆ P :=
    convexHull_min hX_subset hP_convex
  have hcone_subset : cone Y ⊆ recessionCone P := by
    intro r hr
    rcases mem_cone_iff.mp hr with ⟨q, rays, hrays, hcomb⟩
    -- Every conic combination of recession directions is still a recession direction.
    change r ∈ (recessionPointedCone ℝ P : Set (Fin n → ℝ))
    exact PointedCone.conicCombination_mem (fun j ↦ hY_subset (hrays j)) hcomb
  intro x hx
  rcases Set.mem_add.mp hx with ⟨u, hu, l, hl, rfl⟩
  rcases Set.mem_add.mp hu with ⟨y, hy, z, hz, rfl⟩
  have hyP : y ∈ P := hconvexHull_subset hy
  have hz_rec : z ∈ recessionCone P := hcone_subset hz
  have hl_rec : l ∈ recessionCone P := by
    -- A lineality direction is, in particular, a recession direction.
    rw [mem_linealitySpace_iff] at hl
    rw [mem_recessionCone_iff]
    intro x hx a ha
    exact hl hx a
  have hzl_rec : z + l ∈ recessionCone P := by
    -- The recession cone is closed under addition via its canonical pointed-cone owner.
    change z + l ∈ (recessionPointedCone ℝ P : Set (Fin n → ℝ))
    exact add_mem hz_rec hl_rec
  have hyzl : y + (1 : ℝ) • (z + l) ∈ P :=
    (mem_recessionCone_iff.mp hzl_rec) hyP 1 (by positivity)
  simpa [add_assoc, add_left_comm, add_comm] using hyzl

/-- Helper for Theorem 3.37: every matrix polyhedron is convex. -/
lemma polyhedron_le_set_convex
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  intro x hx y hy a₁ a₂ ha₁ ha₂ ha_sum
  -- Each defining row inequality is preserved by convex combinations.
  intro i
  have hx_i : (Matrix.mulVec A x) i ≤ b i := hx i
  have hy_i : (Matrix.mulVec A y) i ≤ b i := hy i
  calc
    (Matrix.mulVec A (a₁ • x + a₂ • y)) i
        = a₁ * (Matrix.mulVec A x) i + a₂ * (Matrix.mulVec A y) i := by
            calc
              ∑ j, A i j * (a₁ * x j + a₂ * y j)
                  = ∑ j, (a₁ * (A i j * x j) + a₂ * (A i j * y j)) := by
                      refine Finset.sum_congr rfl ?_
                      intro j _
                      ring
              _ = a₁ * ∑ j, A i j * x j + a₂ * ∑ j, A i j * y j := by
                    simp [Finset.mul_sum, Finset.sum_add_distrib]
              _ = a₁ * (Matrix.mulVec A x) i + a₂ * (Matrix.mulVec A y) i := by
                    simp [Matrix.mulVec, dotProduct]
    _ ≤ a₁ * b i + a₂ * b i := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hx_i ha₁)
            (mul_le_mul_of_nonneg_left hy_i ha₂)
    _ = (a₁ + a₂) * b i := by ring
    _ = b i := by rw [ha_sum, one_mul]

/-- Helper for Theorem 3.37: a decomposition `P = convexHull ℝ X + cone Y + linealitySpace P`
already forces every generator from `X` to belong to `P`. -/
lemma generators_subset_of_convexHull_add_cone_add_linealitySpace_repr
    (P X Y : Set (Fin n → ℝ))
    (h_repr : P = convexHull ℝ X + cone Y + linealitySpace P) :
    X ⊆ P := by
  intro x hxX
  -- Keep the cone and lineality parts at zero to place each generator directly in the sum.
  rw [h_repr]
  refine Set.mem_add.mpr ?_
  refine ⟨x, ?_, 0, zero_mem_linealitySpace, ?_⟩
  · refine Set.mem_add.mpr ?_
    refine ⟨x, subset_convexHull ℝ X hxX, 0, cone_zero_mem, ?_⟩
    simp
  · simp

/-- Helper for Theorem 3.37: pointwise control of a finite vertex family lifts to the whole convex
hull. -/
lemma seedConvexHull_subset_convexHull_add_lineality
    (P X : Set (Fin n → ℝ))
    {p : ℕ}
    (vertices : Fin p → Fin n → ℝ)
    (hvertices :
      ∀ i : Fin p, vertices i ∈ convexHull ℝ X + linealitySpace P) :
    convexHull ℝ (Set.range vertices) ⊆ convexHull ℝ X + linealitySpace P := by
  have hsubset :
      Set.range vertices ⊆ convexHull ℝ X + linealitySpace P := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact hvertices i
  -- Once each listed vertex is in the target convex set, `convexHull_min` promotes the whole
  -- finite hull.
  refine convexHull_min hsubset ?_
  exact (convex_convexHull ℝ X).add (by
    simpa [coe_linealitySubmodule] using (linealitySubmodule P).convex)

/-- Helper for Theorem 3.37: a matrix polyhedron has only finitely many minimal faces. -/
lemma polyhedron_finite_minimalFaces
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Set.Finite {F : Set (Fin n → ℝ) | IsMinimalFaceOf ℝ (polyhedron_le_set A b) F} := by
  -- Every minimal face is exposed, so Section 3.8 finiteness applies immediately.
  refine
    (polyhedron_finite_faces (P := polyhedron_le_set A b) ⟨m, A, b, rfl⟩).subset ?_
  intro F hF_minimal
  exact minimal_face_isExposed_of_polyhedron A b F hF_minimal

/-- Helper for Theorem 3.37: two points on the same minimal face differ by a lineality vector. -/
lemma minimalFace_point_sub_mem_linealitySpace
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (hF_minimal : IsMinimalFaceOf ℝ (polyhedron_le_set A b) F)
    {x z : Fin n → ℝ}
    (hx : x ∈ F)
    (hz : z ∈ F) :
    z - x ∈ linealitySpace (polyhedron_le_set A b) := by
  have htranslate :
      F =
        (AffineSubspace.mk' x (linealitySubmodule (polyhedron_le_set A b)) :
          Set (Fin n → ℝ)) :=
    minimalFace_eq_point_translate_linealitySubmodule A b F hF_minimal x hx
  have hz_submodule : z - x ∈ linealitySubmodule (polyhedron_le_set A b) := by
    -- The translate description from Theorem 3.33 turns face membership into a kernel statement.
    have hz_translate :
        z ∈
          (AffineSubspace.mk' x (linealitySubmodule (polyhedron_le_set A b)) :
            Set (Fin n → ℝ)) := by
      rw [← htranslate]
      exact hz
    simpa [AffineSubspace.mem_mk'] using hz_translate
  -- Repackage the submodule membership back into the source-facing lineality-space owner.
  exact mem_linealitySubmodule_iff.mp hz_submodule

/-- Helper for Theorem 3.37: after quotienting out lineality, the face-coverage hypotheses should
produce the pointed convex-hull-plus-cone decomposition on the quotient image. -/
lemma linealityQuotientCoordinateImage_subset_convexHull_add_cone_of_generator_coverage
    (P X Y : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty)
    (hX_subset : X ⊆ P)
    (hY_subset : Y ⊆ recessionCone P)
    (hX_minimal : PolyhedronDecomposition.MeetsEveryMinimalFace P X)
    (hY_recession : PolyhedronDecomposition.MeetsEveryLinealitySuccDimensionRecessionFace P Y) :
    linealityQuotientCoordinateMap P '' P ⊆
      convexHull ℝ (linealityQuotientCoordinateMap P '' X) +
        cone (linealityQuotientCoordinateMap P '' Y) := by
  let π := linealityQuotientCoordinateMap P
  let Q : Set (Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ linealitySubmodule P)) → ℝ) := π '' P
  have hQ_nonempty : Q.Nonempty := hP_nonempty.image π
  have hQ_polyhedron : is_polyhedron Q :=
    linearImage_isPolyhedron_of_polyhedron π P hP_polyhedron
  have hQ_recession : recessionCone Q = π '' recessionCone P :=
    recessionCone_linearImage_eq_image_recessionCone_of_polyhedron
      π P hP_polyhedron hP_nonempty
  have hImage_pointed : is_pointed (π '' recessionCone P) :=
    linealityQuotientCoordinateImage_recessionCone_pointed P
  have hQ_pointed : is_pointed Q := by
    rw [is_pointed_iff_eq_zero_of_mem_linealitySpace] at hImage_pointed ⊢
    intro d hd
    apply hImage_pointed d
    rw [← hQ_recession, linealitySpace_recessionCone_eq]
    exact hd
  have hImage_polyhedral : is_polyhedral_cone (π '' recessionCone P) := by
    have hrec_polyhedral :=
      recessionCone_isPolyhedral_of_polyhedron_nonempty Q hQ_polyhedron hQ_nonempty
    rwa [hQ_recession] at hrec_polyhedral
  have hQ_decomposition :=
    pointedPolyhedron_subset_convexHull_extremePoints_add_cone_extremeRays
      Q hQ_nonempty hQ_polyhedron hQ_pointed
  have hvertices_covered : Q.extremePoints ℝ ⊆ π '' X := by
    intro q hq
    let F : Set (Fin n → ℝ) := P ∩ π ⁻¹' ({q} : Set _)
    have hF_minimal : IsMinimalFaceOf ℝ P F :=
      linealityQuotientExtremePointFiber_isMinimalFace P hq
    obtain ⟨x, hxX, hxF⟩ := hX_minimal F hF_minimal
    refine ⟨x, hxX, ?_⟩
    simpa [F, π] using hxF.2
  have hrays_covered :
      {d | IsExtremeRayOfCone (recessionCone Q) d} ⊆ cone (π '' Y) := by
    intro d hd
    have hdImage : IsExtremeRayOfCone (π '' recessionCone P) d := by
      rwa [← hQ_recession]
    have hfiber :=
      linealityQuotientExtremeRayFiber_isExposed_finrank
        P hImage_polyhedral hImage_pointed hdImage
    obtain ⟨y, hyY, hyFiber, hy_not_lineality⟩ :=
      hY_recession (recessionCone P ∩ π ⁻¹' ray d) hfiber.1 (by
        simpa [PolyhedronDecomposition.linealityRank] using hfiber.2)
    rcases mem_ray_iff.mp hyFiber.2 with ⟨μ, hμ_nonneg, hπy⟩
    have hμ_pos : 0 < μ := by
      apply lt_of_le_of_ne hμ_nonneg
      intro hμ_zero
      have hπy_zero : π y = 0 := by simpa [hμ_zero] using hπy
      apply hy_not_lineality
      apply mem_linealitySubmodule_iff.mp
      rw [← linealityQuotientCoordinateMap_ker P, LinearMap.mem_ker]
      exact hπy_zero
    have hπy_cone : π y ∈ cone (π '' Y) :=
      subset_cone (π '' Y) ⟨y, hyY, rfl⟩
    have hscaled : μ⁻¹ • π y ∈ cone (π '' Y) :=
      cone_smul_mem hπy_cone (inv_nonneg.mpr hμ_pos.le)
    have hd_eq : μ⁻¹ • π y = d := by
      rw [hπy, smul_smul, inv_mul_cancel₀ hμ_pos.ne', one_smul]
    rwa [hd_eq] at hscaled
  intro q hq
  rcases hQ_decomposition hq with ⟨u, hu, v, hv, huv⟩
  refine Set.mem_add.mpr ⟨u, ?_, v, ?_, huv⟩
  · exact (convexHull_mono hvertices_covered) hu
  · exact (cone_min hrays_covered) hv

/-- Companion API for Theorem 3.37 (1): once the vertex set `X` meets every minimal face of `P`
and the ray set `Y` meets every exposed face of `recessionCone P` of lineality-successor
dimension away from `linealitySpace P`, with `X ⊆ P` and `Y ⊆ recessionCone P`, the same
decomposition holds directly at the set level. -/
theorem polyhedron_eq_convexHull_add_cone_add_linealitySpace_of_generators
    (P X Y : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty)
    (hX_subset : X ⊆ P)
    (hY_subset : Y ⊆ recessionCone P)
    (hX_minimal : PolyhedronDecomposition.MeetsEveryMinimalFace P X)
    (hY_recession : PolyhedronDecomposition.MeetsEveryLinealitySuccDimensionRecessionFace P Y) :
    P = convexHull ℝ X + cone Y + linealitySpace P := by
  rcases hP_polyhedron with ⟨m, A, b, rfl⟩
  apply Set.Subset.antisymm
  · intro x hx
    let π := linealityQuotientCoordinateMap (polyhedron_le_set A b)
    have hx_quotient :
        π x ∈ convexHull ℝ (π '' X) + cone (π '' Y) := by
      -- Route correction: the ambient inclusion now factors through the quotient image, so the
      -- only missing step is the pointed quotient-core decomposition.
      exact
        linealityQuotientCoordinateImage_subset_convexHull_add_cone_of_generator_coverage
          (polyhedron_le_set A b) X Y ⟨m, A, b, rfl⟩ hP_nonempty hX_subset hY_subset
          hX_minimal hY_recession ⟨x, hx, rfl⟩
    rcases Set.mem_add.mp hx_quotient with ⟨u, hu, v, hv, huv⟩
    have hv_image :
        v ∈ π '' recessionCone (polyhedron_le_set A b) := by
      -- Every quotient cone witness comes from an actual recession direction because `Y` already
      -- lies in the recession cone.
      exact
        mem_linealityQuotientCoordinateImage_recessionCone_of_mem_coneImage
          (polyhedron_le_set A b) Y hY_subset hv
    rcases hv_image with ⟨d, hd_rec, hd_map⟩
    have hxd_map : π (x - d) ∈ convexHull ℝ (π '' X) := by
      -- Removing the lifted recession witness leaves the quotient convex witness.
      have hmap_eq : π (x - d) = u := by
        calc
          π (x - d) = π x - π d := by simp [π]
          _ = (u + v) - v := by rw [← huv, hd_map]
          _ = u := by abel
      simpa [hmap_eq] using hu
    have hxd_mem :
        x - d ∈ convexHull ℝ X + linealitySpace (polyhedron_le_set A b) := by
      -- Pull the quotient convex witness back through the quotient kernel.
      exact
        mem_convexHull_add_lineality_of_linealityQuotientCoordinateMap_mem_convexHullImage
          (polyhedron_le_set A b) X hxd_map
    have hd_mem :
        d ∈ cone Y + linealitySpace (polyhedron_le_set A b) := by
      -- Pull the quotient cone witness back through the same kernel description.
      have hd_map_cone :
          linealityQuotientCoordinateMap (polyhedron_le_set A b) d ∈
            cone (linealityQuotientCoordinateMap (polyhedron_le_set A b) '' Y) := by
        rw [hd_map]
        exact hv
      exact
        mem_cone_add_lineality_of_linealityQuotientCoordinateMap_mem_coneImage
          (polyhedron_le_set A b) Y hd_rec hd_map_cone
    rcases Set.mem_add.mp hxd_mem with ⟨c, hc_hull, l₁, hl₁, hxd_eq⟩
    rcases Set.mem_add.mp hd_mem with ⟨k, hk_cone, l₂, hl₂, hd_eq⟩
    have hl_add : l₁ + l₂ ∈ linealitySpace (polyhedron_le_set A b) := by
      rw [← mem_linealitySubmodule_iff] at hl₁ hl₂ ⊢
      exact add_mem hl₁ hl₂
    refine Set.mem_add.mpr ?_
    refine ⟨c + k, Set.mem_add.mpr ⟨c, hc_hull, k, hk_cone, rfl⟩, l₁ + l₂, hl_add, ?_⟩
    calc
      (c + k) + (l₁ + l₂) = (c + l₁) + (k + l₂) := by abel
      _ = (x - d) + d := by rw [← hxd_eq, ← hd_eq]
      _ = x := by abel
  · -- The listed generators already lie in the polyhedron and its recession cone.
    exact
      convexHull_add_cone_add_linealitySpace_subset
        (polyhedron_le_set A b) X Y (polyhedron_le_set_convex A b) hX_subset hY_subset

/-- Theorem 3.37 (1) (Decomposition Theorem for Polyhedra). If `P ⊆ ℝ^n` is a nonempty
polyhedron, every minimal face of `P` appears among the finite family `minimalFaces`, every
exposed face of `recessionCone P` of dimension
`PolyhedronDecomposition.linealityRank P + 1` appears among the finite family
`recessionFaces`, each `minimalFaces i` is itself a minimal face of `P`, each `recessionFaces i`
is itself an exposed face of `recessionCone P` of that dimension, and `v i`, `r i` are chosen
representatives with
`v i ∈ minimalFaces i` and `r i ∈ recessionFaces i \ linealitySpace P`, then
`P = conv({v i}) + cone({r i}) + lin(P)`. -/
theorem polyhedron_eq_convexHull_add_cone_add_linealitySpace
    (p q : ℕ)
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty)
    (minimalFaces : Fin p → Set (Fin n → ℝ))
    (recessionFaces : Fin q → Set (Fin n → ℝ))
    (v : Fin p → Fin n → ℝ)
    (r : Fin q → Fin n → ℝ)
    (h_minimalFaces_face : ∀ i : Fin p, IsMinimalFaceOf ℝ P (minimalFaces i))
    (h_minimalFaces_cover :
      ∀ F : Set (Fin n → ℝ), IsMinimalFaceOf ℝ P F → ∃ i : Fin p, minimalFaces i = F)
    (h_recessionFaces_face : ∀ i : Fin q, IsExposed ℝ (recessionCone P) (recessionFaces i))
    (h_recessionFaces_dim :
      ∀ i : Fin q,
        Module.finrank ℝ (affineSpan ℝ (recessionFaces i)).direction =
          PolyhedronDecomposition.linealityRank P + 1)
    (h_recessionFaces_cover :
      ∀ R : Set (Fin n → ℝ),
        IsExposed ℝ (recessionCone P) R →
        Module.finrank ℝ (affineSpan ℝ R).direction =
          PolyhedronDecomposition.linealityRank P + 1 →
          ∃ i : Fin q, recessionFaces i = R)
    (hv : ∀ i : Fin p, v i ∈ minimalFaces i)
    (hr : ∀ i : Fin q, r i ∈ recessionFaces i)
    (hr_not_mem_lineality : ∀ i : Fin q, r i ∉ linealitySpace P) :
    P = convexHull ℝ (Set.range v) + cone (Set.range r) + linealitySpace P := by
  -- Convert the finite indexed face data into the set-level incidence predicates expected by the
  -- generator-based decomposition theorem.
  refine polyhedron_eq_convexHull_add_cone_add_linealitySpace_of_generators
    P (Set.range v) (Set.range r) hP_polyhedron hP_nonempty ?_ ?_ ?_ ?_
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    have hsubset : minimalFaces i ⊆ P :=
      (h_minimalFaces_face i).isExtreme.subset
    exact hsubset (hv i)
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    exact (h_recessionFaces_face i).subset (hr i)
  · intro F hF_minimal
    -- Cover the given minimal face by one of the listed family members and choose its generator.
    rcases h_minimalFaces_cover F hF_minimal with ⟨i, rfl⟩
    refine ⟨v i, ?_, hv i⟩
    exact ⟨i, rfl⟩
  · intro R hR_exposed hR_dim
    -- Cover the given recession face by one of the listed family members and choose its
    -- generator outside the lineality space.
    rcases h_recessionFaces_cover R hR_exposed hR_dim with ⟨i, rfl⟩
    refine ⟨r i, ?_, hr i, hr_not_mem_lineality i⟩
    exact ⟨i, rfl⟩

/-- Helper for Theorem 3.37: a representation `P = convexHull ℝ X + cone Y + linealitySpace P`
exhibits `P` as a sum of convex sets, hence `P` is convex. -/
lemma convex_of_convexHull_add_cone_add_linealitySpace_repr
    (P X Y : Set (Fin n → ℝ))
    (h_repr : P = convexHull ℝ X + cone Y + linealitySpace P) :
    Convex ℝ P := by
  -- The three source pieces are convex, so their Minkowski sum is convex as well.
  rw [h_repr]
  exact ((convex_convexHull ℝ X).add (cone_convex Y)).add <| by
    simpa [coe_linealitySubmodule] using (linealitySubmodule P).convex

/-- Helper for Theorem 3.37: every cone generator from a representation
`P = convexHull ℝ X + cone Y + linealitySpace P` is a recession direction of `P`. -/
lemma cone_subset_recessionCone_of_convexHull_add_cone_add_linealitySpace_repr
    (P X Y : Set (Fin n → ℝ))
    (h_repr : P = convexHull ℝ X + cone Y + linealitySpace P) :
    cone Y ⊆ recessionCone P := by
  intro r hr
  rcases mem_cone_iff.mp hr with ⟨q, rays, hrays, hcomb⟩
  -- It suffices to show that every listed generator is a recession direction of `P`.
  change r ∈ (recessionPointedCone ℝ P : Set (Fin n → ℝ))
  refine PointedCone.conicCombination_mem ?_ hcomb
  intro j
  change rays j ∈ recessionCone P
  rw [mem_recessionCone_iff]
  intro x hx a ha
  rw [h_repr] at hx ⊢
  rcases Set.mem_add.mp hx with ⟨u, hu, l, hl, rfl⟩
  rcases Set.mem_add.mp hu with ⟨x₀, hx₀, z, hz, rfl⟩
  have hj_cone : rays j ∈ cone Y := subset_cone Y (hrays j)
  have hay_cone : a • rays j ∈ cone Y := cone_smul_mem hj_cone ha
  have hza_cone : z + a • rays j ∈ cone Y := add_mem hz hay_cone
  -- Keep the convex-hull and lineality parts fixed and absorb the extra ray into the cone part.
  refine Set.mem_add.mpr ?_
  refine ⟨x₀ + (z + a • rays j), Set.mem_add.mpr ⟨x₀, hx₀, z + a • rays j, hza_cone, rfl⟩,
    l, hl, ?_⟩
  simp [add_assoc, add_comm]

/-- Helper for Theorem 3.37: recession directions are stable under adding another recession
direction scaled by a nonnegative scalar. -/
lemma recessionCone_add_smul_mem
    (P : Set (Fin n → ℝ))
    {r s : Fin n → ℝ}
    (hr : r ∈ recessionCone P)
    (hs : s ∈ recessionCone P)
    {a : ℝ}
    (ha : 0 ≤ a) :
    r + a • s ∈ recessionCone P := by
  rw [mem_recessionCone_iff] at hr hs ⊢
  intro x hx b hb
  have hxr : x + b • r ∈ P := hr hx b hb
  have hxs : x + b • r + (b * a) • s ∈ P := hs hxr (b * a) (mul_nonneg hb ha)
  -- Normalize the scalar multiplication so the translated point has the desired direction.
  simpa [smul_add, smul_smul, add_assoc, add_comm, mul_comm] using hxs

/-- Helper for Theorem 3.37: translating a point of an exposed face by an ambient lineality
direction stays inside that exposed face. -/
lemma linealityTranslate_mem_exposedFace
    (P F : Set (Fin n → ℝ))
    (hF_exposed : IsExposed ℝ P F)
    {x0 r : Fin n → ℝ}
    (hx0 : x0 ∈ F)
    (hr : r ∈ linealitySpace P)
    (a : ℝ) :
    x0 + a • r ∈ F := by
  obtain ⟨l, rfl⟩ := hF_exposed ⟨x0, hx0⟩
  have hx0P : x0 ∈ P := hx0.1
  have htranslateP : x0 + a • r ∈ P := by
    -- A lineality direction keeps the ambient set invariant under every scalar translate.
    exact (mem_linealitySpace_iff.mp hr) hx0P a
  have hnegTranslateP : x0 + (-a) • r ∈ P := by
    -- The same lineality direction also gives the opposite translate needed for symmetry.
    exact (mem_linealitySpace_iff.mp hr) hx0P (-a)
  have htranslate_le : l (x0 + a • r) ≤ l x0 := hx0.2 _ htranslateP
  have hnegTranslate_le : l (x0 + (-a) • r) ≤ l x0 := hx0.2 _ hnegTranslateP
  have hvalue_eq : l (x0 + a • r) = l x0 := by
    -- Comparing the positive and negative translates forces the exposing functional to be constant
    -- along the whole lineality direction.
    have hplus : l x0 + a * l r ≤ l x0 := by
      simpa [map_add, map_smul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using htranslate_le
    have hminus : l x0 - a * l r ≤ l x0 := by
      simpa [sub_eq_add_neg, map_add, map_smul, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc] using hnegTranslate_le
    have hzero : a * l r = 0 := by
      linarith
    calc
      l (x0 + a • r) = l x0 + a * l r := by
        simp [map_add, map_smul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc]
      _ = l x0 := by simp [hzero]
  refine ⟨htranslateP, ?_⟩
  intro z hz
  calc
    l z ≤ l x0 := hx0.2 _ hz
    _ = l (x0 + a • r) := hvalue_eq.symm

/-- Helper for Theorem 3.37: from a representation
`P = convexHull ℝ X + cone Y + linealitySpace P`, any point of a minimal face of `P` can be
normalized back to the convex-hull summand while staying in that minimal face. -/
lemma convexHullSummand_mem_minimalFace_of_repr
    (P X Y F : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (h_repr : P = convexHull ℝ X + cone Y + linealitySpace P)
    (hF_minimal : IsMinimalFaceOf ℝ P F)
    {z : Fin n → ℝ}
    (hzF : z ∈ F) :
    ∃ q, q ∈ convexHull ℝ X ∧ q ∈ F := by
  rcases hP_polyhedron with ⟨m, A, b, rfl⟩
  have hP_convex :
      Convex ℝ (polyhedron_le_set A b) :=
    convex_of_convexHull_add_cone_add_linealitySpace_repr _ _ _ h_repr
  have hX_subset :
      X ⊆ polyhedron_le_set A b :=
    generators_subset_of_convexHull_add_cone_add_linealitySpace_repr _ _ _ h_repr
  have hconv_subset :
      convexHull ℝ X ⊆ polyhedron_le_set A b :=
    convexHull_min hX_subset hP_convex
  have hcone_subset :
      cone Y ⊆ recessionCone (polyhedron_le_set A b) :=
    cone_subset_recessionCone_of_convexHull_add_cone_add_linealitySpace_repr _ _ _ h_repr
  have hzP : z ∈ polyhedron_le_set A b := by
    have hsubset : F ⊆ polyhedron_le_set A b :=
      hF_minimal.isExtreme.subset
    exact hsubset hzF
  rw [h_repr] at hzP
  rcases Set.mem_add.mp hzP with ⟨u, hu, l, hl, rfl⟩
  rcases Set.mem_add.mp hu with ⟨q, hq_hull, c, hc_cone, rfl⟩
  have hqP : q ∈ polyhedron_le_set A b :=
    hconv_subset hq_hull
  have hq_plus_lP : q + l ∈ polyhedron_le_set A b := by
    -- A lineality direction translates every feasible point in both directions.
    rw [mem_linealitySpace_iff] at hl
    simpa using hl hqP (1 : ℝ)
  have hc_rec : c ∈ recessionCone (polyhedron_le_set A b) :=
    hcone_subset hc_cone
  have hq_plus_l_plus_two_cP : q + l + (2 : ℝ) • c ∈ polyhedron_le_set A b := by
    -- Once the base point is feasible, adding a nonnegative multiple of the recession direction
    -- stays feasible.
    exact (mem_recessionCone_iff.mp hc_rec) hq_plus_lP 2 (by positivity)
  have hmidpoint :
      q + c + l ∈ openSegment ℝ (q + l) (q + l + (2 : ℝ) • c) := by
    -- Route correction: use midpoint extremality inside the minimal face instead of unfolding the
    -- full representation at the target line.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, two_smul] using
      ((mem_openSegment_sub_add :
          ∀ x y : Fin n → ℝ, x ∈ openSegment ℝ (x - y) (x + y))
        (q + l + c) c)
  have hq_plus_lF : q + l ∈ F :=
    hF_minimal.isExtreme.left_mem_of_mem_openSegment hq_plus_lP hq_plus_l_plus_two_cP hzF hmidpoint
  have hq_plus_two_lP : q + (2 : ℝ) • l ∈ polyhedron_le_set A b := by
    -- The same lineality direction also keeps the second endpoint feasible.
    rw [mem_linealitySpace_iff] at hl
    exact hl hqP 2
  have hlineality_midpoint :
      q + l ∈ openSegment ℝ q (q + (2 : ℝ) • l) := by
    -- A second midpoint step removes the remaining lineality translation.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, two_smul] using
      ((mem_openSegment_sub_add :
          ∀ x y : Fin n → ℝ, x ∈ openSegment ℝ (x - y) (x + y))
        (q + l) l)
  have hqF : q ∈ F :=
    hF_minimal.isExtreme.left_mem_of_mem_openSegment hqP hq_plus_two_lP hq_plus_lF
      hlineality_midpoint
  exact ⟨q, hq_hull, hqF⟩

/-- Helper for Theorem 3.37: if an extreme face `F` of `P` contains a point of `convexHull ℝ X`
and `X ⊆ P`, then some actual generator from `X` already lies in `F`. -/
lemma existsGeneratorInExtremeFaceOfConvexHull
    (P X F : Set (Fin n → ℝ))
    (hP_convex : Convex ℝ P)
    (hX_subset : X ⊆ P)
    (hF_extreme : IsExtreme ℝ P F)
    {q : Fin n → ℝ}
    (hq_hull : q ∈ convexHull ℝ X)
    (hqF : q ∈ F) :
    ∃ x, x ∈ X ∧ x ∈ F := by
  by_contra hNo
  have hX_subset_diff : X ⊆ P \ F := by
    intro x hxX
    refine ⟨hX_subset hxX, ?_⟩
    intro hxF
    exact hNo ⟨x, hxX, hxF⟩
  have hdiff_convex : Convex ℝ (P \ F) :=
    hF_extreme.convex_diff hP_convex
  have hq_diff : q ∈ P \ F :=
    convexHull_min hX_subset_diff hdiff_convex hq_hull
  exact hq_diff.2 hqF

/-- Helper for Theorem 3.37: every nonempty exposed face of `recessionCone P` is itself a cone, so
it contains the whole ray generated by any of its points. -/
lemma exposedRecessionFace_contains_ray
    (P : Set (Fin n → ℝ))
    (R : Set (Fin n → ℝ))
    (hR_exposed : IsExposed ℝ (recessionCone P) R)
    {y : Fin n → ℝ}
    (hy : y ∈ R) :
    ray y ⊆ R := by
  obtain ⟨l, rfl⟩ := hR_exposed ⟨y, hy⟩
  have hy_rec : y ∈ recessionCone P := hy.1
  have hy_max : ∀ z ∈ recessionCone P, l z ≤ l y := hy.2
  have hly_nonneg : 0 ≤ l y := by
    simpa using hy_max 0 zero_mem_recessionCone
  have htwo_mem : (2 : ℝ) • y ∈ recessionCone P :=
    smul_mem_recessionCone hy_rec (by positivity)
  have hly_nonpos : l y ≤ 0 := by
    have hdouble : (2 : ℝ) * l y ≤ l y := by
      simpa using hy_max ((2 : ℝ) • y) htwo_mem
    calc
      l y = (2 : ℝ) * l y - l y := by ring
      _ ≤ 0 := sub_nonpos.mpr hdouble
  have hly_zero : l y = 0 := by
    exact le_antisymm hly_nonpos hly_nonneg
  intro x hx
  rcases mem_ray_iff.mp hx with ⟨a, ha, rfl⟩
  refine ⟨smul_mem_recessionCone hy_rec ha, ?_⟩
  intro z hz
  calc
    l z ≤ l y := hy_max z hz
    _ = 0 := hly_zero
    _ = l (a • y) := by simpa [hly_zero]

/-- Helper for Theorem 3.37: a cone point on an exposed face of `recessionCone P` that is outside
the ambient lineality space forces one actual generator from `Y` onto the same face and outside
lineality. -/
lemma existsGeneratorInExposedRecessionFace
    (P Y R : Set (Fin n → ℝ))
    (hY_subset : Y ⊆ recessionCone P)
    (hR_exposed : IsExposed ℝ (recessionCone P) R)
    {c : Fin n → ℝ}
    (hc_cone : c ∈ cone Y)
    (hcR : c ∈ R)
    (hc_not_lineality : c ∉ linealitySpace P) :
    ∃ y, y ∈ Y ∧ y ∈ R ∧ y ∉ linealitySpace P := by
  obtain ⟨l, rfl⟩ := hR_exposed ⟨c, hcR⟩
  rcases mem_cone_iff.mp hc_cone with ⟨q, rays, hrays, hcomb⟩
  rcases hcomb with ⟨coeff, hcoeff_nonneg, hsum⟩
  have hc_rec : c ∈ recessionCone P := hcR.1
  have hmax : ∀ z ∈ recessionCone P, l z ≤ l c := hcR.2
  have hlc_nonneg : 0 ≤ l c := by
    simpa using hmax 0 zero_mem_recessionCone
  have hdouble : (2 : ℝ) * l c ≤ l c := by
    have hdouble' : l ((2 : ℝ) • c) ≤ l c :=
      hmax ((2 : ℝ) • c) (smul_mem_recessionCone hc_rec (by positivity))
    simpa [map_smul, mul_comm, mul_left_comm, mul_assoc] using hdouble'
  have hlc_nonpos : l c ≤ 0 := by
    calc
      l c = (2 : ℝ) * l c - l c := by ring
      _ ≤ 0 := sub_nonpos.mpr hdouble
  have hlc_zero : l c = 0 := le_antisymm hlc_nonpos hlc_nonneg
  have hterms_nonpos : ∀ j : Fin q, coeff j * l (rays j) ≤ 0 := by
    intro j
    have hray_le : l (rays j) ≤ l c := hmax (rays j) (hY_subset (hrays j))
    nlinarith [hcoeff_nonneg j, hray_le, hlc_zero]
  have hsum_zero : ∑ j : Fin q, coeff j * l (rays j) = 0 := by
    -- Applying the exposing functional to the conic combination witnesses that the weighted sum
    -- of all generator values is zero.
    have happly := congrArg l hsum
    simpa [map_sum, map_smul, hlc_zero, mul_comm, mul_left_comm, mul_assoc] using happly.symm
  have hterm_zero :
      ∀ j : Fin q, coeff j * l (rays j) = 0 := by
    intro j
    exact
      (Finset.sum_eq_zero_iff_of_nonpos (fun i _ ↦ hterms_nonpos i)).mp hsum_zero j
        (Finset.mem_univ j)
  have hface_of_pos :
      ∀ j : Fin q,
        0 < coeff j →
          rays j ∈ {x : Fin n → ℝ | x ∈ recessionCone P ∧ ∀ y ∈ recessionCone P, l y ≤ l x} := by
    intro j hj
    have hlj_zero : l (rays j) = 0 := by
      exact (mul_eq_zero.mp (hterm_zero j)).resolve_left (ne_of_gt hj)
    refine ⟨hY_subset (hrays j), ?_⟩
    intro z hz
    calc
      l z ≤ l c := hmax z hz
      _ = 0 := hlc_zero
      _ = l (rays j) := hlj_zero.symm
  have hpositive_nonlineality :
      ∃ j : Fin q, 0 < coeff j ∧ rays j ∉ linealitySpace P := by
    by_contra hnone
    have hterm_lineality : ∀ j : Fin q, coeff j • rays j ∈ linealitySubmodule P := by
      intro j
      by_cases hj0 : coeff j = 0
      · simpa [hj0] using (linealitySubmodule P).zero_mem
      · have hjpos : 0 < coeff j := lt_of_le_of_ne (hcoeff_nonneg j) (Ne.symm hj0)
        have hray_lineality : rays j ∈ linealitySpace P := by
          by_contra hray_not_lineality
          exact hnone ⟨j, hjpos, hray_not_lineality⟩
        have hray_submodule : rays j ∈ linealitySubmodule P := by
          rw [mem_linealitySubmodule_iff]
          exact hray_lineality
        exact (linealitySubmodule P).smul_mem (coeff j) hray_submodule
    have hsum_lineality : ∑ j : Fin q, coeff j • rays j ∈ linealitySubmodule P := by
      exact (linealitySubmodule P).sum_mem (fun j _ ↦ hterm_lineality j)
    have hc_lineality : c ∈ linealitySpace P := by
      have hc_submodule : c ∈ linealitySubmodule P := by
        simpa [hsum] using hsum_lineality
      rw [mem_linealitySubmodule_iff] at hc_submodule
      exact hc_submodule
    exact hc_not_lineality hc_lineality
  rcases hpositive_nonlineality with ⟨j, hjpos, hj_not_lineality⟩
  exact ⟨rays j, hrays j, hface_of_pos j hjpos, hj_not_lineality⟩

/-- Helper for Theorem 3.37: an exposed face of `recessionCone P` whose affine-span direction has
dimension `linealityRank P + 1` contains some point outside `linealitySpace P`. -/
lemma exposedRecessionFace_has_nonlineal_point
    (P R : Set (Fin n → ℝ))
    (hR_exposed : IsExposed ℝ (recessionCone P) R)
    (hR_dim :
      Module.finrank ℝ (affineSpan ℝ R).direction =
        PolyhedronDecomposition.linealityRank P + 1) :
    ∃ z, z ∈ R ∧ z ∉ linealitySpace P := by
  have hR_nonempty : R.Nonempty := by
    by_contra hR_empty
    have hdim_zero : Module.finrank ℝ (affineSpan ℝ R).direction = 0 := by
      simpa [Set.not_nonempty_iff_eq_empty.mp hR_empty]
    omega
  by_contra hno
  have hsubset_lineality : R ⊆ linealitySpace P := by
    intro z hz
    by_contra hz_not_lineality
    exact hno ⟨z, hz, hz_not_lineality⟩
  have hAff_le : affineSpan ℝ R ≤ affineSpan ℝ (linealitySpace P) :=
    affineSpan_mono ℝ hsubset_lineality
  have hdir_le : (affineSpan ℝ R).direction ≤ linealitySubmodule P := by
    have hdir_le' :
        (affineSpan ℝ R).direction ≤ (affineSpan ℝ (linealitySpace P)).direction :=
      AffineSubspace.direction_le hAff_le
    have hlineality_aff :
        affineSpan ℝ (linealitySpace P) = (linealitySubmodule P).toAffineSubspace := by
      rw [show linealitySpace P = (linealitySubmodule P : Set (Fin n → ℝ)) from
          (coe_linealitySubmodule P).symm]
      exact AffineSubspace.affineSpan_coe (k := ℝ) (linealitySubmodule P).toAffineSubspace
    have hlineality_dir :
        (affineSpan ℝ (linealitySpace P)).direction = linealitySubmodule P := by
      rw [hlineality_aff, Submodule.toAffineSubspace_direction]
    exact hlineality_dir ▸ hdir_le'
  have hfinrank_le :
      Module.finrank ℝ (affineSpan ℝ R).direction ≤ PolyhedronDecomposition.linealityRank P := by
    simpa [PolyhedronDecomposition.linealityRank] using Submodule.finrank_mono hdir_le
  omega

/-- Helper for Theorem 3.37: after decomposing a point of an exposed recession face into a cone
part and a lineality part, the cone summand still lies on the same exposed face. -/
lemma coneSummand_mem_exposedRecessionFace_of_repr
    (P R : Set (Fin n → ℝ))
    (hR_exposed : IsExposed ℝ (recessionCone P) R)
    {z c l : Fin n → ℝ}
    (hzR : z ∈ R)
    (hl_lineality : l ∈ linealitySpace P)
    (hz_eq : c + l = z) :
    c ∈ R := by
  have hl_recession : l ∈ linealitySpace (recessionCone P) := by
    simpa [linealitySpace_recessionCone_eq P] using hl_lineality
  have htranslated :
      z + (-1 : ℝ) • l ∈ R :=
    linealityTranslate_mem_exposedFace (recessionCone P) R hR_exposed hzR hl_recession (-1)
  have hstrip : z + (-1 : ℝ) • l = c := by
    calc
      z + (-1 : ℝ) • l = (c + l) + (-1 : ℝ) • l := by rw [hz_eq]
      _ = c := by simp [add_assoc]
  exact hstrip ▸ htranslated

/-- Companion API for Theorem 3.37 (2): the vertex generators in a decomposition
`P = conv(X) + cone(Y) + lin(P)` meet every minimal face of `P`. -/
theorem convex_generators_meet_every_minimalFace
    (P : Set (Fin n → ℝ))
    (X Y : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (h_repr : P = convexHull ℝ X + cone Y + linealitySpace P)
    (F : Set (Fin n → ℝ))
    (hF_minimal : IsMinimalFaceOf ℝ P F) :
    ∃ x, x ∈ X ∧ x ∈ F := by
  have hP_convex : Convex ℝ P :=
    convex_of_convexHull_add_cone_add_linealitySpace_repr _ _ _ h_repr
  have hX_subset : X ⊆ P :=
    generators_subset_of_convexHull_add_cone_add_linealitySpace_repr _ _ _ h_repr
  obtain ⟨z, hzF⟩ := hF_minimal.nonempty
  obtain ⟨q, hq_hull, hqF⟩ :=
    convexHullSummand_mem_minimalFace_of_repr P X Y F hP_polyhedron h_repr hF_minimal hzF
  -- Strip the cone and lineality parts first, then use extremality to force an actual generator
  -- from `X` onto the minimal face.
  exact
    existsGeneratorInExtremeFaceOfConvexHull
      P X F hP_convex hX_subset hF_minimal.isExtreme hq_hull hqF

/-- Helper for Theorem 3.37: a nonempty exposed face whose affine-span direction already has the
same dimension as the ambient lineality space is minimal. -/
lemma exposedFace_linealityRank_isMinimalFace
    (P F : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hF_exposed : IsExposed ℝ P F)
    (hF_nonempty : F.Nonempty)
    (hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction =
        PolyhedronDecomposition.linealityRank P) :
    IsMinimalFaceOf ℝ P F := by
  have hF_nonempty' : F.Nonempty := hF_nonempty
  obtain ⟨x0, hx0F⟩ := hF_nonempty
  have hx0_aff : x0 ∈ affineSpan ℝ F := subset_affineSpan ℝ F hx0F
  have hle :
      linealitySubmodule P ≤ (affineSpan ℝ F).direction := by
    intro r hr
    have hr_lineality : r ∈ linealitySpace P := mem_linealitySubmodule_iff.mp hr
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff]
    refine ⟨x0 + r, ?_, ?_⟩
    · have hx0_add : x0 + r ∈ F := by
        simpa using linealityTranslate_mem_exposedFace P F hF_exposed hx0F hr_lineality (1 : ℝ)
      exact subset_affineSpan ℝ F hx0_add
    · ext i
      simp
  have hdir :
      (affineSpan ℝ F).direction = linealitySubmodule P := by
    have hfinrank :
        Module.finrank ℝ (linealitySubmodule P) =
          Module.finrank ℝ (affineSpan ℝ F).direction := by
      simpa [PolyhedronDecomposition.linealityRank] using hF_dim.symm
    exact (Submodule.eq_of_le_of_finrank_eq hle hfinrank).symm
  rw [isMinimalFaceOf_iff]
  refine ⟨hF_nonempty', hF_exposed.isExtreme, ?_⟩
  intro G hG_nonempty hG_extreme hGF
  have hG_extreme_in_F : IsExtreme ℝ F G := by
    -- Restrict the ambient extremality to the exposed face `F`.
    exact hG_extreme.mono hF_exposed.isExtreme.subset hGF
  obtain ⟨x0, hx0G⟩ := hG_nonempty
  have hx0F : x0 ∈ F := hGF hx0G
  intro y hyF
  let r : Fin n → ℝ := y - x0
  have hy_dir : y -ᵥ x0 ∈ (affineSpan ℝ F).direction :=
    AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ F hyF)
      (subset_affineSpan ℝ F hx0F)
  have hr_lin : r ∈ linealitySubmodule P := by
    -- The affine-direction equality reduces the displacement to an ambient lineality direction.
    simpa [r, hdir, vsub_eq_sub] using hy_dir
  have hr_lineality : r ∈ linealitySpace P := mem_linealitySubmodule_iff.mp hr_lin
  have hmirror' : x0 + (-1 : ℝ) • r ∈ F :=
    linealityTranslate_mem_exposedFace P F hF_exposed hx0F hr_lineality (-1)
  have hmirror : x0 - r ∈ F := by
    simpa [sub_eq_add_neg] using hmirror'
  have hseg : x0 ∈ openSegment ℝ (x0 - r) (x0 + r) := by
    -- The base point sits in the open segment between opposite lineality translates.
    simpa [r] using (mem_openSegment_sub_add (𝕜 := ℝ) x0 r)
  have hy_in_G : x0 + r ∈ G :=
    hG_extreme_in_F.right_mem_of_mem_openSegment
      hmirror (by simpa [r] using hyF) hx0G hseg
  -- Midpoint extremality forces the entire exposed face `F` to lie in `G`.
  simpa [r] using hy_in_G

/-- Theorem 3.37 (2). If `P ⊆ ℝ^n` is a nonempty polyhedron and admits a representation
`P = conv(X) + cone(Y) + lin(P)` in which `cone Y` is pointed, then every nonempty exposed face
of `P` of dimension `PolyhedronDecomposition.linealityRank P` contains one of the generators from
`X`. -/
theorem convex_generators_meet_every_lineality_dimension_face
    (P : Set (Fin n → ℝ))
    (X Y : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty)
    (h_repr : P = convexHull ℝ X + cone Y + linealitySpace P)
    (hY_pointed : is_pointed (cone Y))
    : PolyhedronDecomposition.MeetsEveryLinealityDimensionFace P X :=
  by
  intro F hF_exposed hF_nonempty hF_dim
  have hF_minimal : IsMinimalFaceOf ℝ P F :=
    exposedFace_linealityRank_isMinimalFace P F hP_polyhedron hF_exposed hF_nonempty hF_dim
  -- Route correction: convert the lineality-dimension exposed face into a minimal face and then
  -- reuse the already-closed minimal-face generator theorem.
  exact convex_generators_meet_every_minimalFace P X Y hP_polyhedron h_repr F hF_minimal

/-- Theorem 3.37 (3). If `P ⊆ ℝ^n` is a nonempty polyhedron, `cone Y` is pointed, and the
recession cone itself admits the representation
`recessionCone P = cone(Y) + linealitySpace P`, then every exposed face of `recessionCone P` of
dimension `PolyhedronDecomposition.linealityRank P + 1` contains the ray generated by some
`y ∈ Y` with `y ∉ linealitySpace P`. -/
theorem cone_generators_meet_every_lineality_succ_dimension_recession_face
    (P : Set (Fin n → ℝ))
    (Y : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty)
    (h_recession_repr : recessionCone P = cone Y + linealitySpace P)
    (hY_pointed : is_pointed (cone Y)) :
    PolyhedronDecomposition.ContainsGeneratorRayInEveryLinealitySuccDimensionRecessionFace P
      Y :=
  by
  intro R hR_exposed hR_dim
  have hY_subset : Y ⊆ recessionCone P := by
    intro y hy
    -- Each listed generator is a recession direction because it appears in the explicit
    -- recession-cone decomposition with zero lineality part.
    rw [h_recession_repr]
    exact Set.mem_add.mpr ⟨y, subset_cone Y hy, 0, zero_mem_linealitySpace, by simp⟩
  obtain ⟨z, hzR, hz_not_lineality⟩ :=
    exposedRecessionFace_has_nonlineal_point P R hR_exposed hR_dim
  have hz_rec : z ∈ recessionCone P := hR_exposed.subset hzR
  rw [h_recession_repr] at hz_rec
  rcases Set.mem_add.mp hz_rec with ⟨c, hc_cone, l, hl_lineality, hz_eq⟩
  have hcR : c ∈ R :=
    coneSummand_mem_exposedRecessionFace_of_repr P R hR_exposed hzR hl_lineality hz_eq
  have hc_not_lineality : c ∉ linealitySpace P := by
    intro hc_lineality
    have hc_submodule : c ∈ linealitySubmodule P := by
      rw [mem_linealitySubmodule_iff]
      exact hc_lineality
    have hl_submodule : l ∈ linealitySubmodule P := by
      rw [mem_linealitySubmodule_iff]
      exact hl_lineality
    have hz_submodule : z ∈ linealitySubmodule P := by
      simpa [hz_eq] using (linealitySubmodule P).add_mem hc_submodule hl_submodule
    exact hz_not_lineality (by
      rw [mem_linealitySubmodule_iff] at hz_submodule
      exact hz_submodule)
  obtain ⟨y, hyY, hyR, hy_not_lineality⟩ :=
    existsGeneratorInExposedRecessionFace
      P Y R hY_subset hR_exposed hc_cone hcR hc_not_lineality
  refine ⟨y, hyY, hy_not_lineality, ?_⟩
  -- Once one generator lies on the exposed recession face, the whole generated ray does as well.
  exact exposedRecessionFace_contains_ray P R hR_exposed hyR

/-- ch3_sec3_12_theorem_3_37

Theorem 3.37 (Decomposition Theorem for Polyhedra): if `P ⊆ ℝ^n` is a nonempty polyhedron, the
finite families `minimalFaces` and `recessionFaces` really enumerate the minimal faces of `P` and
the lineality-successor-dimensional exposed faces of `recessionCone P`, each listed family member
is itself such a face, and `v`, `r` choose generators on those faces, then
`P = conv({v i}) + cone({r i}) + lin(P)`. Furthermore, if
`P = conv(X) + cone(Y) + lin(P)` and `cone Y` is pointed, then every nonempty exposed face of `P`
of lineality dimension contains a point of `X`; and if moreover
`recessionCone P = cone(Y) + linealitySpace P`, then every exposed face of `recessionCone P` of
lineality-successor dimension contains a ray generated by some `y ∈ Y` with
`y ∉ linealitySpace P`.

The companion theorems in this file expose the three clauses separately as projection-style APIs. -/
theorem ch3_sec3_12_theorem_3_37
    (p q : ℕ)
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty)
    (minimalFaces : Fin p → Set (Fin n → ℝ))
    (recessionFaces : Fin q → Set (Fin n → ℝ))
    (v : Fin p → Fin n → ℝ)
    (r : Fin q → Fin n → ℝ)
    (h_minimalFaces_face : ∀ i : Fin p, IsMinimalFaceOf ℝ P (minimalFaces i))
    (h_minimalFaces_cover :
      ∀ F : Set (Fin n → ℝ), IsMinimalFaceOf ℝ P F → ∃ i : Fin p, minimalFaces i = F)
    (h_recessionFaces_face : ∀ i : Fin q, IsExposed ℝ (recessionCone P) (recessionFaces i))
    (h_recessionFaces_dim :
      ∀ i : Fin q,
        Module.finrank ℝ (affineSpan ℝ (recessionFaces i)).direction =
          PolyhedronDecomposition.linealityRank P + 1)
    (h_recessionFaces_cover :
      ∀ R : Set (Fin n → ℝ),
        IsExposed ℝ (recessionCone P) R →
        Module.finrank ℝ (affineSpan ℝ R).direction =
          PolyhedronDecomposition.linealityRank P + 1 →
          ∃ i : Fin q, recessionFaces i = R)
    (hv : ∀ i : Fin p, v i ∈ minimalFaces i)
    (hr : ∀ i : Fin q, r i ∈ recessionFaces i)
    (hr_not_mem_lineality : ∀ i : Fin q, r i ∉ linealitySpace P) :
    P = convexHull ℝ (Set.range v) + cone (Set.range r) + linealitySpace P ∧
      ∀ X Y : Set (Fin n → ℝ),
        P = convexHull ℝ X + cone Y + linealitySpace P →
        is_pointed (cone Y) →
          PolyhedronDecomposition.MeetsEveryLinealityDimensionFace P X ∧
            (recessionCone P = cone Y + linealitySpace P →
              PolyhedronDecomposition.ContainsGeneratorRayInEveryLinealitySuccDimensionRecessionFace
                P Y) :=
  by
  constructor
  · -- The first clause is exactly the finite-family decomposition theorem proved above.
    exact polyhedron_eq_convexHull_add_cone_add_linealitySpace
      p q P hP_polyhedron hP_nonempty minimalFaces recessionFaces v r
      h_minimalFaces_face h_minimalFaces_cover h_recessionFaces_face h_recessionFaces_dim
      h_recessionFaces_cover hv hr hr_not_mem_lineality
  · intro X Y h_repr hY_pointed
    -- Assemble the two converse companion statements from their projection-style APIs.
    refine ⟨?_, ?_⟩
    · exact convex_generators_meet_every_lineality_dimension_face
        P X Y hP_polyhedron hP_nonempty h_repr hY_pointed
    · intro h_recession_repr
      exact cone_generators_meet_every_lineality_succ_dimension_recession_face
        P Y hP_polyhedron hP_nonempty h_recession_repr hY_pointed

end Theorem337
