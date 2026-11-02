import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_1.ch3_sec3_4_1_definition_3_4_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_4.ch3_sec3_4_4_definition_3_4_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15

open scoped Pointwise

section RecessionConeSupport

variable {n : ℕ}

/-- Helper for Theorem 3.37: a polytope admits a `Fin`-indexed vertex family whose convex hull is
exactly that polytope. -/
lemma exists_finIndexedVertexFamily_of_isPolytope
    (Q : Set (Fin n → ℝ))
    (hQ_polytope : Q.IsPolytope ℝ) :
    ∃ p : ℕ, ∃ vertices : Fin p → Fin n → ℝ, Q = convexHull ℝ (Set.range vertices) := by
  rcases hQ_polytope with ⟨V, hV_finite, hQ_eq⟩
  let s : Finset (Fin n → ℝ) := hV_finite.toFinset
  let vertices : Fin s.card → Fin n → ℝ := fun i ↦ ((Finset.equivFin s).symm i).1
  have hV_range : Set.range vertices = V := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      have hi_mem : (((Finset.equivFin s).symm i).1) ∈ (s : Set (Fin n → ℝ)) :=
        ((Finset.equivFin s).symm i).2
      simpa [vertices, s] using hi_mem
    · intro hx
      have hx' : x ∈ (s : Set (Fin n → ℝ)) := by simpa [s] using hx
      refine ⟨(Finset.equivFin s) ⟨x, hx'⟩, ?_⟩
      simp [vertices]
  -- Reindexing does not change the finite convex hull.
  exact ⟨s.card, vertices, by rw [hQ_eq, ← hV_range]⟩

/-- Helper for Theorem 3.37: a linear map sends a finitely generated cone to the cone generated
by the pointwise images of its generators. -/
lemma linearMap_image_finitelyGeneratedCone
    {k q : ℕ}
    (f : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (rays : Fin q → Fin n → ℝ) :
    f '' finitely_generated_cone rays =
      finitely_generated_cone (fun i ↦ f (rays i)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases mem_finitely_generated_cone_iff.mp hx with ⟨μ, hμ, rfl⟩
    refine mem_finitely_generated_cone_iff.mpr ⟨μ, hμ, ?_⟩
    simp [map_sum]
  · intro hz
    rcases mem_finitely_generated_cone_iff.mp hz with ⟨μ, hμ, rfl⟩
    refine ⟨∑ i, μ i • rays i, mem_finitely_generated_cone_iff.mpr ⟨μ, hμ, rfl⟩, ?_⟩
    simp [map_sum]

/-- Helper for Theorem 3.37: a linear image of a polyhedron is again a polyhedron. -/
lemma linearImage_isPolyhedron_of_polyhedron
    {k : ℕ}
    (f : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P) :
    is_polyhedron (f '' P) := by
  rcases (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).1 hP_polyhedron with
    ⟨Q, hQ_polytope, q, rays, hrepr⟩
  have hImage_polytope : (f '' Q).IsPolytope ℝ := by
    rcases hQ_polytope with ⟨V, hV_finite, hV_eq⟩
    refine ⟨f '' V, hV_finite.image f, ?_⟩
    rw [← LinearMap.image_convexHull, hV_eq]
  refine (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).2
    ⟨f '' Q, hImage_polytope, q, fun i ↦ f (rays i), ?_⟩
  calc
    f '' P = f '' (Q + finitely_generated_cone rays) := by rw [hrepr]
    _ = f '' Q + f '' finitely_generated_cone rays := Set.image_add f
    _ = f '' Q + finitely_generated_cone (fun i ↦ f (rays i)) := by
          rw [linearMap_image_finitelyGeneratedCone]

/-- Helper for Theorem 3.37: the recession cone of a nonempty polyhedron is polyhedral. -/
lemma recessionCone_isPolyhedral_of_polyhedron_nonempty
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty) :
    is_polyhedral_cone (recessionCone P) := by
  rcases hP_polyhedron with ⟨m, A, b, rfl⟩
  rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
  exact (is_polyhedral_cone_iff).2 ⟨m, A, rfl⟩

/-- Helper for Theorem 3.37: recession cones commute with linear images of nonempty
polyhedra. -/
lemma recessionCone_linearImage_eq_image_recessionCone_of_polyhedron
    {k : ℕ}
    (f : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_nonempty : P.Nonempty) :
    recessionCone (f '' P) = f '' recessionCone P := by
  rcases hP_polyhedron with ⟨m, A, b, rfl⟩
  rcases (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).1
      (show is_polyhedron (polyhedron_le_set A b) from ⟨m, A, b, rfl⟩) with
    ⟨Q, hQ_polytope, q, rays, hrepr⟩
  rcases exists_finIndexedVertexFamily_of_isPolytope Q hQ_polytope with
    ⟨p, vertices, hQ_vertices⟩
  have hrepr_vertices :
      polyhedron_le_set A b = convexHull ℝ (Set.range vertices) +
        finitely_generated_cone rays := by
    rwa [hQ_vertices] at hrepr
  have hrec_source : recessionCone (polyhedron_le_set A b) = finitely_generated_cone rays :=
    polyhedron_recessionCone_eq_finitely_generated_cone A b vertices rays hP_nonempty
      hrepr_vertices
  have hImage_polytope : (f '' Q).IsPolytope ℝ := by
    rcases hQ_polytope with ⟨V, hV_finite, hV_eq⟩
    refine ⟨f '' V, hV_finite.image f, ?_⟩
    rw [← LinearMap.image_convexHull, hV_eq]
  have hImage_repr :
      f '' polyhedron_le_set A b = f '' Q +
        finitely_generated_cone (fun i ↦ f (rays i)) := by
    calc
      f '' polyhedron_le_set A b = f '' (Q + finitely_generated_cone rays) := by rw [hrepr]
      _ = f '' Q + f '' finitely_generated_cone rays := Set.image_add f
      _ = f '' Q + finitely_generated_cone (fun i ↦ f (rays i)) := by
            rw [linearMap_image_finitelyGeneratedCone]
  have hImage_polyhedron : is_polyhedron (f '' polyhedron_le_set A b) := by
    exact (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).2
      ⟨f '' Q, hImage_polytope, q, fun i ↦ f (rays i), hImage_repr⟩
  rcases hImage_polyhedron with ⟨m', A', b', hImage_matrix⟩
  have hImage_nonempty : (f '' polyhedron_le_set A b).Nonempty := hP_nonempty.image f
  have hImage_repr_vertices :
      polyhedron_le_set A' b' =
        convexHull ℝ (Set.range fun i ↦ f (vertices i)) +
          finitely_generated_cone (fun i ↦ f (rays i)) := by
    rw [← hImage_matrix, hImage_repr, hQ_vertices, LinearMap.image_convexHull]
    congr 2
    ext z
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨vertices i, ⟨i, rfl⟩, rfl⟩
  have hrec_image :
      recessionCone (f '' polyhedron_le_set A b) =
        finitely_generated_cone (fun i ↦ f (rays i)) := by
    rw [hImage_matrix]
    exact polyhedron_recessionCone_eq_finitely_generated_cone A' b'
      (fun i ↦ f (vertices i)) (fun i ↦ f (rays i))
      (by rwa [← hImage_matrix]) hImage_repr_vertices
  rw [hrec_image, hrec_source, linearMap_image_finitelyGeneratedCone]

/-- Helper for Theorem 3.37: the quotient-coordinate map modulo the lineality submodule of `P`. -/
noncomputable abbrev linealityQuotientCoordinateMap (P : Set (Fin n → ℝ)) :
    (Fin n → ℝ) →ₗ[ℝ]
      (Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ linealitySubmodule P)) → ℝ) :=
  ((Module.finBasis ℝ ((Fin n → ℝ) ⧸ linealitySubmodule P)).equivFun.toLinearMap).comp
    (linealitySubmodule P).mkQ

/-- Helper for Theorem 3.37: the quotient-coordinate map kills exactly the lineality submodule. -/
lemma linealityQuotientCoordinateMap_ker (P : Set (Fin n → ℝ)) :
    LinearMap.ker (linealityQuotientCoordinateMap P) = linealitySubmodule P := by
  -- The canonical quotient coordinates are injective on the quotient, so composing them with the
  -- quotient map does not enlarge the kernel.
  simpa [linealityQuotientCoordinateMap] using
    quotient_coordinate_map_ker_eq_submodule (U := linealitySubmodule P)

/-- A lineality direction of `recessionCone P` is already a lineality direction of `P`. -/
lemma mem_linealitySpace_of_mem_linealitySpace_recessionCone
    {P : Set (Fin n → ℝ)} {d : Fin n → ℝ}
    (hd : d ∈ linealitySpace (recessionCone P)) :
    d ∈ linealitySpace P := by
  rw [linealitySpace_eq_recessionCone_inter_neg]
  constructor
  · have hd_rec :=
      (mem_linealitySpace_iff.mp hd) (zero_mem_recessionCone : (0 : Fin n → ℝ) ∈ recessionCone P)
        1
    simpa using hd_rec
  · rw [mem_neg_recessionCone_iff]
    have hneg_rec :=
      (mem_linealitySpace_iff.mp hd) (zero_mem_recessionCone : (0 : Fin n → ℝ) ∈ recessionCone P)
        (-1)
    simpa using hneg_rec

/-- Taking the recession cone does not change the lineality space. -/
lemma linealitySpace_recessionCone_eq
    (P : Set (Fin n → ℝ)) :
    linealitySpace (recessionCone P) = linealitySpace P := by
  ext d
  constructor
  · -- A lineality direction of the recession cone is already lineal for the ambient set.
    exact mem_linealitySpace_of_mem_linealitySpace_recessionCone
  · intro hd
    rw [mem_linealitySpace_iff] at hd ⊢
    intro r hr a
    rw [mem_recessionCone_iff] at hr ⊢
    intro x hx b hb
    have hxd : x + (b * a) • d ∈ P := hd hx (b * a)
    have hsum : x + (b * a) • d + b • r ∈ P := hr hxd b hb
    -- Reassociate the two translated directions into the target recession-cone normal form.
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
      using hsum

/-- If `P` is pointed, then `recessionCone P` is pointed as well. -/
lemma recessionCone_pointed_of_pointed
    {P : Set (Fin n → ℝ)}
    (hP_pointed : is_pointed P) :
    is_pointed (recessionCone P) := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro d hd
  have hdP : d ∈ linealitySpace P :=
    mem_linealitySpace_of_mem_linealitySpace_recessionCone hd
  exact (is_pointed_iff_eq_zero_of_mem_linealitySpace.mp hP_pointed) d hdP

/-- Helper for Theorem 3.37: if two recession directions sum to a lineality direction, then each
summand is already lineal. -/
lemma mem_linealitySpace_of_mem_recessionCone_add
    {P : Set (Fin n → ℝ)} {u v : Fin n → ℝ}
    (hu : u ∈ recessionCone P)
    (hv : v ∈ recessionCone P)
    (huv : u + v ∈ linealitySpace P) :
    u ∈ linealitySpace P := by
  rw [linealitySpace_eq_recessionCone_inter_neg] at huv ⊢
  refine ⟨hu, ?_⟩
  have hneg_sum : -(u + v) ∈ recessionCone P := huv.2
  -- Add the known recession direction `v` back to the negated sum to recover `-u`.
  have hneg_u : -u = -(u + v) + v := by
    abel
  rw [mem_neg_recessionCone_iff]
  change -u ∈ (recessionPointedCone ℝ P : Set (Fin n → ℝ))
  rw [hneg_u]
  change -(u + v) ∈ (recessionPointedCone ℝ P : Set (Fin n → ℝ)) at hneg_sum
  change v ∈ (recessionPointedCone ℝ P : Set (Fin n → ℝ)) at hv
  exact add_mem
    hneg_sum hv

/-- Helper for Theorem 3.37: mapping a finitely generated recession cone through the quotient
coordinates maps the seed generators pointwise. -/
lemma linealityQuotientCoordinateImage_eq_cone_image_generators
    (P : Set (Fin n → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin n → ℝ)
    (hrec : recessionCone P = cone (Set.range rays)) :
    linealityQuotientCoordinateMap P '' recessionCone P =
      cone (Set.range fun i : Fin q ↦ linealityQuotientCoordinateMap P (rays i)) := by
  classical
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hrec] at hz
    rcases mem_cone_iff.mp hz with ⟨m, gens, hgens, hcomb⟩
    refine mem_cone_iff.mpr ⟨m, fun i ↦ linealityQuotientCoordinateMap P (gens i), ?_, ?_⟩
    · intro i
      rcases hgens i with ⟨j, hj⟩
      exact ⟨j, by simp [hj]⟩
    · rcases hcomb with ⟨coeff, hcoeff_nonneg, hsum⟩
      refine ⟨coeff, hcoeff_nonneg, ?_⟩
      calc
        linealityQuotientCoordinateMap P z
            = linealityQuotientCoordinateMap P (∑ i, coeff i • gens i) := by rw [hsum]
        _ = ∑ i, coeff i • linealityQuotientCoordinateMap P (gens i) := by
              simp [map_sum]
  · intro hx
    rcases mem_cone_iff.mp hx with ⟨m, gens, hgens, hcomb⟩
    let src : Fin m → Fin n → ℝ := fun i ↦ rays (Classical.choose (hgens i))
    have hsrc_mem :
        ∀ i : Fin m, src i ∈ Set.range rays := by
      intro i
      exact Set.mem_range_self (Classical.choose (hgens i))
    have hsrc_map :
        ∀ i : Fin m, linealityQuotientCoordinateMap P (src i) = gens i := by
      intro i
      exact Classical.choose_spec (hgens i)
    rcases hcomb with ⟨coeff, hcoeff_nonneg, hsum⟩
    let z : Fin n → ℝ := ∑ i, coeff i • src i
    refine ⟨z, ?_, ?_⟩
    · rw [hrec]
      refine mem_cone_iff.mpr ⟨m, src, ?_, ⟨coeff, hcoeff_nonneg, rfl⟩⟩
      intro i
      exact hsrc_mem i
    · calc
        linealityQuotientCoordinateMap P z
            = ∑ i, coeff i • linealityQuotientCoordinateMap P (src i) := by
                simp [z, map_sum]
        _ = ∑ i, coeff i • gens i := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [hsrc_map i]
        _ = x := hsum.symm

/-- Helper for Theorem 3.37: the quotient-coordinate image of the recession cone is pointed. -/
lemma linealityQuotientCoordinateImage_recessionCone_pointed
    (P : Set (Fin n → ℝ)) :
    is_pointed (linealityQuotientCoordinateMap P '' recessionCone P) := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro x hx
  rw [mem_linealitySpace_iff] at hx
  have hzero_mem :
      (0 :
        Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ linealitySubmodule P)) → ℝ) ∈
        linealityQuotientCoordinateMap P '' recessionCone P := by
    refine ⟨0, zero_mem_recessionCone, ?_⟩
    simp [linealityQuotientCoordinateMap]
  have hx_pos :
      x ∈ linealityQuotientCoordinateMap P '' recessionCone P := by
    simpa using hx hzero_mem 1
  have hx_neg :
      -x ∈ linealityQuotientCoordinateMap P '' recessionCone P := by
    simpa using hx hzero_mem (-1)
  rcases hx_pos with ⟨u, hu, hu_map⟩
  rcases hx_neg with ⟨v, hv, hv_map⟩
  have huv_submodule : u + v ∈ linealitySubmodule P := by
    have huv_zero : linealityQuotientCoordinateMap P (u + v) = 0 := by
      rw [LinearMap.map_add, hu_map, hv_map]
      simp
    rw [← linealityQuotientCoordinateMap_ker P, LinearMap.mem_ker]
    exact huv_zero
  have huv_lineality : u + v ∈ linealitySpace P := by
    rw [mem_linealitySubmodule_iff] at huv_submodule
    exact huv_submodule
  have hu_lineality : u ∈ linealitySpace P :=
    mem_linealitySpace_of_mem_recessionCone_add hu hv huv_lineality
  have hu_submodule : u ∈ linealitySubmodule P := by
    rw [mem_linealitySubmodule_iff]
    exact hu_lineality
  have hu_ker : u ∈ LinearMap.ker (linealityQuotientCoordinateMap P) := by
    rw [linealityQuotientCoordinateMap_ker P]
    exact hu_submodule
  have hu_zero : linealityQuotientCoordinateMap P u = 0 := by
    simpa [LinearMap.mem_ker] using hu_ker
  simpa [hu_map] using hu_zero

/-- Helper for Theorem 3.37: if the quotient-coordinate image of `z` lies in the convex hull of
the quotient images of `X`, then `z` differs from a point of `convexHull ℝ X` by a lineality
vector. -/
lemma mem_convexHull_add_lineality_of_linealityQuotientCoordinateMap_mem_convexHullImage
    (P X : Set (Fin n → ℝ))
    {z : Fin n → ℝ}
    (hz_map :
      linealityQuotientCoordinateMap P z ∈
        convexHull ℝ (linealityQuotientCoordinateMap P '' X)) :
    z ∈ convexHull ℝ X + linealitySpace P := by
  let π := linealityQuotientCoordinateMap P
  have himage_subset : π '' X ⊆ π '' convexHull ℝ X := by
    intro w hw
    rcases hw with ⟨x, hxX, rfl⟩
    exact ⟨x, subset_convexHull ℝ X hxX, rfl⟩
  have himage_convex : Convex ℝ (π '' convexHull ℝ X) := by
    intro a ha b hb α β hα hβ hαβ
    rcases ha with ⟨a₀, ha₀, rfl⟩
    rcases hb with ⟨b₀, hb₀, rfl⟩
    refine ⟨α • a₀ + β • b₀, ?_, ?_⟩
    · exact (convex_convexHull ℝ X) ha₀ hb₀ hα hβ hαβ
    · simp [LinearMap.map_add, LinearMap.map_smul]
  have hz_image : π z ∈ π '' convexHull ℝ X := by
    exact (convexHull_min himage_subset himage_convex) hz_map
  rcases hz_image with ⟨c, hc_hull, hc_map⟩
  have hdiff_submodule : z - c ∈ linealitySubmodule P := by
    have hdiff_zero : π (z - c) = 0 := by
      rw [LinearMap.map_sub, hc_map]
      simp
    rw [← linealityQuotientCoordinateMap_ker P, LinearMap.mem_ker]
    exact hdiff_zero
  have hdiff_lineality : z - c ∈ linealitySpace P := by
    rw [mem_linealitySubmodule_iff] at hdiff_submodule
    exact hdiff_submodule
  refine Set.mem_add.mpr ⟨c, hc_hull, z - c, hdiff_lineality, ?_⟩
  abel

/-- Helper for Theorem 3.37: any conic combination of quotient images of recession generators is
itself the quotient image of a recession direction. -/
lemma mem_linealityQuotientCoordinateImage_recessionCone_of_mem_coneImage
    (P Y : Set (Fin n → ℝ))
    (hY_subset : Y ⊆ recessionCone P)
    {zq :
      Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ linealitySubmodule P)) → ℝ}
    (hzq :
      zq ∈ cone (linealityQuotientCoordinateMap P '' Y)) :
    zq ∈ linealityQuotientCoordinateMap P '' recessionCone P := by
  classical
  rcases mem_cone_iff.mp hzq with ⟨m, gens, hgens, hcomb⟩
  let ys : Fin m → Fin n → ℝ := fun i ↦ Classical.choose (hgens i)
  have hys_mem : ∀ i : Fin m, ys i ∈ Y := by
    intro i
    exact (Classical.choose_spec (hgens i)).1
  have hys_map :
      ∀ i : Fin m, linealityQuotientCoordinateMap P (ys i) = gens i := by
    intro i
    exact (Classical.choose_spec (hgens i)).2
  rcases hcomb with ⟨coeff, hcoeff_nonneg, hsum⟩
  let z : Fin n → ℝ := ∑ i, coeff i • ys i
  refine ⟨z, ?_, ?_⟩
  · change z ∈ (recessionPointedCone ℝ P : Set (Fin n → ℝ))
    exact
      PointedCone.conicCombination_mem
        (fun i ↦ hY_subset (hys_mem i))
        ⟨coeff, hcoeff_nonneg, rfl⟩
  · calc
      linealityQuotientCoordinateMap P z
          = ∑ i, coeff i • linealityQuotientCoordinateMap P (ys i) := by
              simp [z, map_sum]
      _ = ∑ i, coeff i • gens i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hys_map i]
      _ = zq := hsum.symm

/-- Helper for Theorem 3.37: if the quotient-coordinate image of a recession direction lies in the
cone generated by the quotient images of `Y`, then the original direction differs from a conic
combination of `Y` by a lineality vector. -/
lemma mem_cone_add_lineality_of_linealityQuotientCoordinateMap_mem_coneImage
    (P Y : Set (Fin n → ℝ))
    {z : Fin n → ℝ}
    (_hz : z ∈ recessionCone P)
    (hz_map :
      linealityQuotientCoordinateMap P z ∈
        cone (linealityQuotientCoordinateMap P '' Y)) :
    z ∈ cone Y + linealitySpace P := by
  classical
  rcases mem_cone_iff.mp hz_map with ⟨m, gens, hgens, hcomb⟩
  let ys : Fin m → Fin n → ℝ := fun i ↦ Classical.choose (hgens i)
  have hys_mem : ∀ i : Fin m, ys i ∈ Y := by
    intro i
    exact (Classical.choose_spec (hgens i)).1
  have hys_map : ∀ i : Fin m, linealityQuotientCoordinateMap P (ys i) = gens i := by
    intro i
    exact (Classical.choose_spec (hgens i)).2
  rcases hcomb with ⟨coeff, hcoeff_nonneg, hsum⟩
  let c : Fin n → ℝ := ∑ i, coeff i • ys i
  have hc_cone : c ∈ cone Y := by
    refine mem_cone_iff.mpr ⟨m, ys, hys_mem, ⟨coeff, hcoeff_nonneg, rfl⟩⟩
  have hmap_eq : linealityQuotientCoordinateMap P z = linealityQuotientCoordinateMap P c := by
    calc
      linealityQuotientCoordinateMap P z = ∑ i, coeff i • gens i := hsum
      _ = ∑ i, coeff i • linealityQuotientCoordinateMap P (ys i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hys_map i]
      _ = linealityQuotientCoordinateMap P c := by
            simp [c, map_sum]
  have hdiff_submodule : z - c ∈ linealitySubmodule P := by
    have hdiff_zero : linealityQuotientCoordinateMap P (z - c) = 0 := by
      rw [LinearMap.map_sub, hmap_eq]
      simp
    rw [← linealityQuotientCoordinateMap_ker P, LinearMap.mem_ker]
    exact hdiff_zero
  have hdiff_lineality : z - c ∈ linealitySpace P := by
    rw [mem_linealitySubmodule_iff] at hdiff_submodule
    exact hdiff_submodule
  refine Set.mem_add.mpr ⟨c, hc_cone, z - c, hdiff_lineality, ?_⟩
  abel

end RecessionConeSupport
