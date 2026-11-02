import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_theorem_3_17
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_24
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_theorem_3_27
import Mathlib.Data.ZMod.Basic

section Theorem619

open scoped IntegerVectorNotation Matrix

variable {p : ℕ}

/-- Helper for Theorem 6.19: coordinatewise parity equality makes the arithmetic midpoint of two
embedded integer vectors an embedded integer vector again. -/
lemma sameParity_midpoint_memIntegerLattice
    {z z' : Fin p → ℤ}
    (hparity : ∀ i : Fin p, (z i : ZMod 2) = (z' i : ZMod 2)) :
    midpoint ℝ (Int.cast ∘ z) (Int.cast ∘ z') ∈ (ℤ^p : Set (Fin p → ℝ)) := by
  -- Repackage the midpoint coordinates as integer half-sums.
  refine (mem_integerVectors_iff).2 ?_
  refine ⟨fun i ↦ (z i + z' i) / 2, ?_⟩
  ext i
  have hsumEven : Even (z i + z' i) := by
    -- Modulo `2`, equal endpoints give an even coordinate sum.
    rw [← ZMod.intCast_eq_zero_iff_even]
    calc
      (((z i + z' i : ℤ) : ZMod 2)) = ((z i : ZMod 2) + (z' i : ZMod 2)) := by
        simp
      _ = ((z i : ZMod 2) - (z' i : ZMod 2)) := by
        rw [sub_eq_add_neg]
        simp
      _ = ((z i - z' i : ℤ) : ZMod 2) := by
        simp
      _ = 0 := by
        rw [Int.cast_sub, hparity i, sub_self]
  rw [even_iff_two_dvd] at hsumEven
  calc
    midpoint ℝ ((z i : ℝ)) ((z' i : ℝ)) = (((z i : ℝ) + (z' i : ℝ)) / 2) := by
      simp [midpoint, AffineMap.lineMap_apply_module]
      ring
    _ = ((((z i + z' i) / 2 : ℤ) : ℝ)) := by
      symm
      have htwo_ne : ((2 : ℤ) : ℝ) ≠ 0 := by norm_num
      simpa using (Int.cast_div hsumEven htwo_ne)

/-- Helper for Theorem 6.19: strict satisfaction of every row in a finite linear-inequality system
puts a point in the ambient interior of that feasible set. -/
lemma strictRows_mem_interior_linearInequalitySet
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    {A : Matrix ι (Fin p) ℝ}
    {b : ι → ℝ}
    {x : Fin p → ℝ}
    (hstrict : ∀ i : ι, (A *ᵥ x) i < b i) :
    x ∈ interior {y : Fin p → ℝ | A *ᵥ y ≤ b} := by
  let U : Set (Fin p → ℝ) := {y : Fin p → ℝ | ∀ i : ι, (A *ᵥ y) i < b i}
  have hU_open : IsOpen U := by
    -- Each strict row halfspace is open, and finitely many such halfspaces are intersected.
    classical
    rw [show U = ⋂ i : ι, {y : Fin p → ℝ | (A *ᵥ y) i < b i} by
      ext y
      simp [U]]
    refine isOpen_iInter_of_finite fun i ↦ ?_
    have hcont : Continuous fun y : Fin p → ℝ ↦ (A *ᵥ y) i := by
      continuity
    have hconst : Continuous fun _ : Fin p → ℝ ↦ b i := continuous_const
    exact isOpen_lt hcont hconst
  have hxU : x ∈ U := hstrict
  have hUSubset : U ⊆ {y : Fin p → ℝ | A *ᵥ y ≤ b} := by
    intro y hy
    show A *ᵥ y ≤ b
    intro i
    exact (hy i).le
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hU_open.mem_nhds hxU) hUSubset

/-- Helper for Theorem 6.19: if an intrinsic-interior point of one singleton facet is also tight
on another remaining row, then the whole facet lies on that second singleton row. -/
lemma singletonFacet_subset_singletonRow_of_intrinsicInterior_eq_row
    {m : ℕ}
    {A : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {i j : Fin m}
    {x : Fin p → ℝ}
    (hx :
      x ∈ intrinsicInterior ℝ (active_constraint_face A b ({j} : Set (Fin m))))
    (hxi : (A *ᵥ x) i = b i) :
    active_constraint_face A b ({j} : Set (Fin m)) ⊆
      active_constraint_face A b ({i} : Set (Fin m)) := by
  let Fj : Set (Fin p → ℝ) := active_constraint_face A b ({j} : Set (Fin m))
  intro y hy
  have hyP : y ∈ polyhedron_le_set A b := mem_polyhedron_of_mem_active_constraint_face hy
  have hyi_eq : (A *ᵥ y) i = b i := by
    by_cases hyi_eq : (A *ᵥ y) i = b i
    · exact hyi_eq
    · -- An intrinsic-interior point lets us move slightly past `x` along the `y`-direction while
      -- staying inside the singleton facet; if row `i` were strict at `y`, that perturbation
      -- would violate feasibility on row `i`.
      have hyi_lt : (A *ᵥ y) i < b i := lt_of_le_of_ne (hyP i) hyi_eq
      rcases mem_intrinsicInterior.mp hx with ⟨xAff, hxAffInt, hxAff_eq⟩
      -- Local instance justification (torsor witness): the affine-span subtype needs a basepoint
      -- to inherit its affine-space structure, and the intrinsic-interior witness provides one.
      letI : Nonempty ↥(affineSpan ℝ Fj) := ⟨xAff⟩
      have hyAff_mem : y ∈ affineSpan ℝ Fj := subset_affineSpan ℝ Fj hy
      let yAff : affineSpan ℝ Fj := ⟨y, hyAff_mem⟩
      have hhom :
          ∀ᶠ δ in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
            AffineMap.homothety yAff δ xAff ∈ ((↑) ⁻¹' Fj : Set (affineSpan ℝ Fj)) := by
        exact
          (eventually_homothety_mem_of_mem_interior ℝ yAff hxAffInt).filter_mono
            nhdsWithin_le_nhds
      rcases (hhom.and self_mem_nhdsWithin).exists with ⟨δ, hδmem, hδgt⟩
      have hδgt' : 1 < δ := by simpa using hδgt
      have hz_eq :
          ((AffineMap.homothety yAff δ xAff : affineSpan ℝ Fj) : Fin p → ℝ) =
            AffineMap.homothety y δ x := by
        ext k
        simp [yAff, hxAff_eq, AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply]
      have hzFace : AffineMap.homothety y δ x ∈ Fj := by
        rw [← hz_eq]
        exact hδmem
      have hzP : AffineMap.homothety y δ x ∈ polyhedron_le_set A b :=
        mem_polyhedron_of_mem_active_constraint_face hzFace
      have hz_row :
          (A *ᵥ AffineMap.homothety y δ x) i =
            δ * b i + (1 - δ) * (A *ᵥ y) i := by
        calc
          (A *ᵥ AffineMap.homothety y δ x) i
              = (A *ᵥ ((1 - δ) • y + δ • x)) i := by
                  simp [AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply_module]
          _ = (1 - δ) * (A *ᵥ y) i + δ * (A *ᵥ x) i := by
                simp [Matrix.mulVec_add, Matrix.mulVec_smul]
          _ = δ * (A *ᵥ x) i + (1 - δ) * (A *ᵥ y) i := by ring
          _ = δ * b i + (1 - δ) * (A *ᵥ y) i := by rw [hxi]
      have hz_gt : b i < (A *ᵥ AffineMap.homothety y δ x) i := by
        have hδneg : 1 - δ < 0 := by linarith
        calc
          b i = δ * b i + (1 - δ) * b i := by ring
          _ < δ * b i + (1 - δ) * (A *ᵥ y) i := by
                have hmul_lt : (1 - δ) * b i < (1 - δ) * (A *ᵥ y) i :=
                  mul_lt_mul_of_neg_left hyi_lt hδneg
                linarith
          _ = (A *ᵥ AffineMap.homothety y δ x) i := hz_row.symm
      exact False.elim ((not_lt_of_ge (hzP i)) hz_gt)
  refine (mem_active_constraint_face_iff).2 ?_
  constructor
  · intro k hk
    have hki : k = i := by simpa using hk
    simpa [hki] using hyi_eq
  · intro k hk
    exact hyP k

/-- Helper for Theorem 6.19: an intrinsic-interior point of a singleton facet is strict on every
distinct remaining singleton facet row. -/
lemma intrinsicInteriorPoint_strict_on_distinctSingletonFacetRow
    {m : ℕ}
    {A : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {i j : Fin m}
    (hi : i ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) ≠
        active_constraint_face A b ({j} : Set (Fin m)))
    {x : Fin p → ℝ}
    (hx :
      x ∈ intrinsicInterior ℝ (active_constraint_face A b ({j} : Set (Fin m)))) :
    (A *ᵥ x) i < b i := by
  have hxFace : x ∈ active_constraint_face A b ({j} : Set (Fin m)) := intrinsicInterior_subset hx
  have hxP : x ∈ polyhedron_le_set A b := mem_polyhedron_of_mem_active_constraint_face hxFace
  by_contra hnot_lt
  have hxi_eq : (A *ᵥ x) i = b i := le_antisymm (hxP i) (not_lt.mp hnot_lt)
  have hsubset :
      active_constraint_face A b ({j} : Set (Fin m)) ⊆
        active_constraint_face A b ({i} : Set (Fin m)) :=
    singletonFacet_subset_singletonRow_of_intrinsicInterior_eq_row hx hxi_eq
  have hEq :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m)) :=
    singletonActiveConstraintFace_eq_of_subset_of_isFacet A b i j hi hfacet hsubset
  exact hij_face hEq

/-- Helper for Theorem 6.19: distinct facet-relative-interior points have interior midpoint. -/
lemma midpoint_memInterior_of_distinctFacetInteriorPoints
    {K F F' : Set (Fin p → ℝ)}
    (hpoly : is_polyhedron K)
    (hconv : Convex ℝ K)
    (hfull : affineSpan ℝ K = ⊤)
    (hF : IsFacetOf K F)
    (hF' : IsFacetOf K F')
    (hFF' : F ≠ F')
    {x y : Fin p → ℝ}
    (hx : x ∈ intrinsicInterior ℝ F)
    (hy : y ∈ intrinsicInterior ℝ F') :
    midpoint ℝ x y ∈ interior K := by
  -- Route correction: rewrite the two facets as singleton active-constraint faces of one
  -- polyhedron presentation, prove rowwise strictness on the remaining subsystem, and then pass to
  -- ambient interior.
  rcases hpoly with ⟨m, A, b, rfl⟩
  have hK_nonempty : (polyhedron_le_set A b).Nonempty := by
    rcases (Convex.interior_nonempty_iff_affineSpan_eq_top hconv).2 hfull with ⟨z, hz⟩
    exact ⟨z, interior_subset hz⟩
  rcases isFacetOf_iff.mp hF with ⟨hF_nonempty, hF_exposed, hF_codim⟩
  rcases isFacetOf_iff.mp hF' with ⟨hF'_nonempty, hF'_exposed, hF'_codim⟩
  have hF_facet : is_facet (polyhedron_le_set A b) F :=
    isFacet_of_nonempty_finrank_direction_affineSpan_add_one_eq
      A b F hF_exposed hF_nonempty hF_codim
  have hF'_facet : is_facet (polyhedron_le_set A b) F' :=
    isFacet_of_nonempty_finrank_direction_affineSpan_add_one_eq
      A b F' hF'_exposed hF'_nonempty hF'_codim
  rcases exists_eq_active_constraint_face_singleton_of_is_facet A b hK_nonempty F hF_facet with
    ⟨j, hF_eq⟩
  rcases exists_eq_active_constraint_face_singleton_of_is_facet A b hK_nonempty F' hF'_facet with
    ⟨j', hF'_eq⟩
  let Fj : Set (Fin p → ℝ) := active_constraint_face A b ({j.1} : Set (Fin m))
  let Fj' : Set (Fin p → ℝ) := active_constraint_face A b ({j'.1} : Set (Fin m))
  have hFj_nonempty : Fj.Nonempty := by
    simpa [Fj, hF_eq] using hF_nonempty
  have hFj'_nonempty : Fj'.Nonempty := by
    simpa [Fj', hF'_eq] using hF'_nonempty
  -- Local instance justification (torsor witness): the affine-span subtypes of the two singleton
  -- facets need explicit basepoints for the intrinsic-interior API.
  letI : Nonempty ↥(affineSpan ℝ Fj) := by
    rcases hFj_nonempty with ⟨z, hz⟩
    exact ⟨⟨z, subset_affineSpan ℝ Fj hz⟩⟩
  -- Local instance justification (torsor witness): the second singleton facet uses its own
  -- nonempty witness for the same affine-subspace structure.
  letI : Nonempty ↥(affineSpan ℝ Fj') := by
    rcases hFj'_nonempty with ⟨z, hz⟩
    exact ⟨⟨z, subset_affineSpan ℝ Fj' hz⟩⟩
  have hxFj : x ∈ intrinsicInterior ℝ Fj := by
    simpa [Fj, hF_eq] using hx
  have hyFj' : y ∈ intrinsicInterior ℝ Fj' := by
    simpa [Fj', hF'_eq] using hy
  have hxFj_mem : x ∈ Fj := intrinsicInterior_subset hxFj
  have hyFj'_mem : y ∈ Fj' := intrinsicInterior_subset hyFj'
  have hxP : x ∈ polyhedron_le_set A b := mem_polyhedron_of_mem_active_constraint_face hxFj_mem
  have hyP : y ∈ polyhedron_le_set A b := mem_polyhedron_of_mem_active_constraint_face hyFj'_mem
  have hFj_ne_Fj' : Fj ≠ Fj' := by
    intro hEq
    apply hFF'
    calc
      F = Fj := hF_eq
      _ = Fj' := hEq
      _ = F' := hF'_eq.symm
  have hFj_facet :
      is_facet (polyhedron_le_set A b) Fj := by
    simpa [Fj, hF_eq] using hF_facet
  have hFj'_facet :
      is_facet (polyhedron_le_set A b) Fj' := by
    simpa [Fj', hF'_eq] using hF'_facet
  have hstrict_remaining :
      ∀ i : {i // i ∈ remaining_inequality_indices A b},
        (remaining_inequality_matrix A b *ᵥ midpoint ℝ x y) i <
          remaining_inequality_rhs A b i := by
    intro i
    let Fi : Set (Fin p → ℝ) := active_constraint_face A b ({i.1} : Set (Fin m))
    have hmid_row :
        (A *ᵥ midpoint ℝ x y) i.1 =
          (1 / 2 : ℝ) * (A *ᵥ x) i.1 + (1 / 2 : ℝ) * (A *ᵥ y) i.1 := by
      calc
        (A *ᵥ midpoint ℝ x y) i.1
            = (A *ᵥ ((1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y)) i.1 := by
                simp [midpoint, AffineMap.lineMap_apply_module]
        _ = (1 - (1 / 2 : ℝ)) * (A *ᵥ x) i.1 + (1 / 2 : ℝ) * (A *ᵥ y) i.1 := by
              simp [Matrix.mulVec_add, Matrix.mulVec_smul]
        _ = (1 / 2 : ℝ) * (A *ᵥ x) i.1 + (1 / 2 : ℝ) * (A *ᵥ y) i.1 := by ring
    by_cases hiF : Fi = Fj
    · -- On the defining row class of `F`, `x` is tight and `y` is strict because the facets are
      -- distinct.
      have hxFi : x ∈ Fi := by
        simpa [Fi, hiF] using hxFj_mem
      have hxi_eq : (A *ᵥ x) i.1 = b i.1 := by
        have hi_singleton : i.1 ∈ ({i.1} : Set (Fin m)) := by simp
        exact (mem_active_constraint_face_iff.mp hxFi).1 i.1 hi_singleton
      have hiF_ne_Fj' : Fi ≠ Fj' := by
        intro hEq
        apply hFj_ne_Fj'
        calc
          Fj = Fi := hiF.symm
          _ = Fj' := hEq
      have hyi_lt : (A *ᵥ y) i.1 < b i.1 :=
        intrinsicInteriorPoint_strict_on_distinctSingletonFacetRow i.2 hFj'_facet hiF_ne_Fj' hyFj'
      have hmid_lt : (A *ᵥ midpoint ℝ x y) i.1 < b i.1 := by
        rw [hmid_row]
        linarith
      simpa [remaining_inequality_mulVec_apply, remaining_inequality_rhs_apply] using hmid_lt
    · by_cases hiF' : Fi = Fj'
      · -- Symmetrically, on the defining row class of `F'`, `y` is tight and `x` is strict.
        have hyFi : y ∈ Fi := by
          simpa [Fi, hiF'] using hyFj'_mem
        have hyi_eq : (A *ᵥ y) i.1 = b i.1 := by
          have hi_singleton : i.1 ∈ ({i.1} : Set (Fin m)) := by simp
          exact (mem_active_constraint_face_iff.mp hyFi).1 i.1 hi_singleton
        have hiF'_ne_Fj : Fi ≠ Fj := by
          intro hEq
          apply hFj_ne_Fj'
          calc
            Fj = Fi := hEq.symm
            _ = Fj' := hiF'
        have hxi_lt : (A *ᵥ x) i.1 < b i.1 :=
          intrinsicInteriorPoint_strict_on_distinctSingletonFacetRow i.2 hFj_facet hiF'_ne_Fj hxFj
        have hmid_lt : (A *ᵥ midpoint ℝ x y) i.1 < b i.1 := by
          rw [hmid_row]
          linarith
        simpa [remaining_inequality_mulVec_apply, remaining_inequality_rhs_apply] using hmid_lt
      · -- Away from both facet row classes, both intrinsic-interior points are strict.
        have hxi_lt : (A *ᵥ x) i.1 < b i.1 :=
          intrinsicInteriorPoint_strict_on_distinctSingletonFacetRow i.2 hFj_facet hiF hxFj
        have hyi_lt : (A *ᵥ y) i.1 < b i.1 :=
          intrinsicInteriorPoint_strict_on_distinctSingletonFacetRow i.2 hFj'_facet hiF' hyFj'
        have hmid_lt : (A *ᵥ midpoint ℝ x y) i.1 < b i.1 := by
          rw [hmid_row]
          linarith
        simpa [remaining_inequality_mulVec_apply, remaining_inequality_rhs_apply] using hmid_lt
  have hmidInterior_remaining :
      midpoint ℝ x y ∈
        interior {z : Fin p → ℝ |
          remaining_inequality_matrix A b *ᵥ z ≤ remaining_inequality_rhs A b} :=
    strictRows_mem_interior_linearInequalitySet hstrict_remaining
  have himp_eq_univ :
      ({z : Fin p → ℝ | implicit_equality_matrix A b *ᵥ z = implicit_equality_rhs A b} :
        Set (Fin p → ℝ)) = Set.univ := by
    rw [← affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set (A := A)
      (b := b)]
    simp [hfull]
  have hK_eq_remaining :
      polyhedron_le_set A b =
        {z : Fin p → ℝ |
          remaining_inequality_matrix A b *ᵥ z ≤ remaining_inequality_rhs A b} := by
    ext z
    rw [polyhedron_le_set_eq_implicit_eq_and_remaining_subsystems]
    constructor
    · intro hz
      exact hz.2
    · intro hz
      refine ⟨?_, hz⟩
      have hzImp :
          z ∈ ({z : Fin p → ℝ |
            implicit_equality_matrix A b *ᵥ z = implicit_equality_rhs A b} : Set (Fin p → ℝ)) := by
        simp [himp_eq_univ]
      simpa using hzImp
  simpa [hK_eq_remaining] using hmidInterior_remaining

/-- Helper for Theorem 6.19: the parity class attached to the Theorem 6.18 integer witness of a
facet determines that facet uniquely. -/
lemma facetParityClass_injective
    {K : Set (Fin p → ℝ)}
    (hpoly : is_polyhedron K)
    (hconv : Convex ℝ K)
    (hfull : affineSpan ℝ K = ⊤)
    (hfree : is_lattice_free K)
    (w :
      {F : Set (Fin p → ℝ) // IsFacetOf K F} →
        Fin p → ℤ)
    (hw :
      ∀ F : {F : Set (Fin p → ℝ) // IsFacetOf K F},
        (Int.cast ∘ w F) ∈ intrinsicInterior ℝ F.1) :
    Function.Injective (fun F : {F : Set (Fin p → ℝ) // IsFacetOf K F} ↦
      fun i : Fin p ↦ (w F i : ZMod 2)) := by
  intro F G hFG
  by_contra hne
  have hmidInt :
      midpoint ℝ (Int.cast ∘ w F) (Int.cast ∘ w G) ∈ (ℤ^p : Set (Fin p → ℝ)) := by
    exact sameParity_midpoint_memIntegerLattice (z := w F) (z' := w G) (fun i ↦ congrFun hFG i)
  have hmidInterior :
      midpoint ℝ (Int.cast ∘ w F) (Int.cast ∘ w G) ∈ interior K := by
    -- Distinct facet-relative-interior witnesses have an interior midpoint.
    exact midpoint_memInterior_of_distinctFacetInteriorPoints
      hpoly hconv hfull F.2 G.2 (by
        intro hEq
        apply hne
        exact Subtype.ext hEq)
      (hw F) (hw G)
  exact (is_lattice_free.not_mem_interior hfree hmidInt) hmidInterior

/-- Theorem 6.19. Any full-dimensional maximal lattice-free convex set `K ⊆ ℝ^p` has at most
`2^p` facets. -/
theorem maximal_lattice_free_facets_encard_le_two_pow
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    {F : Set (Fin p → ℝ) | IsFacetOf K F}.encard ≤ (2 ^ p : ℕ∞) := by
  classical
  -- Theorem 6.18 supplies the polyhedral presentation and one integer relative-interior witness
  -- on every facet.
  rcases
      (maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice hfull).mp hK with
    ⟨hpoly, hfree, hfacets⟩
  let w : {F : Set (Fin p → ℝ) // IsFacetOf K F} → Fin p → ℤ :=
    fun F ↦ Classical.choose (hfacets F.1 F.2)
  have hw :
      ∀ F : {F : Set (Fin p → ℝ) // IsFacetOf K F},
        (Int.cast ∘ w F) ∈ intrinsicInterior ℝ F.1 := by
    intro F
    exact Classical.choose_spec (hfacets F.1 F.2)
  have hparityInj :
      Function.Injective (fun F : {F : Set (Fin p → ℝ) // IsFacetOf K F} ↦
        fun i : Fin p ↦ (w F i : ZMod 2)) :=
    facetParityClass_injective hpoly (is_maximal_lattice_free.convex hK) hfull hfree w hw
  let parityEmbeddingBase :
      {F : Set (Fin p → ℝ) // IsFacetOf K F} ↪ (Fin p → ZMod 2) :=
    ⟨fun F ↦ fun i : Fin p ↦ (w F i : ZMod 2), hparityInj⟩
  let parityEmbedding :
      {F : Set (Fin p → ℝ) // IsFacetOf K F} ↪
        (Set.univ : Set (Fin p → ZMod 2)) :=
    parityEmbeddingBase.codRestrict Set.univ (fun _ ↦ by
      simp)
  -- Injecting the facet subtype into `Fin p → ZMod 2` gives the cardinal bound.
  calc
    {F : Set (Fin p → ℝ) | IsFacetOf K F}.encard
        ≤ (Set.univ : Set (Fin p → ZMod 2)).encard := by
          simpa using
            (Function.Embedding.encard_le parityEmbedding)
    _ = (2 ^ p : ℕ∞) := by
      rw [Set.encard_univ]
      simp [ZMod.card]

/-- A full-dimensional maximal lattice-free convex set has only finitely many facets. -/
theorem maximal_lattice_free_facets_finite
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    {F : Set (Fin p → ℝ) | IsFacetOf K F}.Finite :=
  Set.finite_of_encard_le_coe (maximal_lattice_free_facets_encard_le_two_pow hfull hK)

/-- Theorem 6.19 in finite-cardinality form: a full-dimensional maximal lattice-free convex set
has at most `2^p` facets. -/
theorem maximal_lattice_free_facets_ncard_le_two_pow
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    {F : Set (Fin p → ℝ) | IsFacetOf K F}.ncard ≤ 2 ^ p :=
  (Set.encard_le_coe_iff_finite_ncard_le.mp
    (maximal_lattice_free_facets_encard_le_two_pow hfull hK)).2

end Theorem619
