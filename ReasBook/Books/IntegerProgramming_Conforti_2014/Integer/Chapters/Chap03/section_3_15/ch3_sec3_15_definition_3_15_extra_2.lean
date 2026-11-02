import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_4.ch3_sec3_4_4_definition_3_4_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_theorem_3_11
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

-- Semantic recall note: this item is source-facing for `polyhedron_projection_cone`, but it
-- reuses the earlier Chapter 3 owners `cone`, `is_polyhedral_cone`, `is_pointed`,
-- `IsExtremeRayOfCone`, and mathlib's canonical ray-equivalence relation `SameRay` directly.

/-- The projection cone attached to the `z`-matrix `B` in a system `A *ᵥ x + B *ᵥ z ≤ b`,
namely the cone of nonnegative row multipliers that annihilate `B`. -/
def polyhedron_projection_cone
    {m p : ℕ}
    (B : Matrix (Fin m) (Fin p) ℝ) : Set (Fin m → ℝ) :=
  {u | 0 ≤ u ∧ u ᵥ* B = 0}

/-- Definition 3.15-extra-2 (1). Membership in the projection cone of
`P = { (x, z) ∈ ℝ^n × ℝ^p | A *ᵥ x + B *ᵥ z ≤ b }` is exactly the condition
`u ᵥ* B = 0` together with pointwise nonnegativity of `u`. -/
theorem mem_polyhedron_projection_cone_iff
    {m p : ℕ}
    {B : Matrix (Fin m) (Fin p) ℝ}
    {u : Fin m → ℝ} :
    u ∈ polyhedron_projection_cone B ↔ 0 ≤ u ∧ u ᵥ* B = 0 := by
  rfl

private lemma neg_single_one_dotProduct
    {m : ℕ}
    (u : Fin m → ℝ)
    (i : Fin m) :
    (fun j ↦ -Pi.single i (1 : ℝ) j) ⬝ᵥ u = -u i := by
  rw [dotProduct, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- The projection cone is polyhedral because it is already given by finitely many homogeneous
linear inequalities and equalities built from `B`. -/
theorem polyhedron_projection_cone_is_polyhedral
    {m p : ℕ}
    (B : Matrix (Fin m) (Fin p) ℝ) :
    is_polyhedral_cone (polyhedron_projection_cone B) := by
  let M : Matrix (Fin (p + (p + m))) (Fin m) ℝ :=
    Fin.addCases Bᵀ (Fin.addCases (-Bᵀ) fun i : Fin m ↦ -Pi.single i (1 : ℝ))
  refine (is_polyhedral_cone_iff).2 ?_
  refine ⟨p + (p + m), M, ?_⟩
  ext u
  constructor
  · rintro ⟨hu_nonneg, huB⟩
    intro s
    cases s using Fin.addCases with
    | left j =>
        have hjM : (M *ᵥ u) (Fin.castAdd (p + m) j) = (Bᵀ *ᵥ u) j := by
          simp [M, Matrix.mulVec, Fin.addCases_left]
        rw [hjM]
        have hj : (Bᵀ *ᵥ u) j = 0 := by
          simpa [Matrix.mulVec_transpose] using congrFun huB j
        simpa using hj.le
    | right s =>
        cases s using Fin.addCases with
        | left j =>
            have hjM : (M *ᵥ u) (Fin.natAdd p (Fin.castAdd m j)) = (-Bᵀ *ᵥ u) j := by
              simp [M, Matrix.mulVec, Fin.addCases_right, Fin.addCases_left]
            rw [hjM]
            have hj : (-Bᵀ *ᵥ u) j = 0 := by
              simpa [Matrix.neg_mulVec, Matrix.mulVec_transpose] using
                congrArg Neg.neg (congrFun huB j)
            simpa using hj.le
        | right i =>
            have hiM :
                (M *ᵥ u) (Fin.natAdd p (Fin.natAdd p i)) = -u i := by
              calc
                (M *ᵥ u) (Fin.natAdd p (Fin.natAdd p i))
                    = (fun j ↦ -Pi.single i (1 : ℝ) j) ⬝ᵥ u := by
                        simp [M, Matrix.mulVec, Fin.addCases_right]
                _ = -u i := neg_single_one_dotProduct u i
            rw [hiM]
            simpa using neg_nonpos.mpr (hu_nonneg i)
  · intro hu
    refine ⟨?_, ?_⟩
    · intro i
      have hi : (M *ᵥ u) (Fin.natAdd p (Fin.natAdd p i)) ≤ 0 := hu (Fin.natAdd p (Fin.natAdd p i))
      have hiM :
          (M *ᵥ u) (Fin.natAdd p (Fin.natAdd p i)) = -u i := by
        calc
          (M *ᵥ u) (Fin.natAdd p (Fin.natAdd p i))
              = (fun j ↦ -Pi.single i (1 : ℝ) j) ⬝ᵥ u := by
                  simp [M, Matrix.mulVec, Fin.addCases_right]
          _ = -u i := neg_single_one_dotProduct u i
      rw [hiM] at hi
      exact neg_nonpos.mp hi
    · ext j
      have hj_nonpos : (M *ᵥ u) (Fin.castAdd (p + m) j) ≤ 0 := hu (Fin.castAdd (p + m) j)
      have hj_neg_nonpos : (M *ᵥ u) (Fin.natAdd p (Fin.castAdd m j)) ≤ 0 :=
        hu (Fin.natAdd p (Fin.castAdd m j))
      have hj₁ : (u ᵥ* B) j ≤ 0 := by
        have hcol : (Bᵀ *ᵥ u) j ≤ 0 := by
          simpa [M, Matrix.mulVec, Fin.addCases_left] using hj_nonpos
        simpa [Matrix.mulVec_transpose] using hcol
      have hj₂ : 0 ≤ (u ᵥ* B) j := by
        have hnegcol : (-Bᵀ *ᵥ u) j ≤ 0 := by
          simpa [M, Matrix.mulVec, Fin.addCases_right, Fin.addCases_left] using hj_neg_nonpos
        have hnegcol' : -((Bᵀ *ᵥ u) j) ≤ 0 := by
          simpa [Matrix.neg_mulVec] using hnegcol
        have hcol : 0 ≤ (Bᵀ *ᵥ u) j := by
          exact neg_nonpos.mp hnegcol'
        simpa [Matrix.mulVec_transpose] using hcol
      exact le_antisymm hj₁ hj₂

/-- Helper for Definition 3.15-extra-2: every generator lies in the pointed-cone hull of its own
singleton. -/
lemma self_mem_singleton_pointedCone_hull
    {m : ℕ} (r : Fin m → ℝ) :
    r ∈ (PointedCone.hull ℝ ({r} : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) := by
  -- The singleton source set already contains its unique generator.
  have hr : r ∈ ({r} : Set (Fin m → ℝ)) := by
    simp
  exact PointedCone.subset_hull hr

/-- Helper for Definition 3.15-extra-2: the pointed-cone hull of the zero singleton is exactly
`{0}`. -/
lemma singleton_pointedCone_hull_zero
    {m : ℕ} :
    (PointedCone.hull ℝ ({(0 : Fin m → ℝ)} : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) =
      ({0} : Set (Fin m → ℝ)) := by
  ext x
  constructor
  · intro hx
    have hx_hull :
        x ∈ PointedCone.hull ℝ ({(0 : Fin m → ℝ)} : Set (Fin m → ℝ)) := by
      simpa using hx
    rw [PointedCone.mem_hull_set] at hx_hull
    rcases hx_hull with ⟨c, hc_source, _, hsum⟩
    -- Every source vector in the support is `0`, so the whole conic sum collapses to `0`.
    have hsum_zero : c.sum (fun m r ↦ r • m) = 0 := by
      calc
        c.sum (fun m r ↦ r • m) = ∑ y : c.support, c y • (y : Fin m → ℝ) := by
          rw [Finsupp.sum, ← Finset.sum_coe_sort c.support]
        _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro y hy
          have hy_zero : (y : Fin m → ℝ) = 0 := Set.mem_singleton_iff.mp (hc_source y.2)
          simp [hy_zero]
    have hx_zero : x = 0 := by
      rw [← hsum]
      exact hsum_zero
    simp [hx_zero]
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    -- The zero coefficient family is the canonical witness for `0 ∈ hull {0}`.
    change (0 : Fin m → ℝ) ∈ PointedCone.hull ℝ ({(0 : Fin m → ℝ)} : Set (Fin m → ℝ))
    rw [PointedCone.mem_hull_set]
    refine ⟨0, ?_, ?_, ?_⟩
    · simp
    · intro y
      simp
    · simp

/-- Helper for Definition 3.15-extra-2: an extreme ray generator belongs to the ambient cone whose
edge it spans. -/
lemma extreme_ray_mem_of_isExtremeRayOfCone
    {m : ℕ} {C : Set (Fin m → ℝ)} {r : Fin m → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    r ∈ C := by
  -- Unfold the extreme-ray alias and evaluate the extreme-subset condition at the generator itself.
  have hr_edge :
      IsEdgeOf C (PointedCone.hull ℝ ({r} : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hr
  exact hr_edge.isExtreme.1 (self_mem_singleton_pointedCone_hull r)

/-- Helper for Definition 3.15-extra-2: an extreme ray generator is necessarily nonzero. -/
lemma extreme_ray_ne_zero
    {m : ℕ} {C : Set (Fin m → ℝ)} {r : Fin m → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    r ≠ 0 := by
  -- Rewriting the ray generator as `0` would force the supporting edge to have dimension `0`.
  have hr_edge :
      IsEdgeOf C (PointedCone.hull ℝ ({r} : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hr
  intro hr_zero
  have hzero_edge : IsEdgeOf C ({0} : Set (Fin m → ℝ)) := by
    simpa [hr_zero, singleton_pointedCone_hull_zero] using hr_edge
  have hdim_zero : Module.finrank ℝ (affineSpan ℝ ({0} : Set (Fin m → ℝ))).direction = 0 := by
    rw [direction_affineSpan, vectorSpan_singleton]
    simp
  have hdim_one : Module.finrank ℝ (affineSpan ℝ ({0} : Set (Fin m → ℝ))).direction = 1 :=
    hzero_edge.finrank_direction_eq_one
  have : (0 : ℕ) = 1 := by
    rwa [hdim_zero] at hdim_one
  exact Nat.zero_ne_one this

/-- Helper for Definition 3.15-extra-2: a nonzero vector on the same ray as a listed generator of
`finitely_generated_cone rays` also lies in that cone. -/
lemma sameRay_mem_finitely_generated_cone_of_mem_of_nonzero
    {m q : ℕ}
    {rays : Fin q → Fin m → ℝ}
    {x y : Fin m → ℝ}
    (hy_nonzero : y ≠ 0)
    (hxy : SameRay ℝ x y)
    (hy : y ∈ finitely_generated_cone rays) :
    x ∈ finitely_generated_cone rays := by
  -- The nonzero endpoint lets us rewrite `x` as a nonnegative scalar multiple of `y`.
  rcases hxy.exists_nonneg_right hy_nonzero with ⟨a, ha, rfl⟩
  exact cone_smul_mem hy ha

/-- Helper for Definition 3.15-extra-2: every extreme generator of the projection cone lies in the
cone generated by any representative family of all extreme rays. -/
lemma extreme_generator_mem_listed_cone
    {m p q : ℕ}
    (B : Matrix (Fin m) (Fin p) ℝ)
    (rays : Fin q → Fin m → ℝ)
    (h_rays_extreme :
      ∀ t : Fin q, IsExtremeRayOfCone (polyhedron_projection_cone B) (rays t))
    (h_extreme_rep :
      ∀ r : Fin m → ℝ, IsExtremeRayOfCone (polyhedron_projection_cone B) r →
        ∃ t : Fin q, SameRay ℝ r (rays t))
    {g : Fin m → ℝ}
    (hg : IsExtremeRayOfCone (polyhedron_projection_cone B) g) :
    g ∈ finitely_generated_cone rays := by
  -- Choose the listed representative of the same ray.
  -- Then transport membership back along `SameRay`.
  rcases h_extreme_rep g hg with ⟨t, hsame⟩
  have hray_mem : rays t ∈ finitely_generated_cone rays := by
    exact subset_cone (Set.range rays) (Set.mem_range_self t)
  have hray_nonzero : rays t ≠ 0 := extreme_ray_ne_zero (h_rays_extreme t)
  exact sameRay_mem_finitely_generated_cone_of_mem_of_nonzero hray_nonzero hsame hray_mem

/-- Helper for Definition 3.15-extra-2: the projection cone contains no nonzero vector together
with its negative. -/
lemma eq_zero_of_mem_projection_cone_of_neg_mem
    {m p : ℕ}
    {B : Matrix (Fin m) (Fin p) ℝ}
    {v : Fin m → ℝ}
    (hv : v ∈ polyhedron_projection_cone B)
    (hnegv : -v ∈ polyhedron_projection_cone B) :
    v = 0 := by
  -- Compare the pointwise nonnegativity constraints for `v` and `-v`.
  obtain ⟨hv_nonneg, _⟩ := mem_polyhedron_projection_cone_iff.mp hv
  obtain ⟨hnegv_nonneg, _⟩ := mem_polyhedron_projection_cone_iff.mp hnegv
  ext i
  exact le_antisymm (neg_nonneg.mp (hnegv_nonneg i)) (hv_nonneg i)

/-- Helper for Definition 3.15-extra-2: the projection cone is closed under nonnegative scalar
multiplication. -/
lemma smul_mem_polyhedron_projection_cone
    {m p : ℕ}
    {B : Matrix (Fin m) (Fin p) ℝ}
    {u : Fin m → ℝ}
    (hu : u ∈ polyhedron_projection_cone B)
    {a : ℝ}
    (ha : 0 ≤ a) :
    a • u ∈ polyhedron_projection_cone B := by
  obtain ⟨hu_nonneg, hu_annihilates⟩ := mem_polyhedron_projection_cone_iff.mp hu
  refine mem_polyhedron_projection_cone_iff.mpr ⟨?_, ?_⟩
  · intro i
    simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg ha (hu_nonneg i)
  · rw [Matrix.smul_vecMul, hu_annihilates, smul_zero]

/-- Helper for Definition 3.15-extra-2: the source-facing finitely generated cone agrees with the
canonical matrix-column cone built from the same finite ray family. -/
lemma finitely_generated_cone_eq_matrix_cone
    {m q : ℕ} (rays : Fin q → Fin m → ℝ) :
    finitely_generated_cone rays =
      (matrix_cone (fun i j ↦ rays j i) : Set (Fin m → ℝ)) := by
  -- Both owners encode the same cone generated by the range of `rays`.
  calc
    finitely_generated_cone rays = cone (Set.range rays) := rfl
    _ = (PointedCone.hull ℝ (Set.range rays) : Set (Fin m → ℝ)) := by
          symm
          exact pointedCone_hull_eq_cone (Set.range rays)
    _ = (matrix_cone (fun i j ↦ rays j i) : Set (Fin m → ℝ)) := by
          rfl

/-- Helper for Definition 3.15-extra-2: a finitely generated cone is closed under adding a
nonnegative multiple of another point from the same cone. -/
lemma finitely_generated_cone_add_smul_mem
    {m q : ℕ} (rays : Fin q → Fin m → ℝ)
    {y r : Fin m → ℝ}
    (hy : y ∈ finitely_generated_cone rays)
    (hr : r ∈ finitely_generated_cone rays)
    {a : ℝ} (ha : 0 ≤ a) :
    y + a • r ∈ finitely_generated_cone rays := by
  -- Expand both cone memberships into nonnegative coefficient families.
  rcases mem_finitely_generated_cone_iff.mp hy with ⟨μ, hμ_nonneg, rfl⟩
  rcases mem_finitely_generated_cone_iff.mp hr with ⟨ν, hν_nonneg, rfl⟩
  refine mem_finitely_generated_cone_iff.mpr ⟨fun i ↦ μ i + a * ν i, ?_, ?_⟩
  · -- The updated coefficients remain nonnegative.
    intro i
    exact add_nonneg (hμ_nonneg i) (mul_nonneg ha (hν_nonneg i))
  · -- Distributing the new coefficients reconstructs `y + a • r`.
    calc
      (∑ i, μ i • rays i) + a • ∑ i, ν i • rays i
          = (∑ i, μ i • rays i) + ∑ i, (a * ν i) • rays i := by
              congr 1
              rw [Finset.smul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [smul_smul]
      _ = ∑ i, (μ i • rays i + (a * ν i) • rays i) := by
            rw [← Finset.sum_add_distrib]
      _ = ∑ i, (μ i + a * ν i) • rays i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [add_smul]

/-- Helper for Definition 3.15-extra-2: any conic representation can be split into the chosen
generator together with a point in the deleted subcone. -/
lemma mem_finitely_generated_cone_split_generator
    {m q : ℕ}
    {rays : Fin (q + 1) → Fin m → ℝ}
    {i : Fin (q + 1)}
    {x : Fin m → ℝ}
    (hx : x ∈ finitely_generated_cone rays) :
    ∃ a : ℝ, 0 ≤ a ∧
      ∃ y : Fin m → ℝ, y ∈ finitely_generated_cone (fun j : Fin q ↦ rays (i.succAbove j)) ∧
        x = a • rays i + y := by
  rcases mem_finitely_generated_cone_iff.mp hx with ⟨μ, hμ_nonneg, hsum⟩
  refine ⟨μ i, hμ_nonneg i, ∑ j : Fin q, μ (i.succAbove j) • rays (i.succAbove j), ?_, ?_⟩
  · -- The tail coefficients witness membership in the cone generated by the deleted family.
    refine mem_finitely_generated_cone_iff.mpr ⟨fun j ↦ μ (i.succAbove j), ?_, rfl⟩
    intro j
    exact hμ_nonneg (i.succAbove j)
  · -- Splitting the total coefficient sum at `i` isolates the chosen generator.
    calc
      x = ∑ j : Fin (q + 1), μ j • rays j := hsum
      _ = μ i • rays i + ∑ j : Fin q, μ (i.succAbove j) • rays (i.succAbove j) := by
            simpa using (Fin.sum_univ_succAbove (f := fun j : Fin (q + 1) ↦ μ j • rays j) i)

/-- Helper for Definition 3.15-extra-2: if one listed generator already lies in the cone generated
by the remaining rays, then deleting it does not change the generated cone. -/
lemma finitely_generated_cone_eq_of_generator_mem_delete
    {m q : ℕ}
    (rays : Fin (q + 1) → Fin m → ℝ)
    (i : Fin (q + 1))
    (hi :
      rays i ∈ finitely_generated_cone (fun j : Fin q ↦ rays (i.succAbove j))) :
    finitely_generated_cone rays =
      finitely_generated_cone (fun j : Fin q ↦ rays (i.succAbove j)) := by
  apply le_antisymm
  · intro x hx
    rcases mem_finitely_generated_cone_split_generator (i := i) hx with
      ⟨a, ha, y, hy, hsplit⟩
    -- The deleted cone contains both the tail point and the nonnegative multiple of the removed
    -- ray.
    have hai : a • rays i ∈ finitely_generated_cone (fun j : Fin q ↦ rays (i.succAbove j)) :=
      cone_smul_mem hi ha
    have hsum :
        y + a • rays i ∈ finitely_generated_cone (fun j : Fin q ↦ rays (i.succAbove j)) :=
      finitely_generated_cone_add_smul_mem (fun j : Fin q ↦ rays (i.succAbove j)) hy hi ha
    simpa [hsplit, add_comm] using hsum
  · -- Every deleted generator is already one of the original generators.
    simpa [finitely_generated_cone] using
      (cone_min (S := Set.range fun j : Fin q ↦ rays (i.succAbove j)) (T := Set.range rays)
        (by
          rintro _ ⟨j, rfl⟩
          exact subset_cone (Set.range rays) (Set.mem_range_self (i.succAbove j))))

/-- Helper for Definition 3.15-extra-2: a non-extreme listed generator of the projection cone is
already generated by the remaining rays. -/
lemma nonextreme_generator_mem_delete
    {m p q : ℕ}
    (B : Matrix (Fin m) (Fin p) ℝ)
    (rays : Fin (q + 1) → Fin m → ℝ)
    (i : Fin (q + 1))
    (h_cone : polyhedron_projection_cone B = finitely_generated_cone rays)
    (hi_not_extreme : ¬ IsExtremeRayOfCone (polyhedron_projection_cone B) (rays i)) :
    rays i ∈ finitely_generated_cone (fun j : Fin q ↦ rays (i.succAbove j)) := by
  let deleted : Fin q → Fin m → ℝ := fun j ↦ rays (i.succAbove j)
  have hdeleted_subset :
      finitely_generated_cone deleted ⊆ polyhedron_projection_cone B := by
    -- Every deleted generator is still one of the original generators, hence remains in the cone.
    intro x hx
    rw [h_cone]
    have hsubset :
        finitely_generated_cone deleted ⊆ finitely_generated_cone rays := by
      simpa [deleted, finitely_generated_cone] using
        (cone_min (S := Set.range deleted) (T := Set.range rays)
          (by
            rintro _ ⟨j, rfl⟩
            exact subset_cone (Set.range rays) (Set.mem_range_self (i.succAbove j))))
    exact hsubset hx
  have hgi_mem : rays i ∈ polyhedron_projection_cone B := by
    rw [h_cone]
    exact subset_cone (Set.range rays) (Set.mem_range_self i)
  by_cases hgi_zero : rays i = 0
  · -- The zero vector belongs to every finitely generated cone.
    refine mem_finitely_generated_cone_iff.mpr ⟨fun _ ↦ 0, ?_, ?_⟩
    · intro j
      simp
    · simp [hgi_zero]
  · classical
    -- Route correction: instead of a minimal-cardinality argument, delete one non-extreme
    -- generator directly by unpacking a proper conic combination witness.
    have hproper :
        ProperConicCombinationOfDistinctConeRays
          (polyhedron_projection_cone B) (rays i) := by
      have hnotnot :
          ¬ ¬ ProperConicCombinationOfDistinctConeRays
            (polyhedron_projection_cone B) (rays i) := by
        simpa [isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
          hgi_mem hgi_zero] using hi_not_extreme
      exact not_not.mp hnotnot
    rcases hproper with
      ⟨r₁, r₂, hr₁_mem, hr₂_mem, hr₁_ne_zero, hr₂_ne_zero, hray_distinct,
        μ₁, μ₂, hμ₁_pos, hμ₂_pos, hray_eq⟩
    rcases mem_finitely_generated_cone_split_generator
        (i := i) (by simpa [h_cone] using hr₁_mem) with
      ⟨α, hα_nonneg, y₁, hy₁, hr₁_split⟩
    rcases mem_finitely_generated_cone_split_generator
        (i := i) (by simpa [h_cone] using hr₂_mem) with
      ⟨β, hβ_nonneg, y₂, hy₂, hr₂_split⟩
    have hy₁_mem : y₁ ∈ polyhedron_projection_cone B := hdeleted_subset hy₁
    have hy₂_mem : y₂ ∈ polyhedron_projection_cone B := hdeleted_subset hy₂
    have htail_mem :
        μ₁ • y₁ + μ₂ • y₂ ∈ finitely_generated_cone deleted := by
      have hμ₁y₁_mem : μ₁ • y₁ ∈ finitely_generated_cone deleted :=
        cone_smul_mem hy₁ (le_of_lt hμ₁_pos)
      exact finitely_generated_cone_add_smul_mem deleted hμ₁y₁_mem hy₂ (le_of_lt hμ₂_pos)
    have htail_mem_projection : μ₁ • y₁ + μ₂ • y₂ ∈ polyhedron_projection_cone B :=
      hdeleted_subset htail_mem
    have hsplit_eq :
        rays i = (μ₁ * α + μ₂ * β) • rays i + (μ₁ • y₁ + μ₂ • y₂) := by
      calc
        rays i = μ₁ • r₁ + μ₂ • r₂ := hray_eq
        _ = μ₁ • (α • rays i + y₁) + μ₂ • (β • rays i + y₂) := by
              rw [hr₁_split, hr₂_split]
        _ = (μ₁ * α + μ₂ * β) • rays i + (μ₁ • y₁ + μ₂ • y₂) := by
              ext j
              simp [Pi.smul_apply, smul_eq_mul]
              ring_nf
    have htail_eq :
        μ₁ • y₁ + μ₂ • y₂ = (1 - (μ₁ * α + μ₂ * β)) • rays i := by
      calc
        μ₁ • y₁ + μ₂ • y₂ = rays i - (μ₁ * α + μ₂ * β) • rays i := by
              rw [eq_sub_iff_add_eq]
              simpa [add_comm, add_left_comm, add_assoc] using hsplit_eq.symm
        _ = (1 - (μ₁ * α + μ₂ * β)) • rays i := by
              ext j
              simp [Pi.smul_apply, smul_eq_mul]
              ring_nf
    have hcoeff_pos : 0 < 1 - (μ₁ * α + μ₂ * β) := by
      by_contra hcoeff_nonpos
      have hcoeff_ge_one : 1 ≤ μ₁ * α + μ₂ * β := by
        linarith
      have hneg_tail_mem : -(μ₁ • y₁ + μ₂ • y₂) ∈ polyhedron_projection_cone B := by
        have hcoeff_nonneg : 0 ≤ (μ₁ * α + μ₂ * β) - 1 := by
          linarith
        have hscaled_mem : ((μ₁ * α + μ₂ * β) - 1) • rays i ∈ polyhedron_projection_cone B :=
          smul_mem_polyhedron_projection_cone hgi_mem hcoeff_nonneg
        have hneg_tail_eq :
            -(μ₁ • y₁ + μ₂ • y₂) = ((μ₁ * α + μ₂ * β) - 1) • rays i := by
          rw [htail_eq]
          ext j
          simp [Pi.smul_apply, smul_eq_mul]
          ring_nf
        simpa [hneg_tail_eq] using hscaled_mem
      have htail_zero : μ₁ • y₁ + μ₂ • y₂ = 0 :=
        eq_zero_of_mem_projection_cone_of_neg_mem htail_mem_projection hneg_tail_mem
      have hneg_μ₁y₁ :
          -(μ₁ • y₁) = μ₂ • y₂ := by
        rw [neg_eq_iff_add_eq_zero]
        simpa [add_comm] using htail_zero
      have hμ₁y₁_mem : μ₁ • y₁ ∈ polyhedron_projection_cone B :=
        smul_mem_polyhedron_projection_cone hy₁_mem (le_of_lt hμ₁_pos)
      have hneg_μ₁y₁_mem : -(μ₁ • y₁) ∈ polyhedron_projection_cone B := by
        have hμ₂y₂_mem : μ₂ • y₂ ∈ polyhedron_projection_cone B :=
          smul_mem_polyhedron_projection_cone hy₂_mem (le_of_lt hμ₂_pos)
        simpa [hneg_μ₁y₁] using hμ₂y₂_mem
      have hμ₁y₁_zero : μ₁ • y₁ = 0 :=
        eq_zero_of_mem_projection_cone_of_neg_mem hμ₁y₁_mem hneg_μ₁y₁_mem
      have hμ₂y₂_zero : μ₂ • y₂ = 0 := by
        simpa [hμ₁y₁_zero] using htail_zero
      have hy₁_zero : y₁ = 0 := by
        rcases smul_eq_zero.mp hμ₁y₁_zero with hμ₁_zero | hy₁_zero
        · exact False.elim ((ne_of_gt hμ₁_pos) hμ₁_zero)
        · exact hy₁_zero
      have hy₂_zero : y₂ = 0 := by
        rcases smul_eq_zero.mp hμ₂y₂_zero with hμ₂_zero | hy₂_zero
        · exact False.elim ((ne_of_gt hμ₂_pos) hμ₂_zero)
        · exact hy₂_zero
      have hr₁_line : r₁ = α • rays i := by
        simpa [hy₁_zero] using hr₁_split
      have hr₂_line : r₂ = β • rays i := by
        simpa [hy₂_zero] using hr₂_split
      have hα_pos : 0 < α := by
        have hα_ne_zero : α ≠ 0 := by
          intro hα_zero
          apply hr₁_ne_zero
          rw [hr₁_line, hα_zero, zero_smul]
        exact lt_of_le_of_ne hα_nonneg hα_ne_zero.symm
      have hβ_pos : 0 < β := by
        have hβ_ne_zero : β ≠ 0 := by
          intro hβ_zero
          apply hr₂_ne_zero
          rw [hr₂_line, hβ_zero, zero_smul]
        exact lt_of_le_of_ne hβ_nonneg hβ_ne_zero.symm
      have hr₁_same : SameRay ℝ r₁ (rays i) := by
        rw [hr₁_line]
        exact SameRay.sameRay_pos_smul_left (rays i) hα_pos
      have hr₂_same : SameRay ℝ r₂ (rays i) := by
        rw [hr₂_line]
        exact SameRay.sameRay_pos_smul_left (rays i) hβ_pos
      have hr₁₂_same : SameRay ℝ r₁ r₂ :=
        SameRay.trans hr₁_same hr₂_same.symm
          (fun hzero_mid ↦ False.elim (hgi_zero hzero_mid))
      exact hray_distinct hr₁₂_same
    have htail_ne_zero : μ₁ • y₁ + μ₂ • y₂ ≠ 0 := by
      intro htail_zero
      have hscaled_zero : (1 - (μ₁ * α + μ₂ * β)) • rays i = 0 := by
        simpa [htail_eq] using htail_zero
      have hgi_zero' : rays i = 0 := by
        rcases smul_eq_zero.mp hscaled_zero with hcoeff_zero | hgi_zero'
        · exact False.elim ((ne_of_gt hcoeff_pos) hcoeff_zero)
        · exact hgi_zero'
      exact hgi_zero hgi_zero'
    have hsame_tail : SameRay ℝ (rays i) (μ₁ • y₁ + μ₂ • y₂) := by
      rw [htail_eq]
      exact SameRay.sameRay_nonneg_smul_right (rays i) (le_of_lt hcoeff_pos)
    exact sameRay_mem_finitely_generated_cone_of_mem_of_nonzero htail_ne_zero hsame_tail htail_mem

/-- Helper for Definition 3.15-extra-2: every finite generating family of the projection cone can
be pruned to one consisting entirely of extreme rays. -/
lemma exists_extreme_ray_generating_family_of_projection_cone_from_finite_family
    {m p q : ℕ}
    (B : Matrix (Fin m) (Fin p) ℝ)
    (rays : Fin q → Fin m → ℝ)
    (h_cone : polyhedron_projection_cone B = finitely_generated_cone rays) :
    ∃ k : ℕ, ∃ gen : Fin k → Fin m → ℝ,
      polyhedron_projection_cone B = finitely_generated_cone gen ∧
        (∀ s : Fin k, IsExtremeRayOfCone (polyhedron_projection_cone B) (gen s)) := by
  induction q with
  | zero =>
      -- The empty generating family already witnesses the zero cone case.
      have hrays : rays = Fin.elim0 := by
        funext j
        exact Fin.elim0 j
      refine ⟨0, Fin.elim0, ?_, ?_⟩
      · simpa [hrays] using h_cone
      intro s
      exact Fin.elim0 s
  | succ q ih =>
      classical
      by_cases hall :
          ∀ s : Fin (q + 1), IsExtremeRayOfCone (polyhedron_projection_cone B) (rays s)
      · -- If every listed generator is already extreme, stop the pruning process.
        exact ⟨q + 1, rays, h_cone, hall⟩
      · -- Otherwise delete one non-extreme generator and recurse on the smaller family.
        obtain ⟨i, hi_not_extreme⟩ := not_forall.mp hall
        have hi_mem :
            rays i ∈ finitely_generated_cone (fun j : Fin q ↦ rays (i.succAbove j)) :=
          nonextreme_generator_mem_delete B rays i h_cone hi_not_extreme
        have hdelete_eq :
            finitely_generated_cone rays =
              finitely_generated_cone (fun j : Fin q ↦ rays (i.succAbove j)) :=
          finitely_generated_cone_eq_of_generator_mem_delete rays i hi_mem
        have hdelete_cone :
            polyhedron_projection_cone B =
              finitely_generated_cone (fun j : Fin q ↦ rays (i.succAbove j)) := by
          rw [h_cone, hdelete_eq]
        exact ih (fun j : Fin q ↦ rays (i.succAbove j)) hdelete_cone

/-- Helper for Definition 3.15-extra-2: a pointed polyhedral projection cone admits a finite
generating family consisting entirely of extreme rays. -/
lemma exists_extreme_ray_generating_family_of_pointed_projection_cone
    {m p : ℕ}
    (B : Matrix (Fin m) (Fin p) ℝ)
    (_h_pointed : is_pointed (polyhedron_projection_cone B)) :
    ∃ k : ℕ, ∃ gen : Fin k → Fin m → ℝ,
      polyhedron_projection_cone B = finitely_generated_cone gen ∧
        (∀ s : Fin k, IsExtremeRayOfCone (polyhedron_projection_cone B) (gen s)) := by
  have h_polyhedral : is_polyhedral_cone (polyhedron_projection_cone B) :=
    polyhedron_projection_cone_is_polyhedral B
  -- Route correction: obtain any finite generating family from Theorem 3.11, then prune away
  -- non-extreme generators one at a time until only extreme rays remain.
  rcases (finitely_generated_cone_iff_polyhedral_cone.mpr h_polyhedral) with ⟨k, R, hR⟩
  have hgen :
      polyhedron_projection_cone B = finitely_generated_cone (fun j : Fin k ↦ fun i ↦ R i j) := by
    calc
      polyhedron_projection_cone B = (matrix_cone R : Set (Fin m → ℝ)) := hR
      _ = finitely_generated_cone (fun j : Fin k ↦ fun i ↦ R i j) := by
            symm
            exact finitely_generated_cone_eq_matrix_cone (fun j : Fin k ↦ fun i ↦ R i j)
  exact exists_extreme_ray_generating_family_of_projection_cone_from_finite_family
    B (fun j : Fin k ↦ fun i ↦ R i j) hgen

/-- Definition 3.15-extra-2 (2). The projection cone `C_P` is automatically polyhedral from its
defining homogeneous matrix system. If `C_P` is pointed and `rays` is a representative family of
the extreme rays of `C_P` up to `SameRay ℝ`, then `C_P` is the cone generated by those extreme
rays. -/
theorem polyhedron_projection_cone_eq_cone_of_extreme_rays
    {m p q : ℕ}
    (B : Matrix (Fin m) (Fin p) ℝ)
    (rays : Fin q → Fin m → ℝ)
    (h_pointed : is_pointed (polyhedron_projection_cone B))
    (h_rays_extreme :
      ∀ t : Fin q, IsExtremeRayOfCone (polyhedron_projection_cone B) (rays t))
    (h_extreme_rep :
      ∀ r : Fin m → ℝ, IsExtremeRayOfCone (polyhedron_projection_cone B) r →
        ∃ t : Fin q, SameRay ℝ r (rays t)) :
    polyhedron_projection_cone B = finitely_generated_cone rays := by
  have h_polyhedral : is_polyhedral_cone (polyhedron_projection_cone B) :=
    polyhedron_projection_cone_is_polyhedral B
  obtain ⟨k, gen, hgen_eq, hgen_extreme⟩ :=
    exists_extreme_ray_generating_family_of_pointed_projection_cone B h_pointed
  rcases h_polyhedral with ⟨K, _, hK_eq⟩
  apply le_antisymm
  · intro u hu
    rw [hgen_eq] at hu
    -- Each extreme generator of the auxiliary family lies in the listed extreme-ray cone.
    have hgen_subset : Set.range gen ⊆ finitely_generated_cone rays := by
      intro g hg
      rcases hg with ⟨s, rfl⟩
      exact extreme_generator_mem_listed_cone B rays h_rays_extreme h_extreme_rep (hgen_extreme s)
    have hgen_cone_subset : finitely_generated_cone gen ⊆ finitely_generated_cone rays := by
      simpa [finitely_generated_cone] using
        (cone_min (S := Set.range gen) (T := Set.range rays) hgen_subset)
    exact hgen_cone_subset hu
  · intro u hu
    rw [mem_cone_iff] at hu
    rcases hu with ⟨k, gen, hgen_source, hu_comb⟩
    rcases hu_comb with ⟨coeff, hcoeff_nonneg, hsum⟩
    -- The polyhedrality witness packages the projection cone as a pointed cone closed under the
    -- conic combinations used to define `finitely_generated_cone`.
    have hterm_mem : ∀ j : Fin k, coeff j • gen j ∈ K := by
      intro j
      rcases hgen_source j with ⟨t, ht⟩
      have hray_mem_projection : rays t ∈ polyhedron_projection_cone B :=
        extreme_ray_mem_of_isExtremeRayOfCone (h_rays_extreme t)
      have hray_mem_K : rays t ∈ K := by
        change rays t ∈ (K : Set (Fin m → ℝ))
        exact hK_eq.symm ▸ hray_mem_projection
      have hgenj_mem_K : gen j ∈ K := by
        simpa [ht] using hray_mem_K
      exact PointedCone.smul_mem K (hcoeff_nonneg j) hgenj_mem_K
    have hu_mem_K : u ∈ K := by
      -- Summing the conic-combination terms stays inside the pointed cone witness `K`.
      have hsum_mem :
          ∑ j : Fin k, coeff j • gen j ∈ K := by
        exact Submodule.sum_mem K (fun j _ ↦ hterm_mem j)
      simpa [hsum] using hsum_mem
    change u ∈ (polyhedron_projection_cone B)
    exact hK_eq ▸ hu_mem_K
