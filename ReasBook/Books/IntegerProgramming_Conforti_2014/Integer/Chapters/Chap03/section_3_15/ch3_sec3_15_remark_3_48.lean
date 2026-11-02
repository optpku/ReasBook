import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_4.ch3_sec3_4_4_definition_3_4_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_definition_3_15_extra_1

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling for this refine pass:
-- * source-facing owner in this section: `polyhedron_projection_cone`
-- * canonical extreme-ray owner reused here: `IsExtremeRayOfCone`
-- * canonical `x`-projection surface reused here: `Prod.fst '' S`
-- This remark is source-facing existence data, so it is stated directly over those owners rather
-- than through a local packaging structure/class.

/-- Helper for Remark 3.48: the projection cone of `B` consists of the nonnegative row
multipliers annihilating `B`. -/
def polyhedron_projection_cone
    {m p : ℕ}
    (B : Matrix (Fin m) (Fin p) ℝ) : Set (Fin m → ℝ) :=
  {u | 0 ≤ u ∧ u ᵥ* B = 0}

/-- Helper for Remark 3.48: membership in `polyhedron_projection_cone B` unfolds to pointwise
nonnegativity together with the annihilation condition `u ᵥ* B = 0`. -/
theorem mem_polyhedron_projection_cone_iff
    {m p : ℕ}
    {B : Matrix (Fin m) (Fin p) ℝ}
    {u : Fin m → ℝ} :
    u ∈ polyhedron_projection_cone B ↔ 0 ≤ u ∧ u ᵥ* B = 0 := by
  rfl

/-- Helper for Remark 3.48: every generator belongs to the pointed-cone hull of its singleton. -/
lemma self_mem_singletonPointedConeHull
    {m : ℕ}
    (r : Fin m → ℝ) :
    r ∈ (PointedCone.hull ℝ ({r} : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) := by
  exact PointedCone.subset_hull (by simp)

/-- Helper for Remark 3.48: the pointed-cone hull of the zero singleton is exactly `{0}`. -/
lemma singletonPointedConeHullZero
    {m : ℕ} :
    (PointedCone.hull ℝ ({(0 : Fin m → ℝ)} : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) =
      ({0} : Set (Fin m → ℝ)) := by
  ext x
  constructor
  · intro hx
    rw [SetLike.mem_coe, PointedCone.mem_hull_set] at hx
    rcases hx with ⟨c, hc_source, _, hsum⟩
    -- Every supporting vector is `0`, so the conic sum itself is `0`.
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
    rw [SetLike.mem_coe, PointedCone.mem_hull_set]
    refine ⟨0, ?_, ?_, ?_⟩
    · simp
    · intro y
      simp
    · simp

/-- Helper for Remark 3.48: an extreme-ray generator lies in the cone whose edge it spans. -/
lemma extreme_ray_mem_of_isExtremeRayOfCone
    {m : ℕ}
    {C : Set (Fin m → ℝ)}
    {r : Fin m → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    r ∈ C := by
  have hr_edge :
      IsEdgeOf C (PointedCone.hull ℝ ({r} : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hr
  exact hr_edge.isExtreme.1 (self_mem_singletonPointedConeHull r)

/-- Helper for Remark 3.48: an extreme-ray generator cannot be the zero vector. -/
lemma extreme_ray_ne_zero
    {m : ℕ}
    {C : Set (Fin m → ℝ)}
    {r : Fin m → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    r ≠ 0 := by
  have hr_edge :
      IsEdgeOf C (PointedCone.hull ℝ ({r} : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hr
  intro hr_zero
  have hzero_edge : IsEdgeOf C ({0} : Set (Fin m → ℝ)) := by
    simpa [hr_zero, singletonPointedConeHullZero] using hr_edge
  have hdim_zero : Module.finrank ℝ (affineSpan ℝ ({0} : Set (Fin m → ℝ))).direction = 0 := by
    rw [direction_affineSpan, vectorSpan_singleton]
    simp
  have hdim_one : Module.finrank ℝ (affineSpan ℝ ({0} : Set (Fin m → ℝ))).direction = 1 :=
    hzero_edge.finrank_direction_eq_one
  have : (0 : ℕ) = 1 := by
    rwa [hdim_zero] at hdim_one
  exact Nat.zero_ne_one this

/-- Helper for Remark 3.48: if both `v` and `-v` lie in the projection cone, then `v = 0`. -/
lemma eq_zero_of_mem_projection_cone_of_neg_mem
    {m p : ℕ}
    {B : Matrix (Fin m) (Fin p) ℝ}
    {v : Fin m → ℝ}
    (hv : v ∈ polyhedron_projection_cone B)
    (hnegv : -v ∈ polyhedron_projection_cone B) :
    v = 0 := by
  obtain ⟨hv_nonneg, _⟩ := mem_polyhedron_projection_cone_iff.mp hv
  obtain ⟨hnegv_nonneg, _⟩ := mem_polyhedron_projection_cone_iff.mp hnegv
  ext i
  exact le_antisymm (neg_nonneg.mp (hnegv_nonneg i)) (hv_nonneg i)

local notation "zeroProjectionConeFin2" =>
  polyhedron_projection_cone (0 : Matrix (Fin 2) (Fin 0) ℝ)

local notation "firstCoordinateRay" =>
  (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ)

local notation "secondCoordinateRay" =>
  (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ)

local notation "chosenA" =>
  ((fun _ _ ↦ (1 : ℝ)) : Matrix (Fin 2) (Fin 1) ℝ)

local notation "chosenB" =>
  (0 : Matrix (Fin 2) (Fin 0) ℝ)

local notation "chosenb" =>
  (fun _ : Fin 2 ↦ (1 : ℝ))

/-- Helper for Remark 3.48: a positive weighted sum of two nonnegative reals vanishes only when
both summands vanish. -/
lemma positiveWeightedSumEqZeroOfNonneg
    {μ₁ μ₂ a b : ℝ}
    (hμ₁ : 0 < μ₁)
    (hμ₂ : 0 < μ₂)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hsum : μ₁ * a + μ₂ * b = 0) :
    a = 0 ∧ b = 0 := by
  -- Each weighted term is nonnegative, so their sum can vanish only termwise.
  have hμ₁a_nonneg : 0 ≤ μ₁ * a := mul_nonneg (le_of_lt hμ₁) ha
  have hμ₂b_nonneg : 0 ≤ μ₂ * b := mul_nonneg (le_of_lt hμ₂) hb
  have hμ₁a_zero : μ₁ * a = 0 := by
    linarith
  have hμ₂b_zero : μ₂ * b = 0 := by
    linarith
  constructor
  · exact (mul_eq_zero.mp hμ₁a_zero).resolve_left hμ₁.ne'
  · exact (mul_eq_zero.mp hμ₂b_zero).resolve_left hμ₂.ne'

/-- Helper for Remark 3.48: with `B = 0` on `Fin 2 × Fin 0`, the projection cone is exactly the
coordinatewise nonnegative orthant. -/
lemma memZeroProjectionConeFin2_iff
    {u : Fin 2 → ℝ} :
    u ∈ zeroProjectionConeFin2 ↔ 0 ≤ u := by
  -- The left-kernel condition is automatic because there are no `z`-columns.
  rw [mem_polyhedron_projection_cone_iff]
  constructor
  · intro hu
    exact hu.1
  · intro hu
    refine ⟨hu, ?_⟩
    ext j
    exact Fin.elim0 j

/-- Helper for Remark 3.48: each coordinate ray of the `Fin 2` orthant lies in the chosen
projection cone. -/
lemma coordinateRay_mem_zeroProjectionCone
    (t : Fin 2) :
    (Pi.single t (1 : ℝ) : Fin 2 → ℝ) ∈ zeroProjectionConeFin2 := by
  -- Coordinate rays are pointwise nonnegative, so they satisfy the orthant description.
  refine memZeroProjectionConeFin2_iff.mpr ?_
  intro i
  fin_cases t <;> fin_cases i <;> simp [Pi.single]

/-- Helper for Remark 3.48: any nonzero orthant vector whose second coordinate is `0` lies on the
first coordinate ray. -/
lemma sameRayFirstCoordinateRayOfZeroProjectionCone
    {r : Fin 2 → ℝ}
    (hr : r ∈ zeroProjectionConeFin2)
    (hr1 : r 1 = 0)
    (hr_ne_zero : r ≠ 0) :
    SameRay ℝ r firstCoordinateRay := by
  have hr_nonneg : 0 ≤ r := memZeroProjectionConeFin2_iff.mp hr
  -- Nonnegativity plus `r 1 = 0` leaves only the first coordinate as a possible support.
  have hr0_ne : r 0 ≠ 0 := by
    intro hr0
    apply hr_ne_zero
    ext i
    fin_cases i <;> simp [hr0, hr1]
  have hr0_pos : 0 < r 0 := lt_of_le_of_ne (hr_nonneg 0) (Ne.symm hr0_ne)
  have hr_eq : r = r 0 • firstCoordinateRay := by
    ext i
    fin_cases i <;> simp [Pi.single, hr1]
  -- Rewriting `r` as a positive multiple of the first coordinate ray identifies the ray.
  rw [hr_eq]
  exact SameRay.sameRay_pos_smul_left firstCoordinateRay hr0_pos

/-- Helper for Remark 3.48: any nonzero orthant vector whose first coordinate is `0` lies on the
second coordinate ray. -/
lemma sameRaySecondCoordinateRayOfZeroProjectionCone
    {r : Fin 2 → ℝ}
    (hr : r ∈ zeroProjectionConeFin2)
    (hr0 : r 0 = 0)
    (hr_ne_zero : r ≠ 0) :
    SameRay ℝ r secondCoordinateRay := by
  have hr_nonneg : 0 ≤ r := memZeroProjectionConeFin2_iff.mp hr
  -- Symmetrically, vanishing of the first coordinate forces support on the second ray.
  have hr1_ne : r 1 ≠ 0 := by
    intro hr1
    apply hr_ne_zero
    ext i
    fin_cases i <;> simp [hr0, hr1]
  have hr1_pos : 0 < r 1 := lt_of_le_of_ne (hr_nonneg 1) (Ne.symm hr1_ne)
  have hr_eq : r = r 1 • secondCoordinateRay := by
    ext i
    fin_cases i <;> simp [Pi.single, hr0]
  -- Rewriting `r` as a positive multiple of the second coordinate ray identifies the ray.
  rw [hr_eq]
  exact SameRay.sameRay_pos_smul_left secondCoordinateRay hr1_pos

/-- Helper for Remark 3.48: the two coordinate rays in `ℝ²` are not the same ray. -/
lemma firstCoordinateRayNotSameRaySecondCoordinateRay :
    ¬ SameRay ℝ firstCoordinateRay secondCoordinateRay := by
  intro hsame
  have hfirst_ne_zero : firstCoordinateRay ≠ 0 := by
    simp [Pi.single]
  have hsecond_ne_zero : secondCoordinateRay ≠ 0 := by
    simp [Pi.single]
  -- Positive proportionality would force a positive scalar to vanish in the first coordinate.
  rcases hsame.exists_pos hfirst_ne_zero hsecond_ne_zero with ⟨a, b, ha, hb, hab⟩
  have hab0 := congrArg (fun r : Fin 2 → ℝ ↦ r 0) hab
  simp [Pi.single] at hab0
  linarith

/-- Helper for Remark 3.48: each coordinate ray is an extreme ray of the orthant
`zeroProjectionConeFin2`. -/
lemma coordinateRayIsExtremeOfZeroProjectionCone
    (t : Fin 2) :
    IsExtremeRayOfCone zeroProjectionConeFin2 (Pi.single t (1 : ℝ)) := by
  fin_cases t
  · have hmem : firstCoordinateRay ∈ zeroProjectionConeFin2 :=
      coordinateRay_mem_zeroProjectionCone 0
    have hne : firstCoordinateRay ≠ 0 := by
      simp [Pi.single]
    refine (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays hmem hne).2 ?_
    intro hproper
    rcases hproper with
      ⟨u, v, hu, hv, hu_ne, hv_ne, huv_not_same, μ₁, μ₂, hμ₁, hμ₂, hdecomp⟩
    have hu_nonneg : 0 ≤ u := memZeroProjectionConeFin2_iff.mp hu
    have hv_nonneg : 0 ≤ v := memZeroProjectionConeFin2_iff.mp hv
    -- The second coordinate of `e₀ = μ₁ u + μ₂ v` forces both second coordinates to vanish.
    have hcoord := congrArg (fun r : Fin 2 → ℝ ↦ r 1) hdecomp
    have hsum : μ₁ * u 1 + μ₂ * v 1 = 0 := by
      simpa [Pi.add_apply, Pi.smul_apply, Pi.single] using hcoord.symm
    have huv_second_zero :=
      positiveWeightedSumEqZeroOfNonneg hμ₁ hμ₂ (hu_nonneg 1) (hv_nonneg 1) hsum
    have hu_same : SameRay ℝ u firstCoordinateRay :=
      sameRayFirstCoordinateRayOfZeroProjectionCone hu huv_second_zero.1 hu_ne
    have hv_same : SameRay ℝ v firstCoordinateRay :=
      sameRayFirstCoordinateRayOfZeroProjectionCone hv huv_second_zero.2 hv_ne
    have huv_same : SameRay ℝ u v :=
      SameRay.trans hu_same hv_same.symm (fun hzero ↦ False.elim (hne hzero))
    exact huv_not_same huv_same
  · have hmem : secondCoordinateRay ∈ zeroProjectionConeFin2 :=
      coordinateRay_mem_zeroProjectionCone 1
    have hne : secondCoordinateRay ≠ 0 := by
      simp [Pi.single]
    refine (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays hmem hne).2 ?_
    intro hproper
    rcases hproper with
      ⟨u, v, hu, hv, hu_ne, hv_ne, huv_not_same, μ₁, μ₂, hμ₁, hμ₂, hdecomp⟩
    have hu_nonneg : 0 ≤ u := memZeroProjectionConeFin2_iff.mp hu
    have hv_nonneg : 0 ≤ v := memZeroProjectionConeFin2_iff.mp hv
    -- The first coordinate of `e₁ = μ₁ u + μ₂ v` forces both first coordinates to vanish.
    have hcoord := congrArg (fun r : Fin 2 → ℝ ↦ r 0) hdecomp
    have hsum : μ₁ * u 0 + μ₂ * v 0 = 0 := by
      simpa [Pi.add_apply, Pi.smul_apply, Pi.single] using hcoord.symm
    have huv_first_zero :=
      positiveWeightedSumEqZeroOfNonneg hμ₁ hμ₂ (hu_nonneg 0) (hv_nonneg 0) hsum
    have hu_same : SameRay ℝ u secondCoordinateRay :=
      sameRaySecondCoordinateRayOfZeroProjectionCone hu huv_first_zero.1 hu_ne
    have hv_same : SameRay ℝ v secondCoordinateRay :=
      sameRaySecondCoordinateRayOfZeroProjectionCone hv huv_first_zero.2 hv_ne
    have huv_same : SameRay ℝ u v :=
      SameRay.trans hu_same hv_same.symm (fun hzero ↦ False.elim (hne hzero))
    exact huv_not_same huv_same

/-- Helper for Remark 3.48: every extreme ray of the orthant `zeroProjectionConeFin2` is generated
by one of the two coordinate rays. -/
lemma sameRayCoordinateRayOfExtremeZeroProjectionCone
    {r : Fin 2 → ℝ}
    (hr : IsExtremeRayOfCone zeroProjectionConeFin2 r) :
    ∃ t : Fin 2, SameRay ℝ r (Pi.single t (1 : ℝ)) := by
  have hr_mem : r ∈ zeroProjectionConeFin2 := extreme_ray_mem_of_isExtremeRayOfCone hr
  have hr_nonneg : 0 ≤ r := memZeroProjectionConeFin2_iff.mp hr_mem
  have hr_ne_zero : r ≠ 0 := extreme_ray_ne_zero hr
  -- If one coordinate vanishes, the vector lies on the corresponding coordinate ray.
  by_cases hr0 : r 0 = 0
  · exact ⟨1, sameRaySecondCoordinateRayOfZeroProjectionCone hr_mem hr0 hr_ne_zero⟩
  by_cases hr1 : r 1 = 0
  · exact ⟨0, sameRayFirstCoordinateRayOfZeroProjectionCone hr_mem hr1 hr_ne_zero⟩
  -- If both coordinates are positive, `r` splits as a proper conic combination of distinct rays.
  have hr0_pos : 0 < r 0 := lt_of_le_of_ne (hr_nonneg 0) (Ne.symm hr0)
  have hr1_pos : 0 < r 1 := lt_of_le_of_ne (hr_nonneg 1) (Ne.symm hr1)
  have hnotproper :
      ¬ ProperConicCombinationOfDistinctConeRays zeroProjectionConeFin2 r :=
    (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays hr_mem hr_ne_zero).1 hr
  have hproper :
      ProperConicCombinationOfDistinctConeRays zeroProjectionConeFin2 r := by
    refine ⟨firstCoordinateRay, secondCoordinateRay, ?_, ?_, ?_, ?_,
      firstCoordinateRayNotSameRaySecondCoordinateRay, r 0, r 1, hr0_pos, hr1_pos, ?_⟩
    · exact coordinateRay_mem_zeroProjectionCone 0
    · exact coordinateRay_mem_zeroProjectionCone 1
    · simp [Pi.single]
    · simp [Pi.single]
    · -- The orthant vector decomposes as the sum of its two coordinate parts.
      ext i
      fin_cases i <;> simp [Pi.single]
  exact False.elim (hnotproper hproper)

/-- Helper for Remark 3.48: the `Fin 2` orthant projection cone is pointed. -/
lemma zeroProjectionConePointedFin2 :
    is_pointed zeroProjectionConeFin2 := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro r hr
  rw [mem_linealitySpace_iff] at hr
  have hzero_mem : (0 : Fin 2 → ℝ) ∈ zeroProjectionConeFin2 := by
    exact memZeroProjectionConeFin2_iff.mpr (by simp)
  -- Apply the lineality translation rule at the origin with scalars `1` and `-1`.
  have hr_mem : r ∈ zeroProjectionConeFin2 := by
    simpa using hr hzero_mem (1 : ℝ)
  have hneg_mem : -r ∈ zeroProjectionConeFin2 := by
    simpa using hr hzero_mem (-1 : ℝ)
  exact eq_zero_of_mem_projection_cone_of_neg_mem hr_mem hneg_mem

/-- Helper for Remark 3.48: for the duplicated-row witness, every listed ray inequality is exactly
the scalar bound `x 0 ≤ 1`. -/
lemma chosenWitnessRayInequality_iff
    (t : Fin 2)
    (x : Fin 1 → ℝ) :
    (Pi.single t (1 : ℝ)) ⬝ᵥ (chosenA *ᵥ x) ≤
      (Pi.single t (1 : ℝ)) ⬝ᵥ chosenb ↔
      x 0 ≤ 1 := by
  -- Each row of `A` and each entry of `b` is `1`, so both ray inequalities are identical.
  fin_cases t <;> simp [Matrix.mulVec, dotProduct, Pi.single]

/-- Remark 3.48. There exist projection data for which the extreme-ray inequalities describing
`proj_x(P)` are sufficient, one of those inequalities is already implied by the others, and the
listed multipliers still form a nontrivial representative family of all extreme rays of the
projection cone up to `SameRay ℝ`. -/
theorem exists_redundant_extreme_ray_projection_inequality :
    ∃ (m n p q : ℕ)
      (A : Matrix (Fin m) (Fin n) ℝ)
      (B : Matrix (Fin m) (Fin p) ℝ)
      (b : Fin m → ℝ)
      (rays : Fin q → Fin m → ℝ)
      (t₀ : Fin q),
      1 < q ∧
        Pairwise (fun i j ↦ ¬ SameRay ℝ (rays i) (rays j)) ∧
        (∀ t : Fin q, IsExtremeRayOfCone (polyhedron_projection_cone B) (rays t)) ∧
        (∀ r : Fin m → ℝ, IsExtremeRayOfCone (polyhedron_projection_cone B) r →
          ∃ t : Fin q, SameRay ℝ r (rays t)) ∧
        Prod.fst '' {xz : (Fin n → ℝ) × (Fin p → ℝ) | A *ᵥ xz.1 + B *ᵥ xz.2 ≤ b} =
          {x : Fin n → ℝ | ∀ t : Fin q, rays t ⬝ᵥ (A *ᵥ x) ≤ rays t ⬝ᵥ b} ∧
        {x : Fin n → ℝ | ∀ t : Fin q, rays t ⬝ᵥ (A *ᵥ x) ≤ rays t ⬝ᵥ b} =
          {x : Fin n → ℝ | ∀ t : Fin q,
              t ≠ t₀ → rays t ⬝ᵥ (A *ᵥ x) ≤ rays t ⬝ᵥ b} := by
  refine ⟨2, 1, 0, 2, chosenA, chosenB, chosenb, (fun t ↦ Pi.single t (1 : ℝ)), 0, ?_⟩
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · -- The two listed rays are genuinely distinct in `SameRay`.
    intro i j hij
    fin_cases i <;> fin_cases j
    · contradiction
    · exact firstCoordinateRayNotSameRaySecondCoordinateRay
    · simpa [SameRay.sameRay_comm] using firstCoordinateRayNotSameRaySecondCoordinateRay
    · contradiction
  · -- Each listed multiplier is an extreme ray of the concrete projection cone.
    intro t
    exact coordinateRayIsExtremeOfZeroProjectionCone t
  · -- Every extreme ray of the concrete cone is represented by one of the listed rays.
    intro r hr
    exact sameRayCoordinateRayOfExtremeZeroProjectionCone hr
  · ext x
    rw [mem_image_fst_iff]
    constructor
    · rintro ⟨z, hxz⟩
      -- Any feasible witness gives the common row inequality `x 0 ≤ 1`.
      have hrow : x 0 ≤ 1 := by
        have hxz0 := hxz 0
        simpa [Matrix.mulVec, dotProduct, Pi.single] using hxz0
      intro t
      exact (chosenWitnessRayInequality_iff t x).2 hrow
    · intro hx
      -- Conversely, the shared inequality already makes the unique `z`-choice feasible.
      have hrow : x 0 ≤ 1 :=
        (chosenWitnessRayInequality_iff 0 x).1 (hx 0)
      refine ⟨0, ?_⟩
      intro i
      fin_cases i <;> simpa [Matrix.mulVec, dotProduct, Pi.single] using hrow
  · ext x
    constructor
    · intro hx t ht
      exact hx t
    · intro hx t
      fin_cases t
      · -- Dropping the first inequality loses nothing because the second one is identical.
        have hsecond :
            secondCoordinateRay ⬝ᵥ (chosenA *ᵥ x) ≤ secondCoordinateRay ⬝ᵥ chosenb :=
          hx 1 (by simp)
        exact (chosenWitnessRayInequality_iff 0 x).2
          ((chosenWitnessRayInequality_iff 1 x).1 hsecond)
      · exact hx 1 (by simp)
