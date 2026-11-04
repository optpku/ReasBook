/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_example_3_45

open scoped BigOperators Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tooling was unavailable in this environment: `tool_search` exposed no deferred
-- Lean search tools such as `lean_leansearch`, so this file reuses the shared Section 3.18 facet
-- owner together with the earlier Section 3.15 octahedron/projection declarations.

/-- The signed subset inequality indexed by `S`, written as a coefficient vector. -/
def octahedron_signed_face_normal {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i ↦ if i ∈ S then 1 else -1

/-- The signed subset sum is the dot product with `octahedron_signed_face_normal S`. -/
theorem octahedron_signed_face_normal_dotProduct {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) :
    octahedron_signed_face_normal S ⬝ᵥ x = signed_coordinate_sum S x := by
  classical
  rw [dotProduct, signed_coordinate_sum]
  calc
    ∑ i : Fin n, octahedron_signed_face_normal S i * x i
        = ∑ i : Fin n,
            ((if i ∈ S then x i else 0) + (if i ∈ Finset.univ \ S then -x i else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hiS : i ∈ S
            · simp [octahedron_signed_face_normal, hiS]
            · simp [octahedron_signed_face_normal, hiS]
    _ = S.sum (fun i ↦ x i) + (Finset.univ \ S).sum (fun i ↦ -x i) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem]
          simp
    _ = S.sum (fun i ↦ x i) - (Finset.univ \ S).sum fun i ↦ x i := by
          rw [sub_eq_add_neg, Finset.sum_neg_distrib]

/-- The equality face of `octahedron n` cut out by the signed subset inequality indexed by `S`. -/
abbrev octahedron_signed_face (n : ℕ) (S : Finset (Fin n)) : Set (Fin n → ℝ) :=
  face_set (octahedron n) (octahedron_signed_face_normal S) 1

/-- Membership in `octahedron_signed_face n S` means lying in `octahedron n` with the signed
subset inequality for `S` tight at equality. -/
theorem mem_octahedron_signed_face_iff {n : ℕ} {S : Finset (Fin n)} {x : Fin n → ℝ} :
    x ∈ octahedron_signed_face n S ↔ x ∈ octahedron n ∧ signed_coordinate_sum S x = 1 := by
  rw [mem_face_set_iff, ← octahedron_signed_face_normal_dotProduct]

/-- The vertices of `octahedron n` are the signed unit vectors in `Fin n → ℝ`. -/
def octahedron_vertices (n : ℕ) : Set (Fin n → ℝ) :=
  Set.range (fun i : Fin n ↦ Pi.single i (1 : ℝ)) ∪
    Set.range (fun i : Fin n ↦ -Pi.single i (1 : ℝ))

/-- Membership in `octahedron_vertices n` means being a positive or negative unit vector. -/
theorem mem_octahedron_vertices_iff {n : ℕ} {x : Fin n → ℝ} :
    x ∈ octahedron_vertices n ↔
      (∃ i : Fin n, x = Pi.single i (1 : ℝ)) ∨
        ∃ i : Fin n, x = -Pi.single i (1 : ℝ) := by
  constructor
  · intro hx
    simpa [octahedron_vertices, eq_comm] using hx
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> simp [octahedron_vertices]

/-- The equality face of `octahedron_extension n` cut out by the coordinate inequality `z i ≥ 0`. -/
def octahedron_extension_coordinate_face (n : ℕ) (i : Fin (n + n)) :
    Set ((Fin n → ℝ) × (Fin (n + n) → ℝ)) :=
  {xz | xz ∈ octahedron_extension n ∧ xz.2 i = 0}

/-- Membership in `octahedron_extension_coordinate_face n i` means lying in the lifted
octahedron extension with `z i = 0`. -/
theorem mem_octahedron_extension_coordinate_face_iff
    {n : ℕ} {i : Fin (n + n)} {xz : (Fin n → ℝ) × (Fin (n + n) → ℝ)} :
    xz ∈ octahedron_extension_coordinate_face n i ↔
      xz ∈ octahedron_extension n ∧ xz.2 i = 0 := by
  rfl

/-- Helper for Exercise 3.33: the positive block of the lifted variables as a linear map. -/
def octahedron_extension_pos_linearMap (n : ℕ) :
    (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i : Fin n ↦
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + n) ↦ ℝ) (Fin.castAdd n i)

/-- Helper for Exercise 3.33: the negative block of the lifted variables as a linear map. -/
def octahedron_extension_neg_linearMap (n : ℕ) :
    (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i : Fin n ↦
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + n) ↦ ℝ) (Fin.natAdd n i)

/-- Helper for Exercise 3.33: the lifted polyhedron is the graph of the signed-coordinate map on
the standard simplex. -/
def octahedron_extension_graphLinearMap (n : ℕ) :
    (Fin (n + n) → ℝ) →ₗ[ℝ] ((Fin n → ℝ) × (Fin (n + n) → ℝ)) :=
  LinearMap.prod
    (octahedron_extension_pos_linearMap n - octahedron_extension_neg_linearMap n)
    LinearMap.id

/-- Helper for Exercise 3.33: the graph vertices are the images of the simplex basis vertices. -/
def octahedron_extension_graphVertex (n : ℕ) (i : Fin (n + n)) :
    (Fin n → ℝ) × (Fin (n + n) → ℝ) :=
  octahedron_extension_graphLinearMap n (Pi.single i (1 : ℝ))

/-- Helper for Exercise 3.33: the graph map remembers the lifted coordinates, so it is injective. -/
theorem octahedron_extension_graphLinearMap_injective (n : ℕ) :
    Function.Injective (octahedron_extension_graphLinearMap n) := by
  -- The second component of the graph map is the identity on the lifted variables.
  intro z w hzw
  have hsnd := congrArg Prod.snd hzw
  simpa [octahedron_extension_graphLinearMap] using hsnd

/-- Helper for Exercise 3.33: the signed octahedron is convex. -/
theorem convex_octahedron (n : ℕ) : Convex ℝ (octahedron n) := by
  -- The `ℓ¹` inequality is preserved under convex combinations by the triangle inequality.
  intro x hx y hy a b ha hb hab
  rw [mem_octahedron_iff] at hx hy ⊢
  calc
    ∑ i : Fin n, |(a • x + b • y) i|
        = ∑ i : Fin n, |a * x i + b * y i| := by
            simp [Pi.smul_apply]
    _ ≤ ∑ i : Fin n, (a * |x i| + b * |y i|) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          calc
            |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
            _ = a * |x i| + b * |y i| := by
                  simp [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * ∑ i : Fin n, |x i| + b * ∑ i : Fin n, |y i| := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * 1 + b * 1 := by
          gcongr
    _ = 1 := by nlinarith

/-- Helper for Exercise 3.33: the signed unit vector associated to `i` and the sign pattern `S`. -/
def octahedron_signed_vertex {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : Fin n → ℝ :=
  if i ∈ S then Pi.single i (1 : ℝ) else -Pi.single i (1 : ℝ)

/-- Helper for Exercise 3.33: each signed unit vector lies in the octahedron. -/
theorem octahedron_signed_vertex_mem_octahedron {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    octahedron_signed_vertex S i ∈ octahedron n := by
  -- A signed unit vector has exactly one nonzero coordinate, so its `ℓ¹` norm is `1`.
  have hsingle : ∑ x : Fin n, |Pi.single i (1 : ℝ) x| = 1 := by
    calc
      ∑ x : Fin n, |Pi.single i (1 : ℝ) x|
          = ∑ x : Fin n, Pi.single i (1 : ℝ) x := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              by_cases hji : j = i
              · subst j
                simp
              · simp [hji]
      _ = 1 := by
            simp
  rw [mem_octahedron_iff, octahedron_signed_vertex]
  by_cases hiS : i ∈ S
  · simp [hiS, hsingle]
  · simp [hiS, hsingle]

/-- Helper for Exercise 3.33: the signed inequality indexed by `S` is tight on each sign-compatible
vertex. -/
theorem signed_coordinate_sum_octahedron_signed_vertex {n : ℕ} (S : Finset (Fin n))
    (i : Fin n) :
    signed_coordinate_sum S (octahedron_signed_vertex S i) = 1 := by
  -- The sign-compatible unit vector contributes exactly one unit to the signed sum.
  rw [octahedron_signed_vertex]
  by_cases hiS : i ∈ S
  · simp [signed_coordinate_sum, hiS]
  · simp [signed_coordinate_sum, hiS]

/-- Helper for Exercise 3.33: each sign-compatible signed unit vector belongs to the equality face
cut out by the corresponding signed inequality. -/
theorem octahedron_signed_vertex_mem_face {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    octahedron_signed_vertex S i ∈ octahedron_signed_face n S := by
  -- Membership in the equality face is exactly octahedron membership plus tightness of the
  -- supporting inequality.
  rw [mem_octahedron_signed_face_iff]
  exact ⟨octahedron_signed_vertex_mem_octahedron S i,
    signed_coordinate_sum_octahedron_signed_vertex S i⟩

/-- Helper for Exercise 3.33: the signed face is convex. -/
theorem convex_octahedron_signed_face (n : ℕ) (S : Finset (Fin n)) :
    Convex ℝ (octahedron_signed_face n S) := by
  -- Route correction: instead of unfolding the face as a raw set intersection, keep the source
  -- supporting-functional viewpoint and transport the equality through the signed dot product.
  intro x hx y hy a b ha hb hab
  rw [mem_octahedron_signed_face_iff] at hx hy ⊢
  refine ⟨convex_octahedron n hx.1 hy.1 ha hb hab, ?_⟩
  calc
    signed_coordinate_sum S (a • x + b • y)
        = octahedron_signed_face_normal S ⬝ᵥ (a • x + b • y) := by
            symm
            rw [octahedron_signed_face_normal_dotProduct]
    _ = octahedron_signed_face_normal S ⬝ᵥ (a • x) +
          octahedron_signed_face_normal S ⬝ᵥ (b • y) := by
            rw [dotProduct_add]
    _ = a * (octahedron_signed_face_normal S ⬝ᵥ x) +
          b * (octahedron_signed_face_normal S ⬝ᵥ y) := by
            rw [dotProduct_smul, dotProduct_smul]
            simp [smul_eq_mul]
    _ = a * signed_coordinate_sum S x + b * signed_coordinate_sum S y := by
          rw [octahedron_signed_face_normal_dotProduct, octahedron_signed_face_normal_dotProduct]
    _ = 1 := by nlinarith [hx.2, hy.2, hab]

/-- Helper for Exercise 3.33: the sign-compatible signed unit vectors are affinely independent. -/
theorem octahedron_signed_vertex_affineIndependent {n : ℕ} (S : Finset (Fin n)) :
    AffineIndependent ℝ (octahedron_signed_vertex S) := by
  -- The signed vertex family is the standard basis rescaled coordinatewise by the units `±1`.
  let w : Fin n → ℝˣ := fun i ↦ if i ∈ S then 1 else -1
  let basis : Fin n → Fin n → ℝ := fun i ↦ Pi.single i (1 : ℝ)
  have hEq : octahedron_signed_vertex S = w • basis := by
    funext i
    by_cases hiS : i ∈ S
    · simp [octahedron_signed_vertex, w, basis, hiS]
    · simp [octahedron_signed_vertex, w, basis, hiS]
  -- Turning linear independence into affine independence matches the ambient vector-space setting.
  simpa only [hEq] using
    (((Pi.linearIndependent_single_one (Fin n) ℝ).units_smul w).affineIndependent)

/-- Helper for Exercise 3.33: on a signed equality face, the total slack in the inequality
`signed_coordinate_sum S x ≤ ∑ i, |x i|` vanishes. -/
theorem octahedron_signed_face_defect_sum_eq_zero {n : ℕ} (S : Finset (Fin n))
    {x : Fin n → ℝ} (hx : x ∈ octahedron_signed_face n S) :
    ∑ i : Fin n, (if i ∈ S then |x i| - x i else |x i| + x i) = 0 := by
  rw [mem_octahedron_signed_face_iff] at hx
  have hsum_abs_eq_one : ∑ i : Fin n, |x i| = 1 := by
    -- Equality of the face inequality forces equality in the ambient `ℓ¹` bound as well.
    have hoct : ∑ i : Fin n, |x i| ≤ 1 := mem_octahedron_iff.mp hx.1
    have hsigned : signed_coordinate_sum S x ≤ ∑ i : Fin n, |x i| :=
      signed_coordinate_sum_le_sum_abs S x
    linarith
  -- Rewrite the defect sum as the gap `∑ |x i| - signed_coordinate_sum S x`.
  calc
    ∑ i : Fin n, (if i ∈ S then |x i| - x i else |x i| + x i)
        = ∑ i : Fin n, |x i| - signed_coordinate_sum S x := by
            rw [signed_coordinate_sum]
            calc
              ∑ i : Fin n, (if i ∈ S then |x i| - x i else |x i| + x i)
                  = ∑ i : Fin n, (|x i| + if i ∈ S then -x i else x i) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      by_cases hiS : i ∈ S <;> simp [hiS, sub_eq_add_neg]
              _ = (∑ i : Fin n, |x i|) + ∑ i : Fin n, (if i ∈ S then -x i else x i) := by
                    rw [Finset.sum_add_distrib]
              _ = (∑ i : Fin n, |x i|) -
                    (S.sum (fun i ↦ x i) - (Finset.univ \ S).sum fun i ↦ x i) := by
                    congr 1
                    calc
                      ∑ i : Fin n, (if i ∈ S then -x i else x i)
                          = ∑ i : Fin n,
                              ((if i ∈ S then -x i else 0) +
                                (if i ∈ Finset.univ \ S then x i else 0)) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro i hi
                                  by_cases hiS : i ∈ S <;> simp [hiS]
                      _ = S.sum (fun i ↦ -x i) + (Finset.univ \ S).sum (fun i ↦ x i) := by
                            rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem]
                            simp
                      _ = -(S.sum fun i ↦ x i) + (Finset.univ \ S).sum fun i ↦ x i := by
                            rw [Finset.sum_neg_distrib]
                      _ = -((S.sum fun i ↦ x i) - (Finset.univ \ S).sum fun i ↦ x i) := by
                            ring
    _ = 0 := by
          linarith [hsum_abs_eq_one, hx.2]

/-- Helper for Exercise 3.33: every point on the signed equality face is the convex combination
of the sign-compatible signed unit vectors with weights `|x i|`. -/
theorem octahedron_signed_face_barycentric_formula {n : ℕ} (S : Finset (Fin n))
    {x : Fin n → ℝ} (hx : x ∈ octahedron_signed_face n S) :
    (∑ i : Fin n, |x i| = 1) ∧ x = ∑ i : Fin n, |x i| • octahedron_signed_vertex S i := by
  rw [mem_octahedron_signed_face_iff] at hx
  have hsum_abs_eq_one : ∑ i : Fin n, |x i| = 1 := by
    -- The face equality saturates the octahedron bound.
    have hoct : ∑ i : Fin n, |x i| ≤ 1 := mem_octahedron_iff.mp hx.1
    have hsigned : signed_coordinate_sum S x ≤ ∑ i : Fin n, |x i| :=
      signed_coordinate_sum_le_sum_abs S x
    linarith
  have hdefect_zero := octahedron_signed_face_defect_sum_eq_zero S (x := x) (by
    exact (mem_octahedron_signed_face_iff).2 hx)
  have hdefect_nonneg :
      ∀ i ∈ Finset.univ, 0 ≤ (if i ∈ S then |x i| - x i else |x i| + x i) := by
    intro i hi
    by_cases hiS : i ∈ S
    · simpa [hiS] using sub_nonneg.mpr (le_abs_self (x i))
    · have habs : -x i ≤ |x i| := neg_le_abs (x i)
      simp [hiS]
      linarith
  have hdefect_each :
      ∀ i : Fin n, (if i ∈ S then |x i| - x i else |x i| + x i) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg hdefect_nonneg).mp hdefect_zero i (by simp)
  refine ⟨hsum_abs_eq_one, ?_⟩
  -- The coordinatewise defect equalities recover the sign pattern, so only the matching basis
  -- vector survives in each coordinate of the barycentric sum.
  ext j
  have hsum_apply :
      (∑ i : Fin n, |x i| • octahedron_signed_vertex S i) j =
        if j ∈ S then |x j| else -|x j| := by
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · by_cases hjS : j ∈ S <;> simp [octahedron_signed_vertex, hjS]
    · intro i hi hij
      by_cases hiS : i ∈ S <;> simp [octahedron_signed_vertex, hiS, hij]
    · intro hj
      exact (hj (by simp)).elim
  by_cases hjS : j ∈ S
  · have hjzero : |x j| - x j = 0 := by simpa [hjS] using hdefect_each j
    have hcoord : x j = |x j| := by linarith
    calc
      x j = |x j| := hcoord
      _ = (∑ i : Fin n, |x i| • octahedron_signed_vertex S i) j := by
            simp [hsum_apply, hjS]
  · have hjzero : |x j| + x j = 0 := by simpa [hjS] using hdefect_each j
    have hcoord : x j = -|x j| := by linarith
    calc
      x j = -|x j| := hcoord
      _ = (∑ i : Fin n, |x i| • octahedron_signed_vertex S i) j := by
            simp [hsum_apply, hjS]

/-- Helper for Exercise 3.33: equality in the signed inequality identifies the signed face with the
convex hull of the sign-compatible signed unit vectors. -/
theorem octahedron_signed_face_eq_convexHull_signed_vertices {n : ℕ} (S : Finset (Fin n)) :
    octahedron_signed_face n S = convexHull ℝ (Set.range (octahedron_signed_vertex S)) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases octahedron_signed_face_barycentric_formula S hx with ⟨hsum_abs_eq_one, hrepr⟩
    -- The source proof reconstructs every face point as a center of mass of the compatible
    -- signed vertices, which is automatically in their convex hull.
    have hcenter :
        Finset.univ.centerMass (fun i : Fin n ↦ |x i|) (octahedron_signed_vertex S) ∈
          convexHull ℝ (Set.range (octahedron_signed_vertex S)) := by
      refine Finset.univ.centerMass_mem_convexHull (fun i hi ↦ abs_nonneg (x i)) ?_ ?_
      · simp [hsum_abs_eq_one]
      · intro i hi
        exact ⟨i, rfl⟩
    have hcenter_eq :
        Finset.univ.centerMass (fun i : Fin n ↦ |x i|) (octahedron_signed_vertex S) =
          ∑ i : Fin n, |x i| • octahedron_signed_vertex S i := by
      simpa using
        (Finset.centerMass_eq_of_sum_1
          (t := Finset.univ) (w := fun i : Fin n ↦ |x i|) (z := octahedron_signed_vertex S)
          (by simpa using hsum_abs_eq_one))
    rw [hcenter_eq] at hcenter
    exact hrepr.symm ▸ hcenter
  · -- The reverse inclusion is immediate from convexity of the face and the fact that each
    -- sign-compatible signed unit vector lies on the face.
    refine convexHull_min ?_ (convex_octahedron_signed_face n S)
    rintro _ ⟨i, rfl⟩
    exact octahedron_signed_vertex_mem_face S i

/-- Helper for Exercise 3.33: the positive projection sends a positive-block basis vector to the
matching unit vector. -/
theorem octahedron_extension_pos_linearMap_single_castAdd {n : ℕ} (j : Fin n) :
    octahedron_extension_pos_linearMap n (Pi.single (Fin.castAdd n j) (1 : ℝ)) =
      Pi.single j (1 : ℝ) := by
  -- Only the `j`-th positive coordinate survives when we read a positive-block basis vector
  -- through the positive projection.
  ext k
  by_cases hkj : k = j
  · subst k
    simp [octahedron_extension_pos_linearMap]
  · simp [octahedron_extension_pos_linearMap, hkj]

/-- Helper for Exercise 3.33: the negative projection kills a positive-block basis vector. -/
theorem octahedron_extension_neg_linearMap_single_castAdd {n : ℕ} (j k : Fin n) :
    octahedron_extension_neg_linearMap n (Pi.single (Fin.castAdd n j) (1 : ℝ)) k = 0 := by
  -- Positive-block and negative-block indices are disjoint inside `Fin (n + n)`.
  have hlt : Fin.castAdd n j < Fin.natAdd n k := by
    change (Fin.castAdd n j).1 < (Fin.natAdd n k).1
    simp [Fin.natAdd]
    omega
  have hneq : Fin.natAdd n k ≠ Fin.castAdd n j := by
    intro hEq
    exact (ne_of_lt hlt) hEq.symm
  have hneq' : ¬k.addNat n = Fin.castAdd n j := by
    simpa using hneq
  simpa [octahedron_extension_neg_linearMap, Pi.single_apply] using
    (if_neg hneq' : (if k.addNat n = Fin.castAdd n j then (1 : ℝ) else 0) = 0)

/-- Helper for Exercise 3.33: the positive projection kills a negative-block basis vector. -/
theorem octahedron_extension_pos_linearMap_single_natAdd {n : ℕ} (j k : Fin n) :
    octahedron_extension_pos_linearMap n (Pi.single (Fin.natAdd n j) (1 : ℝ)) k = 0 := by
  -- The negative block lives strictly after the positive block in the lifted indexing.
  have hgt : Fin.castAdd n k < Fin.natAdd n j := by
    change (Fin.castAdd n k).1 < (Fin.natAdd n j).1
    simp [Fin.natAdd]
    omega
  have hneq : Fin.castAdd n k ≠ Fin.natAdd n j := ne_of_lt hgt
  have hneq' : ¬Fin.castAdd n k = j.addNat n := by
    simpa using hneq
  simpa [octahedron_extension_pos_linearMap, Pi.single_apply] using
    (if_neg hneq' : (if Fin.castAdd n k = j.addNat n then (1 : ℝ) else 0) = 0)

/-- Helper for Exercise 3.33: the negative projection sends a negative-block basis vector to the
matching unit vector. -/
theorem octahedron_extension_neg_linearMap_single_natAdd {n : ℕ} (j : Fin n) :
    octahedron_extension_neg_linearMap n (Pi.single (Fin.natAdd n j) (1 : ℝ)) =
      Pi.single j (1 : ℝ) := by
  -- Only the `j`-th negative coordinate survives when we read a negative-block basis vector
  -- through the negative projection.
  ext k
  by_cases hkj : k = j
  · subst k
    simp [octahedron_extension_neg_linearMap]
  · simp [octahedron_extension_neg_linearMap, hkj]

/-- Helper for Exercise 3.33: the first component of a graph vertex is the corresponding signed unit
vector. -/
theorem octahedron_extension_graphVertex_fst_eq_signed_vertex {n : ℕ} (i : Fin (n + n)) :
    Prod.fst (octahedron_extension_graphVertex n i) =
      match finSumFinEquiv.symm i with
      | Sum.inl j => Pi.single j (1 : ℝ)
      | Sum.inr j => -Pi.single j (1 : ℝ) := by
  -- Split the simplex basis index into the positive and negative blocks and compute the signed
  -- projection using the blockwise basis-vector formulas proved just above.
  cases h : finSumFinEquiv.symm i with
  | inl j =>
      have hi : i = Fin.castAdd n j := by
        simpa [h] using (finSumFinEquiv.apply_symm_apply i).symm
      subst i
      -- On the positive block, the graph map is `(+e^j, e^j)` and the first component is `e^j`.
      ext k
      have hpos :
          octahedron_extension_pos_linearMap n (Pi.single (Fin.castAdd n j) (1 : ℝ)) k =
            (Pi.single j (1 : ℝ) : Fin n → ℝ) k := by
        simpa using congrArg (fun v : Fin n → ℝ ↦ v k)
          (octahedron_extension_pos_linearMap_single_castAdd (n := n) j)
      have hneg :
          octahedron_extension_neg_linearMap n (Pi.single (Fin.castAdd n j) (1 : ℝ)) k = 0 :=
        octahedron_extension_neg_linearMap_single_castAdd (n := n) j k
      -- Evaluate the first component as the positive block minus the vanishing negative block.
      simp [octahedron_extension_graphVertex, octahedron_extension_graphLinearMap,
        LinearMap.sub_apply, hpos, hneg]
  | inr j =>
      have hi : i = Fin.natAdd n j := by
        simpa [h] using (finSumFinEquiv.apply_symm_apply i).symm
      subst i
      -- On the negative block, the graph map is `(-e^j, e^{n+j})` and the first component is
      -- `-e^j`.
      ext k
      have hpos :
          octahedron_extension_pos_linearMap n (Pi.single (Fin.natAdd n j) (1 : ℝ)) k = 0 :=
        octahedron_extension_pos_linearMap_single_natAdd (n := n) j k
      have hneg :
          octahedron_extension_neg_linearMap n (Pi.single (Fin.natAdd n j) (1 : ℝ)) k =
            (Pi.single j (1 : ℝ) : Fin n → ℝ) k := by
        simpa using congrArg (fun v : Fin n → ℝ ↦ v k)
          (octahedron_extension_neg_linearMap_single_natAdd (n := n) j)
      -- Evaluate the first component as the zero positive block minus the negative unit vector.
      change
        octahedron_extension_pos_linearMap n (Pi.single (Fin.natAdd n j) (1 : ℝ)) k -
            octahedron_extension_neg_linearMap n (Pi.single (Fin.natAdd n j) (1 : ℝ)) k =
          -((Pi.single j (1 : ℝ) : Fin n → ℝ) k)
      rw [hpos, hneg]
      simp

/-- Helper for Exercise 3.33: projecting the graph vertices to the `x`-coordinates gives exactly
the signed unit vertices of the octahedron. -/
theorem octahedron_graph_vertices_fst_eq_vertices {n : ℕ} :
    Prod.fst '' Set.range (octahedron_extension_graphVertex n) = octahedron_vertices n := by
  -- The graph vertices split into the positive and negative simplex basis vectors, and the first
  -- component computation identifies those images with the signed unit vertices.
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    rw [mem_octahedron_vertices_iff]
    -- Read the first component via the graph-vertex block computation.
    simpa [octahedron_extension_graphVertex_fst_eq_signed_vertex] using
      (show
        ((∃ j : Fin n,
            Prod.fst (octahedron_extension_graphVertex n i) = Pi.single j (1 : ℝ)) ∨
          ∃ j : Fin n,
            Prod.fst (octahedron_extension_graphVertex n i) = -Pi.single j (1 : ℝ)) from by
          cases h : finSumFinEquiv.symm i with
          | inl j =>
              left
              exact ⟨j, by simpa [h] using
                (octahedron_extension_graphVertex_fst_eq_signed_vertex (n := n) i)⟩
          | inr j =>
              right
              exact ⟨j, by simpa [h] using
                (octahedron_extension_graphVertex_fst_eq_signed_vertex (n := n) i)⟩)
  · rw [mem_octahedron_vertices_iff]
    rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · -- The positive unit vector is the first component of the positive-block graph vertex.
      refine ⟨octahedron_extension_graphVertex n (Fin.castAdd n j), ⟨Fin.castAdd n j, rfl⟩, ?_⟩
      have hsplit : finSumFinEquiv.symm (Fin.castAdd n j) = Sum.inl j := by
        exact finSumFinEquiv_symm_apply_castAdd (n := n) j
      have hfst :=
        octahedron_extension_graphVertex_fst_eq_signed_vertex (n := n) (Fin.castAdd n j)
      rw [hsplit] at hfst
      exact hfst
    · -- The negative unit vector is the first component of the negative-block graph vertex.
      refine ⟨octahedron_extension_graphVertex n (Fin.natAdd n j), ⟨Fin.natAdd n j, rfl⟩, ?_⟩
      have hsplit : finSumFinEquiv.symm (Fin.natAdd n j) = Sum.inr j := by
        simpa using (finSumFinEquiv_symm_apply_natAdd (m := n) (n := n) j)
      rw [octahedron_extension_graphVertex_fst_eq_signed_vertex (n := n) (Fin.natAdd n j), hsplit]

/-- Helper for Exercise 3.33: the first component of each graph vertex is one of the signed unit
vertices of the octahedron. -/
theorem octahedron_extension_graphVertex_fst_mem_vertices {n : ℕ} (i : Fin (n + n)) :
    Prod.fst (octahedron_extension_graphVertex n i) ∈ octahedron_vertices n := by
  -- The graph-vertex computation reduces membership to the positive or negative standard basis
  -- case according to the block containing `i`.
  rw [mem_octahedron_vertices_iff]
  cases h : finSumFinEquiv.symm i with
  | inl j =>
      left
      exact ⟨j, by
        simpa [h] using octahedron_extension_graphVertex_fst_eq_signed_vertex (n := n) i⟩
  | inr j =>
      right
      exact ⟨j, by
        simpa [h] using octahedron_extension_graphVertex_fst_eq_signed_vertex (n := n) i⟩

/-- Helper for Exercise 3.33: the positive unit vector `e^i` lies in `octahedron n`. -/
theorem positiveUnit_mem_octahedron {n : ℕ} (i : Fin n) :
    Pi.single i (1 : ℝ) ∈ octahedron n := by
  -- This is the sign-compatible unit-vector case from the signed-face helper family.
  simpa [octahedron_signed_vertex] using
    (octahedron_signed_vertex_mem_octahedron ({i} : Finset (Fin n)) i)

/-- Helper for Exercise 3.33: the negative unit vector `-e^i` lies in `octahedron n`. -/
theorem negativeUnit_mem_octahedron {n : ℕ} (i : Fin n) :
    -Pi.single i (1 : ℝ) ∈ octahedron n := by
  -- This is the opposite-sign unit-vector case from the same signed-vertex family.
  simpa [octahedron_signed_vertex] using
    (octahedron_signed_vertex_mem_octahedron (∅ : Finset (Fin n)) i)

/-- Helper for Exercise 3.33: every point of `octahedron n` is a convex combination of the first
components of the graph vertices of the lifted extension. -/
theorem octahedronConvexCombinationFromExtension {n : ℕ} (hn : 0 < n)
    {x : Fin n → ℝ} (hx : x ∈ octahedron n) :
    ∃ w : Fin (n + n) → ℝ,
      (∀ i, 0 ≤ w i) ∧
      (∑ i, w i = 1) ∧
      x = ∑ i, w i • Prod.fst (octahedron_extension_graphVertex n i) := by
  rcases exists_mem_octahedron_extension_of_sum_abs_le_one hn (mem_octahedron_iff.mp hx) with
    ⟨z, hz⟩
  rw [mem_octahedron_extension_iff] at hz
  rcases hz with ⟨hcoord, hsum, hz_pos, hz_neg⟩
  refine ⟨z, ?_, ?_, ?_⟩
  · -- Split the lifted coordinates into the positive and negative blocks to recover global
    -- nonnegativity of the barycentric weights.
    intro i
    cases h : finSumFinEquiv.symm i with
    | inl j =>
        have hi : i = Fin.castAdd n j := by
          simpa [h] using (finSumFinEquiv.apply_symm_apply i).symm
        rw [hi]
        simpa [octahedron_extension_pos] using hz_pos j
    | inr j =>
        have hi : i = Fin.natAdd n j := by
          simpa [h] using (finSumFinEquiv.apply_symm_apply i).symm
        rw [hi]
        simpa [octahedron_extension_neg] using hz_neg j
  · -- The extension normalization equation is exactly the simplex weight sum.
    rw [Fin.sum_univ_add]
    simpa [octahedron_extension_pos, octahedron_extension_neg, Finset.sum_add_distrib] using hsum
  · -- Route correction: expand the extension point through the graph linear map instead of using
    -- a brittle split-index barycentric rewrite.
    have hgraph : octahedron_extension_graphLinearMap n z = (x, z) := by
      ext
      · simp [octahedron_extension_graphLinearMap, octahedron_extension_pos_linearMap,
          octahedron_extension_neg_linearMap, octahedron_extension_pos,
          octahedron_extension_neg, hcoord]
      · simp [octahedron_extension_graphLinearMap]
    have hz_decomp : z = ∑ i : Fin (n + n), z i • Pi.single i (1 : ℝ) := by
      ext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp
      · intro j hj hij
        simp [hij]
      · intro hi
        exact (hi (by simp)).elim
    calc
      x = Prod.fst (octahedron_extension_graphLinearMap n z) := by
            simpa using (congrArg Prod.fst hgraph).symm
      _ = Prod.fst
            (octahedron_extension_graphLinearMap n
              (∑ i : Fin (n + n), z i • Pi.single i (1 : ℝ))) := by
            simpa using
              congrArg
                (fun w : Fin (n + n) → ℝ ↦ Prod.fst (octahedron_extension_graphLinearMap n w))
                hz_decomp
      _ = ∑ i : Fin (n + n), z i • Prod.fst (octahedron_extension_graphVertex n i) := by
            change
              (LinearMap.fst ℝ (Fin n → ℝ) (Fin (n + n) → ℝ))
                  (octahedron_extension_graphLinearMap n
                    (∑ i : Fin (n + n), z i • Pi.single i (1 : ℝ))) =
                ∑ i : Fin (n + n), z i • Prod.fst (octahedron_extension_graphVertex n i)
            simp [octahedron_extension_graphVertex, map_sum]

/-- Helper for Exercise 3.33: the octahedron is the convex hull of its signed unit vertices. -/
theorem octahedron_eq_convexHull_vertices {n : ℕ} (hn : 0 < n) :
    octahedron n = convexHull ℝ (octahedron_vertices n) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases octahedronConvexCombinationFromExtension hn hx with ⟨w, hw_nonneg, hw_sum, hx_repr⟩
    -- The lifted extension witness gives a bona fide convex combination of signed vertices.
    have hcenter :
        Finset.univ.centerMass w (fun i : Fin (n + n) ↦
          Prod.fst (octahedron_extension_graphVertex n i)) ∈
            convexHull ℝ (octahedron_vertices n) := by
      refine Finset.univ.centerMass_mem_convexHull (fun i hi ↦ hw_nonneg i) ?_ ?_
      · simp [hw_sum]
      · intro i hi
        exact octahedron_extension_graphVertex_fst_mem_vertices (n := n) i
    have hcenter_eq :
        Finset.univ.centerMass w
            (fun i : Fin (n + n) ↦ Prod.fst (octahedron_extension_graphVertex n i)) =
          ∑ i : Fin (n + n), w i • Prod.fst (octahedron_extension_graphVertex n i) := by
      simpa using
        (Finset.centerMass_eq_of_sum_1 (t := Finset.univ) (w := w)
          (z := fun i : Fin (n + n) ↦ Prod.fst (octahedron_extension_graphVertex n i)) hw_sum)
    rw [hcenter_eq] at hcenter
    exact hx_repr.symm ▸ hcenter
  · -- Every signed unit vertex already lies in `octahedron n`, so convexity gives the reverse
    -- inclusion immediately.
    refine convexHull_min ?_ (convex_octahedron n)
    intro x hx
    rw [mem_octahedron_vertices_iff] at hx
    rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact positiveUnit_mem_octahedron (n := n) i
    · exact negativeUnit_mem_octahedron (n := n) i

/-- Helper for Exercise 3.33: the affine span of the octahedron has full dimension `n`. -/
theorem octahedron_finrank_direction_affineSpan {n : ℕ} (_hn : 0 < n) :
    Module.finrank ℝ (affineSpan ℝ (octahedron n)).direction = n := by
  have hzero : (0 : Fin n → ℝ) ∈ octahedron n := by
    -- The origin satisfies the `ℓ¹` inequality with equality `0 ≤ 1`.
    rw [mem_octahedron_iff]
    simp
  have hbasis_le :
      Submodule.span ℝ (Set.range (fun i : Fin n ↦ (Pi.single i (1 : ℝ) : Fin n → ℝ))) ≤
        vectorSpan ℝ (octahedron n) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    -- Each positive unit vector lies in the octahedron, so its difference from the origin lies in
    -- the vector span of the octahedron.
    rw [vectorSpan_eq_span_vsub_set_right ℝ hzero]
    exact Submodule.subset_span ⟨Pi.single i (1 : ℝ), positiveUnit_mem_octahedron (n := n) i, by
      simp⟩
  have hbasis_top :
      Submodule.span ℝ (Set.range (fun i : Fin n ↦ (Pi.single i (1 : ℝ) : Fin n → ℝ))) = ⊤ := by
    -- The standard basis of `Fin n → ℝ` spans the whole ambient space.
    simpa using
      (Pi.linearIndependent_single_one (Fin n) ℝ).span_eq_top_of_card_eq_finrank'
        (by simp)
  have hvector_top : vectorSpan ℝ (octahedron n) = ⊤ := by
    -- The octahedron contains the standard basis, so its vector span is already the whole space.
    exact top_unique <| by
      rw [← hbasis_top]
      exact hbasis_le
  calc
    Module.finrank ℝ (affineSpan ℝ (octahedron n)).direction
        = Module.finrank ℝ (vectorSpan ℝ (octahedron n)) := by
            rw [direction_affineSpan]
    _ = Module.finrank ℝ (⊤ : Submodule ℝ (Fin n → ℝ)) := by rw [hvector_top]
    _ = n := by simp

/-- Helper for Exercise 3.33: insert a zero into the omitted coordinate and keep the remaining
coordinates unchanged. -/
def coordinate_face_insertZeroLinearMap {m : ℕ} (i : Fin m) :
    ({j : Fin m // j ≠ i} → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.pi fun k : Fin m ↦
    if h : k = i then
      (0 : ({j : Fin m // j ≠ i} → ℝ) →ₗ[ℝ] ℝ)
    else
      LinearMap.proj (R := ℝ) (φ := fun _ : {j : Fin m // j ≠ i} ↦ ℝ) ⟨k, h⟩

/-- Helper for Exercise 3.33: evaluating the zero-insertion map is the expected `if`-formula. -/
theorem coordinate_face_insertZeroLinearMap_apply {m : ℕ} (i : Fin m)
    (w : {j : Fin m // j ≠ i} → ℝ) (k : Fin m) :
    coordinate_face_insertZeroLinearMap i w k = if h : k = i then 0 else w ⟨k, h⟩ := by
  -- Expand the `pi`-linear map coordinatewise and split on the omitted index.
  by_cases hk : k = i
  · simp [coordinate_face_insertZeroLinearMap, hk]
  · simp [coordinate_face_insertZeroLinearMap, hk]

/-- Helper for Exercise 3.33: the simplex face `z i = 0` is the image of the smaller simplex on
the omitted-index subtype under zero insertion. -/
theorem stdSimplex_coordinate_face_eq_image_insertZero {m : ℕ} (i : Fin m) :
    {z : Fin m → ℝ | z ∈ stdSimplex ℝ (Fin m) ∧ z i = 0} =
      coordinate_face_insertZeroLinearMap i '' stdSimplex ℝ {j : Fin m // j ≠ i} := by
  -- Route correction: identify the coordinate face with a smaller simplex before pushing convex
  -- hulls, instead of reconstructing barycentric weights directly in the ambient space.
  ext z
  constructor
  · intro hz
    refine ⟨fun j ↦ z j.1, ?_, ?_⟩
    · -- Restricting a face point to the omitted coordinates preserves simplex nonnegativity
      -- and sum.
      refine ⟨fun j ↦ hz.1.1 j.1, ?_⟩
      rw [← hz.1.2, Fintype.sum_eq_add_sum_subtype_ne (f := z) i, hz.2, zero_add]
    · -- Reinserting the omitted zero recovers the original face point coordinatewise.
      ext k
      by_cases hk : k = i
      · simp [coordinate_face_insertZeroLinearMap_apply, hk, hz.2]
      · simp [coordinate_face_insertZeroLinearMap_apply, hk]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · -- Zero insertion preserves simplex membership because it adds one zero coordinate.
      refine ⟨?_, ?_⟩
      · intro k
        by_cases hk : k = i
        · simp [coordinate_face_insertZeroLinearMap_apply, hk]
        · simpa [coordinate_face_insertZeroLinearMap_apply, hk] using hw.1 ⟨k, hk⟩
      · rw [Fintype.sum_eq_add_sum_subtype_ne (f := coordinate_face_insertZeroLinearMap i w) i]
        have hsum_sub :
            (∑ x : {j : Fin m // j ≠ i},
                coordinate_face_insertZeroLinearMap i w x.1) =
              ∑ x : {j : Fin m // j ≠ i}, w x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [coordinate_face_insertZeroLinearMap_apply, x.2]
        rw [hsum_sub, hw.2]
        simp [coordinate_face_insertZeroLinearMap_apply]
    · -- The inserted point vanishes at the omitted coordinate by construction.
      simp [coordinate_face_insertZeroLinearMap_apply]

/-- Helper for Exercise 3.33: inserting the omitted simplex basis vector produces the ambient basis
vector at the same coordinate. -/
theorem coordinate_face_insertZeroLinearMap_apply_single {m : ℕ} (i : Fin m)
    (j : {j : Fin m // j ≠ i}) :
    coordinate_face_insertZeroLinearMap i (Pi.single j (1 : ℝ)) = Pi.single j.1 (1 : ℝ) := by
  -- The only surviving coordinate is the one indexed by `j`.
  ext k
  by_cases hk : k = i
  · simp [coordinate_face_insertZeroLinearMap_apply, hk, j.2]
  · simp [coordinate_face_insertZeroLinearMap_apply, hk, Pi.single_apply, Subtype.ext_iff]

/-- Helper for Exercise 3.33: every simplex coordinate face is the convex hull of the basis vectors
omitting that coordinate. -/
theorem stdSimplex_coordinate_face_eq_convexHull_omitted_basis {m : ℕ} (i : Fin m) :
    {z : Fin m → ℝ | z ∈ stdSimplex ℝ (Fin m) ∧ z i = 0} =
      convexHull ℝ (Set.range (fun j : {j : Fin m // j ≠ i} ↦ Pi.single j.1 (1 : ℝ))) := by
  -- Rewrite the coordinate face as a smaller simplex and then push its basis-vertex convex hull
  -- through the zero-insertion linear map.
  rw [stdSimplex_coordinate_face_eq_image_insertZero]
  rw [← convexHull_rangle_single_eq_stdSimplex (R := ℝ) (ι := {j : Fin m // j ≠ i})]
  rw [LinearMap.image_convexHull]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, (coordinate_face_insertZeroLinearMap_apply_single i j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Pi.single j (1 : ℝ), ⟨j, rfl⟩, coordinate_face_insertZeroLinearMap_apply_single i j⟩

/-- Helper for Exercise 3.33: the standard simplex on `Fin m` has affine dimension `m - 1`. -/
theorem stdSimplex_finrank_direction_affineSpan {m : ℕ} (hm : 0 < m) :
    Module.finrank ℝ (affineSpan ℝ (stdSimplex ℝ (Fin m))).direction = m - 1 := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  -- The simplex is the convex hull of `m` affinely independent basis vertices.
  rw [← convexHull_rangle_single_eq_stdSimplex (R := ℝ) (ι := Fin m), affineSpan_convexHull,
    direction_affineSpan]
  have hcard :
      Module.finrank ℝ (vectorSpan ℝ (Set.range fun i : Fin m ↦ Pi.single i (1 : ℝ))) + 1 = m := by
    simpa using
      (AffineIndependent.finrank_vectorSpan_add_one
        (k := ℝ) (p := fun i : Fin m ↦ Pi.single i (1 : ℝ))
        ((Pi.linearIndependent_single_one (Fin m) ℝ).affineIndependent))
  omega

/-- Helper for Exercise 3.33: on a simplex equality face, any coordinate with strict coefficient
slack must vanish. -/
theorem stdSimplexFace_coord_eq_zero_of_lt {m : ℕ} {c : Fin m → ℝ} {δ : ℝ}
    (i : Fin m) {x : Fin m → ℝ}
    (hvalid : is_valid_inequality (stdSimplex ℝ (Fin m)) c δ)
    (hx : x ∈ face_set (stdSimplex ℝ (Fin m)) c δ) (hi : c i < δ) :
    x i = 0 := by
  rw [mem_face_set_iff] at hx
  have hbound : ∀ j : Fin m, c j ≤ δ := by
    intro j
    simpa [dotProduct, Pi.single_apply] using hvalid (single_mem_stdSimplex ℝ j)
  have hdefect :
      ∑ j : Fin m, x j * (δ - c j) = 0 := by
    -- Expand the defect sum into `δ * (∑ x j) - c ⬝ᵥ x`.
    calc
      ∑ j : Fin m, x j * (δ - c j)
          = ∑ j : Fin m, (δ * x j - c j * x j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = δ * ∑ j : Fin m, x j - c ⬝ᵥ x := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum, dotProduct]
      _ = 0 := by
            rw [hx.1.2, hx.2]
            ring
  have hnonneg :
      ∀ j ∈ Finset.univ, 0 ≤ x j * (δ - c j) := by
    intro j hj
    exact mul_nonneg (hx.1.1 j) (sub_nonneg.mpr (hbound j))
  have hterm_le :
      x i * (δ - c i) ≤ ∑ j : Fin m, x j * (δ - c j) := by
    exact Finset.single_le_sum (fun j _ ↦ hnonneg j (by simp)) (by simp)
  have hterm_eq : x i * (δ - c i) = 0 := by
    have hterm_nonneg : 0 ≤ x i * (δ - c i) := hnonneg i (by simp)
    linarith
  have hgap_ne : δ - c i ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr hi)
  exact (mul_eq_zero.mp hterm_eq).resolve_right hgap_ne

/-- Helper for Exercise 3.33: a nonempty simplex equality face is the convex hull of the basis
vertices whose coefficients are tight. -/
theorem stdSimplexFace_eq_convexHull_tightBasis {m : ℕ} {c : Fin m → ℝ} {δ : ℝ}
    (hvalid : is_valid_inequality (stdSimplex ℝ (Fin m)) c δ)
    (_hface_nonempty : (face_set (stdSimplex ℝ (Fin m)) c δ).Nonempty) :
    face_set (stdSimplex ℝ (Fin m)) c δ =
      convexHull ℝ (Set.range (fun i : {i : Fin m // c i = δ} ↦ Pi.single i.1 (1 : ℝ))) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rw [mem_face_set_iff] at hx
    have hbound : ∀ j : Fin m, c j ≤ δ := by
      intro j
      simpa [dotProduct, Pi.single_apply] using hvalid (single_mem_stdSimplex ℝ j)
    have hsum_tight :
        ∑ i : {i : Fin m // c i = δ}, x i.1 = 1 := by
      -- Tight coordinates carry the entire barycentric mass because all slack coordinates vanish.
      calc
        ∑ i : {i : Fin m // c i = δ}, x i.1
            = ∑ j : Fin m, if c j = δ then x j else 0 := by
                simpa [Finset.sum_filter] using
                  (Finset.sum_toFinset_eq_subtype
                    (p := fun j : Fin m ↦ c j = δ) (f := fun j : Fin m ↦ x j)).symm
        _ = ∑ j : Fin m, x j := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              by_cases hjtight : c j = δ
              · simp [hjtight]
              · have hjlt : c j < δ := lt_of_le_of_ne (hbound j) hjtight
                simp [hjtight, stdSimplexFace_coord_eq_zero_of_lt (i := j) hvalid hx hjlt]
        _ = 1 := hx.1.2
    have hx_repr :
        x = ∑ i : {i : Fin m // c i = δ}, x i.1 • Pi.single i.1 (1 : ℝ) := by
      -- Only tight basis vectors can contribute to a point on the equality face.
      ext k
      by_cases hk : c k = δ
      · let ik : {i : Fin m // c i = δ} := ⟨k, hk⟩
        rw [Finset.sum_apply, Finset.sum_eq_single ik]
        · simp [ik]
        · intro j hj hjne
          have hjk : j.1 ≠ k := by
            intro hEq
            apply hjne
            exact Subtype.ext (by simpa [ik] using hEq)
          simp [hjk]
        · intro hik
          exact (hik (by simp)).elim
      · have hklt : c k < δ := lt_of_le_of_ne (hbound k) hk
        have hxk : x k = 0 := stdSimplexFace_coord_eq_zero_of_lt (i := k) hvalid hx hklt
        have hsum_zero :
            (∑ i : {i : Fin m // c i = δ}, x i.1 • Pi.single i.1 (1 : ℝ)) k = 0 := by
          rw [Finset.sum_apply]
          refine Finset.sum_eq_zero ?_
          intro j hj
          have hjk : j.1 ≠ k := by
            intro hEq
            exact hk (by simpa [hEq] using j.2)
          rw [Pi.smul_apply]
          simp [hjk]
        simpa [hxk] using hsum_zero.symm
    have hcenter :
        Finset.univ.centerMass (fun i : {i : Fin m // c i = δ} ↦ x i.1)
            (fun i : {i : Fin m // c i = δ} ↦ (Pi.single i.1 (1 : ℝ) : Fin m → ℝ)) ∈
          convexHull ℝ
            (Set.range (fun i : {i : Fin m // c i = δ} ↦ (Pi.single i.1 (1 : ℝ) : Fin m → ℝ))) := by
      refine Finset.univ.centerMass_mem_convexHull (fun i hi ↦ hx.1.1 i.1) ?_ ?_
      · simp [hsum_tight]
      · intro i hi
        exact ⟨i, rfl⟩
    have hcenter_eq :
        Finset.univ.centerMass (fun i : {i : Fin m // c i = δ} ↦ x i.1)
            (fun i : {i : Fin m // c i = δ} ↦ (Pi.single i.1 (1 : ℝ) : Fin m → ℝ)) =
          ∑ i : {i : Fin m // c i = δ}, x i.1 • Pi.single i.1 (1 : ℝ) := by
      simpa using
        (Finset.centerMass_eq_of_sum_1
          (t := Finset.univ) (w := fun i : {i : Fin m // c i = δ} ↦ x i.1)
          (z := fun i : {i : Fin m // c i = δ} ↦ (Pi.single i.1 (1 : ℝ) : Fin m → ℝ)) hsum_tight)
    rw [hcenter_eq] at hcenter
    exact hx_repr.symm ▸ hcenter
  · have hconv_face :
        Convex ℝ (face_set (stdSimplex ℝ (Fin m)) c δ) := by
      exact (isExposed_face_set_of_valid_inequality (P := stdSimplex ℝ (Fin m))
        (c := c) (δ := δ) hvalid).convex (convex_stdSimplex ℝ (Fin m))
    -- Every tight basis vertex already lies on the equality face.
    refine convexHull_min ?_ hconv_face
    rintro _ ⟨i, rfl⟩
    rw [mem_face_set_iff]
    refine ⟨single_mem_stdSimplex ℝ i.1, ?_⟩
    simpa [dotProduct, Pi.single_apply] using i.2

/-- Helper for Exercise 3.33: a simplex facet has exactly `m - 1` tight basis vertices. -/
theorem stdSimplexTightBasis_card_of_facet {m : ℕ} (hm : 0 < m) {c : Fin m → ℝ} {δ : ℝ}
    (hvalid : is_valid_inequality (stdSimplex ℝ (Fin m)) c δ)
    (hFacet : IsFacetOf (stdSimplex ℝ (Fin m)) (face_set (stdSimplex ℝ (Fin m)) c δ)) :
    Fintype.card {i : Fin m // c i = δ} = m - 1 := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hFacet' := (isFacetOf_iff.mp hFacet)
  have hdim_face :
      Module.finrank ℝ (affineSpan ℝ (face_set (stdSimplex ℝ (Fin m)) c δ)).direction = m - 2 := by
    have hface_plus_one :
        Module.finrank ℝ (affineSpan ℝ (face_set (stdSimplex ℝ (Fin m)) c δ)).direction + 1 =
          m - 1 := by
      simpa [stdSimplex_finrank_direction_affineSpan hm] using hFacet'.2.2
    omega
  rw [stdSimplexFace_eq_convexHull_tightBasis hvalid hFacet'.1, affineSpan_convexHull,
    direction_affineSpan] at hdim_face
  have htight_nonempty : Nonempty {i : Fin m // c i = δ} := by
    have hconv_nonempty :
        (convexHull ℝ
          (Set.range
            (fun i : {i : Fin m // c i = δ} ↦ (Pi.single i.1 (1 : ℝ) : Fin m → ℝ)))).Nonempty := by
      rw [← stdSimplexFace_eq_convexHull_tightBasis hvalid hFacet'.1]
      exact hFacet'.1
    rw [convexHull_nonempty_iff] at hconv_nonempty
    rcases hconv_nonempty with ⟨y, ⟨i, rfl⟩⟩
    exact ⟨i⟩
  letI : Nonempty {i : Fin m // c i = δ} := htight_nonempty
  let p : {i : Fin m // c i = δ} → Fin m → ℝ := fun i ↦ Pi.single i.1 (1 : ℝ)
  have hp_aff : AffineIndependent ℝ p := by
    simpa [p] using
      (((Pi.linearIndependent_single_one (Fin m) ℝ).affineIndependent).subtype
        {i : Fin m | c i = δ})
  have hcard :
      Module.finrank ℝ
          (vectorSpan ℝ (Set.range p)) + 1 =
        Fintype.card {i : Fin m // c i = δ} := by
    simpa [p] using
      (AffineIndependent.finrank_vectorSpan_add_one (k := ℝ) (p := p) hp_aff)
  have hdim_face' : Module.finrank ℝ (vectorSpan ℝ (Set.range p)) = m - 2 := by
    simpa [p] using hdim_face
  have hm_ge_two : 2 ≤ m := by
    have hface_plus_one :
        Module.finrank ℝ (affineSpan ℝ (face_set (stdSimplex ℝ (Fin m)) c δ)).direction + 1 =
          m - 1 := by
      simpa [stdSimplex_finrank_direction_affineSpan hm] using hFacet'.2.2
    have hm_sub_pos : 0 < m - 1 := by
      have hsucc_pos :
          0 <
            Module.finrank ℝ (affineSpan ℝ (face_set (stdSimplex ℝ (Fin m)) c δ)).direction + 1 :=
        Nat.succ_pos _
      omega
    omega
  calc
    Fintype.card {i : Fin m // c i = δ}
        = Module.finrank ℝ (vectorSpan ℝ (Set.range p)) + 1 := by
          simpa using hcard.symm
    _ = (m - 2) + 1 := by rw [hdim_face']
    _ = m - 1 := by omega

/-- Helper for Exercise 3.33: every facet of the standard simplex is obtained by omitting one
coordinate vertex. -/
theorem stdSimplexFacet_eq_coordinateFace {m : ℕ} (hm : 0 < m)
    {F : Set (Fin m → ℝ)} (hF : IsFacetOf (stdSimplex ℝ (Fin m)) F) :
    ∃ i : Fin m, F = {z : Fin m → ℝ | z ∈ stdSimplex ℝ (Fin m) ∧ z i = 0} := by
  classical
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  rcases (isFacetOf_iff.mp hF) with ⟨hF_nonempty, hF_exposed, hF_dim⟩
  rcases hF_exposed.exists_eq_face_set_of_nonempty hF_nonempty with ⟨c, δ, hvalid, hF_eq⟩
  have hFacetFace :
      IsFacetOf (stdSimplex ℝ (Fin m)) (face_set (stdSimplex ℝ (Fin m)) c δ) := by
    simpa [hF_eq] using hF
  have htight_card :
      Fintype.card {i : Fin m // c i = δ} = m - 1 :=
    stdSimplexTightBasis_card_of_facet hm hvalid hFacetFace
  have hslack_card :
      Fintype.card {i : Fin m // c i ≠ δ} = 1 := by
    have hcompl := Fintype.card_subtype_compl (p := fun i : Fin m ↦ c i = δ)
    calc
      Fintype.card {i : Fin m // c i ≠ δ}
          = m - Fintype.card {i : Fin m // c i = δ} := by
              convert hcompl using 1
              simp
      _ = m - (m - 1) := by rw [htight_card]
      _ = 1 := by omega
  obtain ⟨u⟩ := (Fintype.card_eq_one_iff_nonempty_unique).1 hslack_card
  letI : Unique {i : Fin m // c i ≠ δ} := u
  let i0 : {i : Fin m // c i ≠ δ} := default
  have hbound : ∀ j : Fin m, c j ≤ δ := by
    intro j
    simpa [dotProduct, Pi.single_apply] using hvalid (single_mem_stdSimplex ℝ j)
  have htight_of_ne : ∀ j : Fin m, j ≠ i0.1 → c j = δ := by
    intro j hj
    by_contra hj_slack
    have : (⟨j, hj_slack⟩ : {i : Fin m // c i ≠ δ}) = i0 := by
      exact Subsingleton.elim _ _
    exact hj (Subtype.ext_iff.mp this)
  refine ⟨i0.1, ?_⟩
  rw [hF_eq]
  ext x
  constructor
  · intro hx
    rw [mem_face_set_iff] at hx
    have hi0_lt : c i0.1 < δ := lt_of_le_of_ne (hbound i0.1) i0.2
    exact ⟨hx.1, stdSimplexFace_coord_eq_zero_of_lt (i := i0.1) hvalid hx hi0_lt⟩
  · intro hx
    rw [mem_face_set_iff]
    refine ⟨hx.1, ?_⟩
    have hcoeff : ∀ j : Fin m, c j * x j = δ * x j := by
      intro j
      by_cases hj : j = i0.1
      · subst j
        rw [hx.2]
        ring
      · rw [htight_of_ne j hj]
    calc
      c ⬝ᵥ x = ∑ j : Fin m, δ * x j := by
                rw [dotProduct]
                refine Finset.sum_congr rfl ?_
                intro j hj
                exact hcoeff j
      _ = δ * ∑ j : Fin m, x j := by rw [Finset.mul_sum]
      _ = δ := by rw [hx.1.2, mul_one]

/-- Helper for Exercise 3.33: the lifted octahedron extension is convex. -/
theorem convex_octahedron_extension (n : ℕ) :
    Convex ℝ (octahedron_extension n) := by
  intro x hx y hy a b ha hb hab
  rcases x with ⟨x₁, z₁⟩
  rcases y with ⟨x₂, z₂⟩
  rw [mem_octahedron_extension_iff] at hx hy ⊢
  rcases hx with ⟨hxcoord, hxsum, hxpos, hxneg⟩
  rcases hy with ⟨hycoord, hysum, hypos, hyneg⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The defining relation `x = z⁺ - z⁻` is preserved coordinatewise by convex combinations.
    ext i
    have hx_i := congrArg (fun v : Fin n → ℝ ↦ v i) hxcoord
    have hy_i := congrArg (fun v : Fin n → ℝ ↦ v i) hycoord
    simp [octahedron_extension_pos, octahedron_extension_neg, Pi.smul_apply,
      hx_i, hy_i, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc]
  · -- The normalization equation is linear in the lifted variables.
    calc
      ∑ i : Fin n,
          (octahedron_extension_pos (a • z₁ + b • z₂) i +
            octahedron_extension_neg (a • z₁ + b • z₂) i)
          = a * ∑ i : Fin n,
              (octahedron_extension_pos z₁ i + octahedron_extension_neg z₁ i) +
            b * ∑ i : Fin n,
              (octahedron_extension_pos z₂ i + octahedron_extension_neg z₂ i) := by
                simp [octahedron_extension_pos, octahedron_extension_neg, Pi.smul_apply,
                  Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_assoc,
                  add_left_comm, add_comm]
      _ = 1 := by nlinarith [hxsum, hysum, hab]
  · -- Nonnegativity of the positive block is preserved under convex combinations with
    -- nonnegative coefficients.
    intro i
    have hnonneg :=
      add_nonneg (mul_nonneg ha (hxpos i)) (mul_nonneg hb (hypos i))
    simpa [octahedron_extension_pos, Pi.smul_apply, mul_add, add_mul] using hnonneg
  · -- The same holds for the negative block.
    intro i
    have hnonneg :=
      add_nonneg (mul_nonneg ha (hxneg i)) (mul_nonneg hb (hyneg i))
    simpa [octahedron_extension_neg, Pi.smul_apply, mul_add, add_mul] using hnonneg

/-- Helper for Exercise 3.33: every coordinate index has a different companion index because the
lifted variable set has cardinality `2n ≥ 2`. -/
theorem octahedron_extension_exists_other_index {n : ℕ} (i : Fin (n + n)) :
    ∃ j : Fin (n + n), j ≠ i := by
  -- The set of lifted coordinates cannot be a singleton because its cardinality is even.
  have hpos : 0 < n + n := by
    refine Nat.pos_of_ne_zero ?_
    intro h
    simpa [h] using i.isLt
  have htwo : 1 < n + n := by omega
  by_cases hi0 : i.1 = 0
  · refine ⟨⟨1, htwo⟩, ?_⟩
    intro h
    have : (1 : ℕ) = 0 := by simpa [hi0] using congrArg Fin.val h.symm
    omega
  · refine ⟨⟨0, hpos⟩, ?_⟩
    intro h
    exact hi0 (by simpa using congrArg Fin.val h.symm)

/-- Part (1) of Exercise 3.33: every signed subset inequality defining `octahedron n` cuts out a
facet. -/
theorem octahedron_signed_face_isFacetOf
    {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    IsFacetOf (octahedron n) (octahedron_signed_face n S) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have h_nonempty : (octahedron_signed_face n S).Nonempty := by
    -- Any compatible signed unit vertex lies on the equality face.
    exact ⟨octahedron_signed_vertex S ⟨0, hn⟩, octahedron_signed_vertex_mem_face S ⟨0, hn⟩⟩
  have h_valid :
      is_valid_inequality (octahedron n) (octahedron_signed_face_normal S) 1 := by
    -- The signed-face inequality is one of the defining octahedron inequalities.
    intro x hx
    simpa [octahedron_signed_face_normal_dotProduct] using
      (mem_octahedron_iff_forall_signed_coordinate_sum_le_one.mp hx) S
  have h_exposed : IsExposed ℝ (octahedron n) (octahedron_signed_face n S) := by
    -- Equality in a valid inequality always defines an exposed face.
    simpa [octahedron_signed_face] using
      isExposed_face_set_of_valid_inequality (P := octahedron n)
        (c := octahedron_signed_face_normal S) (δ := 1) h_valid
  have h_face_dim :
      Module.finrank ℝ (affineSpan ℝ (octahedron_signed_face n S)).direction = n - 1 := by
    -- The face is the convex hull of `n` affinely independent signed unit vertices.
    rw [octahedron_signed_face_eq_convexHull_signed_vertices, affineSpan_convexHull,
      direction_affineSpan]
    have hcard :
        Module.finrank ℝ (vectorSpan ℝ (Set.range (octahedron_signed_vertex S))) + 1 = n := by
      simpa using
        (AffineIndependent.finrank_vectorSpan_add_one
          (k := ℝ) (p := octahedron_signed_vertex S)
          (octahedron_signed_vertex_affineIndependent S))
    omega
  rw [isFacetOf_iff]
  refine ⟨h_nonempty, h_exposed, ?_⟩
  have hoct_dim := octahedron_finrank_direction_affineSpan hn
  omega

/-- Helper for Exercise 3.33: the face cut out by `x i = 1` consists of the single positive unit
vector `e^i`. -/
theorem positiveCoordinateFace_eq_singleton {n : ℕ} (i : Fin n) :
    face_set (octahedron n) (Pi.single i (1 : ℝ)) 1 = {Pi.single i (1 : ℝ)} := by
  ext x
  constructor
  · intro hx
    rw [mem_face_set_iff, mem_octahedron_iff] at hx
    have hxi : x i = 1 := by
      simpa using hx.2
    have hsum_eq : ∑ j : Fin n, |x j| = 1 := by
      have hsum_le : ∑ j : Fin n, |x j| ≤ 1 := hx.1
      have hi_le_sum :
          |x i| ≤ ∑ j : Fin n, |x j| := by
        exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x j)) (by simp)
      have habs_i : |x i| = 1 := by simp [hxi]
      linarith
    have hrest_eq_zero :
        Finset.sum (Finset.univ.erase i) (fun j : Fin n ↦ |x j|) = 0 := by
      rw [← Finset.sum_erase_add (s := Finset.univ) (a := i) (f := fun j : Fin n ↦ |x j|)
        (by simp)] at hsum_eq
      have habs_i : |x i| = 1 := by simp [hxi]
      linarith
    have hrest_nonneg :
        ∀ j ∈ Finset.univ.erase i, 0 ≤ |x j| := by
      intro j hj
      exact abs_nonneg (x j)
    have hzero : ∀ j : Fin n, j ≠ i → x j = 0 := by
      intro j hji
      have habs_zero :
          |x j| = 0 := by
        exact (Finset.sum_eq_zero_iff_of_nonneg hrest_nonneg).mp hrest_eq_zero j (by simp [hji])
      exact abs_eq_zero.mp habs_zero
    have hx_eq : x = Pi.single i (1 : ℝ) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [hxi]
      · simp [hji, hzero j hji]
    simp [hx_eq]
  · rintro rfl
    -- The positive unit vector lies in the octahedron and makes the supporting inequality tight.
    rw [mem_face_set_iff]
    refine ⟨positiveUnit_mem_octahedron (n := n) i, ?_⟩
    simp

/-- Helper for Exercise 3.33: the face cut out by `-x i = 1` consists of the single negative unit
vector `-e^i`. -/
theorem negativeCoordinateFace_eq_singleton {n : ℕ} (i : Fin n) :
    face_set (octahedron n) (-Pi.single i (1 : ℝ)) 1 = {-Pi.single i (1 : ℝ)} := by
  ext x
  constructor
  · intro hx
    have hnegx : -x ∈ face_set (octahedron n) (Pi.single i (1 : ℝ)) 1 := by
      -- Negating the point turns the reflected supporting equation into the positive one.
      rw [mem_face_set_iff] at hx ⊢
      refine ⟨?_, ?_⟩
      · rw [mem_octahedron_iff] at hx ⊢
        simpa using hx.1
      · simpa [dotProduct] using hx.2
    have hsingle : -x ∈ ({Pi.single i (1 : ℝ)} : Set (Fin n → ℝ)) := by
      simpa [positiveCoordinateFace_eq_singleton (n := n) i] using hnegx
    have hsingle_eq : -x = Pi.single i (1 : ℝ) := by
      simpa using hsingle
    have hx_eq : x = -Pi.single i (1 : ℝ) := by
      simpa using congrArg Neg.neg hsingle_eq
    simp [hx_eq]
  · rintro rfl
    -- The reflected unit vector is the negative of a positive singleton-face point.
    rw [mem_face_set_iff]
    refine ⟨negativeUnit_mem_octahedron (n := n) i, ?_⟩
    rw [dotProduct, Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · intro hi
      exact (hi (by simp)).elim

/-- Helper for Exercise 3.33: the positive unit vector `e^i` is an exposed, hence extreme, point of
`octahedron n`. -/
theorem positiveUnit_mem_extremePoints {n : ℕ} (i : Fin n) :
    Pi.single i (1 : ℝ) ∈ (octahedron n).extremePoints ℝ := by
  -- The coordinate inequality `x i ≤ 1` is valid on `octahedron n`, and its equality face is the
  -- singleton `{e^i}`.
  have h_valid : is_valid_inequality (octahedron n) (Pi.single i (1 : ℝ)) 1 := by
    intro x hx
    have hsum_le : ∑ j : Fin n, |x j| ≤ 1 := mem_octahedron_iff.mp hx
    calc
      (Pi.single i (1 : ℝ)) ⬝ᵥ x = x i := by simp
      _ ≤ |x i| := le_abs_self (x i)
      _ ≤ ∑ j : Fin n, |x j| := by
            exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x j)) (by simp)
      _ ≤ 1 := hsum_le
  have h_exposed :
      IsExposed ℝ (octahedron n) {Pi.single i (1 : ℝ)} := by
    -- Rewrite the equality face to the canonical singleton before converting exposed sets to
    -- exposed points.
    rw [← positiveCoordinateFace_eq_singleton (n := n) i]
    exact isExposed_face_set_of_valid_inequality h_valid
  exact exposedPoints_subset_extremePoints <|
    (mem_exposedPoints_iff_exposed_singleton).2 h_exposed

/-- Helper for Exercise 3.33: the negative unit vector `-e^i` is an exposed, hence extreme, point
of `octahedron n`. -/
theorem negativeUnit_mem_extremePoints {n : ℕ} (i : Fin n) :
    -Pi.single i (1 : ℝ) ∈ (octahedron n).extremePoints ℝ := by
  -- The reflected coordinate inequality `-x i ≤ 1` has the singleton face `{-e^i}`.
  have h_valid : is_valid_inequality (octahedron n) (-Pi.single i (1 : ℝ)) 1 := by
    intro x hx
    have hsum_le : ∑ j : Fin n, |x j| ≤ 1 := mem_octahedron_iff.mp hx
    calc
      (-Pi.single i (1 : ℝ)) ⬝ᵥ x = -x i := by simp
      _ ≤ |x i| := by simpa using neg_le_abs (x i)
      _ ≤ ∑ j : Fin n, |x j| := by
            exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x j)) (by simp)
      _ ≤ 1 := hsum_le
  have h_exposed :
      IsExposed ℝ (octahedron n) {-Pi.single i (1 : ℝ)} := by
    -- Rewrite the equality face to the canonical singleton before applying the exposed-point API.
    rw [← negativeCoordinateFace_eq_singleton (n := n) i]
    exact isExposed_face_set_of_valid_inequality h_valid
  exact exposedPoints_subset_extremePoints <|
    (mem_exposedPoints_iff_exposed_singleton).2 h_exposed

/-- Helper for Exercise 3.33: every signed unit vertex of the octahedron is an extreme point. -/
theorem octahedronVertex_mem_extremePoints {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ octahedron_vertices n) :
    x ∈ (octahedron n).extremePoints ℝ := by
  -- Split the signed vertex into the positive and negative basis-vector cases.
  rw [mem_octahedron_vertices_iff] at hx
  rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact positiveUnit_mem_extremePoints (n := n) i
  · exact negativeUnit_mem_extremePoints (n := n) i

/-- Part (2) of Exercise 3.33: the vertices of `octahedron n` are exactly the signed unit vectors
`± e^i`. -/
theorem octahedron_extremePoints_eq_vertices
    {n : ℕ} (hn : 0 < n) :
    (octahedron n).extremePoints ℝ = octahedron_vertices n := by
  apply Set.Subset.antisymm
  · intro x hx
    -- After rewriting the octahedron as a convex hull of its vertices, extreme points can only be
    -- those vertices.
    rw [octahedron_eq_convexHull_vertices hn] at hx
    exact extremePoints_convexHull_subset hx
  · intro x hx
    exact octahedronVertex_mem_extremePoints hx

/-- Part (3) of Exercise 3.33: `octahedron n` has exactly `2n` vertices. -/
theorem octahedron_vertices_ncard
    {n : ℕ} (hn : 0 < n) :
    ((octahedron n).extremePoints ℝ).ncard = n + n := by
  rw [octahedron_extremePoints_eq_vertices hn, octahedron_vertices]
  have hpos_inj :
      Function.Injective (fun i : Fin n ↦ (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    intro i j hij
    have hcoord := congrArg (fun f : Fin n → ℝ ↦ f i) hij
    by_cases hji : j = i
    · exact hji.symm
    · simp [hji] at hcoord
  have hneg_inj :
      Function.Injective (fun i : Fin n ↦ (-Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    intro i j hij
    exact hpos_inj <| by simpa using neg_injective hij
  have hdisj :
      Disjoint
        (Set.range (fun i : Fin n ↦ (Pi.single i (1 : ℝ) : Fin n → ℝ)))
        (Set.range (fun i : Fin n ↦ (-Pi.single i (1 : ℝ) : Fin n → ℝ))) := by
    refine Set.disjoint_left.2 ?_
    intro x hxpos hxneg
    rcases hxpos with ⟨i, rfl⟩
    rcases hxneg with ⟨j, hj⟩
    have hcoord := congrArg (fun f : Fin n → ℝ ↦ f i) hj
    by_cases hji : j = i
    · subst j
      norm_num at hcoord
    · simp [hji] at hcoord
  rw [Set.ncard_union_eq hdisj, Set.ncard_range_of_injective hpos_inj,
    Set.ncard_range_of_injective hneg_inj]
  simp

/- Exercise 3.33 (4): Example 3.45 already proves that the projection onto the `x`-coordinates of
the lifted polyhedron is `octahedron n`. -/
#check image_fst_octahedron_extension_eq_octahedron

/-- Helper for Exercise 3.33: the lifted polyhedron is the graph image of the standard simplex on
`Fin (n + n)`. -/
theorem octahedron_extension_eq_graph_image_stdSimplex {n : ℕ} :
    octahedron_extension n =
      octahedron_extension_graphLinearMap n '' stdSimplex ℝ (Fin (n + n)) := by
  ext xz
  constructor
  · intro hxz
    rcases xz with ⟨x, z⟩
    rw [mem_octahedron_extension_iff] at hxz
    rcases hxz with ⟨hx, hsum, hz_pos, hz_neg⟩
    refine ⟨z, ?_, ?_⟩
    · -- Every lifted feasible point has nonnegative coordinates summing to one.
      refine ⟨?_, ?_⟩
      · intro j
        cases h : finSumFinEquiv.symm j with
        | inl i =>
            have hj : Fin.castAdd n i = j := by
              simpa [h] using (finSumFinEquiv.apply_symm_apply j)
            rw [← hj]
            simpa [octahedron_extension_pos] using hz_pos i
        | inr i =>
            have hj : Fin.natAdd n i = j := by
              simpa [h] using (finSumFinEquiv.apply_symm_apply j)
            rw [← hj]
            simpa [octahedron_extension_neg] using hz_neg i
      · -- The simplex normalization is exactly the extension's sum equation.
        rw [Fin.sum_univ_add]
        simpa [octahedron_extension_pos, octahedron_extension_neg,
          Finset.sum_add_distrib] using hsum
    · -- The graph map reconstructs the original lifted point.
      ext
      · simp [octahedron_extension_graphLinearMap, octahedron_extension_pos_linearMap,
          octahedron_extension_neg_linearMap, octahedron_extension_pos,
          octahedron_extension_neg, hx]
      · simp [octahedron_extension_graphLinearMap]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_octahedron_extension_iff]
    have hz_nonneg : ∀ i : Fin (n + n), 0 ≤ z i := hz.1
    have hsum : ∑ i : Fin (n + n), z i = 1 := hz.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The first graph component is the signed projection of `z`.
      ext i
      simp [octahedron_extension_graphLinearMap, octahedron_extension_pos_linearMap,
        octahedron_extension_neg_linearMap, octahedron_extension_pos,
        octahedron_extension_neg]
    · -- Splitting the total simplex sum recovers the extension normalization equation.
      rw [Fin.sum_univ_add] at hsum
      rw [Finset.sum_add_distrib]
      simpa [octahedron_extension_graphLinearMap, octahedron_extension_pos_linearMap,
        octahedron_extension_neg_linearMap, octahedron_extension_pos,
        octahedron_extension_neg] using hsum
    · intro i
      simpa [octahedron_extension_pos] using hz_nonneg (Fin.castAdd n i)
    · intro i
      simpa [octahedron_extension_neg] using hz_nonneg (Fin.natAdd n i)

/-- Helper for Exercise 3.33: every graph vertex whose index is not `i` belongs to the coordinate
face `z i = 0`. -/
theorem octahedron_extension_graphVertex_mem_coordinate_face {n : ℕ}
    (i : Fin (n + n)) (j : {j : Fin (n + n) // j ≠ i}) :
    octahedron_extension_graphVertex n j.1 ∈ octahedron_extension_coordinate_face n i := by
  -- A graph vertex comes from a simplex basis vertex, and omitting `i` forces the `i`-th lifted
  -- coordinate to vanish.
  rw [mem_octahedron_extension_coordinate_face_iff]
  refine ⟨?_, ?_⟩
  · rw [octahedron_extension_eq_graph_image_stdSimplex]
    exact ⟨Pi.single j.1 (1 : ℝ), single_mem_stdSimplex ℝ j.1, rfl⟩
  · simp [octahedron_extension_graphVertex, octahedron_extension_graphLinearMap, j.2]

/-- Helper for Exercise 3.33: the extension coordinate face is exactly the graph image of the
simplex coordinate face omitting the same lifted coordinate. -/
theorem octahedron_extension_coordinate_face_eq_graph_image_coordinate_face
    {n : ℕ} (i : Fin (n + n)) :
    octahedron_extension_coordinate_face n i =
      octahedron_extension_graphLinearMap n ''
        {z : Fin (n + n) → ℝ | z ∈ stdSimplex ℝ (Fin (n + n)) ∧ z i = 0} := by
  -- Route correction: isolate the transport through the graph map before any convex-hull rewrite.
  ext xz
  constructor
  · intro hxz
    rw [mem_octahedron_extension_coordinate_face_iff] at hxz
    rcases hxz with ⟨hxz_ext, hxz_zero⟩
    rw [octahedron_extension_eq_graph_image_stdSimplex] at hxz_ext
    rcases hxz_ext with ⟨z, hz_simplex, rfl⟩
    refine ⟨z, ?_, rfl⟩
    -- The second component of the graph map is the identity, so the face equation
    -- becomes `z i = 0`.
    refine ⟨hz_simplex, ?_⟩
    simpa [octahedron_extension_graphLinearMap] using hxz_zero
  · rintro ⟨z, hz, rfl⟩
    rw [mem_octahedron_extension_coordinate_face_iff]
    refine ⟨?_, ?_⟩
    · -- Any simplex point maps into the graph description of the extension.
      rw [octahedron_extension_eq_graph_image_stdSimplex]
      exact ⟨z, hz.1, rfl⟩
    · -- The graph map preserves the lifted coordinates in its second component.
      simpa [octahedron_extension_graphLinearMap] using hz.2

/-- Helper for Exercise 3.33: the coordinate face `z i = 0` is the convex hull of the graph
vertices omitting index `i`. -/
theorem octahedron_extension_coordinate_face_eq_convexHull_omitted_graph_vertices
    {n : ℕ} (i : Fin (n + n)) :
    octahedron_extension_coordinate_face n i =
      convexHull ℝ
        (Set.range
          (fun j : {j : Fin (n + n) // j ≠ i} ↦ octahedron_extension_graphVertex n j.1)) := by
  -- Transport the omitted-coordinate simplex face through the graph map and identify the basis
  -- images with the omitted graph vertices.
  rw [octahedron_extension_coordinate_face_eq_graph_image_coordinate_face]
  rw [stdSimplex_coordinate_face_eq_convexHull_omitted_basis]
  rw [LinearMap.image_convexHull]
  congr 1
  ext xz
  constructor
  · rintro ⟨z, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Pi.single j.1 (1 : ℝ), ⟨j, rfl⟩, rfl⟩

/-- Helper for Exercise 3.33: `octahedron_extension n` is the convex hull of its graph vertices. -/
theorem octahedron_extension_eq_convexHull_graph_vertices {n : ℕ} :
    octahedron_extension n =
      convexHull ℝ (Set.range (octahedron_extension_graphVertex n)) := by
  -- Replace the simplex by the convex hull of its basis vertices, then push forward through the
  -- graph linear map.
  rw [octahedron_extension_eq_graph_image_stdSimplex]
  rw [← convexHull_rangle_single_eq_stdSimplex (R := ℝ) (ι := Fin (n + n))]
  rw [LinearMap.image_convexHull]
  congr 1
  ext p
  constructor
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Pi.single i (1 : ℝ), ⟨i, rfl⟩, rfl⟩

/-- Helper for Exercise 3.33: the graph vertices inherit affine independence from the simplex
basis vertices. -/
theorem octahedron_extension_graph_vertices_affineIndependent {n : ℕ} [NeZero n] :
    AffineIndependent ℝ (octahedron_extension_graphVertex n) := by
  -- The standard basis vectors are linearly independent, and the injective graph map preserves
  -- affine independence.
  simpa [octahedron_extension_graphVertex] using
    ((Pi.linearIndependent_single_one (Fin (n + n)) ℝ).affineIndependent).map'
      (octahedron_extension_graphLinearMap n).toAffineMap
      (octahedron_extension_graphLinearMap_injective n)

/-- Helper for Exercise 3.33: omitting one graph vertex preserves affine independence. -/
theorem octahedron_extension_omitted_graph_vertices_affineIndependent {n : ℕ}
    [NeZero n] (i : Fin (n + n)) :
    AffineIndependent ℝ
      (fun j : {j : Fin (n + n) // j ≠ i} ↦ octahedron_extension_graphVertex n j.1) := by
  -- This is the omitted-coordinate subfamily of the already affine-independent graph vertices.
  simpa using
    (octahedron_extension_graph_vertices_affineIndependent (n := n)).subtype
      {j : Fin (n + n) | j ≠ i}

/-- Helper for Exercise 3.33: every lifted coordinate of a feasible extension point is nonnegative.
-/
theorem octahedron_extension_coordinate_nonneg {n : ℕ} (i : Fin (n + n))
    {xz : (Fin n → ℝ) × (Fin (n + n) → ℝ)} (hxz : xz ∈ octahedron_extension n) :
    0 ≤ xz.2 i := by
  rcases xz with ⟨x, z⟩
  rw [mem_octahedron_extension_iff] at hxz
  rcases hxz with ⟨hx, hsum, hz_pos, hz_neg⟩
  cases h : finSumFinEquiv.symm i with
  | inl j =>
      have hi : i = Fin.castAdd n j := by
        simpa [h] using (finSumFinEquiv.apply_symm_apply i).symm
      rw [hi]
      simpa [octahedron_extension_pos] using hz_pos j
  | inr j =>
      have hi : i = Fin.natAdd n j := by
        simpa [h] using (finSumFinEquiv.apply_symm_apply i).symm
      rw [hi]
      simpa [octahedron_extension_neg] using hz_neg j

/-- Helper for Exercise 3.33: the affine span of the graph vertices has dimension `2n - 1`. -/
theorem octahedron_extension_graph_vertices_finrank {n : ℕ} (hn : 0 < n) :
    Module.finrank ℝ
      (vectorSpan ℝ (Set.range (octahedron_extension_graphVertex n))) = n + n - 1 := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have h_aff : AffineIndependent ℝ (octahedron_extension_graphVertex n) :=
    octahedron_extension_graph_vertices_affineIndependent (n := n)
  -- Affine independence of `2n` graph vertices gives a `(2n - 1)`-dimensional span.
  have hcard :
      Module.finrank ℝ
          (vectorSpan ℝ (Set.range (octahedron_extension_graphVertex n))) + 1 =
        n + n := by
    simpa using
      (AffineIndependent.finrank_vectorSpan_add_one
        (p := octahedron_extension_graphVertex n) h_aff)
  omega

/-- Part (5) of Exercise 3.33: the lifted polyhedron `octahedron_extension n` has affine dimension
`2n - 1`, measured in the chapter's natural-number `finrank` convention. -/
theorem octahedron_extension_finrank_direction_affineSpan
    {n : ℕ} :
    Module.finrank ℝ (affineSpan ℝ (octahedron_extension n)).direction = n + n - 1 := by
  by_cases hn : n = 0
  · -- In the degenerate case there are no lifted coordinates, so the extension is empty.
    subst hn
    have h_empty : octahedron_extension 0 = ∅ := by
      ext xz
      simp [octahedron_extension]
    rw [h_empty, AffineSubspace.span_empty]
    simp
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    -- The graph-simplex description reduces the affine span to the span of the graph vertices.
    rw [octahedron_extension_eq_convexHull_graph_vertices, affineSpan_convexHull,
      direction_affineSpan]
    exact octahedron_extension_graph_vertices_finrank hpos

/-- Part (6) of Exercise 3.33: for each coordinate `i`, the inequality `z i ≥ 0` cuts out a facet
of the
lifted polyhedron `octahedron_extension n`. -/
theorem octahedron_extension_coordinate_face_isFacetOf
    {n : ℕ} (i : Fin (n + n)) :
    IsFacetOf (octahedron_extension n) (octahedron_extension_coordinate_face n i) := by
  have hn_ne : n ≠ 0 := by
    intro hn
    subst hn
    exact Nat.not_lt_zero _ i.isLt
  letI : NeZero n := ⟨hn_ne⟩
  have h_nonempty : (octahedron_extension_coordinate_face n i).Nonempty := by
    -- Any graph vertex other than the omitted one lies on the coordinate face `z i = 0`.
    rcases octahedron_extension_exists_other_index (n := n) i with ⟨j, hj⟩
    exact ⟨octahedron_extension_graphVertex n j,
      octahedron_extension_graphVertex_mem_coordinate_face (n := n) i ⟨j, hj⟩⟩
  rcases octahedron_extension_exists_other_index (n := n) i with ⟨j, hj⟩
  letI : Nonempty {j : Fin (n + n) // j ≠ i} := ⟨⟨j, hj⟩⟩
  let l :
      StrongDual ℝ ((Fin n → ℝ) × (Fin (n + n) → ℝ)) :=
    -((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin (n + n) → ℝ)))
  have h_exposed_eq :
      octahedron_extension_coordinate_face n i = l.toExposed (octahedron_extension n) := by
    ext xz
    constructor
    · intro hx
      rw [mem_octahedron_extension_coordinate_face_iff] at hx
      refine ⟨hx.1, ?_⟩
      intro yz hyz
      have hy_nonneg : 0 ≤ yz.2 i := octahedron_extension_coordinate_nonneg (n := n) i hyz
      simp [l, hx.2, hy_nonneg]
    · intro hx
      obtain ⟨yz, hyz⟩ := h_nonempty
      rw [mem_octahedron_extension_coordinate_face_iff] at hyz
      have hy_le : l yz ≤ l xz := hx.2 yz hyz.1
      have hx_nonneg : 0 ≤ xz.2 i := octahedron_extension_coordinate_nonneg (n := n) i hx.1
      have hl_nonneg : 0 ≤ l xz := by
        simpa [l, hyz.2] using hy_le
      have hl_nonpos : l xz ≤ 0 := by
        simpa [l] using neg_nonpos.mpr hx_nonneg
      have hl_eq : l xz = 0 := le_antisymm hl_nonpos hl_nonneg
      have hcoord : xz.2 i = 0 := by
        simp [l] at hl_eq
        linarith
      exact (mem_octahedron_extension_coordinate_face_iff).2 ⟨hx.1, hcoord⟩
  have h_exposed :
      IsExposed ℝ (octahedron_extension n) (octahedron_extension_coordinate_face n i) := by
    rw [h_exposed_eq]
    exact ContinuousLinearMap.toExposed.isExposed
  have h_face_dim :
      Module.finrank ℝ
          (affineSpan ℝ (octahedron_extension_coordinate_face n i)).direction =
        n + n - 2 := by
    -- The coordinate face is the convex hull of the omitted graph vertices, which still form an
    -- affine-independent family of size `2n - 1`.
    rw [octahedron_extension_coordinate_face_eq_convexHull_omitted_graph_vertices,
      affineSpan_convexHull, direction_affineSpan]
    have hcard :
        Module.finrank ℝ
            (vectorSpan ℝ
              (Set.range (fun j : {j : Fin (n + n) // j ≠ i} ↦
                octahedron_extension_graphVertex n j.1))) + 1 =
          n + n - 1 := by
      simpa using
        (AffineIndependent.finrank_vectorSpan_add_one
          (p := fun j : {j : Fin (n + n) // j ≠ i} ↦ octahedron_extension_graphVertex n j.1)
          (octahedron_extension_omitted_graph_vertices_affineIndependent (n := n) i))
    omega
  rw [isFacetOf_iff]
  refine ⟨h_nonempty, h_exposed, ?_⟩
  have hdim := octahedron_extension_finrank_direction_affineSpan (n := n)
  omega

/-- Helper for Exercise 3.33: the injective graph map preserves affine-span dimension on image
sets. -/
theorem octahedron_extension_graph_image_finrank_direction_affineSpan
    {n : ℕ} {s : Set (Fin (n + n) → ℝ)} :
    Module.finrank ℝ
        (affineSpan ℝ (octahedron_extension_graphLinearMap n '' s)).direction =
      Module.finrank ℝ (affineSpan ℝ s).direction := by
  let G := octahedron_extension_graphLinearMap n
  let Gaff : (Fin (n + n) → ℝ) →ᵃ[ℝ] ((Fin n → ℝ) × (Fin (n + n) → ℝ)) := G.toAffineMap
  have hmap :
      affineSpan ℝ (G '' s) = AffineSubspace.map Gaff (affineSpan ℝ s) := by
    symm
    simpa [G, Gaff] using (AffineSubspace.map_span Gaff s)
  rw [hmap, AffineSubspace.map_direction]
  let e :
      (affineSpan ℝ s).direction ≃ₗ[ℝ]
        Submodule.map G (affineSpan ℝ s).direction :=
    Submodule.equivMapOfInjective G (octahedron_extension_graphLinearMap_injective n)
      (affineSpan ℝ s).direction
  simpa [e] using (LinearEquiv.finrank_eq e).symm

/-- Exercise 3.33 (7): every facet of `octahedron_extension n` is one of the coordinate faces
defined by an inequality `z i ≥ 0`. -/
theorem octahedron_extension_facets_eq_coordinate_faces
    {n : ℕ} :
    {F : Set ((Fin n → ℝ) × (Fin (n + n) → ℝ)) | IsFacetOf (octahedron_extension n) F} =
      Set.range (fun i : Fin (n + n) ↦ octahedron_extension_coordinate_face n i) := by
  classical
  by_cases hn : n = 0
  · subst hn
    have h_empty : octahedron_extension 0 = ∅ := by
      ext xz
      simp [octahedron_extension]
    ext F
    constructor
    · intro hF
      have hF' := isFacetOf_iff.mp hF
      have hsubset : F ⊆ octahedron_extension 0 := hF'.2.1.subset
      rcases hF'.1 with ⟨xz, hxz⟩
      have hxz_ext : xz ∈ octahedron_extension 0 := hsubset hxz
      exfalso
      simp [h_empty] at hxz_ext
    · intro hF
      rcases hF with ⟨i, _⟩
      exact Fin.elim0 i
  · ext F
    constructor
    · intro hF
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hF' := isFacetOf_iff.mp hF
      obtain ⟨l, hF_eq⟩ := hF'.2.1 hF'.1
      let G := octahedron_extension_graphLinearMap n
      let Fz : Set (Fin (n + n) → ℝ) :=
        {z | z ∈ stdSimplex ℝ (Fin (n + n)) ∧
          ∀ w ∈ stdSimplex ℝ (Fin (n + n)), l (G w) ≤ l (G z)}
      have hF_image : F = G '' Fz := by
        ext xz
        constructor
        · intro hxz
          rw [hF_eq] at hxz
          rw [octahedron_extension_eq_graph_image_stdSimplex] at hxz
          rcases hxz.1 with ⟨z, hz, rfl⟩
          refine ⟨z, ?_, rfl⟩
          refine ⟨hz, ?_⟩
          intro w hw
          have hGw : G w ∈ G '' stdSimplex ℝ (Fin (n + n)) := by
            exact ⟨w, hw, rfl⟩
          exact hxz.2 (G w) hGw
        · rintro ⟨z, hz, rfl⟩
          rw [hF_eq]
          refine ⟨?_, ?_⟩
          · rw [octahedron_extension_eq_graph_image_stdSimplex]
            exact ⟨z, hz.1, rfl⟩
          · intro yz hyz
            rw [octahedron_extension_eq_graph_image_stdSimplex] at hyz
            rcases hyz with ⟨w, hw, rfl⟩
            exact hz.2 w hw
      have hFz_nonempty : Fz.Nonempty := by
        rcases hF'.1 with ⟨xz, hxz⟩
        rw [hF_image] at hxz
        rcases hxz with ⟨z, hz, rfl⟩
        exact ⟨z, hz⟩
      let Gclm : (Fin (n + n) → ℝ) →L[ℝ] ((Fin n → ℝ) × (Fin (n + n) → ℝ)) :=
        G.toContinuousLinearMap
      have hFz_exposed :
          IsExposed ℝ (stdSimplex ℝ (Fin (n + n))) Fz := by
        change IsExposed ℝ (stdSimplex ℝ (Fin (n + n)))
          ((l.comp Gclm).toExposed (stdSimplex ℝ (Fin (n + n))))
        exact ContinuousLinearMap.toExposed.isExposed
      have hFz_dim :
          Module.finrank ℝ (affineSpan ℝ Fz).direction + 1 =
            Module.finrank ℝ (affineSpan ℝ (stdSimplex ℝ (Fin (n + n)))).direction := by
        have hdim := hF'.2.2
        rw [hF_image, octahedron_extension_eq_graph_image_stdSimplex,
          octahedron_extension_graph_image_finrank_direction_affineSpan (n := n) (s := Fz),
          octahedron_extension_graph_image_finrank_direction_affineSpan (n := n)
            (s := stdSimplex ℝ (Fin (n + n)))] at hdim
        exact hdim
      have hFz_facet :
          IsFacetOf (stdSimplex ℝ (Fin (n + n))) Fz := by
        exact ⟨hFz_nonempty, hFz_exposed, hFz_dim⟩
      have hnn : 0 < n + n := by omega
      rcases stdSimplexFacet_eq_coordinateFace (m := n + n) hnn hFz_facet with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      symm
      calc
        F = G '' Fz := hF_image
        _ = G '' {z : Fin (n + n) → ℝ | z ∈ stdSimplex ℝ (Fin (n + n)) ∧ z i = 0} := by
              rw [hi]
        _ = octahedron_extension_coordinate_face n i := by
              simpa [G] using
                (octahedron_extension_coordinate_face_eq_graph_image_coordinate_face
                  (n := n) i).symm
    · rintro ⟨i, rfl⟩
      exact octahedron_extension_coordinate_face_isFacetOf (n := n) i

/-- Part (8) of Exercise 3.33: `octahedron_extension n` has exactly `2n` facets. -/
theorem octahedron_extension_facets_ncard
    {n : ℕ} :
    {F : Set ((Fin n → ℝ) × (Fin (n + n) → ℝ)) | IsFacetOf (octahedron_extension n) F}.ncard =
      n + n := by
  rw [octahedron_extension_facets_eq_coordinate_faces]
  simpa using Set.ncard_range_of_injective (f := fun i : Fin (n + n) ↦
    octahedron_extension_coordinate_face n i) <| by
      intro i j hij
      by_contra hne
      have hmem :
          octahedron_extension_graphVertex n i ∈ octahedron_extension_coordinate_face n j := by
        exact octahedron_extension_graphVertex_mem_coordinate_face (n := n) j ⟨i, hne⟩
      have hnot_mem :
          octahedron_extension_graphVertex n i ∉ octahedron_extension_coordinate_face n i := by
        intro hi
        rw [mem_octahedron_extension_coordinate_face_iff] at hi
        have hcoord : (octahedron_extension_graphVertex n i).2 i = 0 := hi.2
        simp [octahedron_extension_graphVertex, octahedron_extension_graphLinearMap] at hcoord
      have hmem_self :
          octahedron_extension_graphVertex n i ∈ octahedron_extension_coordinate_face n i := by
        simpa [hij] using hmem
      exact hnot_mem hmem_self
