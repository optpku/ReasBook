/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_claim_5_4_1_extra_1

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

-- Domain sampling note:
-- * core/canonical convex-geometry owner for vertices: `Set.extremePoints ℝ`
-- * chapter graph-polytope coordinate style: finite edge-coordinate spaces `E → ℝ`
-- This file keeps the source-facing rim/spoke coordinate model for `W_n`, but the vertex-counting
-- statements are refined to the canonical owner surface `Set.extremePoints ℝ`.

section Exercise73

/-- The edge index set for the wheel `W_n`, with `Sum.inl i` representing the rim edge
`v_(i+1) v_(i+2)` and `Sum.inr i` representing the spoke `v_0 v_(i+1)`, both cyclically modulo
`n`. -/
abbrev wheel_edge (n : ℕ) := Fin n ⊕ Fin n

/-- The edge-coordinate space of `W_n`, viewed as `ℝ^(2n)` with separate coordinates for rim and
spoke edges. -/
abbrev wheel_edge_coords (n : ℕ) := wheel_edge n → ℝ

/-- The rim edge of `W_n` indexed by `i`. -/
def wheel_rim_edge {n : ℕ} (i : Fin n) : wheel_edge n :=
  Sum.inl i

/-- The spoke edge of `W_n` indexed by `i`. -/
def wheel_spoke_edge {n : ℕ} (i : Fin n) : wheel_edge n :=
  Sum.inr i

/-- The cyclic successor of an index on the rim of `W_n`. -/
def wheel_next {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ (lt_of_lt_of_le (Nat.succ_pos _) (Nat.succ_le_of_lt i.is_lt))⟩

/-- The Hamiltonian-cycle incidence vector obtained by deleting the rim edge indexed by `missing`
and replacing it by the two spokes to its endpoints. -/
def wheel_hamiltonian_cycle_vector (n : ℕ) (missing : Fin n) : wheel_edge_coords n :=
  fun e ↦
    match e with
    | Sum.inl i => if i = missing then 0 else 1
    | Sum.inr i => if i = missing ∨ i = wheel_next missing then 1 else 0

/-- On rim coordinates, `wheel_hamiltonian_cycle_vector n missing` is `0` exactly at the deleted
rim edge and `1` on the remaining rim edges. -/
theorem wheel_hamiltonian_cycle_vector_apply_rim
    {n : ℕ} (missing i : Fin n) :
    wheel_hamiltonian_cycle_vector n missing (wheel_rim_edge i) =
      if i = missing then 0 else 1 := by
  simp [wheel_hamiltonian_cycle_vector, wheel_rim_edge]

/-- On spoke coordinates, `wheel_hamiltonian_cycle_vector n missing` is `1` exactly on the two
spokes incident to the deleted rim edge and `0` on all other spokes. -/
theorem wheel_hamiltonian_cycle_vector_apply_spoke
    {n : ℕ} (missing i : Fin n) :
    wheel_hamiltonian_cycle_vector n missing (wheel_spoke_edge i) =
      if i = missing ∨ i = wheel_next missing then 1 else 0 := by
  simp [wheel_hamiltonian_cycle_vector, wheel_spoke_edge]

/-- The set of Hamiltonian-cycle incidence vectors of the wheel `W_n`, indexed by the deleted rim
edge. -/
def wheel_hamiltonian_cycle_vectors (n : ℕ) : Set (wheel_edge_coords n) :=
  Set.range (wheel_hamiltonian_cycle_vector n)

/-- Membership in `wheel_hamiltonian_cycle_vectors n` means that the point is the incidence vector
of the Hamiltonian cycle obtained by deleting one rim edge of `W_n`. -/
theorem mem_wheel_hamiltonian_cycle_vectors_iff
    {n : ℕ} {x : wheel_edge_coords n} :
    x ∈ wheel_hamiltonian_cycle_vectors n ↔
      ∃ missing : Fin n, x = wheel_hamiltonian_cycle_vector n missing := by
  constructor
  · rintro ⟨missing, rfl⟩
    exact ⟨missing, rfl⟩
  · rintro ⟨missing, rfl⟩
    exact ⟨missing, rfl⟩

/-- Each deleted-rim-edge Hamiltonian cycle vector belongs to `wheel_hamiltonian_cycle_vectors n`.
-/
theorem wheel_hamiltonian_cycle_vector_mem_cycle_vectors
    (n : ℕ) (missing : Fin n) :
    wheel_hamiltonian_cycle_vector n missing ∈ wheel_hamiltonian_cycle_vectors n :=
  Set.mem_range_self missing

/-- Distinct deleted rim edges of `W_n` yield distinct Hamiltonian-cycle incidence vectors. -/
theorem wheel_hamiltonian_cycle_vector_injective
    (n : ℕ) :
    Function.Injective (wheel_hamiltonian_cycle_vector n) := by
  intro missing₁ missing₂ h
  by_contra hne
  have hEval :
      wheel_hamiltonian_cycle_vector n missing₁ (wheel_rim_edge missing₁) =
        wheel_hamiltonian_cycle_vector n missing₂ (wheel_rim_edge missing₁) :=
    congrArg (fun x ↦ x (wheel_rim_edge missing₁)) h
  simp [wheel_hamiltonian_cycle_vector_apply_rim, hne] at hEval

/-- The deleted-rim-edge indexing family provides exactly `n` Hamiltonian-cycle incidence vectors.
-/
theorem wheel_hamiltonian_cycle_vectors_ncard
    (n : ℕ) :
    (wheel_hamiltonian_cycle_vectors n).ncard = n := by
  simpa [wheel_hamiltonian_cycle_vectors] using
    Set.ncard_range_of_injective (wheel_hamiltonian_cycle_vector_injective n)

/-- `Hamilton(W_n)`, defined as the convex hull of the `0,1` incidence vectors of the Hamiltonian
cycles of the wheel `W_n`. -/
def wheel_hamiltonian_polytope (n : ℕ) : Set (wheel_edge_coords n) :=
  convexHull ℝ (wheel_hamiltonian_cycle_vectors n)

/-- `wheel_hamiltonian_polytope n` unfolds to the convex hull of the Hamiltonian-cycle incidence
vectors of `W_n`. -/
theorem wheel_hamiltonian_polytope_eq_convexHull
    (n : ℕ) :
    wheel_hamiltonian_polytope n =
      convexHull ℝ (wheel_hamiltonian_cycle_vectors n) := rfl

/-- Each Hamiltonian-cycle incidence vector of `W_n` lies in `Hamilton(W_n)`. -/
theorem wheel_hamiltonian_cycle_vector_mem_polytope
    (n : ℕ) (missing : Fin n) :
    wheel_hamiltonian_cycle_vector n missing ∈ wheel_hamiltonian_polytope n :=
  subset_convexHull ℝ (wheel_hamiltonian_cycle_vectors n)
    (wheel_hamiltonian_cycle_vector_mem_cycle_vectors n missing)

/-- Helper for Exercise 7.3: the cyclic successor on `Fin n` is injective when `n` is positive. -/
lemma wheel_next_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective (wheel_next (n := n)) := by
  haveI : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  intro i j hij
  -- Rewrite `wheel_next` as addition by `1` in `Fin n` and cancel the common summand.
  have hij' : i + 1 = j + 1 := by
    simpa [wheel_next, Fin.add_def] using hij
  exact add_right_cancel hij'

/-- Helper for Exercise 7.3: when `n ≥ 2`, the cyclic successor never fixes a rim index. -/
lemma wheel_next_ne_self
    {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    wheel_next i ≠ i := by
  intro hi
  -- Comparing values shows `(i + 1) % n = i`, impossible when `n ≥ 2`.
  have hval : (i.1 + 1) % n = i.1 := by
    simpa [wheel_next] using congrArg Fin.val hi
  have hi_lt : i.1 < n := i.is_lt
  by_cases hlt : i.1 + 1 < n
  · have hmod : (i.1 + 1) % n = i.1 + 1 := Nat.mod_eq_of_lt hlt
    omega
  · have hge : n ≤ i.1 + 1 := le_of_not_gt hlt
    have hle : i.1 + 1 ≤ n := Nat.succ_le_of_lt hi_lt
    have hs : i.1 + 1 = n := le_antisymm hle hge
    have hmod : (i.1 + 1) % n = 0 := by
      have hpos : 0 < n := by omega
      simp [hs]
    rw [hmod] at hval
    omega

/-- Helper for Exercise 7.3: the Hamiltonian-cycle incidence vectors lie in the ambient unit box.
-/
lemma wheel_hamiltonian_cycle_vectors_subset_unitBox
    (n : ℕ) :
    wheel_hamiltonian_cycle_vectors n ⊆
      Set.univ.pi (fun _ : wheel_edge n ↦ Set.Icc (0 : ℝ) 1) := by
  intro x hx
  rcases mem_wheel_hamiltonian_cycle_vectors_iff.mp hx with ⟨missing, rfl⟩
  rw [Set.mem_univ_pi]
  intro e
  cases e with
  | inl i =>
      -- Rim coordinates are exactly `0` or `1`.
      by_cases h : i = missing
      · subst h
        simp [wheel_hamiltonian_cycle_vector]
      · simp [wheel_hamiltonian_cycle_vector, h]
  | inr i =>
      -- Spoke coordinates are exactly `0` or `1`.
      by_cases h : i = missing ∨ i = wheel_next missing
      · simp [wheel_hamiltonian_cycle_vector, h]
      · simp [wheel_hamiltonian_cycle_vector, h]

/-- Helper for Exercise 7.3: the wheel Hamiltonian polytope stays inside the ambient unit box. -/
lemma wheel_hamiltonian_polytope_subset_unitBox
    (n : ℕ) :
    wheel_hamiltonian_polytope n ⊆
      Set.univ.pi (fun _ : wheel_edge n ↦ Set.Icc (0 : ℝ) 1) := by
  -- Place the generators in the unit box and use convex-hull minimality.
  rw [wheel_hamiltonian_polytope_eq_convexHull]
  refine convexHull_min (wheel_hamiltonian_cycle_vectors_subset_unitBox n) ?_
  exact convex_pi fun _ _ ↦ convex_Icc (0 : ℝ) 1

/-- Helper for Exercise 7.3: the extreme points of the ambient unit box are exactly the `0/1`
edge-coordinate vectors. -/
lemma wheel_unitBox_extremePoints_eq_zeroOne
    (n : ℕ) :
    (Set.univ.pi (fun _ : wheel_edge n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ =
      {x : wheel_edge_coords n | ∀ e, x e = 0 ∨ x e = 1} := by
  -- Compute extreme points coordinatewise and simplify each interval to `{0, 1}`.
  rw [extremePoints_pi]
  ext x
  simp [Set.extremePoints_Icc, zero_le_one]

/-- The vertices of `Hamilton(W_n)` are exactly the Hamiltonian-cycle incidence vectors obtained
by deleting one rim edge. This is the source-facing bridge from the generating family to the
canonical vertex owner `Set.extremePoints ℝ`. -/
theorem wheel_hamiltonian_polytope_extremePoints_eq_cycle_vectors
    (n : ℕ) :
    (wheel_hamiltonian_polytope n).extremePoints ℝ =
      wheel_hamiltonian_cycle_vectors n := by
  refine Set.Subset.antisymm ?_ ?_
  · -- Extreme points of a convex hull come from the generating set.
    exact extremePoints_convexHull_subset
  · intro x hx
    have hxHull : x ∈ wheel_hamiltonian_polytope n :=
      subset_convexHull ℝ (wheel_hamiltonian_cycle_vectors n) hx
    have hxBoxExtreme :
        x ∈ (Set.univ.pi (fun _ : wheel_edge n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ := by
      rcases mem_wheel_hamiltonian_cycle_vectors_iff.mp hx with ⟨missing, rfl⟩
      rw [wheel_unitBox_extremePoints_eq_zeroOne]
      intro e
      cases e with
      | inl i =>
          -- Each rim coordinate is one of the two box vertices.
          by_cases h : i = missing
          · subst h
            simp [wheel_hamiltonian_cycle_vector]
          · simp [wheel_hamiltonian_cycle_vector, h]
      | inr i =>
          -- Each spoke coordinate is also one of the two box vertices.
          by_cases h : i = missing ∨ i = wheel_next missing
          · simp [wheel_hamiltonian_cycle_vector, h]
          · simp [wheel_hamiltonian_cycle_vector, h]
    -- Transfer extremality from the unit box to the smaller convex hull.
    exact
      inter_extremePoints_subset_extremePoints_of_subset
        (wheel_hamiltonian_polytope_subset_unitBox n) ⟨hxHull, hxBoxExtreme⟩

/-- A point is a vertex of `Hamilton(W_n)` exactly when it is the incidence vector of the
Hamiltonian cycle obtained by deleting one rim edge. -/
theorem mem_wheel_hamiltonian_polytope_extremePoints_iff
    {n : ℕ} {x : wheel_edge_coords n} :
    x ∈ (wheel_hamiltonian_polytope n).extremePoints ℝ ↔
      ∃ missing : Fin n, x = wheel_hamiltonian_cycle_vector n missing := by
  rw [wheel_hamiltonian_polytope_extremePoints_eq_cycle_vectors]
  exact mem_wheel_hamiltonian_cycle_vectors_iff

/-- The equality face of `Hamilton(W_n)` cut out by the rim-edge upper bound
`x_(v_(i+1) v_(i+2)) ≤ 1`. -/
def wheel_rim_upper_face (n : ℕ) (i : Fin n) : Set (wheel_edge_coords n) :=
  {x | x ∈ wheel_hamiltonian_polytope n ∧ x (wheel_rim_edge i) = 1}

/-- Membership in `wheel_rim_upper_face n i` means lying in `Hamilton(W_n)` and meeting the
rim-edge upper bound at equality. -/
theorem mem_wheel_rim_upper_face_iff
    {n : ℕ} (i : Fin n) {x : wheel_edge_coords n} :
    x ∈ wheel_rim_upper_face n i ↔
      x ∈ wheel_hamiltonian_polytope n ∧ x (wheel_rim_edge i) = 1 := Iff.rfl

/-- The linear system consisting of the rim-edge sum equation, the spoke reconstruction
equalities, and the rim-edge upper bounds that yields the minimal description of `Hamilton(W_n)`.
-/
def wheel_hamiltonian_constraint_set (n : ℕ) : Set (wheel_edge_coords n) :=
  {x |
    (∑ i : Fin n, x (wheel_rim_edge i)) = (n - 1 : ℝ) ∧
      (∀ i : Fin n,
        x (wheel_spoke_edge (wheel_next i)) =
          (2 : ℝ) - x (wheel_rim_edge i) - x (wheel_rim_edge (wheel_next i))) ∧
      (∀ i : Fin n, x (wheel_rim_edge i) ≤ 1)}

/-- Membership in `wheel_hamiltonian_constraint_set n` means satisfying the rim-edge sum
equation, the spoke reconstruction equalities, and the rim-edge upper bounds. -/
theorem mem_wheel_hamiltonian_constraint_set_iff
    {n : ℕ} {x : wheel_edge_coords n} :
    x ∈ wheel_hamiltonian_constraint_set n ↔
      (∑ i : Fin n, x (wheel_rim_edge i)) = (n - 1 : ℝ) ∧
        (∀ i : Fin n,
          x (wheel_spoke_edge (wheel_next i)) =
            (2 : ℝ) - x (wheel_rim_edge i) - x (wheel_rim_edge (wheel_next i))) ∧
        (∀ i : Fin n, x (wheel_rim_edge i) ≤ 1) := Iff.rfl

/-- Helper for Exercise 7.3: relative to the deleted edge `0`, the nonzero rim coordinates of the
tail difference family are the negated standard basis vectors. -/
lemma wheelHamiltonianCycleVectorTailSub_applyRim
    (n : ℕ) (j k : Fin n) :
    (wheel_hamiltonian_cycle_vector (n + 1) j.succ - wheel_hamiltonian_cycle_vector (n + 1) 0)
        (wheel_rim_edge k.succ) =
      if k = j then (-1 : ℝ) else 0 := by
  -- Evaluate both Hamiltonian-cycle vectors on the same nonzero rim coordinate.
  by_cases hkj : k = j
  · subst hkj
    norm_num [Pi.sub_apply, wheel_hamiltonian_cycle_vector_apply_rim]
  · norm_num [Pi.sub_apply, wheel_hamiltonian_cycle_vector_apply_rim, hkj]

/-- Helper for Exercise 7.3: the spoke coordinate opposite `i` is recovered from the two adjacent
rim coordinates in the canonical constraint-set normal form. -/
lemma wheelHamiltonianCycleVector_spokeReconstruction
    (n : ℕ) (hn : 3 ≤ n) (missing i : Fin n) :
    wheel_hamiltonian_cycle_vector n missing (wheel_spoke_edge (wheel_next i)) =
      (2 : ℝ) - wheel_hamiltonian_cycle_vector n missing (wheel_rim_edge i) -
        wheel_hamiltonian_cycle_vector n missing (wheel_rim_edge (wheel_next i)) := by
  have hpos : 0 < n := by omega
  have htwo : 2 ≤ n := by omega
  have hnext_injective : Function.Injective (wheel_next (n := n)) :=
    wheel_next_injective hpos
  -- Split on whether the deleted rim edge is the left endpoint of the spoke under study.
  by_cases him : i = missing
  · subst missing
    have hnext_ne : wheel_next i ≠ i :=
      wheel_next_ne_self htwo i
    -- At the deleted rim edge, exactly the two incident spokes survive.
    norm_num [wheel_hamiltonian_cycle_vector_apply_spoke,
      wheel_hamiltonian_cycle_vector_apply_rim, hnext_ne]
  · -- Otherwise the spoke is present exactly when the deleted edge is the predecessor of `i`.
    by_cases hprev : wheel_next i = missing
    · norm_num [wheel_hamiltonian_cycle_vector_apply_spoke,
        wheel_hamiltonian_cycle_vector_apply_rim, him, hprev]
    · have hnext_ne : wheel_next i ≠ wheel_next missing := by
        intro hEq
        exact him (hnext_injective hEq)
      norm_num [wheel_hamiltonian_cycle_vector_apply_spoke,
        wheel_hamiltonian_cycle_vector_apply_rim, him, hprev, hnext_ne]

/-- Helper for Exercise 7.3: projecting the tail-difference family to the nonzero rim
coordinates identifies it with the negated standard basis, hence the tail family is linearly
independent. -/
lemma wheelHamiltonianCycleVectorTail_linearIndependent
    (n : ℕ) :
    LinearIndependent ℝ
      (fun j : Fin n ↦
        wheel_hamiltonian_cycle_vector (n + 1) j.succ -
          wheel_hamiltonian_cycle_vector (n + 1) 0) := by
  let projNonzeroRim : wheel_edge_coords (n + 1) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi fun k : Fin n => LinearMap.proj (wheel_rim_edge k.succ)
  have hproj :
      (projNonzeroRim ∘
        fun j : Fin n ↦
          wheel_hamiltonian_cycle_vector (n + 1) j.succ -
            wheel_hamiltonian_cycle_vector (n + 1) 0) =
        fun j : Fin n ↦ Pi.single j (-1 : ℝ) := by
    -- Evaluate the projection coordinatewise and use the tail rim formula.
    funext j
    ext k
    simpa [projNonzeroRim, LinearMap.proj_apply, Pi.single_apply] using
      wheelHamiltonianCycleVectorTailSub_applyRim n j k
  have himage :
      LinearIndependent ℝ
        (projNonzeroRim ∘
          fun j : Fin n ↦
            wheel_hamiltonian_cycle_vector (n + 1) j.succ -
              wheel_hamiltonian_cycle_vector (n + 1) 0) := by
    -- The projected family is the signed standard basis of `Fin n → ℝ`.
    rw [hproj]
    exact Pi.linearIndependent_single_of_ne_zero
      (v := fun _ : Fin n => (-1 : ℝ)) fun _ ↦ by norm_num
  -- Pull linear independence back along the projection map.
  exact LinearIndependent.of_comp projNonzeroRim himage

/-- Helper for Exercise 7.3: deleting one rim edge produces an affinely independent family of
wheel Hamiltonian-cycle incidence vectors. -/
lemma wheelHamiltonianCycleVector_affineIndependent
    (n : ℕ) :
    AffineIndependent ℝ (wheel_hamiltonian_cycle_vector n) := by
  cases n with
  | zero =>
      -- The empty indexing family is automatically affinely independent.
      simpa using affineIndependent_of_subsingleton ℝ (wheel_hamiltonian_cycle_vector 0)
  | succ q =>
      -- Route correction: reuse the Chapter 3 tail theorem instead of normalizing `vsub`s
      -- directly inside the affine-independence proof.
      rw [affineIndependent_iff_linearIndependent_tail_sub]
      exact wheelHamiltonianCycleVectorTail_linearIndependent q

/-- Helper for Exercise 7.3: the rim upper face is exactly the convex hull of the cycle vectors
whose deleted rim edge is not `i`. -/
lemma wheelRimUpperFace_eq_convexHull_omittedCycleVectors
    (n : ℕ) (i : Fin n) :
    wheel_rim_upper_face n i =
      convexHull ℝ
        (Set.range (fun j : {j : Fin n // j ≠ i} ↦ wheel_hamiltonian_cycle_vector n j.1)) := by
  have hgenerators_le :
      wheel_hamiltonian_cycle_vectors n ⊆
        ((LinearMap.proj (wheel_rim_edge i) :
          wheel_edge_coords n →ₗ[ℝ] ℝ)) ⁻¹' Set.Iic (1 : ℝ) := by
    intro x hx
    rcases mem_wheel_hamiltonian_cycle_vectors_iff.mp hx with ⟨missing, rfl⟩
    -- Every Hamiltonian-cycle generator has rim coordinates in `{0, 1}`.
    by_cases hmi : i = missing
    · subst hmi
      simp [wheel_hamiltonian_cycle_vector_apply_rim]
    · simp [wheel_hamiltonian_cycle_vector_apply_rim, hmi]
  calc
    wheel_rim_upper_face n i
        = convexHull ℝ (wheel_hamiltonian_cycle_vectors n) ∩
            ((LinearMap.proj (wheel_rim_edge i) :
              wheel_edge_coords n →ₗ[ℝ] ℝ)) ⁻¹' ({1} : Set ℝ) := by
              -- Rewrite the face as the equality slice of the rim-coordinate projection.
              ext x
              simp [wheel_rim_upper_face, wheel_hamiltonian_polytope_eq_convexHull]
    _ = convexHull ℝ
          (wheel_hamiltonian_cycle_vectors n ∩
            ((LinearMap.proj (wheel_rim_edge i) :
              wheel_edge_coords n →ₗ[ℝ] ℝ)) ⁻¹' ({1} : Set ℝ)) := by
              exact convexHull_inter_hyperplane_eq
                (wheel_hamiltonian_cycle_vectors n)
                (LinearMap.proj (wheel_rim_edge i) : wheel_edge_coords n →ₗ[ℝ] ℝ) 1
                hgenerators_le
    _ = convexHull ℝ
          (Set.range (fun j : {j : Fin n // j ≠ i} ↦ wheel_hamiltonian_cycle_vector n j.1)) := by
            -- The boundary generators are exactly the cycles omitting a different rim edge.
            congr 1
            ext x
            constructor
            · intro hx
              rcases hx with ⟨hxCycle, hxEq⟩
              rcases mem_wheel_hamiltonian_cycle_vectors_iff.mp hxCycle with ⟨missing, rfl⟩
              have hmissing_ne : missing ≠ i := by
                intro hmi
                subst hmi
                simp [wheel_hamiltonian_cycle_vector_apply_rim] at hxEq
              exact ⟨⟨missing, hmissing_ne⟩, rfl⟩
            · rintro ⟨j, rfl⟩
              refine ⟨wheel_hamiltonian_cycle_vector_mem_cycle_vectors n j.1, ?_⟩
              have hji : i ≠ j.1 := by
                intro hij
                exact j.2 hij.symm
              simp [wheel_hamiltonian_cycle_vector_apply_rim, hji]

/-- Helper for Exercise 7.3: the canonical barycentric weights from a feasible wheel point are
nonnegative and sum to `1`. -/
lemma wheelConstraintWeights_sum_one
    {n : ℕ} {x : wheel_edge_coords n}
    (hn : 0 < n) (hx : x ∈ wheel_hamiltonian_constraint_set n) :
    (∀ i : Fin n, 0 ≤ 1 - x (wheel_rim_edge i)) ∧
      (∑ i : Fin n, (1 - x (wheel_rim_edge i))) = 1 := by
  rw [mem_wheel_hamiltonian_constraint_set_iff] at hx
  rcases hx with ⟨hxsum, _, hxbound⟩
  refine ⟨?_, ?_⟩
  · intro i
    -- The upper bound `x_e ≤ 1` gives nonnegative barycentric weights `1 - x_e`.
    linarith [hxbound i]
  · -- The rim-sum equation normalizes the barycentric weights.
    calc
      (∑ i : Fin n, (1 - x (wheel_rim_edge i)))
          = (∑ i : Fin n, (1 : ℝ)) - ∑ i : Fin n, x (wheel_rim_edge i) := by
              rw [Finset.sum_sub_distrib]
      _ = (n : ℝ) - (n - 1 : ℝ) := by simp [hxsum]
      _ = 1 := by
            have hpred : ((n - 1 : ℕ) : ℝ) + 1 = n := by
              exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
            linarith

/-- Helper for Exercise 7.3: the barycentric weights `1 - x_e` reconstruct a feasible point of
the wheel constraint set as a weighted sum of the Hamiltonian-cycle generators. -/
lemma wheelConstraint_weightedCycleSum_eq
    (n : ℕ) (hn : 3 ≤ n) {x : wheel_edge_coords n}
    (hx : x ∈ wheel_hamiltonian_constraint_set n) :
    (∑ i : Fin n, (1 - x (wheel_rim_edge i)) • wheel_hamiltonian_cycle_vector n i) = x := by
  have hpos : 0 < n := by omega
  have htwo : 2 ≤ n := by omega
  have hweights := wheelConstraintWeights_sum_one hpos hx
  rw [mem_wheel_hamiltonian_constraint_set_iff] at hx
  rcases hx with ⟨_, hxspoke, _⟩
  have hnext_injective : Function.Injective (wheel_next (n := n)) :=
    wheel_next_injective hpos
  have hnext_surjective : Function.Surjective (wheel_next (n := n)) :=
    (Finite.injective_iff_surjective (f := wheel_next (n := n))).mp hnext_injective
  ext e
  cases e with
  | inl k =>
      -- On rim coordinates, all barycentric weights contribute except the deleted edge `k`.
      calc
        (∑ i : Fin n, (1 - x (wheel_rim_edge i)) • wheel_hamiltonian_cycle_vector n i)
            (wheel_rim_edge k)
            = ∑ i : Fin n,
                ((1 - x (wheel_rim_edge i)) • wheel_hamiltonian_cycle_vector n i)
                  (wheel_rim_edge k) := by
                    rw [Finset.sum_apply]
        _ = ∑ i : Fin n, (if k = i then 0 else 1 - x (wheel_rim_edge i)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [Pi.smul_apply, wheel_hamiltonian_cycle_vector_apply_rim]
                by_cases hik : k = i
                · simp [hik]
                · simp [hik]
        _ = Finset.sum (Finset.univ.erase k)
              (fun i : Fin n ↦ if k = i then 0 else 1 - x (wheel_rim_edge i)) := by
                symm
                exact
                  (Finset.sum_erase (s := Finset.univ)
                    (f := fun i : Fin n ↦ if k = i then 0 else 1 - x (wheel_rim_edge i))
                    (a := k) (by simp))
        _ = Finset.sum (Finset.univ.erase k) (fun i : Fin n ↦ 1 - x (wheel_rim_edge i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hik : k ≠ i := by
                intro hki
                exact (Finset.mem_erase.mp hi).1 hki.symm
              simp [hik]
        _ = x (wheel_rim_edge k) := by
              have hsplit :
                  Finset.sum (Finset.univ.erase k) (fun i : Fin n ↦ 1 - x (wheel_rim_edge i)) +
                      (1 - x (wheel_rim_edge k)) =
                    ∑ i : Fin n, (1 - x (wheel_rim_edge i)) := by
                simpa using Finset.sum_erase_add
                  (f := fun i : Fin n ↦ 1 - x (wheel_rim_edge i))
                  (s := Finset.univ) (a := k) (Finset.mem_univ k)
              linarith [hsplit, hweights.2]
  | inr j =>
      rcases hnext_surjective j with ⟨i, rfl⟩
      have hnext_ne : i ≠ wheel_next i := by
        intro hi
        exact wheel_next_ne_self htwo i hi.symm
      -- On spoke coordinates, only the two adjacent deleted edges contribute.
      calc
        (∑ missing : Fin n,
            (1 - x (wheel_rim_edge missing)) • wheel_hamiltonian_cycle_vector n missing)
            (wheel_spoke_edge (wheel_next i))
            = ∑ missing : Fin n,
                ((1 - x (wheel_rim_edge missing)) • wheel_hamiltonian_cycle_vector n missing)
                  (wheel_spoke_edge (wheel_next i)) := by
                    rw [Finset.sum_apply]
        _ = ∑ missing : Fin n,
                (if wheel_next i = missing ∨ wheel_next i = wheel_next missing
                  then 1 - x (wheel_rim_edge missing) else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro missing hmissing
                    rw [Pi.smul_apply, wheel_hamiltonian_cycle_vector_apply_spoke]
                    by_cases h :
                        wheel_next i = missing ∨ wheel_next i = wheel_next missing
                    · simp [h]
                    · simp [h]
        _ = Finset.sum
                (Finset.univ.filter
                  (fun missing : Fin n ↦
                    wheel_next i = missing ∨ wheel_next i = wheel_next missing))
                (fun missing : Fin n ↦ 1 - x (wheel_rim_edge missing)) := by
                  rw [← Finset.sum_filter]
        _ = Finset.sum ({i, wheel_next i} : Finset (Fin n))
              (fun missing : Fin n ↦ 1 - x (wheel_rim_edge missing)) := by
                have hfilter :
                    Finset.univ.filter
                      (fun missing : Fin n ↦
                        wheel_next i = missing ∨ wheel_next i = wheel_next missing) =
                      ({i, wheel_next i} : Finset (Fin n)) := by
                  ext missing
                  simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
                    hnext_injective.eq_iff, eq_comm, or_comm]
                rw [hfilter]
        _ = (2 : ℝ) - x (wheel_rim_edge i) - x (wheel_rim_edge (wheel_next i)) := by
              have hring :
                  (2 : ℝ) - (x (wheel_rim_edge i) + x (wheel_rim_edge (wheel_next i))) =
                    (2 : ℝ) - x (wheel_rim_edge i) - x (wheel_rim_edge (wheel_next i)) := by
                ring
              simpa [hnext_ne] using hring
        _ = x (wheel_spoke_edge (wheel_next i)) := by
              rw [hxspoke i]

/-- Helper for Exercise 7.3: every point of the wheel constraint set is a convex combination of
the Hamiltonian-cycle incidence vectors. -/
lemma wheelHamiltonianConstraintSet_subset_polytope
    (n : ℕ) (hn : 3 ≤ n) :
    wheel_hamiltonian_constraint_set n ⊆ wheel_hamiltonian_polytope n := by
  intro x hx
  have hpos : 0 < n := by omega
  have hweights := wheelConstraintWeights_sum_one hpos hx
  rw [wheel_hamiltonian_polytope_eq_convexHull]
  -- The feasible point is the barycenter of the Hamiltonian-cycle generators with the canonical
  -- rim-complement weights.
  exact mem_convexHull_of_exists_fintype
    (s := wheel_hamiltonian_cycle_vectors n)
    (x := x)
    (w := fun i : Fin n ↦ 1 - x (wheel_rim_edge i))
    (z := wheel_hamiltonian_cycle_vector n)
    hweights.1
    hweights.2
    (fun i ↦ wheel_hamiltonian_cycle_vector_mem_cycle_vectors n i)
    (wheelConstraint_weightedCycleSum_eq n hn hx)

/-- Helper for Exercise 7.3: the wheel Hamiltonian constraint set is convex. -/
lemma wheelHamiltonianConstraintSet_convex
    (n : ℕ) :
    Convex ℝ (wheel_hamiltonian_constraint_set n) := by
  intro x hx y hy a b ha hb hab
  rw [mem_wheel_hamiltonian_constraint_set_iff] at hx hy ⊢
  rcases hx with ⟨hxsum, hxspoke, hxbound⟩
  rcases hy with ⟨hysum, hyspoke, hybound⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The rim-sum equation is preserved by affine combinations.
    calc
      ∑ i : Fin n, (a • x + b • y) (wheel_rim_edge i)
          = ∑ i : Fin n, (a * x (wheel_rim_edge i) + b * y (wheel_rim_edge i)) := by
              simp [Pi.smul_apply]
      _ = a * ∑ i : Fin n, x (wheel_rim_edge i) + b * ∑ i : Fin n, y (wheel_rim_edge i) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = a * (n - 1 : ℝ) + b * (n - 1 : ℝ) := by rw [hxsum, hysum]
      _ = (n - 1 : ℝ) := by nlinarith
  · intro i
    -- Each spoke reconstruction equality is linear in the ambient coordinates.
    calc
      (a • x + b • y) (wheel_spoke_edge (wheel_next i))
          = a * x (wheel_spoke_edge (wheel_next i)) +
              b * y (wheel_spoke_edge (wheel_next i)) := by
                simp [Pi.smul_apply]
      _ = a * ((2 : ℝ) - x (wheel_rim_edge i) - x (wheel_rim_edge (wheel_next i))) +
            b * ((2 : ℝ) - y (wheel_rim_edge i) - y (wheel_rim_edge (wheel_next i))) := by
              rw [hxspoke, hyspoke]
      _ = (2 : ℝ) - (a * x (wheel_rim_edge i) + b * y (wheel_rim_edge i)) -
            (a * x (wheel_rim_edge (wheel_next i)) +
              b * y (wheel_rim_edge (wheel_next i))) := by
              nlinarith
      _ = (2 : ℝ) - (a • x + b • y) (wheel_rim_edge i) -
            (a • x + b • y) (wheel_rim_edge (wheel_next i)) := by
              simp [Pi.smul_apply]
  · intro i
    -- The rim upper bounds are preserved by convex combinations.
    have hxi : x (wheel_rim_edge i) ≤ 1 := hxbound i
    have hyi : y (wheel_rim_edge i) ≤ 1 := hybound i
    calc
      (a • x + b • y) (wheel_rim_edge i)
          = a * x (wheel_rim_edge i) + b * y (wheel_rim_edge i) := by
              simp [Pi.smul_apply]
      _ ≤ 1 := by nlinarith

/-- Helper for Exercise 7.3: each Hamiltonian-cycle incidence vector satisfies the wheel
constraint system when `n ≥ 3`. -/
lemma wheel_hamiltonian_cycle_vector_mem_constraint_set
    (n : ℕ) (hn : 3 ≤ n) (missing : Fin n) :
    wheel_hamiltonian_cycle_vector n missing ∈ wheel_hamiltonian_constraint_set n := by
  rw [mem_wheel_hamiltonian_constraint_set_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- The rim coordinates contribute `1` everywhere except at the deleted rim edge.
    calc
      ∑ i : Fin n, wheel_hamiltonian_cycle_vector n missing (wheel_rim_edge i)
          = ∑ i : Fin n, (if i = missing then (0 : ℝ) else 1) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [wheel_hamiltonian_cycle_vector_apply_rim]
      _ = Finset.sum (Finset.univ.erase missing)
            (fun i : Fin n ↦ if i = missing then (0 : ℝ) else 1) := by
            symm
            exact
              (Finset.sum_erase (s := Finset.univ)
                (f := fun i : Fin n ↦ if i = missing then (0 : ℝ) else 1)
                (a := missing) (by simp))
      _ = Finset.sum (Finset.univ.erase missing) (fun _ : Fin n ↦ (1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_ne : i ≠ missing := (Finset.mem_erase.mp hi).1
            simp [hi_ne]
      _ = ((Finset.univ.erase missing).card : ℝ) := by simp
      _ = (n - 1 : ℝ) := by
            have hnn : 1 ≤ n := by omega
            simp [Finset.card_erase_of_mem, Nat.cast_sub hnn]
  · intro i
    -- The spoke relation is exactly the local reconstruction lemma proved above.
    simpa using wheelHamiltonianCycleVector_spokeReconstruction n hn missing i
  · intro i
    -- Every rim coordinate is either `0` or `1`.
    by_cases hi : i = missing
    · subst hi
      simp [wheel_hamiltonian_cycle_vector_apply_rim]
    · simp [wheel_hamiltonian_cycle_vector_apply_rim, hi]

/-- Helper for Exercise 7.3: the wheel Hamiltonian polytope satisfies every constraint because
its generators do and the constraint set is convex. -/
lemma wheelHamiltonianPolytope_subset_constraintSet
    (n : ℕ) (hn : 3 ≤ n) :
    wheel_hamiltonian_polytope n ⊆ wheel_hamiltonian_constraint_set n := by
  rw [wheel_hamiltonian_polytope_eq_convexHull]
  refine convexHull_min ?_ (wheelHamiltonianConstraintSet_convex n)
  intro x hx
  rcases mem_wheel_hamiltonian_cycle_vectors_iff.mp hx with ⟨missing, rfl⟩
  -- Reduce the convex-hull generators to the already verified cycle-vector constraints.
  exact wheel_hamiltonian_cycle_vector_mem_constraint_set n hn missing

/-- Part (1) of Exercise 7.3. For `n ≥ 3`, the chapter-level polyhedral dimension owner
`polyhedronDim` assigns dimension `n - 1` to `Hamilton(W_n)`. -/
theorem exercise_7_3_wheel_hamiltonian_polytope_dimension
    (n : ℕ) (hn : 3 ≤ n) :
    polyhedronDim (wheel_hamiltonian_polytope n) = n - 1 := by
  have hcard : Fintype.card (Fin n) = (n - 1) + 1 := by
    rw [Fintype.card_fin]
    omega
  -- Rewrite the polyhedral dimension to the vector span of the generating vertex family.
  rw [polyhedronDim, wheel_hamiltonian_polytope_eq_convexHull, affineSpan_convexHull,
    direction_affineSpan]
  exact (wheelHamiltonianCycleVector_affineIndependent n).finrank_vectorSpan hcard

/-- Part (2) of Exercise 7.3. The vertices of `Hamilton(W_n)` are exactly the Hamiltonian cycle
incidence vectors indexed by the deleted rim edge, so `Hamilton(W_n)` has exactly `n` vertices.
The vertex-count conclusion itself does not require the ambient hypothesis `3 ≤ n`. -/
theorem exercise_7_3_wheel_hamiltonian_vertex_count
    (n : ℕ) :
    ((wheel_hamiltonian_polytope n).extremePoints ℝ).ncard = n := by
  rw [wheel_hamiltonian_polytope_extremePoints_eq_cycle_vectors]
  exact wheel_hamiltonian_cycle_vectors_ncard n

/-- Helper for Exercise 7.3: the barycentric map sending simplex basis vertices to the wheel
Hamiltonian-cycle incidence vectors. -/
def wheelHamiltonianBarycentricLinearMap (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] wheel_edge_coords n :=
  LinearMap.pi fun e : wheel_edge n ↦
    ∑ i : Fin n, (wheel_hamiltonian_cycle_vector n i e) • LinearMap.proj i

/-- Helper for Exercise 7.3: the barycentric map evaluates coordinatewise as the expected weighted
sum of Hamiltonian-cycle incidence vectors. -/
lemma wheelHamiltonianBarycentricLinearMap_apply
    (n : ℕ) (z : Fin n → ℝ) (e : wheel_edge n) :
    wheelHamiltonianBarycentricLinearMap n z e =
      ∑ i : Fin n, z i * wheel_hamiltonian_cycle_vector n i e := by
  -- Evaluate the `pi`-linear map at one edge coordinate and simplify the projection summands.
  simp [wheelHamiltonianBarycentricLinearMap, mul_comm]

/-- Helper for Exercise 7.3: each simplex basis vertex maps to the corresponding deleted-edge
Hamiltonian-cycle vector. -/
lemma wheelHamiltonianBarycentricLinearMap_apply_single
    (n : ℕ) (i : Fin n) :
    wheelHamiltonianBarycentricLinearMap n (Pi.single i (1 : ℝ)) =
      wheel_hamiltonian_cycle_vector n i := by
  -- The `i`-th basis vector selects exactly the `i`-th Hamiltonian-cycle generator.
  ext e
  simp [wheelHamiltonianBarycentricLinearMap_apply, Pi.single_apply]

/-- Helper for Exercise 7.3: on a rim coordinate, the barycentric image is the total weight minus
the weight of the omitted edge. -/
lemma wheelHamiltonianBarycentricLinearMap_apply_rim
    (n : ℕ) (z : Fin n → ℝ) (k : Fin n) :
    wheelHamiltonianBarycentricLinearMap n z (wheel_rim_edge k) =
      (∑ i : Fin n, z i) - z k := by
  -- Split off the deleted edge `k`; every other generator contributes `1` on rim coordinate `k`.
  calc
    wheelHamiltonianBarycentricLinearMap n z (wheel_rim_edge k)
        = ∑ i : Fin n, z i * (if k = i then (0 : ℝ) else 1) := by
            simp [wheelHamiltonianBarycentricLinearMap_apply,
              wheel_hamiltonian_cycle_vector_apply_rim]
    _ = Finset.sum (Finset.univ.erase k)
          (fun i : Fin n ↦ z i * (if k = i then (0 : ℝ) else 1)) := by
          symm
          exact
            (Finset.sum_erase (s := Finset.univ)
              (f := fun i : Fin n ↦ z i * (if k = i then (0 : ℝ) else 1))
              (a := k) (by simp))
    _ = Finset.sum (Finset.univ.erase k) (fun i : Fin n ↦ z i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hik : k ≠ i := by
            intro hki
            exact (Finset.mem_erase.mp hi).1 hki.symm
          simp [hik]
    _ = (∑ i : Fin n, z i) - z k := by
          exact
            (Finset.sum_erase_eq_sub (s := Finset.univ)
              (f := fun i : Fin n ↦ z i) (a := k) (Finset.mem_univ k))

/-- Helper for Exercise 7.3: on the standard simplex, the `i`-th rim coordinate equals
`1 - z i`. -/
lemma wheelHamiltonianBarycentricLinearMap_apply_rim_on_stdSimplex
    {n : ℕ} {z : Fin n → ℝ} (hz : z ∈ stdSimplex ℝ (Fin n)) (i : Fin n) :
    wheelHamiltonianBarycentricLinearMap n z (wheel_rim_edge i) = 1 - z i := by
  -- The simplex normalization turns the total barycentric weight into `1`.
  rw [wheelHamiltonianBarycentricLinearMap_apply_rim]
  linarith [hz.2]

/-- Helper for Exercise 7.3: the standard simplex on `Fin m` has affine dimension `m - 1`. -/
lemma wheelStdSimplex_finrank_direction_affineSpan {m : ℕ} (hm : 0 < m) :
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

/-- Helper for Exercise 7.3: on a simplex equality face, any coordinate whose coefficient is
strictly below the face value must vanish. -/
lemma wheelStdSimplexFace_coord_eq_zero_of_lt {m : ℕ} {c : Fin m → ℝ} {δ : ℝ}
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

/-- Helper for Exercise 7.3: a nonempty equality face of the standard simplex is the convex hull
of the basis vertices on which the defining inequality is tight. -/
lemma wheelStdSimplexFace_eq_convexHull_tightBasis {m : ℕ} {c : Fin m → ℝ} {δ : ℝ}
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
                simp [hjtight, wheelStdSimplexFace_coord_eq_zero_of_lt (i := j) hvalid hx hjlt]
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
        have hxk : x k = 0 := wheelStdSimplexFace_coord_eq_zero_of_lt (i := k) hvalid hx hklt
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

/-- Helper for Exercise 7.3: a facet of the standard simplex is supported by exactly `m - 1`
basis vertices. -/
lemma wheelStdSimplexTightBasis_card_of_facet {m : ℕ} (hm : 0 < m) {c : Fin m → ℝ} {δ : ℝ}
    (hvalid : is_valid_inequality (stdSimplex ℝ (Fin m)) c δ)
    (hFacet : IsFacetOf (stdSimplex ℝ (Fin m)) (face_set (stdSimplex ℝ (Fin m)) c δ)) :
    Fintype.card {i : Fin m // c i = δ} = m - 1 := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hFacet' := isFacetOf_iff.mp hFacet
  have hdim_face :
      Module.finrank ℝ (affineSpan ℝ (face_set (stdSimplex ℝ (Fin m)) c δ)).direction = m - 2 := by
    have hface_plus_one :
        Module.finrank ℝ (affineSpan ℝ (face_set (stdSimplex ℝ (Fin m)) c δ)).direction + 1 =
          m - 1 := by
      simpa [wheelStdSimplex_finrank_direction_affineSpan hm] using hFacet'.2.2
    omega
  rw [wheelStdSimplexFace_eq_convexHull_tightBasis hvalid hFacet'.1, affineSpan_convexHull,
    direction_affineSpan] at hdim_face
  have htight_nonempty : Nonempty {i : Fin m // c i = δ} := by
    have hconv_nonempty :
        (convexHull ℝ
          (Set.range
            (fun i : {i : Fin m // c i = δ} ↦ (Pi.single i.1 (1 : ℝ) : Fin m → ℝ)))).Nonempty := by
      rw [← wheelStdSimplexFace_eq_convexHull_tightBasis hvalid hFacet'.1]
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
      simpa [wheelStdSimplex_finrank_direction_affineSpan hm] using hFacet'.2.2
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

/-- Helper for Exercise 7.3: every facet of the standard simplex is obtained by omitting one
coordinate vertex. -/
lemma wheelStdSimplexFacet_eq_coordinateFace {m : ℕ} (hm : 0 < m)
    {F : Set (Fin m → ℝ)} (hF : IsFacetOf (stdSimplex ℝ (Fin m)) F) :
    ∃ i : Fin m, F = {z : Fin m → ℝ | z ∈ stdSimplex ℝ (Fin m) ∧ z i = 0} := by
  classical
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  rcases isFacetOf_iff.mp hF with ⟨hF_nonempty, hF_exposed, hF_dim⟩
  rcases hF_exposed.exists_eq_face_set_of_nonempty hF_nonempty with ⟨c, δ, hvalid, hF_eq⟩
  have hFacetFace :
      IsFacetOf (stdSimplex ℝ (Fin m)) (face_set (stdSimplex ℝ (Fin m)) c δ) := by
    simpa [hF_eq] using hF
  have htight_card :
      Fintype.card {i : Fin m // c i = δ} = m - 1 :=
    wheelStdSimplexTightBasis_card_of_facet hm hvalid hFacetFace
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
    exact ⟨hx.1, wheelStdSimplexFace_coord_eq_zero_of_lt (i := i0.1) hvalid hx hi0_lt⟩
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

/-- Helper for Exercise 7.3: the barycentric map is injective once at least two rim indices are
available. -/
lemma wheelHamiltonianBarycentricLinearMap_injective
    (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (wheelHamiltonianBarycentricLinearMap n) := by
  intro z w hzw
  let d : ℝ := (∑ i : Fin n, z i) - ∑ i : Fin n, w i
  have hcoord : ∀ k : Fin n, z k - w k = d := by
    intro k
    -- Equal barycentric images have equal rim coordinates, which isolates one coefficient gap.
    have hk :
        wheelHamiltonianBarycentricLinearMap n z (wheel_rim_edge k) =
          wheelHamiltonianBarycentricLinearMap n w (wheel_rim_edge k) := by
      exact congrArg (fun x : wheel_edge_coords n ↦ x (wheel_rim_edge k)) hzw
    rw [wheelHamiltonianBarycentricLinearMap_apply_rim,
      wheelHamiltonianBarycentricLinearMap_apply_rim] at hk
    dsimp [d]
    linarith
  have hsum_diff :
      ∑ k : Fin n, (z k - w k) = d := by
    -- Summing the coordinate gaps recovers the global weight difference.
    dsimp [d]
    rw [Finset.sum_sub_distrib]
  have hsum_const :
      ∑ k : Fin n, (z k - w k) = (n : ℝ) * d := by
    -- The rim identities show that every coordinate gap equals the same constant `d`.
    calc
      ∑ k : Fin n, (z k - w k) = ∑ k : Fin n, d := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact hcoord k
      _ = (n : ℝ) * d := by simp
  have hn_real : (1 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (show 1 < 2 by norm_num) hn
  have hd : d = 0 := by
    nlinarith [hsum_diff, hsum_const, hn_real]
  -- Once the common gap vanishes, every simplex coordinate agrees.
  ext k
  linarith [hcoord k, hd]

/-- Helper for Exercise 7.3: the Hamiltonian-cycle generators are exactly the barycentric images
of the simplex basis vertices. -/
lemma wheelHamiltonianCycleVectors_eq_image_basisRange
    (n : ℕ) :
    wheel_hamiltonian_cycle_vectors n =
      wheelHamiltonianBarycentricLinearMap n ''
        Set.range (fun i : Fin n ↦ Pi.single i (1 : ℝ)) := by
  -- Match each deleted-edge generator with the corresponding simplex basis vector.
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Pi.single i (1 : ℝ), ⟨i, rfl⟩,
      wheelHamiltonianBarycentricLinearMap_apply_single n i⟩
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (wheelHamiltonianBarycentricLinearMap_apply_single n i).symm⟩

/-- Helper for Exercise 7.3: the wheel Hamiltonian polytope is the barycentric image of the
standard simplex. -/
lemma wheelHamiltonianPolytope_eq_image_stdSimplex
    (n : ℕ) :
    wheel_hamiltonian_polytope n =
      wheelHamiltonianBarycentricLinearMap n '' stdSimplex ℝ (Fin n) := by
  -- Replace the simplex by the convex hull of its basis vertices and push that hull through the
  -- barycentric map.
  rw [wheel_hamiltonian_polytope_eq_convexHull,
    wheelHamiltonianCycleVectors_eq_image_basisRange]
  rw [← convexHull_rangle_single_eq_stdSimplex (R := ℝ) (ι := Fin n)]
  rw [← LinearMap.image_convexHull]

/-- Helper for Exercise 7.3: the equality face `x_(rim i) = 1` is the barycentric image of the
simplex coordinate face `z i = 0`. -/
lemma wheelRimUpperFace_eq_image_coordinateFace
    (n : ℕ) (i : Fin n) :
    wheel_rim_upper_face n i =
      wheelHamiltonianBarycentricLinearMap n ''
        {z : Fin n → ℝ | z ∈ stdSimplex ℝ (Fin n) ∧ z i = 0} := by
  -- Route correction: transport the face through the barycentric image before using any facet
  -- classification theorem.
  ext x
  constructor
  · intro hx
    rw [mem_wheel_rim_upper_face_iff] at hx
    rcases hx with ⟨hxPoly, hxEq⟩
    rw [wheelHamiltonianPolytope_eq_image_stdSimplex] at hxPoly
    rcases hxPoly with ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    refine ⟨hz, ?_⟩
    have hcoord := wheelHamiltonianBarycentricLinearMap_apply_rim_on_stdSimplex
      (n := n) hz i
    linarith
  · rintro ⟨z, hz, rfl⟩
    rw [mem_wheel_rim_upper_face_iff]
    refine ⟨?_, ?_⟩
    · rw [wheelHamiltonianPolytope_eq_image_stdSimplex]
      exact ⟨z, hz.1, rfl⟩
    · have hcoord := wheelHamiltonianBarycentricLinearMap_apply_rim_on_stdSimplex
        (n := n) hz.1 i
      linarith [hcoord, hz.2]

/-- Helper for Exercise 7.3: the injective barycentric map preserves affine-span dimension on
image sets. -/
lemma wheelHamiltonianBarycentricImage_finrank_direction_affineSpan
    (n : ℕ) (hn : 2 ≤ n) {s : Set (Fin n → ℝ)} :
    Module.finrank ℝ
        (affineSpan ℝ (wheelHamiltonianBarycentricLinearMap n '' s)).direction =
      Module.finrank ℝ (affineSpan ℝ s).direction := by
  let L := wheelHamiltonianBarycentricLinearMap n
  let Laff : (Fin n → ℝ) →ᵃ[ℝ] wheel_edge_coords n := L.toAffineMap
  have hmap :
      affineSpan ℝ (L '' s) = AffineSubspace.map Laff (affineSpan ℝ s) := by
    -- Mapping the affine span is the canonical way to describe the image affine span.
    symm
    simpa [L, Laff] using (AffineSubspace.map_span Laff s)
  rw [hmap, AffineSubspace.map_direction]
  let e :
      (affineSpan ℝ s).direction ≃ₗ[ℝ]
        Submodule.map L (affineSpan ℝ s).direction :=
    Submodule.equivMapOfInjective L
      (wheelHamiltonianBarycentricLinearMap_injective n hn)
      (affineSpan ℝ s).direction
  simpa [e] using (LinearEquiv.finrank_eq e).symm

/-- Helper for Exercise 7.3: omitting one deleted-edge generator preserves affine independence. -/
lemma wheelOmittedCycleVectors_affineIndependent
    (n : ℕ) (i : Fin n) :
    AffineIndependent ℝ
      (fun j : {j : Fin n // j ≠ i} ↦ wheel_hamiltonian_cycle_vector n j.1) := by
  -- This is the omitted-index subfamily of the already affine-independent cycle-vector family.
  simpa using
    (wheelHamiltonianCycleVector_affineIndependent n).subtype {j : Fin n | j ≠ i}

/-- Helper for Exercise 7.3: each rim-edge upper-bound equality face is a facet. -/
lemma wheelRimUpperFace_isFacet
    (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    IsFacetOf (wheel_hamiltonian_polytope n) (wheel_rim_upper_face n i) := by
  have hpos : 0 < n := by omega
  have htwo : 2 ≤ n := by omega
  have h_nonempty : (wheel_rim_upper_face n i).Nonempty := by
    -- Deleting the next rim edge keeps edge `i` present, so that generator lies on the face.
    refine ⟨wheel_hamiltonian_cycle_vector n (wheel_next i), ?_⟩
    rw [mem_wheel_rim_upper_face_iff]
    refine ⟨wheel_hamiltonian_cycle_vector_mem_polytope n (wheel_next i), ?_⟩
    have hineq : i ≠ wheel_next i := by
      intro hii
      exact (wheel_next_ne_self htwo i) hii.symm
    simp [wheel_hamiltonian_cycle_vector_apply_rim, hineq]
  have hvalid :
      ∀ x ∈ wheel_hamiltonian_polytope n,
        (LinearMap.proj (wheel_rim_edge i) : wheel_edge_coords n →ₗ[ℝ] ℝ) x ≤ 1 := by
    intro x hx
    have hxBox := wheel_hamiltonian_polytope_subset_unitBox n hx
    rw [Set.mem_univ_pi] at hxBox
    exact (hxBox (wheel_rim_edge i)).2
  have hx0_eq :
      (LinearMap.proj (wheel_rim_edge i) : wheel_edge_coords n →ₗ[ℝ] ℝ)
          (wheel_hamiltonian_cycle_vector n (wheel_next i)) = 1 := by
    have hineq : i ≠ wheel_next i := by
      intro hii
      exact (wheel_next_ne_self htwo i) hii.symm
    simp [LinearMap.proj_apply, wheel_hamiltonian_cycle_vector_apply_rim, hineq]
  let rimProj : wheel_edge_coords n →ₗ[ℝ] ℝ := LinearMap.proj (wheel_rim_edge i)
  let rimProjCLM : wheel_edge_coords n →L[ℝ] ℝ :=
    ⟨rimProj, rimProj.continuous_of_finiteDimensional⟩
  have h_exposed_eq :
      wheel_rim_upper_face n i =
        rimProjCLM.toExposed (wheel_hamiltonian_polytope n) := by
    -- Equality at the sharp rim-coordinate upper bound is exactly the maximizing set.
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      refine ⟨hxP, ?_⟩
      intro y hyP
      calc
        rimProj y ≤ 1 := hvalid y hyP
        _ = rimProj x := by simp [rimProj, hxEq]
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hx_upper : rimProj x ≤ 1 := hvalid x hx.1
      have hx_lower : 1 ≤ rimProj x := by
        have hmax :=
          hx.2 (wheel_hamiltonian_cycle_vector n (wheel_next i))
            (wheel_hamiltonian_cycle_vector_mem_polytope n (wheel_next i))
        simpa [rimProjCLM, rimProj, hx0_eq] using hmax
      have hx_eq : rimProj x = 1 := by
        linarith
      simpa [rimProj, LinearMap.proj_apply] using hx_eq
  have h_exposed :
      IsExposed ℝ (wheel_hamiltonian_polytope n) (wheel_rim_upper_face n i) := by
    -- Rewriting the equality face as a `toExposed` set yields the exposed-face owner directly.
    rw [h_exposed_eq]
    exact ContinuousLinearMap.toExposed.isExposed
  have h_face_dim :
      Module.finrank ℝ (affineSpan ℝ (wheel_rim_upper_face n i)).direction = n - 2 := by
    -- The face is the convex hull of an omitted affine-independent subfamily of size `n - 1`.
    rw [wheelRimUpperFace_eq_convexHull_omittedCycleVectors, affineSpan_convexHull,
      direction_affineSpan]
    letI : Nonempty {j : Fin n // j ≠ i} :=
      ⟨⟨wheel_next i, wheel_next_ne_self htwo i⟩⟩
    have hcard :
        Module.finrank ℝ
            (vectorSpan ℝ
              (Set.range
                (fun j : {j : Fin n // j ≠ i} ↦ wheel_hamiltonian_cycle_vector n j.1))) + 1 =
          n - 1 := by
      simpa using
        (AffineIndependent.finrank_vectorSpan_add_one
          (p := fun j : {j : Fin n // j ≠ i} ↦ wheel_hamiltonian_cycle_vector n j.1)
          (wheelOmittedCycleVectors_affineIndependent n i))
    omega
  have h_poly_dim :
      Module.finrank ℝ (affineSpan ℝ (wheel_hamiltonian_polytope n)).direction = n - 1 := by
    simpa [polyhedronDim] using
      exercise_7_3_wheel_hamiltonian_polytope_dimension n hn
  rw [isFacetOf_iff]
  -- The exposed omitted-generator face has codimension one inside the full wheel polytope.
  refine ⟨h_nonempty, h_exposed, ?_⟩
  rw [h_face_dim, h_poly_dim]
  omega

/-- Helper for Exercise 7.3: distinct rim indices define distinct upper-bound equality faces. -/
lemma wheelRimUpperFace_injective
    (n : ℕ) :
    Function.Injective (wheel_rim_upper_face n) := by
  intro i j hij
  by_contra hne
  have hmem_j :
      wheel_hamiltonian_cycle_vector n i ∈ wheel_rim_upper_face n j := by
    rw [mem_wheel_rim_upper_face_iff]
    refine ⟨wheel_hamiltonian_cycle_vector_mem_polytope n i, ?_⟩
    have hji : j ≠ i := by simpa [eq_comm] using hne
    simp [wheel_hamiltonian_cycle_vector_apply_rim, hji]
  have hmem :
      wheel_hamiltonian_cycle_vector n i ∈ wheel_rim_upper_face n i := by
    simpa [hij] using hmem_j
  have hnot_mem :
      wheel_hamiltonian_cycle_vector n i ∉ wheel_rim_upper_face n i := by
    intro hi
    rw [mem_wheel_rim_upper_face_iff] at hi
    have : wheel_hamiltonian_cycle_vector n i (wheel_rim_edge i) = 1 := hi.2
    simp [wheel_hamiltonian_cycle_vector_apply_rim] at this
  exact hnot_mem hmem

/-- Helper for Exercise 7.3: every facet of the wheel Hamiltonian polytope is one of the rim-edge
upper-bound equality faces. -/
lemma wheelHamiltonianPolytope_facets_eq_rimUpperFaces
    (n : ℕ) (hn : 3 ≤ n) :
    {F : Set (wheel_edge_coords n) | IsFacetOf (wheel_hamiltonian_polytope n) F} =
      Set.range (wheel_rim_upper_face n) := by
  classical
  ext F
  constructor
  · intro hF
    have hpos : 0 < n := by omega
    have htwo : 2 ≤ n := by omega
    have hF' := isFacetOf_iff.mp hF
    obtain ⟨l, hF_eq⟩ := hF'.2.1 hF'.1
    let L := wheelHamiltonianBarycentricLinearMap n
    let Fz : Set (Fin n → ℝ) :=
      {z | z ∈ stdSimplex ℝ (Fin n) ∧
        ∀ w ∈ stdSimplex ℝ (Fin n), l (L w) ≤ l (L z)}
    have hF_image : F = L '' Fz := by
      -- Pull the exposed wheel facet back along the barycentric simplex parametrization.
      ext x
      constructor
      · intro hx
        rw [hF_eq] at hx
        rw [wheelHamiltonianPolytope_eq_image_stdSimplex] at hx
        rcases hx.1 with ⟨z, hz, rfl⟩
        refine ⟨z, ?_, rfl⟩
        refine ⟨hz, ?_⟩
        intro w hw
        have hLw : L w ∈ L '' stdSimplex ℝ (Fin n) := ⟨w, hw, rfl⟩
        exact hx.2 (L w) hLw
      · rintro ⟨z, hz, rfl⟩
        rw [hF_eq]
        refine ⟨?_, ?_⟩
        · rw [wheelHamiltonianPolytope_eq_image_stdSimplex]
          exact ⟨z, hz.1, rfl⟩
        · intro y hy
          rw [wheelHamiltonianPolytope_eq_image_stdSimplex] at hy
          rcases hy with ⟨w, hw, rfl⟩
          exact hz.2 w hw
    have hFz_nonempty : Fz.Nonempty := by
      rcases hF'.1 with ⟨x, hx⟩
      rw [hF_image] at hx
      rcases hx with ⟨z, hz, rfl⟩
      exact ⟨z, hz⟩
    let Lclm : (Fin n → ℝ) →L[ℝ] wheel_edge_coords n := L.toContinuousLinearMap
    have hFz_exposed :
        IsExposed ℝ (stdSimplex ℝ (Fin n)) Fz := by
      -- The pulled-back maximizer set is exposed by the composed supporting functional.
      change IsExposed ℝ (stdSimplex ℝ (Fin n))
        ((l.comp Lclm).toExposed (stdSimplex ℝ (Fin n)))
      exact ContinuousLinearMap.toExposed.isExposed
    have hFz_dim :
        Module.finrank ℝ (affineSpan ℝ Fz).direction + 1 =
          Module.finrank ℝ (affineSpan ℝ (stdSimplex ℝ (Fin n))).direction := by
      -- Injectivity of the barycentric map transports the codimension-one equation to the simplex.
      have hdim := hF'.2.2
      rw [hF_image, wheelHamiltonianPolytope_eq_image_stdSimplex,
        wheelHamiltonianBarycentricImage_finrank_direction_affineSpan n htwo (s := Fz),
        wheelHamiltonianBarycentricImage_finrank_direction_affineSpan n htwo
          (s := stdSimplex ℝ (Fin n))] at hdim
      exact hdim
    have hFz_facet :
        IsFacetOf (stdSimplex ℝ (Fin n)) Fz := by
      exact ⟨hFz_nonempty, hFz_exposed, hFz_dim⟩
    rcases wheelStdSimplexFacet_eq_coordinateFace (m := n) hpos hFz_facet with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    symm
    calc
      F = L '' Fz := hF_image
      _ = L '' {z : Fin n → ℝ | z ∈ stdSimplex ℝ (Fin n) ∧ z i = 0} := by rw [hi]
      _ = wheel_rim_upper_face n i := by
            simpa [L] using (wheelRimUpperFace_eq_image_coordinateFace n i).symm
  · rintro ⟨i, rfl⟩
    exact wheelRimUpperFace_isFacet n hn i

/-- Exercise 7.3 (3). For `n ≥ 3`, the wheel Hamiltonian polytope has exactly `n` facets. -/
theorem exercise_7_3_wheel_hamiltonian_polytope_facet_count
    (n : ℕ) (hn : 3 ≤ n) :
    {F : Set (wheel_edge_coords n) | IsFacetOf (wheel_hamiltonian_polytope n) F}.ncard = n := by
  classical
  -- Classify all facets as rim-coordinate faces and count those faces by injectivity.
  rw [wheelHamiltonianPolytope_facets_eq_rimUpperFaces n hn]
  simpa using Set.ncard_range_of_injective (wheelRimUpperFace_injective n)

/-- Part (4) of Exercise 7.3. For each rim edge of `W_n`, the inequality
`x_e ≤ 1` defines a facet of `Hamilton(W_n)`. -/
theorem exercise_7_3_rim_edge_upper_bound_defines_facet
    (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    IsFacetOf (wheel_hamiltonian_polytope n) (wheel_rim_upper_face n i) := by
  -- The wheel rim equality face is exactly the omitted-generator face proved facet-worthy above.
  exact wheelRimUpperFace_isFacet n hn i

/-- Part (5) of Exercise 7.3. For `n ≥ 3`, `Hamilton(W_n)` is described minimally by the
rim-edge sum equation, the spoke reconstruction equalities, and the rim-edge upper bounds. -/
theorem exercise_7_3_wheel_hamiltonian_polytope_eq_constraint_set
    (n : ℕ) (hn : 3 ≤ n) :
    wheel_hamiltonian_polytope n = wheel_hamiltonian_constraint_set n := by
  -- The forward inclusion is generatorwise convexity, and the reverse inclusion is the
  -- barycentric reconstruction proved above.
  refine Set.Subset.antisymm ?_ ?_
  · exact wheelHamiltonianPolytope_subset_constraintSet n hn
  · exact wheelHamiltonianConstraintSet_subset_polytope n hn

end Exercise73
