/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_21
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.incident_edge_finset

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SimpleGraph
open scoped BigOperators

attribute [local instance] Classical.propDecidable

-- Semantic search note: the deferred Lean semantic-search tool `lean_leansearch` was not
-- available in this environment, so this file reuses the Chapter 3 complete-graph owners
-- `complete_graph_edges` and `hamiltonian_path_edge_finset`, adding only the tour-closing edge.

/-- The last permutation position in `Fin (n + 2)`, used to close the Hamiltonian tour determined
by `σ`. -/
def hamiltonian_tour_last_position (n : ℕ) : Fin (n + 2) :=
  ⟨n + 1, Nat.lt_succ_self (n + 1)⟩

/-- The closing edge of the Hamiltonian tour on `Fin (n + 2)` determined by `σ`, joining the first
and last vertices of the permutation. -/
theorem hamiltonian_tour_closing_edge_not_isDiag {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) :
    ¬ (s(σ 0, σ (hamiltonian_tour_last_position n)) : Sym2 (Fin (n + 2))).IsDiag := by
  rw [Sym2.mk_isDiag_iff]
  intro hdiag
  have hneq : (0 : Fin (n + 2)) ≠ hamiltonian_tour_last_position n := by
    simp [hamiltonian_tour_last_position]
  exact hneq (σ.injective hdiag)

/-- The wraparound edge closing the Hamiltonian tour determined by `σ`. -/
def hamiltonian_tour_closing_edge {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) :
    complete_graph_edges (n + 2) :=
  ⟨s(σ 0, σ (hamiltonian_tour_last_position n)), hamiltonian_tour_closing_edge_not_isDiag σ⟩

/-- The finite edge set of the Hamiltonian tour determined by `σ`. It is the Chapter 3
Hamiltonian-path edge set together with the closing edge from the last permutation position back
to the first. -/
def hamiltonian_tour_edge_finset {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finset (complete_graph_edges n) :=
  match n with
  | 0 => ∅
  | 1 => ∅
  | _ + 2 => insert (hamiltonian_tour_closing_edge σ) (hamiltonian_path_edge_finset σ)

/-- The edge `e` belongs to the Hamiltonian tour determined by the permutation `σ` when its
endpoints occur as one of the path edges or as the closing edge. -/
def is_hamiltonian_tour_edge {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : complete_graph_edges n) : Prop :=
  e ∈ hamiltonian_tour_edge_finset σ

/-- The incidence vector of the Hamiltonian tour of the complete graph on `Fin n` determined by
the permutation `σ`. -/
def hamiltonian_tour_incidence_vector {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    complete_graph_edges n → ℝ :=
  fun e ↦ if is_hamiltonian_tour_edge σ e then 1 else 0

/-- The traveling salesman polytope on `n` nodes is the convex hull of the incidence vectors of
the Hamiltonian tours of the complete graph on `Fin n`. -/
def travelingSalesmanPolytope (n : ℕ) : Set (complete_graph_edges n → ℝ) :=
  convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) ↦ hamiltonian_tour_incidence_vector σ)

/-- The traveling salesman polytope is the convex hull of the permutation-induced Hamiltonian-tour
incidence vectors. -/
theorem travelingSalesmanPolytope_eq_convexHull (n : ℕ) :
    travelingSalesmanPolytope n =
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) ↦ hamiltonian_tour_incidence_vector σ) :=
  rfl

/-- Reindexing the graph-level incidence finset of `completeGraph (Fin n)` along
`completeGraphEdgeEquiv.symm` recovers the complete-graph edge coordinates incident to `i`. -/
theorem mem_completeGraph_incidentEdgeFinset_iff
    {n : ℕ} {i : Fin n} {e : complete_graph_edges n} :
    e ∈ (incidentEdgeFinset (completeGraph (Fin n)) i).map completeGraphEdgeEquiv.symm.toEmbedding ↔
      i ∈ (e : Sym2 (Fin n)) := by
  constructor
  · intro he
    rw [Finset.mem_map] at he
    rcases he with ⟨e', he', hcoe⟩
    have hmem : i ∈ (e' : Sym2 (Fin n)) :=
      mem_incidentEdgeFinset_iff.1 he'
    simpa [completeGraphEdgeEquiv] using hcoe ▸ hmem
  · intro he
    rw [Finset.mem_map]
    refine ⟨completeGraphEdgeEquiv e, ?_, by simp⟩
    exact mem_incidentEdgeFinset_iff.2 he

/-- The degree-constraint set cutting out the affine hull of the traveling salesman polytope on
`n` nodes. -/
def travelingSalesmanDegreeConstraintSet (n : ℕ) : Set (complete_graph_edges n → ℝ) :=
  {x | ∀ i : Fin n,
      ((incidentEdgeFinset (completeGraph (Fin n)) i).map
          completeGraphEdgeEquiv.symm.toEmbedding).sum x = (2 : ℝ)}

/-- Membership in `travelingSalesmanDegreeConstraintSet n` means satisfying the degree equation
on the graph-level incidence finset of `completeGraph (Fin n)`, reindexed to the
`complete_graph_edges n` coordinates. -/
theorem mem_travelingSalesmanDegreeConstraintSet_iff {n : ℕ} {x : complete_graph_edges n → ℝ} :
    x ∈ travelingSalesmanDegreeConstraintSet n ↔
      ∀ i : Fin n,
        ((incidentEdgeFinset (completeGraph (Fin n)) i).map
            completeGraphEdgeEquiv.symm.toEmbedding).sum x = (2 : ℝ) :=
  Iff.rfl

/-- The `complete_graph_edges n` coordinates incident to the vertex `i`. This is the local
complete-graph filter view of the shared graph-level owner `incidentEdgeFinset`. -/
private def completeGraphIncidentEdgeFinset (n : ℕ) (i : Fin n) :
    Finset (complete_graph_edges n) :=
  Finset.univ.filter fun e ↦ i ∈ (e : Sym2 (Fin n))

/-- The local complete-graph incident-edge filter view agrees with the reindexed graph-level owner
used in `travelingSalesmanDegreeConstraintSet`. -/
private theorem completeGraphIncidentEdgeFinset_eq
    (n : ℕ) (i : Fin n) :
    completeGraphIncidentEdgeFinset n i =
      (incidentEdgeFinset (completeGraph (Fin n)) i).map
        completeGraphEdgeEquiv.symm.toEmbedding := by
  -- Both finite edge sets record exactly the coordinates whose unordered pair contains `i`.
  ext e
  simpa [completeGraphIncidentEdgeFinset] using
    (mem_completeGraph_incidentEdgeFinset_iff (i := i) (e := e)).symm

/-- Membership in the local complete-graph incident-edge finset means that `i` is an endpoint of
the edge coordinate `e`. -/
private theorem mem_completeGraphIncidentEdgeFinset_iff
    {n : ℕ} {i : Fin n} {e : complete_graph_edges n} :
    e ∈ completeGraphIncidentEdgeFinset n i ↔ i ∈ (e : Sym2 (Fin n)) := by
  -- This is just the defining filter condition.
  simp [completeGraphIncidentEdgeFinset]

/-- Helper for Theorem 7.18: for `m ≥ 2`, the affine hull of the Hamiltonian-path polytope is the
constant-sum affine slice `∑ e, x e = m - 1`. -/
theorem affineSpan_hamiltonianPathPolytope_eq_constantSumSlice
    (m : ℕ) (hm : 2 ≤ m) :
    (affineSpan ℝ (hamiltonian_path_polytope m) : Set (complete_graph_edges m → ℝ)) =
      {x | ∑ e, x e = ((m - 1 : ℕ) : ℝ)} := by
  classical
  let sumCoords : (complete_graph_edges m → ℝ) →ₗ[ℝ] ℝ :=
    (Pi.basisFun ℝ (complete_graph_edges m)).sumCoords
  let x₀ : complete_graph_edges m → ℝ :=
    hamiltonian_path_incidence_vector (Equiv.refl (Fin m))
  let H : AffineSubspace ℝ (complete_graph_edges m → ℝ) :=
    AffineSubspace.mk' x₀ (LinearMap.ker sumCoords)
  have hx₀_mem_poly : x₀ ∈ hamiltonian_path_polytope m := by
    -- The identity permutation contributes one generating vertex of the Hamiltonian-path polytope.
    rw [hamiltonian_path_polytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self (Equiv.refl (Fin m)))
  have hx₀_mem_aff :
      x₀ ∈ affineSpan ℝ (hamiltonian_path_polytope m) := by
    -- Any polytope vertex lies in the affine span of the polytope.
    exact subset_affineSpan ℝ _ hx₀_mem_poly
  have hx₀_mem_H : x₀ ∈ H := by
    -- The chosen base point belongs to the affine slice by construction.
    rw [show H = AffineSubspace.mk' x₀ (LinearMap.ker sumCoords) by rfl]
    rw [AffineSubspace.mem_mk']
    simp
  have hdir_eq :
      (affineSpan ℝ (hamiltonian_path_polytope m)).direction = H.direction := by
    -- Example 3.21 already identifies the path-polytope direction with the zero-sum hyperplane.
    refine le_antisymm ?_ ?_
    · simpa [H, sumCoords] using
        hamiltonian_path_polytope_direction_le_sumCoords_ker m
    · simpa [H, sumCoords] using
        sumCoords_ker_le_hamiltonian_path_direction m hm
  have hAffEq : affineSpan ℝ (hamiltonian_path_polytope m) = H := by
    -- Equal directions plus one common point determine the affine subspace.
    exact AffineSubspace.ext_of_direction_eq hdir_eq ⟨x₀, hx₀_mem_aff, hx₀_mem_H⟩
  calc
    (affineSpan ℝ (hamiltonian_path_polytope m) : Set (complete_graph_edges m → ℝ)) = H := by
      simpa using congrArg
        (fun A : AffineSubspace ℝ (complete_graph_edges m → ℝ) =>
          (A : Set (complete_graph_edges m → ℝ))) hAffEq
    _ = {x | ∑ e, x e = ((m - 1 : ℕ) : ℝ)} := by
      -- Expanding the affine-slice membership rewrites it to the expected constant-sum equation.
      ext x
      have hx₀_sum : sumCoords x₀ = ((m - 1 : ℕ) : ℝ) := by
        simpa [sumCoords, x₀] using
          hamiltonian_path_incidence_vector_sum m (Equiv.refl (Fin m))
      constructor
      · intro hx
        have hx' : x ∈ H := hx
        rw [show H = AffineSubspace.mk' x₀ (LinearMap.ker sumCoords) by rfl] at hx'
        rw [AffineSubspace.mem_mk'] at hx'
        change sumCoords (x - x₀) = 0 at hx'
        rw [LinearMap.map_sub, hx₀_sum] at hx'
        have hxsum : sumCoords x = ((m - 1 : ℕ) : ℝ) := by
          linarith
        simpa [Set.mem_setOf_eq, sumCoords] using hxsum
      · intro hx
        change x ∈ H
        rw [show H = AffineSubspace.mk' x₀ (LinearMap.ker sumCoords) by rfl]
        rw [AffineSubspace.mem_mk']
        change sumCoords (x - x₀) = 0
        have hxsum : sumCoords x = ((m - 1 : ℕ) : ℝ) := by
          simpa [Set.mem_setOf_eq, sumCoords] using hx
        rw [LinearMap.map_sub, hx₀_sum]
        rw [hxsum, sub_self]

/-- Helper for Theorem 7.18: the old complete-graph edges embed into the enlarged complete graph
by applying `Fin.castSucc` to both endpoints. -/
private theorem oldEdgeEmb_not_isDiag {m : ℕ} (e : complete_graph_edges m) :
    ¬ (Sym2.map Fin.castSucc (e : Sym2 (Fin m))).IsDiag := by
  -- Non-diagonal unordered pairs stay non-diagonal under an injective vertex embedding.
  let hcast : Function.Injective (@Fin.castSucc m) := by
    intro a b hab
    exact Fin.ext (by simpa using congrArg (fun z : Fin (m + 1) ↦ z.1) hab)
  intro hdiag
  exact e.2 ((Sym2.isDiag_map hcast).1 hdiag)

/-- Helper for Theorem 7.18: the old-edge coordinate embedding `K_m → K_{m+1}`. -/
private def oldEdgeEmb {m : ℕ} (e : complete_graph_edges m) : complete_graph_edges (m + 1) :=
  ⟨Sym2.map Fin.castSucc (e : Sym2 (Fin m)), oldEdgeEmb_not_isDiag e⟩

/-- Helper for Theorem 7.18: the star edge joining an old vertex to the new last vertex. -/
private theorem newVertexEdge_not_isDiag {m : ℕ} (i : Fin m) :
    ¬ (s(Fin.castSucc i, Fin.last m) : Sym2 (Fin (m + 1))).IsDiag := by
  -- The embedded old vertex is never equal to the new last vertex.
  rw [Sym2.mk_isDiag_iff]
  exact Fin.castSucc_ne_last i

/-- Helper for Theorem 7.18: the edge joining `i` to the new last vertex in `K_{m+1}`. -/
private def newVertexEdge {m : ℕ} (i : Fin m) : complete_graph_edges (m + 1) :=
  ⟨s(Fin.castSucc i, Fin.last m), newVertexEdge_not_isDiag i⟩

/-- Helper for Theorem 7.18: the old-edge embedding is injective. -/
private theorem oldEdgeEmb_injective {m : ℕ} :
    Function.Injective (@oldEdgeEmb m) := by
  let hcast : Function.Injective (@Fin.castSucc m) := by
    intro a b hab
    exact Fin.ext (by simpa using congrArg (fun z : Fin (m + 1) ↦ z.1) hab)
  intro e₁ e₂ h
  apply Subtype.ext
  exact Sym2.map.injective hcast (congrArg Subtype.val h)

/-- Helper for Theorem 7.18: distinct star edges correspond to distinct old vertices. -/
private theorem newVertexEdge_injective {m : ℕ} :
    Function.Injective (@newVertexEdge m) := by
  intro i j h
  have hval :
      (s(Fin.castSucc i, Fin.last m) : Sym2 (Fin (m + 1))) =
        s(Fin.castSucc j, Fin.last m) := congrArg Subtype.val h
  rw [Sym2.eq_iff] at hval
  rcases hval with hpair | hpair
  · exact Fin.ext (by simpa using congrArg (fun z : Fin (m + 1) ↦ z.1) hpair.1)
  · exact False.elim ((Fin.castSucc_ne_last i) hpair.1)

/-- Helper for Theorem 7.18: an old edge never coincides with a star edge. -/
private theorem oldEdgeEmb_ne_newVertexEdge {m : ℕ}
    (e : complete_graph_edges m) (i : Fin m) :
    oldEdgeEmb e ≠ newVertexEdge i := by
  intro h
  have hlast : Fin.last m ∈ ((oldEdgeEmb e : complete_graph_edges (m + 1)) : Sym2 (Fin (m + 1))) := by
    simpa [h, newVertexEdge]
  rw [oldEdgeEmb] at hlast
  rw [Sym2.mem_map] at hlast
  rcases hlast with ⟨a, -, ha⟩
  exact Fin.castSucc_ne_last a ha

/-- Helper for Theorem 7.18: the incident-edge sum linear map on `K_n`. -/
private def travelingSalesmanDegreeMap (n : ℕ) :
    (complete_graph_edges n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := (completeGraphIncidentEdgeFinset n i).sum x
  map_add' x y := by
    -- Summing coordinates incident to a fixed vertex is linear in the edge vector.
    ext i
    exact Finset.sum_add_distrib
  map_smul' a x := by
    -- Scalar multiplication pulls through the finite incident-edge sum.
    ext i
    simp [Finset.mul_sum]

/-- Helper for Theorem 7.18: the degree map just packages the local incident-edge sums. -/
private theorem travelingSalesmanDegreeMap_apply {n : ℕ} (x : complete_graph_edges n → ℝ)
    (i : Fin n) :
    travelingSalesmanDegreeMap n x i = (completeGraphIncidentEdgeFinset n i).sum x := rfl

/-- Helper for Theorem 7.18: membership in the degree-constraint set is equivalent to the degree
map being constantly equal to `2`. -/
private theorem mem_travelingSalesmanDegreeConstraintSet_iff_degreeMap
    {n : ℕ} {x : complete_graph_edges n → ℝ} :
    x ∈ travelingSalesmanDegreeConstraintSet n ↔ travelingSalesmanDegreeMap n x = fun _ ↦ (2 : ℝ) := by
  -- The set definition and the linear map have the same coordinate equations.
  constructor
  · intro hx
    ext i
    simpa [travelingSalesmanDegreeMap_apply, completeGraphIncidentEdgeFinset_eq] using
      (mem_travelingSalesmanDegreeConstraintSet_iff.mp hx) i
  · intro hx
    rw [mem_travelingSalesmanDegreeConstraintSet_iff]
    intro i
    simpa [travelingSalesmanDegreeMap_apply, completeGraphIncidentEdgeFinset_eq] using
      congrArg (fun f : Fin n → ℝ ↦ f i) hx

/-- Helper for Theorem 7.18: the edge coordinate on two distinct vertices. -/
private theorem edgeBetween_not_isDiag {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ¬ (s(i, j) : Sym2 (Fin n)).IsDiag := by
  -- Distinct endpoints define a genuine complete-graph edge.
  rw [Sym2.mk_isDiag_iff]
  exact hij

/-- Helper for Theorem 7.18: the complete-graph edge on two distinct vertices. -/
private def edgeBetween {n : ℕ} (i j : Fin n) (hij : i ≠ j) : complete_graph_edges n :=
  ⟨s(i, j), edgeBetween_not_isDiag hij⟩

/-- Helper for Theorem 7.18: the concrete edge `{i,j}` is incident to `v` exactly when `v` is one
of its endpoints. -/
private theorem mem_completeGraphIncidentEdgeFinset_edgeBetween_iff
    {n : ℕ} {i j v : Fin n} (hij : i ≠ j) :
    edgeBetween i j hij ∈ completeGraphIncidentEdgeFinset n v ↔ v = i ∨ v = j := by
  -- Unfold the concrete edge and read membership in the unordered pair `{i,j}`.
  rw [mem_completeGraphIncidentEdgeFinset_iff, edgeBetween]
  simp [Sym2.mem_iff, eq_comm, or_left_comm, or_assoc]

/-- Helper for Theorem 7.18: evaluating a basis edge on the degree map returns the corresponding
endpoint indicator. -/
private theorem travelingSalesmanDegreeMap_apply_basisFun
    {n : ℕ} (e : complete_graph_edges n) (v : Fin n) :
    travelingSalesmanDegreeMap n (Pi.basisFun ℝ (complete_graph_edges n) e) v =
      if e ∈ completeGraphIncidentEdgeFinset n v then 1 else 0 := by
  -- The basis function contributes only at its own coordinate inside the incident-edge sum.
  rw [travelingSalesmanDegreeMap_apply]
  by_cases he : e ∈ completeGraphIncidentEdgeFinset n v
  · simp [Pi.basisFun, he]
  · simp [Pi.basisFun, he]

/-- Helper for Theorem 7.18: the raw linear completion formula from old edge coordinates to the
enlarged edge space. -/
private def completePathToTourRaw (m : ℕ) (x : complete_graph_edges m → ℝ) :
    complete_graph_edges (m + 1) → ℝ :=
  (∑ e : complete_graph_edges m,
      x e • Pi.basisFun ℝ (complete_graph_edges (m + 1)) (oldEdgeEmb e)) +
    ∑ i : Fin m,
      (-(completeGraphIncidentEdgeFinset m i).sum x) •
        Pi.basisFun ℝ (complete_graph_edges (m + 1)) (newVertexEdge i)

/-- Helper for Theorem 7.18: the linear part of the path-to-tour completion map. -/
private def completePathToTourLinearMap (m : ℕ) :
    (complete_graph_edges m → ℝ) →ₗ[ℝ] (complete_graph_edges (m + 1) → ℝ) :=
  (∑ e : complete_graph_edges m,
      (LinearMap.single ℝ (fun _ : complete_graph_edges (m + 1) ↦ ℝ) (oldEdgeEmb e)).comp
        (LinearMap.proj e)) +
    ∑ i : Fin m,
      (-1 : ℝ) •
        ((LinearMap.single ℝ (fun _ : complete_graph_edges (m + 1) ↦ ℝ) (newVertexEdge i)).comp
          ((LinearMap.proj i).comp (travelingSalesmanDegreeMap m)))

/-- Helper for Theorem 7.18: the constant star contribution of value `2` on each new-vertex
edge. -/
private def completePathToTourConstant (m : ℕ) : complete_graph_edges (m + 1) → ℝ :=
  ∑ i : Fin m, (2 : ℝ) • Pi.basisFun ℝ (complete_graph_edges (m + 1)) (newVertexEdge i)

/-- Helper for Theorem 7.18: the affine completion map. -/
private def completePathToTourAffineMap (m : ℕ) :
    (complete_graph_edges m → ℝ) →ᵃ[ℝ] (complete_graph_edges (m + 1) → ℝ) :=
  (completePathToTourLinearMap m).toAffineMap +ᵥ
    AffineMap.const ℝ (complete_graph_edges m → ℝ) (completePathToTourConstant m)

/-- Helper for Theorem 7.18: the affine completion map adds the constant star contribution `2` on
the new-vertex edges. -/
private theorem completePathToTourAffineMap_apply_oldEdgeEmb
    {m : ℕ} (x : complete_graph_edges m → ℝ) (e : complete_graph_edges m) :
    completePathToTourAffineMap m x (oldEdgeEmb e) = x e := by
  -- Route correction: normalize only the owner coordinate `oldEdgeEmb e`; the abandoned whole-slice
  -- image proof needed much stronger formulas than the theorem actually uses.
  simp [completePathToTourAffineMap, completePathToTourLinearMap, completePathToTourConstant,
    oldEdgeEmb_ne_newVertexEdge]
  simp [Pi.single_apply, oldEdgeEmb_injective.eq_iff]

/-- Helper for Theorem 7.18: the linear part of the completion map copies the old-edge
coordinates verbatim. -/
private theorem completePathToTourLinearMap_apply_oldEdgeEmb
    {m : ℕ} (x : complete_graph_edges m → ℝ) (e : complete_graph_edges m) :
    completePathToTourLinearMap m x (oldEdgeEmb e) = x e := by
  -- Evaluating the linear part on an embedded old edge kills every star coordinate.
  simp [completePathToTourLinearMap, oldEdgeEmb_ne_newVertexEdge]
  simp [Pi.single_apply, oldEdgeEmb_injective.eq_iff]

/-- Helper for Theorem 7.18: the completion map puts `2 - deg_x(i)` on the new-vertex edge at
`i`. -/
private theorem completePathToTourAffineMap_apply_newVertexEdge
    {m : ℕ} (x : complete_graph_edges m → ℝ) (i : Fin m) :
    completePathToTourAffineMap m x (newVertexEdge i) =
      2 - (completeGraphIncidentEdgeFinset m i).sum x := by
  -- Route correction: evaluate the completion owner only on the single star coordinate
  -- `newVertexEdge i`, where the copied old-edge block vanishes and the star block is diagonal.
  simp [completePathToTourAffineMap, completePathToTourLinearMap, completePathToTourConstant,
    oldEdgeEmb_ne_newVertexEdge]
  simp [Pi.single_apply, newVertexEdge_injective.eq_iff, travelingSalesmanDegreeMap_apply,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Helper for Theorem 7.18: the completion affine map is injective because the old-edge
coordinates are a left inverse. -/
private theorem completePathToTourAffineMap_injective {m : ℕ} :
    Function.Injective (completePathToTourAffineMap m) := by
  intro x y hxy
  -- Comparing the copied old-edge coordinates recovers the original edge vector.
  ext e
  have hcoord :
      completePathToTourAffineMap m x (oldEdgeEmb e) =
      completePathToTourAffineMap m y (oldEdgeEmb e) := by
    simpa using congrArg (fun z : complete_graph_edges (m + 1) → ℝ ↦ z (oldEdgeEmb e)) hxy
  simpa [completePathToTourAffineMap_apply_oldEdgeEmb] using hcoord

/-- Helper for Theorem 7.18: the linear part of the completion map is injective because the
old-edge coordinates are a left inverse. -/
private theorem completePathToTourLinearMap_injective {m : ℕ} :
    Function.Injective (completePathToTourLinearMap m) := by
  intro x y hxy
  -- Comparing the copied old-edge coordinates already recovers the original source vector.
  ext e
  have hcoord :
      completePathToTourLinearMap m x (oldEdgeEmb e) =
        completePathToTourLinearMap m y (oldEdgeEmb e) := by
    simpa using congrArg (fun z : complete_graph_edges (m + 1) → ℝ ↦ z (oldEdgeEmb e)) hxy
  simpa [completePathToTourLinearMap_apply_oldEdgeEmb] using hcoord

/-- Helper for Theorem 7.18: old-edge incidence is preserved under the embedding
`K_m ↪ K_{m+1}`. -/
private theorem oldEdgeEmb_mem_completeGraphIncidentEdgeFinset_iff
    {m : ℕ} {i : Fin m} {e : complete_graph_edges m} :
    oldEdgeEmb e ∈ completeGraphIncidentEdgeFinset (m + 1) (Fin.castSucc i) ↔
      e ∈ completeGraphIncidentEdgeFinset m i := by
  -- The embedded old edge is incident to `castSucc i` exactly when the original edge is incident
  -- to `i`.
  rw [mem_completeGraphIncidentEdgeFinset_iff, mem_completeGraphIncidentEdgeFinset_iff, oldEdgeEmb]
  constructor
  · intro h
    rw [Sym2.mem_map] at h
    rcases h with ⟨a, ha, ha'⟩
    have hai : a = i := Fin.ext (by simpa using congrArg (fun z : Fin (m + 1) ↦ z.1) ha')
    simpa [hai] using ha
  · intro h
    rw [Sym2.mem_map]
    exact ⟨i, h, rfl⟩

/-- Helper for Theorem 7.18: a star edge is incident to `castSucc i` exactly when it is the star
edge anchored at `i`. -/
private theorem newVertexEdge_mem_completeGraphIncidentEdgeFinset_castSucc_iff
    {m : ℕ} {i j : Fin m} :
    newVertexEdge j ∈ completeGraphIncidentEdgeFinset (m + 1) (Fin.castSucc i) ↔ i = j := by
  -- Among the star edges, only the one attached to `i` meets `castSucc i`.
  rw [mem_completeGraphIncidentEdgeFinset_iff, newVertexEdge]
  constructor
  · intro h
    rcases (Sym2.mem_iff.mp h) with hEq | hEq
    · exact Fin.ext (by simpa using congrArg (fun z : Fin (m + 1) ↦ z.1) hEq)
    · exact False.elim ((Fin.castSucc_ne_last i) hEq)
  · intro h
    simp [Sym2.mem_iff, h]

/-- Helper for Theorem 7.18: no embedded old edge is incident to the new last vertex. -/
private theorem oldEdgeEmb_not_mem_completeGraphIncidentEdgeFinset_last
    {m : ℕ} {e : complete_graph_edges m} :
    oldEdgeEmb e ∉ completeGraphIncidentEdgeFinset (m + 1) (Fin.last m) := by
  -- The old-edge embedding never creates an endpoint at the new last vertex.
  rw [mem_completeGraphIncidentEdgeFinset_iff, oldEdgeEmb]
  intro h
  rw [Sym2.mem_map] at h
  rcases h with ⟨a, -, ha⟩
  exact Fin.castSucc_ne_last a ha

/-- Helper for Theorem 7.18: every star edge is incident to the new last vertex. -/
private theorem newVertexEdge_mem_completeGraphIncidentEdgeFinset_last
    {m : ℕ} (i : Fin m) :
    newVertexEdge i ∈ completeGraphIncidentEdgeFinset (m + 1) (Fin.last m) := by
  -- The new last vertex is one endpoint of every star edge by definition.
  rw [mem_completeGraphIncidentEdgeFinset_iff, newVertexEdge]
  simp [Sym2.mem_iff]

/-- Helper for Theorem 7.18: summing the incident-edge sums over all old vertices double-counts
each old edge. -/
private theorem sum_completeGraphIncidentEdgeFinset_sum_eq_twice
    {m : ℕ} (x : complete_graph_edges m → ℝ) :
    ∑ i : Fin m, (completeGraphIncidentEdgeFinset m i).sum x = 2 * ∑ e, x e := by
  -- Rewrite each incident sum as a complete-graph indicator sum, swap summations, and count the
  -- two endpoints of each non-diagonal edge.
  calc
    ∑ i : Fin m, (completeGraphIncidentEdgeFinset m i).sum x =
        ∑ i : Fin m,
          (Finset.univ : Finset (complete_graph_edges m)).sum
            (fun e ↦ if i ∈ (e : Sym2 (Fin m)) then x e else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          calc
            (completeGraphIncidentEdgeFinset m i).sum x =
                (Finset.univ : Finset (complete_graph_edges m)).sum
                  (fun e ↦ if e ∈ completeGraphIncidentEdgeFinset m i then x e else 0) := by
                    simpa using
                      (complete_graph_sum_ite_eq_sum_filter
                        (p := fun e : complete_graph_edges m ↦ e ∈ completeGraphIncidentEdgeFinset m i)
                        (f := x)).symm
            _ = (Finset.univ : Finset (complete_graph_edges m)).sum
                  (fun e ↦ if i ∈ (e : Sym2 (Fin m)) then x e else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro e he
                    by_cases hm : e ∈ completeGraphIncidentEdgeFinset m i
                    · have hi_mem : i ∈ (e : Sym2 (Fin m)) :=
                        (mem_completeGraphIncidentEdgeFinset_iff (i := i) (e := e)).1 hm
                      simp [hm, hi_mem]
                    · have hi_mem : i ∉ (e : Sym2 (Fin m)) := by
                        intro hi_mem
                        exact hm ((mem_completeGraphIncidentEdgeFinset_iff (i := i) (e := e)).2 hi_mem)
                      simp [hm, hi_mem]
    _ = (Finset.univ : Finset (complete_graph_edges m)).sum
          (fun e ↦ ∑ i : Fin m, if i ∈ (e : Sym2 (Fin m)) then x e else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ e : complete_graph_edges m, (2 : ℝ) * x e := by
          refine Finset.sum_congr rfl ?_
          intro e he
          calc
            (∑ i : Fin m, if i ∈ (e : Sym2 (Fin m)) then x e else 0) =
                ((((e : Sym2 (Fin m)).toFinset).card : ℕ) : ℝ) * x e := by
                  calc
                    (∑ i : Fin m, if i ∈ (e : Sym2 (Fin m)) then x e else 0) =
                        Finset.sum ((e : Sym2 (Fin m)).toFinset) (fun _ ↦ x e) := by
                          have htoFinset :
                              (e : Sym2 (Fin m)).toFinset =
                                (Finset.univ.filter fun i : Fin m ↦ i ∈ (e : Sym2 (Fin m))) := by
                            ext i
                            simp [Sym2.mem_toFinset]
                          rw [htoFinset, Finset.sum_filter]
                    _ = ((((e : Sym2 (Fin m)).toFinset).card : ℕ) : ℝ) * x e := by
                          simp
            _ = (2 : ℝ) * x e := by
                  have hcardNat : ((e : Sym2 (Fin m)).toFinset).card = 2 := by
                    simpa using Sym2.card_toFinset_of_not_isDiag (e : Sym2 (Fin m)) e.2
                  norm_num [hcardNat]
    _ = 2 * ∑ e, x e := by
          simpa using (Finset.mul_sum (s := (Finset.univ : Finset (complete_graph_edges m)))
            (a := (2 : ℝ)) (f := x)).symm

/-- Helper for Theorem 7.18: the injective completion affine map preserves the affine-span
dimension of image sets. -/
private theorem completePathToTourAffineMap_image_finrank_direction_affineSpan
    {m : ℕ} {s : Set (complete_graph_edges m → ℝ)} :
    Module.finrank ℝ
        (affineSpan ℝ (completePathToTourAffineMap m '' s)).direction =
      Module.finrank ℝ (affineSpan ℝ s).direction := by
  let F := completePathToTourAffineMap m
  have hmap :
      affineSpan ℝ (F '' s) = AffineSubspace.map F (affineSpan ℝ s) := by
    -- The affine span of an affine image is the affine image of the affine span.
    symm
    simpa [F] using (AffineSubspace.map_span F s)
  rw [hmap, AffineSubspace.map_direction]
  let e :
      (affineSpan ℝ s).direction ≃ₗ[ℝ] Submodule.map F.linear (affineSpan ℝ s).direction :=
    Submodule.equivMapOfInjective F.linear
      (by simpa [F, completePathToTourAffineMap] using completePathToTourLinearMap_injective)
      (affineSpan ℝ s).direction
  simpa [e] using (LinearEquiv.finrank_eq e).symm

/-- Helper for Theorem 7.18: the three-edge witness sends the degree map to the basis vector at
the distinguished vertex `a`. -/
private theorem travelingSalesmanDegreeMap_threeEdgeWitness
    {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    travelingSalesmanDegreeMap n
      ((1 / 2 : ℝ) •
        (Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween a b hab) +
          Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween a c hac) -
            Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween b c hbc))) =
      Pi.basisFun ℝ (Fin n) a := by
  -- At `a` the two positive incident edges contribute `2`, at `b` and `c` the positive and
  -- negative terms cancel, and every other vertex sees no incident edge from the witness.
  ext v
  simp only [LinearMap.map_smul, LinearMap.map_add, LinearMap.map_sub, Pi.smul_apply,
    Pi.add_apply, Pi.sub_apply, travelingSalesmanDegreeMap_apply_basisFun]
  by_cases hva : v = a
  · subst hva
    simp [mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, hab, hac, hbc, Pi.basisFun]
    norm_num
  · by_cases hvb : v = b
    · subst hvb
      simp [mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, hab, hac, hbc, hva, Pi.basisFun]
    · by_cases hvc : v = c
      · subst hvc
        simp [mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, hab, hac, hbc, hva, hvb,
          Pi.basisFun]
      · simp [travelingSalesmanDegreeMap_apply, travelingSalesmanDegreeMap_apply_basisFun,
          mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, hab, hac, hbc, hva, hvb, hvc,
          Pi.basisFun]

/-- Helper for Theorem 7.18: every standard basis vector of `Fin n → ℝ` lies in the range of the
traveling-salesman degree map once `n ≥ 3`. -/
private theorem travelingSalesmanDegreeMap_basisFun_mem_range
    {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    Pi.basisFun ℝ (Fin n) i ∈ LinearMap.range (travelingSalesmanDegreeMap n) := by
  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  let v2 : Fin n := ⟨2, by omega⟩
  have hv01 : v0 ≠ v1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [v0, v1] at hval
  have hv02 : v0 ≠ v2 := by
    intro h
    have hval := congrArg Fin.val h
    simp [v0, v2] at hval
  have hv12 : v1 ≠ v2 := by
    intro h
    have hval := congrArg Fin.val h
    simp [v1, v2] at hval
  by_cases hi0 : i = v0
  · subst hi0
    refine ⟨(1 / 2 : ℝ) •
      (Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween v0 v1 hv01) +
        Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween v0 v2 hv02) -
          Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween v1 v2 hv12)), ?_⟩
    simpa [v0, v1, v2] using
      travelingSalesmanDegreeMap_threeEdgeWitness (a := v0) (b := v1) (c := v2)
        hv01 hv02 hv12
  · by_cases hi1 : i = v1
    · subst hi1
      refine ⟨(1 / 2 : ℝ) •
        (Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween v1 v0 hv01.symm) +
          Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween v1 v2 hv12) -
            Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween v0 v2 hv02)), ?_⟩
      simpa [v0, v1, v2] using
        travelingSalesmanDegreeMap_threeEdgeWitness (a := v1) (b := v0) (c := v2)
          hv01.symm hv12 hv02
    · refine ⟨(1 / 2 : ℝ) •
        (Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween i v0 hi0) +
          Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween i v1 hi1) -
            Pi.basisFun ℝ (complete_graph_edges n) (edgeBetween v0 v1 hv01)), ?_⟩
      simpa [v0, v1] using
        travelingSalesmanDegreeMap_threeEdgeWitness (a := i) (b := v0) (c := v1)
          hi0 hi1 hv01

/-- Helper for Theorem 7.18: the kernel of the degree map has the expected codimension `n`. -/
private theorem travelingSalesmanDegreeMap_ker_finrank
    (n : ℕ) (hn : 3 ≤ n) :
    Module.finrank ℝ (LinearMap.ker (travelingSalesmanDegreeMap n)) = Nat.choose n 2 - n := by
  classical
  have hsurj : Function.Surjective (travelingSalesmanDegreeMap n) := by
    -- Summing basis-vector preimages recovers an arbitrary target vector.
    intro y
    have hbasis :
        ∀ i : Fin n, ∃ x, travelingSalesmanDegreeMap n x = Pi.basisFun ℝ (Fin n) i := by
      intro i
      simpa [LinearMap.mem_range] using travelingSalesmanDegreeMap_basisFun_mem_range hn i
    choose x hx using hbasis
    refine ⟨∑ i : Fin n, y i • x i, ?_⟩
    ext i
    calc
      travelingSalesmanDegreeMap n (∑ j : Fin n, y j • x j) i =
          ∑ j : Fin n, y j * travelingSalesmanDegreeMap n (x j) i := by
            simp
      _ = ∑ j : Fin n, y j * Pi.basisFun ℝ (Fin n) j i := by
            simp [hx]
      _ = y i := by
            simpa [Pi.basisFun, Pi.smul_apply] using
              congrArg (fun f : Fin n → ℝ ↦ f i) ((Pi.basisFun ℝ (Fin n)).sum_repr y)
  have hrange :
      LinearMap.range (travelingSalesmanDegreeMap n) = ⊤ := by
    exact LinearMap.range_eq_top.2 hsurj
  have hfinrank :=
    LinearMap.finrank_range_add_finrank_ker (travelingSalesmanDegreeMap n)
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    at hfinrank
  rw [card_complete_graph_edges] at hfinrank
  have hfinrank' :
      n + Module.finrank ℝ (LinearMap.ker (travelingSalesmanDegreeMap n)) = Nat.choose n 2 := by
    simpa using hfinrank
  rw [Nat.add_comm] at hfinrank'
  exact Nat.eq_sub_of_add_eq hfinrank'

/-- Helper for Theorem 7.18: once one tour vector satisfies the degree equations, the whole degree
slice is the affine translate of the degree-map kernel through that vector. -/
private theorem travelingSalesmanDegreeConstraintSet_eq_affineTranslate
    {n : ℕ} {x₀ : complete_graph_edges n → ℝ}
    (hx₀ : x₀ ∈ travelingSalesmanDegreeConstraintSet n) :
    travelingSalesmanDegreeConstraintSet n =
      (AffineSubspace.mk' x₀ (LinearMap.ker (travelingSalesmanDegreeMap n)) :
        Set (complete_graph_edges n → ℝ)) := by
  have hx₀_degree : travelingSalesmanDegreeMap n x₀ = fun _ ↦ (2 : ℝ) :=
    mem_travelingSalesmanDegreeConstraintSet_iff_degreeMap.mp hx₀
  ext x
  constructor
  · intro hx
    -- Matching degree right-hand sides makes the difference land in the kernel.
    change x - x₀ ∈ LinearMap.ker (travelingSalesmanDegreeMap n)
    have hx_degree : travelingSalesmanDegreeMap n x = fun _ ↦ (2 : ℝ) :=
      mem_travelingSalesmanDegreeConstraintSet_iff_degreeMap.mp hx
    show travelingSalesmanDegreeMap n (x - x₀) = 0
    rw [LinearMap.map_sub, hx_degree, hx₀_degree, sub_self]
  · intro hx
    -- Conversely, a kernel difference preserves the constant degree vector `2`.
    change x - x₀ ∈ LinearMap.ker (travelingSalesmanDegreeMap n) at hx
    change travelingSalesmanDegreeMap n (x - x₀) = 0 at hx
    rw [LinearMap.map_sub, hx₀_degree] at hx
    have hx_degree : travelingSalesmanDegreeMap n x = fun _ ↦ (2 : ℝ) := sub_eq_zero.mp hx
    exact mem_travelingSalesmanDegreeConstraintSet_iff_degreeMap.mpr hx_degree

/-- Helper for Theorem 7.18: extend a path permutation by fixing the new last vertex. -/
private def completePathToTourPerm {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m + 1)) where
  toFun := Fin.lastCases (Fin.last m) (fun i ↦ Fin.castSucc (σ i))
  invFun := Fin.lastCases (Fin.last m) (fun i ↦ Fin.castSucc (σ.symm i))
  left_inv := by
    -- Evaluate the extension on the old vertices and on the new last vertex separately.
    intro i
    cases i using Fin.lastCases with
    | last =>
        simp [Fin.lastCases]
    | cast i =>
        simp [Fin.lastCases]
  right_inv := by
    -- The inverse has the same shape, so the two cases close by the same simplification.
    intro i
    cases i using Fin.lastCases with
    | last =>
        simp [Fin.lastCases]
    | cast i =>
        simp [Fin.lastCases]

/-- Helper for Theorem 7.18: the completion permutation agrees with `σ` on the old vertices. -/
private theorem completePathToTourPerm_apply_castSucc
    {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    completePathToTourPerm σ (Fin.castSucc i) = Fin.castSucc (σ i) := by
  -- On old vertices, the extension is just `σ` followed by `castSucc`.
  simp [completePathToTourPerm]

/-- Helper for Theorem 7.18: the completion permutation fixes the new last vertex. -/
private theorem completePathToTourPerm_apply_last
    {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    completePathToTourPerm σ (Fin.last m) = Fin.last m := by
  -- The completion keeps the new vertex fixed so it can close the path into a tour.
  simp [completePathToTourPerm]

/-- Helper for Theorem 7.18: the completion permutation sends `0` to the embedded image of `σ 0`. -/
private theorem completePathToTourPerm_apply_zero
    {m : ℕ} (σ : Equiv.Perm (Fin (m + 2))) :
    completePathToTourPerm σ 0 = Fin.castSucc (σ 0) := by
  simpa using completePathToTourPerm_apply_castSucc σ (0 : Fin (m + 2))

/-- Helper for Theorem 7.18: a path edge is incident exactly to its two consecutive permutation
vertices. -/
private theorem pathEdgeOfIndex_mem_completeGraphIncidentEdgeFinset_iff
    {m : ℕ} (σ : Equiv.Perm (Fin m)) (k : Fin (m - 1)) (v : Fin m) :
    path_edge_of_index σ k ∈ completeGraphIncidentEdgeFinset m v ↔
      v = σ ⟨k.1, by
        have hk : k.1 < m - 1 := k.2
        omega⟩ ∨
        v = σ ⟨k.1 + 1, by
          have hk : k.1 < m - 1 := k.2
          omega⟩ := by
  -- Unfold the edge coordinate and read the two endpoints directly from the unordered pair.
  rw [mem_completeGraphIncidentEdgeFinset_iff]
  change
    v ∈
        (s(σ ⟨k.1, by
            have hk : k.1 < m - 1 := k.2
            omega⟩, σ ⟨k.1 + 1, by
            have hk : k.1 < m - 1 := k.2
            omega⟩) : Sym2 (Fin m)) ↔
      v = σ ⟨k.1, by
        have hk : k.1 < m - 1 := k.2
        omega⟩ ∨
        v = σ ⟨k.1 + 1, by
          have hk : k.1 < m - 1 := k.2
          omega⟩
  simp [Sym2.mem_iff, eq_comm, or_left_comm, or_assoc]

/-- Helper for Theorem 7.18: every path-incidence vertex has degree `1` at the two endpoints and
degree `2` at the interior vertices. -/
private theorem hamiltonianPathIncidenceVector_incidentSum
    {m : ℕ} (hm : 2 ≤ m) (σ : Equiv.Perm (Fin m)) (v : Fin m) :
    (completeGraphIncidentEdgeFinset m v).sum (hamiltonian_path_incidence_vector σ) =
      if v = σ ⟨0, by omega⟩ ∨ v = σ ⟨m - 1, by omega⟩ then 1 else 2 := by
  classical
  have hfirst_lt : 0 < m := by
    omega
  let first : Fin m := ⟨0, hfirst_lt⟩
  have hlast_lt : m - 1 < m := by
    omega
  let last : Fin m := ⟨m - 1, hlast_lt⟩
  let p : Fin m := σ.symm v
  have hpv : σ p = v := by
    simp [p]
  have hsum :
      (completeGraphIncidentEdgeFinset m v).sum (hamiltonian_path_incidence_vector σ) =
        (((Finset.univ.filter fun k : Fin (m - 1) =>
            k.1 = p.1 ∨ k.1 + 1 = p.1).card : ℕ) : ℝ) := by
    -- Count incident path edges by pulling the edge-image finset back to the consecutive indices.
    calc
      (completeGraphIncidentEdgeFinset m v).sum (hamiltonian_path_incidence_vector σ) =
          ((((completeGraphIncidentEdgeFinset m v ∩ hamiltonian_path_edge_finset σ).card : ℕ) :
            ℝ)) := by
            simp [hamiltonian_path_incidence_vector]
      _ =
          ((((hamiltonian_path_edge_finset σ).filter
              fun e ↦ e ∈ completeGraphIncidentEdgeFinset m v).card : ℕ) : ℝ) := by
            refine congrArg (fun s : Finset (complete_graph_edges m) => (((s.card : ℕ) : ℝ))) ?_
            ext e
            simp [Finset.mem_inter, and_comm, and_left_comm, and_assoc]
      _ =
          ((((Finset.univ.filter fun k : Fin (m - 1) =>
                path_edge_of_index σ k ∈ completeGraphIncidentEdgeFinset m v).image
                (path_edge_of_index σ)).card : ℕ) : ℝ) := by
            rw [hamiltonian_path_edge_finset, Finset.filter_image]
      _ =
          (((Finset.univ.filter fun k : Fin (m - 1) =>
                path_edge_of_index σ k ∈ completeGraphIncidentEdgeFinset m v).card : ℕ) : ℝ) := by
            rw [Finset.card_image_of_injective _ (path_edge_of_index_injective σ)]
      _ =
          (((Finset.univ.filter fun k : Fin (m - 1) =>
                k.1 = p.1 ∨ k.1 + 1 = p.1).card : ℕ) : ℝ) := by
            refine congrArg (fun s : Finset (Fin (m - 1)) => (((s.card : ℕ) : ℝ))) ?_
            ext k
            simp [pathEdgeOfIndex_mem_completeGraphIncidentEdgeFinset_iff]
            constructor
            · intro hk
              rcases hk with hk | hk
              · left
                simpa using (congrArg Fin.val (σ.injective (hpv.trans hk))).symm
              · right
                simpa using (congrArg Fin.val (σ.injective (hpv.trans hk))).symm
            · intro hk
              rcases hk with hk | hk
              · left
                have hpEq : p = k.castLT (Nat.lt_of_lt_of_le k.2 (Nat.sub_le _ _)) := by
                  apply Fin.ext
                  exact hk.symm
                simpa [p, hpEq] using hpv.symm
              · right
                have hklt : k.1 + 1 < m := by
                  have hk' : k.1 < m - 1 := k.2
                  omega
                have hpEq : p = ⟨k.1 + 1, hklt⟩ := by
                  apply Fin.ext
                  exact hk.symm
                simpa [p, hpEq] using hpv.symm
  by_cases hp0 : p = first
  · -- At the first permutation position, exactly the first path edge is incident to `v`.
    have hp0_val : p.1 = 0 := by
      simpa [first] using congrArg Fin.val hp0
    have hfilter :
        Finset.univ.filter (fun k : Fin (m - 1) => k.1 = p.1 ∨ k.1 + 1 = p.1) =
          {⟨0, by omega⟩} := by
      ext k
      simp [hp0_val]
      constructor
      · intro hk
        apply Fin.ext
        omega
      · intro hk
        simpa using congrArg Fin.val hk
    have hcard :
        (((Finset.univ.filter fun k : Fin (m - 1) => k.1 = p.1 ∨ k.1 + 1 = p.1).card : ℕ) : ℝ) =
          1 := by
      rw [hfilter]
      norm_num
    rw [hsum, if_pos]
    · exact hcard
    · left
      simpa [first, hp0] using hpv.symm
  · by_cases hplast : p = last
    · -- At the last permutation position, exactly the final path edge is incident to `v`.
      have hplast_val : p.1 = m - 1 := by
        simpa [last] using congrArg Fin.val hplast
      have hfilter :
          Finset.univ.filter (fun k : Fin (m - 1) => k.1 = p.1 ∨ k.1 + 1 = p.1) =
            {⟨m - 2, by omega⟩} := by
        ext k
        simp [hplast_val]
        constructor
        · intro hk
          rcases hk with hk | hk
          · have hklt : k.1 < m - 1 := k.2
            have : False := by omega
            exact False.elim this
          · have hk_val : k.1 = m - 2 := by omega
            exact Fin.ext hk_val
        · intro hk
          have hk_val : k.1 = m - 2 := by
            simpa using congrArg Fin.val hk
          right
          omega
      have hcard :
          (((Finset.univ.filter fun k : Fin (m - 1) => k.1 = p.1 ∨ k.1 + 1 = p.1).card : ℕ) : ℝ) =
            1 := by
        rw [hfilter]
        norm_num
      rw [hsum, if_pos]
      · exact hcard
      · right
        simpa [last, hplast] using hpv.symm
    · -- In the interior, the incident path edges are exactly the predecessor and successor edges.
      have hp_ne_zero : p.1 ≠ 0 := by
        intro hp_eq_zero
        apply hp0
        apply Fin.ext
        simpa [first] using hp_eq_zero
      have hp_ne_last : p.1 ≠ m - 1 := by
        intro hp_eq_last
        apply hplast
        apply Fin.ext
        simpa [last] using hp_eq_last
      have hp_pos : 0 < p.1 := by
        omega
      have hp_lt_last : p.1 < m - 1 := by
        omega
      let leftEdge : Fin (m - 1) := ⟨p.1 - 1, by omega⟩
      let rightEdge : Fin (m - 1) := ⟨p.1, hp_lt_last⟩
      have hfilter :
          Finset.univ.filter (fun k : Fin (m - 1) => k.1 = p.1 ∨ k.1 + 1 = p.1) =
            {leftEdge, rightEdge} := by
        ext k
        simp [leftEdge, rightEdge]
        constructor
        · intro hk
          rcases hk with hk | hk
          · right
            apply Fin.ext
            exact hk
          · left
            have hklt : k.1 < m - 1 := k.2
            have hk_val : k.1 = p.1 - 1 := by omega
            exact Fin.ext hk_val
        · intro hk
          rcases hk with hk | hk
          · right
            have hk_val : k.1 = p.1 - 1 := by
              simpa using congrArg Fin.val hk
            omega
          · left
            exact congrArg Fin.val hk
      have hne : leftEdge ≠ rightEdge := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [leftEdge, rightEdge] at hval
        exact hp_ne_zero (by omega)
      have hend_false :
          ¬ (v = σ ⟨0, by omega⟩ ∨ v = σ ⟨m - 1, by omega⟩) := by
        intro hend
        rcases hend with hv0 | hvlast
        · exact hp0 (σ.injective (hpv.trans hv0))
        · exact hplast (σ.injective (hpv.trans hvlast))
      rw [hsum, if_neg hend_false, hfilter]
      simp [hne]

/-- Helper for Theorem 7.18: completing a path incidence vector puts `1` exactly on the two star
edges corresponding to the path endpoints. -/
private theorem completePathToTourAffineMap_apply_hamiltonianPathIncidence_newVertexEdge
    {m : ℕ} (hm : 2 ≤ m) (σ : Equiv.Perm (Fin m)) (v : Fin m) :
    completePathToTourAffineMap m (hamiltonian_path_incidence_vector σ) (newVertexEdge v) =
      if v = σ ⟨0, by omega⟩ ∨ v = σ ⟨m - 1, by omega⟩ then 1 else 0 := by
  -- Route correction: compute the star coordinate through the endpoint-degree formula for the
  -- source Hamiltonian path, rather than reopening the abandoned global slice-image route.
  rw [completePathToTourAffineMap_apply_newVertexEdge]
  rw [hamiltonianPathIncidenceVector_incidentSum hm σ v]
  split_ifs <;> norm_num

/-- Helper for Theorem 7.18: every edge of the enlarged complete graph is either an embedded old
edge or a star edge at the new last vertex. -/
private theorem completeGraphEdge_eq_oldEdgeEmb_or_newVertexEdge
    {m : ℕ} (e : complete_graph_edges (m + 1)) :
    (∃ e0 : complete_graph_edges m, oldEdgeEmb e0 = e) ∨ ∃ i : Fin m, newVertexEdge i = e := by
  rcases e with ⟨z, hz⟩
  have hz_repr : ∃ a b : Fin (m + 1), z = s(a, b) := by
    rw [← Sym2.exists]
    exact ⟨z, rfl⟩
  rcases hz_repr with ⟨a, b, rfl⟩
  by_cases hlast : (Fin.last m : Fin (m + 1)) ∈ (s(a, b) : Sym2 (Fin (m + 1)))
  · -- If the new last vertex is an endpoint, the edge is one of the star coordinates.
    simp [Sym2.mem_iff] at hlast
    rcases hlast with ha | hb
    · cases b using Fin.lastCases with
      | last =>
          exact False.elim <| hz (by simp [ha])
      | cast i =>
          right
          refine ⟨i, ?_⟩
          apply Subtype.ext
          simp [newVertexEdge, ha]
    · cases a using Fin.lastCases with
      | last =>
          exact False.elim <| hz (by simp [hb])
      | cast i =>
          right
          refine ⟨i, ?_⟩
          apply Subtype.ext
          simp [newVertexEdge, hb]
  · -- Otherwise both endpoints come from `Fin.castSucc`, so the edge is an embedded old edge.
    have ha_ne_last : a ≠ Fin.last m := by
      intro ha
      exact hlast (by simpa [ha, Sym2.mem_iff])
    have hb_ne_last : b ≠ Fin.last m := by
      intro hb
      exact hlast (by simpa [hb, Sym2.mem_iff])
    cases a using Fin.lastCases with
    | last =>
        exact False.elim (ha_ne_last rfl)
    | cast i =>
        cases b using Fin.lastCases with
        | last =>
            exact False.elim (hb_ne_last rfl)
        | cast j =>
            have hij : i ≠ j := by
              intro hij
              apply hz
              rw [Sym2.mk_isDiag_iff]
              simpa [hij]
            have hnotdiag0 : ¬ (s(i, j) : Sym2 (Fin m)).IsDiag := by
              rw [Sym2.mk_isDiag_iff]
              exact hij
            let e0 : complete_graph_edges m := ⟨s(i, j), hnotdiag0⟩
            left
            refine ⟨e0, ?_⟩
            apply Subtype.ext
            simp [e0, oldEdgeEmb]

/-- Helper for Theorem 7.18: an embedded old edge belongs to the completed tour exactly when the
original edge belongs to the original path. -/
private theorem oldEdgeEmb_mem_hamiltonianTourEdgeFinset_completePathToTourPerm_iff
    {m : ℕ} (σ : Equiv.Perm (Fin (m + 2))) (e : complete_graph_edges (m + 2)) :
    oldEdgeEmb e ∈ hamiltonian_tour_edge_finset (completePathToTourPerm σ) ↔
      e ∈ hamiltonian_path_edge_finset σ := by
  let first : Fin (m + 2) := ⟨0, by omega⟩
  have hclosingEq :
      hamiltonian_tour_closing_edge (n := m + 1) (completePathToTourPerm σ) =
        newVertexEdge (σ first) := by
    have hlastPos : hamiltonian_tour_last_position (m + 1) = Fin.last (m + 2) := by
      apply Fin.ext
      simp [hamiltonian_tour_last_position]
    apply Subtype.ext
    simp only [hamiltonian_tour_closing_edge, newVertexEdge, Sym2.eq_iff]
    left
    constructor
    · simpa [first] using completePathToTourPerm_apply_zero (m := m) σ
    · simpa [hlastPos] using completePathToTourPerm_apply_last (m := m + 2) σ
  have hnotClosing :
      oldEdgeEmb e ≠ hamiltonian_tour_closing_edge (n := m + 1) (completePathToTourPerm σ) := by
    intro h
    have hlast_mem :
        hamiltonian_tour_closing_edge (n := m + 1) (completePathToTourPerm σ) ∈
          completeGraphIncidentEdgeFinset (m + 3) (Fin.last (m + 2)) := by
      simpa [hclosingEq] using newVertexEdge_mem_completeGraphIncidentEdgeFinset_last (σ first)
    exact oldEdgeEmb_not_mem_completeGraphIncidentEdgeFinset_last (e := e) (h ▸ hlast_mem)
  have hpathCast :
      ∀ k0 : Fin (m + 1),
        path_edge_of_index (completePathToTourPerm σ) k0.castSucc =
          oldEdgeEmb (path_edge_of_index σ k0) := by
    intro k0
    -- For the old positions, the completed permutation just applies `σ` and then embeds.
    apply Subtype.ext
    simp only [path_edge_of_index, oldEdgeEmb, Sym2.map_mk, Sym2.eq_iff]
    left
    constructor
    · change completePathToTourPerm σ (Fin.castSucc k0.castSucc) =
          Fin.castSucc (σ k0.castSucc)
      simpa using completePathToTourPerm_apply_castSucc σ k0.castSucc
    · change completePathToTourPerm σ (Fin.castSucc k0.succ) =
          Fin.castSucc (σ k0.succ)
      simpa using completePathToTourPerm_apply_castSucc σ k0.succ
  have hpathLast :
      path_edge_of_index (completePathToTourPerm σ) (Fin.last (m + 1)) =
        newVertexEdge (σ (Fin.last (m + 1))) := by
    -- The last path edge in the completed path is the star edge from the last old endpoint to
    -- the new vertex.
    apply Subtype.ext
    simp only [path_edge_of_index, newVertexEdge, Sym2.eq_iff]
    left
    constructor
    · change completePathToTourPerm σ (Fin.castSucc (Fin.last (m + 1))) =
          Fin.castSucc (σ (Fin.last (m + 1)))
      simpa using completePathToTourPerm_apply_castSucc σ (Fin.last (m + 1))
    · change completePathToTourPerm σ (Fin.last (m + 2)) = Fin.last (m + 2)
      simpa using completePathToTourPerm_apply_last (m := m + 2) σ
  rw [hamiltonian_tour_edge_finset]
  simp [hnotClosing]
  constructor
  · intro h
    have hpath : is_hamiltonian_path_edge (completePathToTourPerm σ) (oldEdgeEmb e) := by
      simpa [is_hamiltonian_path_edge] using h
    rw [is_hamiltonian_path_edge_iff_exists_index] at hpath
    rcases hpath with ⟨k, hk⟩
    by_cases hlastk : k = Fin.last (m + 1)
    · have hnew :
          oldEdgeEmb e = newVertexEdge (σ (Fin.last (m + 1))) := by
        calc
          oldEdgeEmb e = path_edge_of_index (completePathToTourPerm σ) k := hk.symm
          _ = path_edge_of_index (completePathToTourPerm σ) (Fin.last (m + 1)) := by
                simpa [hlastk]
          _ = newVertexEdge (σ (Fin.last (m + 1))) := hpathLast
      exact False.elim (oldEdgeEmb_ne_newVertexEdge e _ hnew)
    · have hklt : k.1 < m + 1 := by
        have hk_ne_last : k.1 ≠ m + 1 := by
          intro hk_eq_last
          apply hlastk
          apply Fin.ext
          simpa using hk_eq_last
        omega
      let k0 : Fin (m + 1) := k.castLT hklt
      have hkCast :
          path_edge_of_index (completePathToTourPerm σ) k =
            oldEdgeEmb (path_edge_of_index σ k0) := by
        simpa [k0, Fin.castSucc_castLT] using hpathCast k0
      have hk0' : path_edge_of_index σ k0 = e := oldEdgeEmb_injective (hkCast.symm.trans hk)
      exact (is_hamiltonian_path_edge_iff_exists_index σ e).2 ⟨k0, hk0'⟩
  · intro h
    have hpath : is_hamiltonian_path_edge σ e := by
      simpa [is_hamiltonian_path_edge] using h
    rw [is_hamiltonian_path_edge_iff_exists_index] at hpath
    rcases hpath with ⟨k0, hk0⟩
    have hpath' :
        ∃ k : Fin (m + 2), path_edge_of_index (completePathToTourPerm σ) k = oldEdgeEmb e := by
      refine ⟨k0.castSucc, ?_⟩
      calc
        path_edge_of_index (completePathToTourPerm σ) k0.castSucc =
            oldEdgeEmb (path_edge_of_index σ k0) := hpathCast k0
        _ = oldEdgeEmb e := by simpa [hk0]
    exact (is_hamiltonian_path_edge_iff_exists_index _ _).2 hpath'

/-- Helper for Theorem 7.18: a star edge belongs to the completed tour exactly when it is one of
the two endpoint star edges. -/
private theorem newVertexEdge_mem_hamiltonianTourEdgeFinset_completePathToTourPerm_iff
    {m : ℕ} (σ : Equiv.Perm (Fin (m + 2))) (j : Fin (m + 2)) :
    newVertexEdge j ∈ hamiltonian_tour_edge_finset (completePathToTourPerm σ) ↔
      j = σ ⟨0, by omega⟩ ∨ j = σ ⟨m + 1, by omega⟩ := by
  let first : Fin (m + 2) := ⟨0, by omega⟩
  let last : Fin (m + 2) := ⟨m + 1, by omega⟩
  have hpathCast :
      ∀ k0 : Fin (m + 1),
        path_edge_of_index (completePathToTourPerm σ) k0.castSucc =
          oldEdgeEmb (path_edge_of_index σ k0) := by
    intro k0
    -- The old consecutive edges of the path stay inside the embedded old complete graph.
    apply Subtype.ext
    simp only [path_edge_of_index, oldEdgeEmb, Sym2.map_mk, Sym2.eq_iff]
    left
    constructor
    · change completePathToTourPerm σ (Fin.castSucc k0.castSucc) =
          Fin.castSucc (σ k0.castSucc)
      simpa using completePathToTourPerm_apply_castSucc σ k0.castSucc
    · change completePathToTourPerm σ (Fin.castSucc k0.succ) =
          Fin.castSucc (σ k0.succ)
      simpa using completePathToTourPerm_apply_castSucc σ k0.succ
  have hpathLast :
      path_edge_of_index (completePathToTourPerm σ) (Fin.last (m + 1)) =
        newVertexEdge (σ last) := by
    -- The final completed-path edge is the star edge from the last old endpoint to the new
    -- vertex.
    apply Subtype.ext
    simp only [path_edge_of_index, newVertexEdge, Sym2.eq_iff]
    left
    constructor
    · change completePathToTourPerm σ (Fin.castSucc (Fin.last (m + 1))) =
          Fin.castSucc (σ last)
      simpa [last] using completePathToTourPerm_apply_castSucc σ (Fin.last (m + 1))
    · change completePathToTourPerm σ (Fin.last (m + 2)) = Fin.last (m + 2)
      simpa using completePathToTourPerm_apply_last (m := m + 2) σ
  have hclosingEq :
      hamiltonian_tour_closing_edge (n := m + 1) (completePathToTourPerm σ) =
        newVertexEdge (σ first) := by
    -- The closing edge joins the first old endpoint to the new last vertex.
    have hlastPos : hamiltonian_tour_last_position (m + 1) = Fin.last (m + 2) := by
      apply Fin.ext
      simp [hamiltonian_tour_last_position]
    apply Subtype.ext
    simp only [hamiltonian_tour_closing_edge, newVertexEdge, Sym2.eq_iff]
    left
    constructor
    · simpa [first] using completePathToTourPerm_apply_zero (m := m) σ
    · simpa [hlastPos] using completePathToTourPerm_apply_last (m := m + 2) σ
  have hpathMem :
      newVertexEdge j ∈ hamiltonian_path_edge_finset (completePathToTourPerm σ) ↔
        j = σ last := by
    constructor
    · intro h
      have hpath : is_hamiltonian_path_edge (completePathToTourPerm σ) (newVertexEdge j) := by
        simpa [is_hamiltonian_path_edge] using h
      rw [is_hamiltonian_path_edge_iff_exists_index] at hpath
      rcases hpath with ⟨k, hk⟩
      by_cases hlastk : k = Fin.last (m + 1)
      · have hjEq :
            newVertexEdge j = newVertexEdge (σ last) := by
          calc
            newVertexEdge j = path_edge_of_index (completePathToTourPerm σ) k := hk.symm
            _ = path_edge_of_index (completePathToTourPerm σ) (Fin.last (m + 1)) := by
                  simpa [hlastk]
            _ = newVertexEdge (σ last) := hpathLast
        exact newVertexEdge_injective hjEq
      · have hklt : k.1 < m + 1 := by
          have hk_ne_last : k.1 ≠ m + 1 := by
            intro hk_eq_last
            apply hlastk
            apply Fin.ext
            simpa using hk_eq_last
          omega
        let k0 : Fin (m + 1) := k.castLT hklt
        have hkCast :
            path_edge_of_index (completePathToTourPerm σ) k =
              oldEdgeEmb (path_edge_of_index σ k0) := by
          simpa [k0, Fin.castSucc_castLT] using hpathCast k0
        have hconflict :
            oldEdgeEmb (path_edge_of_index σ k0) = newVertexEdge j := hkCast.symm.trans hk
        exact False.elim (oldEdgeEmb_ne_newVertexEdge _ _ hconflict)
    · intro hj
      have hpath :
          ∃ k : Fin (m + 2), path_edge_of_index (completePathToTourPerm σ) k = newVertexEdge j := by
        refine ⟨Fin.last (m + 1), ?_⟩
        simpa [hj] using hpathLast
      exact (is_hamiltonian_path_edge_iff_exists_index _ _).2 hpath
  have hclosingMem :
      newVertexEdge j = hamiltonian_tour_closing_edge (n := m + 1) (completePathToTourPerm σ) ↔
        j = σ first := by
    constructor
    · intro h
      have hjEq : newVertexEdge j = newVertexEdge (σ 0) := by
        simpa [first, hclosingEq] using h
      exact newVertexEdge_injective hjEq
    · intro hj
      simpa [hclosingEq, hj]
  rw [hamiltonian_tour_edge_finset]
  simp [hclosingMem, hpathMem, first, last]

/-- Helper for Theorem 7.18: completing a Hamiltonian-path vertex produces a Hamiltonian-tour
vertex. -/
private theorem completePathToTourAffineMap_pathVertex_eq_tourVertex
    {m : ℕ} (hm : 2 ≤ m) (σ : Equiv.Perm (Fin m)) :
    completePathToTourAffineMap m (hamiltonian_path_incidence_vector σ) =
      hamiltonian_tour_incidence_vector (completePathToTourPerm σ) := by
  obtain ⟨n, hn_eq⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm] at hn_eq
  subst hn_eq
  ext e
  rcases completeGraphEdge_eq_oldEdgeEmb_or_newVertexEdge e with
    (⟨e0, rfl⟩ | ⟨i, rfl⟩)
  · -- On the embedded old-edge block, completion just copies the path coordinates.
    rw [completePathToTourAffineMap_apply_oldEdgeEmb, hamiltonian_path_incidence_vector,
      hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge]
    by_cases hmem : e0 ∈ hamiltonian_path_edge_finset σ
    · have htour :
          oldEdgeEmb e0 ∈ hamiltonian_tour_edge_finset (completePathToTourPerm σ) :=
        (oldEdgeEmb_mem_hamiltonianTourEdgeFinset_completePathToTourPerm_iff (m := n) σ e0).2 hmem
      simp [hmem, htour]
    · have htour :
          oldEdgeEmb e0 ∉ hamiltonian_tour_edge_finset (completePathToTourPerm σ) := by
        intro htour
        exact hmem
          ((oldEdgeEmb_mem_hamiltonianTourEdgeFinset_completePathToTourPerm_iff (m := n) σ e0).1
            htour)
      simp [hmem, htour]
  · -- On the star block, completion records exactly the two path endpoints.
    rw [completePathToTourAffineMap_apply_hamiltonianPathIncidence_newVertexEdge hm σ i]
    rw [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge]
    by_cases hmem : i = σ 0 ∨ i = σ ⟨n + 1, by omega⟩
    · have htour :
          newVertexEdge i ∈ hamiltonian_tour_edge_finset (completePathToTourPerm σ) :=
        (newVertexEdge_mem_hamiltonianTourEdgeFinset_completePathToTourPerm_iff (m := n) σ i).2 hmem
      simp [hmem, htour]
    · have htour :
          newVertexEdge i ∉ hamiltonian_tour_edge_finset (completePathToTourPerm σ) := by
        intro htour
        exact hmem
          ((newVertexEdge_mem_hamiltonianTourEdgeFinset_completePathToTourPerm_iff (m := n) σ i).1
            htour)
      simp [hmem, htour]

/-- Helper for Theorem 7.18: the closing edge of a Hamiltonian tour is incident exactly to the
first and last permutation vertices. -/
private theorem hamiltonianTourClosingEdge_mem_completeGraphIncidentEdgeFinset_iff
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (v : Fin (n + 2)) :
    hamiltonian_tour_closing_edge σ ∈ completeGraphIncidentEdgeFinset (n + 2) v ↔
      v = σ 0 ∨ v = σ (hamiltonian_tour_last_position n) := by
  -- The closing edge is literally the unordered pair `{σ 0, σ last}`.
  rw [mem_completeGraphIncidentEdgeFinset_iff, hamiltonian_tour_closing_edge]
  simp [Sym2.mem_iff, eq_comm, or_left_comm, or_assoc]

/-- Helper for Theorem 7.18: for `n ≥ 3`, the closing edge is not already one of the path edges. -/
private theorem hamiltonianTourClosingEdge_not_mem_hamiltonianPathEdgeFinset
    {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + 2))) :
    hamiltonian_tour_closing_edge σ ∉ hamiltonian_path_edge_finset σ := by
  intro hmem
  have hpath : is_hamiltonian_path_edge σ (hamiltonian_tour_closing_edge σ) := by
    simpa [is_hamiltonian_path_edge] using hmem
  rw [is_hamiltonian_path_edge_iff_exists_index] at hpath
  rcases hpath with ⟨k, hk⟩
  let first : Fin (n + 2) := ⟨0, by omega⟩
  let lastPos : Fin (n + 2) := hamiltonian_tour_last_position n
  have hfirst_mem :
      path_edge_of_index σ k ∈ completeGraphIncidentEdgeFinset (n + 2) (σ first) := by
    have hclosing_mem :
        hamiltonian_tour_closing_edge σ ∈ completeGraphIncidentEdgeFinset (n + 2) (σ first) := by
      exact
        (hamiltonianTourClosingEdge_mem_completeGraphIncidentEdgeFinset_iff
          (σ := σ) (v := σ first)).2 (Or.inl rfl)
    simpa [hk, first] using hclosing_mem
  have hlast_mem :
      path_edge_of_index σ k ∈ completeGraphIncidentEdgeFinset (n + 2) (σ lastPos) := by
    have hclosing_mem :
        hamiltonian_tour_closing_edge σ ∈ completeGraphIncidentEdgeFinset (n + 2) (σ lastPos) := by
      exact
        (hamiltonianTourClosingEdge_mem_completeGraphIncidentEdgeFinset_iff
          (σ := σ) (v := σ lastPos)).2 (Or.inr rfl)
    simpa [hk] using hclosing_mem
  have hk_zero : k.1 = 0 := by
    rcases (pathEdgeOfIndex_mem_completeGraphIncidentEdgeFinset_iff
        (m := n + 2) σ k (σ first)).1 hfirst_mem with hk0 | hk1
    · simpa [first] using congrArg Fin.val (σ.injective hk0).symm
    · have hval := congrArg Fin.val (σ.injective hk1)
      have : False := by simpa [first] using hval
      exact False.elim this
  have hk_last : k.1 = n := by
    rcases (pathEdgeOfIndex_mem_completeGraphIncidentEdgeFinset_iff
        (m := n + 2) σ k (σ lastPos)).1 hlast_mem with hk0 | hk1
    · have hval := congrArg Fin.val (σ.injective hk0)
      simp [lastPos, hamiltonian_tour_last_position] at hval
      omega
    · have hval := congrArg Fin.val (σ.injective hk1)
      simp [lastPos, hamiltonian_tour_last_position] at hval
      omega
  omega

/-- Helper for Theorem 7.18: every Hamiltonian tour has incident-edge sum `2` at every vertex. -/
private theorem hamiltonianTourIncidenceVector_incidentSum
    {m : ℕ} (σ : Equiv.Perm (Fin (m + 3))) (v : Fin (m + 3)) :
    (completeGraphIncidentEdgeFinset (m + 3) v).sum (hamiltonian_tour_incidence_vector σ) = 2 := by
  let first : Fin (m + 3) := ⟨0, by omega⟩
  let last : Fin (m + 3) := Fin.last (m + 2)
  have hclosing_not_mem :
      hamiltonian_tour_closing_edge (n := m + 1) σ ∉ hamiltonian_path_edge_finset σ := by
    simpa using
      (hamiltonianTourClosingEdge_not_mem_hamiltonianPathEdgeFinset
        (n := m + 1) (hn := by omega) (σ := σ))
  have hpointwise :
      ∀ e : complete_graph_edges (m + 3),
        hamiltonian_tour_incidence_vector σ e =
          hamiltonian_path_incidence_vector σ e +
            if e = hamiltonian_tour_closing_edge (n := m + 1) σ then 1 else 0 := by
    intro e
    by_cases he : e = hamiltonian_tour_closing_edge (n := m + 1) σ
    · subst he
      simp [is_hamiltonian_tour_edge, hamiltonian_tour_edge_finset, hamiltonian_tour_incidence_vector,
        hamiltonian_path_incidence_vector, hclosing_not_mem]
    · by_cases hpath : e ∈ hamiltonian_path_edge_finset σ
      · simp [is_hamiltonian_tour_edge, hamiltonian_tour_edge_finset, hamiltonian_tour_incidence_vector,
          hamiltonian_path_incidence_vector, hclosing_not_mem, he, hpath]
      · simp [is_hamiltonian_tour_edge, hamiltonian_tour_edge_finset, hamiltonian_tour_incidence_vector,
          hamiltonian_path_incidence_vector, hclosing_not_mem, he, hpath]
  have hclosing_sum :
      (completeGraphIncidentEdgeFinset (m + 3) v).sum
          (fun e ↦ if e = hamiltonian_tour_closing_edge (n := m + 1) σ then (1 : ℝ) else 0) =
        if hamiltonian_tour_closing_edge (n := m + 1) σ ∈ completeGraphIncidentEdgeFinset (m + 3) v
        then 1 else 0 := by
    by_cases hmem :
        hamiltonian_tour_closing_edge (n := m + 1) σ ∈ completeGraphIncidentEdgeFinset (m + 3) v
    · simp [hmem]
    · simp [hmem]
  have hpath_sum :
      (completeGraphIncidentEdgeFinset (m + 3) v).sum (hamiltonian_path_incidence_vector σ) =
        if v = σ first ∨ v = σ last then 1 else 2 := by
    simpa [first, last] using
      (hamiltonianPathIncidenceVector_incidentSum (m := m + 3) (by omega) σ v)
  have hclosing_incident :
      hamiltonian_tour_closing_edge (n := m + 1) σ ∈ completeGraphIncidentEdgeFinset (m + 3) v ↔
        v = σ first ∨ v = σ last := by
    simpa [first, last, hamiltonian_tour_last_position] using
      (hamiltonianTourClosingEdge_mem_completeGraphIncidentEdgeFinset_iff
        (n := m + 1) (σ := σ) (v := v))
  calc
    (completeGraphIncidentEdgeFinset (m + 3) v).sum (hamiltonian_tour_incidence_vector σ) =
        (completeGraphIncidentEdgeFinset (m + 3) v).sum
            (fun e : complete_graph_edges (m + 3) ↦
              hamiltonian_path_incidence_vector σ e +
                (if e = hamiltonian_tour_closing_edge (n := m + 1) σ then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simpa using hpointwise e
    _ =
        (completeGraphIncidentEdgeFinset (m + 3) v).sum (hamiltonian_path_incidence_vector σ) +
          (completeGraphIncidentEdgeFinset (m + 3) v).sum
            (fun e ↦ if e = hamiltonian_tour_closing_edge (n := m + 1) σ then (1 : ℝ) else 0) := by
          rw [Finset.sum_add_distrib]
    _ =
        (if v = σ first ∨ v = σ last then 1 else 2) +
          (if hamiltonian_tour_closing_edge (n := m + 1) σ ∈
                completeGraphIncidentEdgeFinset (m + 3) v then 1 else 0) := by
          rw [hpath_sum, hclosing_sum]
    _ = 2 := by
          by_cases hends : v = σ first ∨ v = σ last
          · have hmem :
              hamiltonian_tour_closing_edge (n := m + 1) σ ∈
                completeGraphIncidentEdgeFinset (m + 3) v :=
              hclosing_incident.mpr hends
            norm_num [hends, hmem]
          · have hmem :
              hamiltonian_tour_closing_edge (n := m + 1) σ ∉
                completeGraphIncidentEdgeFinset (m + 3) v := by
              intro hmem
              exact hends (hclosing_incident.mp hmem)
            norm_num [hends, hmem]

/-- Helper for Theorem 7.18: every Hamiltonian-tour incidence vector satisfies the degree
constraints. -/
private theorem hamiltonianTourIncidenceVector_mem_degreeConstraintSet
    {n : ℕ} (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n)) :
    hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanDegreeConstraintSet n := by
  -- Package the local incident-sum computation into the public degree-slice membership condition.
  obtain ⟨m, hm_eq⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hm_eq
  subst hm_eq
  rw [mem_travelingSalesmanDegreeConstraintSet_iff]
  intro i
  rw [← completeGraphIncidentEdgeFinset_eq]
  simpa using hamiltonianTourIncidenceVector_incidentSum (m := m) σ i

/-- Helper for Theorem 7.18: completing every Hamiltonian-path vertex should produce a
Hamiltonian-tour vertex, so the completed-path image lies in the TSP polytope. -/
private theorem completePathToTourAffineMap_image_subset_travelingSalesmanPolytope
    (m : ℕ) (hm : 2 ≤ m) :
    completePathToTourAffineMap m '' hamiltonian_path_polytope m ⊆
      travelingSalesmanPolytope (m + 1) := by
  -- Push the explicit completed-tour generator bridge through the convex-hull presentation of the
  -- Hamiltonian-path polytope.
  rw [hamiltonian_path_polytope_eq_convexHull, travelingSalesmanPolytope_eq_convexHull,
    AffineMap.image_convexHull]
  refine convexHull_min ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨σ, rfl⟩
    refine subset_convexHull ℝ _ ?_
    refine ⟨completePathToTourPerm σ, ?_⟩
    simpa using (completePathToTourAffineMap_pathVertex_eq_tourVertex (m := m) hm σ).symm
  · exact convex_convexHull ℝ _

/-- Helper for Theorem 7.18: every Hamiltonian-tour vertex satisfies the degree equations, so the
traveling salesman polytope lies inside the degree slice. -/
private theorem travelingSalesmanPolytope_subset_degreeConstraintSet
    (n : ℕ) (hn : 3 ≤ n) :
    travelingSalesmanPolytope n ⊆ travelingSalesmanDegreeConstraintSet n := by
  -- The degree slice is convex, so it is enough to check the Hamiltonian-tour generators.
  rw [travelingSalesmanPolytope_eq_convexHull]
  refine convexHull_min ?_ ?_
  · rintro _ ⟨σ, rfl⟩
    exact hamiltonianTourIncidenceVector_mem_degreeConstraintSet hn σ
  · have hbase :
          hamiltonian_tour_incidence_vector (Equiv.refl (Fin n)) ∈
            travelingSalesmanDegreeConstraintSet n := by
            exact hamiltonianTourIncidenceVector_mem_degreeConstraintSet hn (Equiv.refl (Fin n))
    have hconv :
        Convex ℝ (travelingSalesmanDegreeConstraintSet n) := by
        rw [travelingSalesmanDegreeConstraintSet_eq_affineTranslate (n := n) hbase]
        exact AffineSubspace.convex _
    simpa using hconv

/-- Theorem 7.18 (1). For `n ≥ 3`, the affine hull of the traveling salesman polytope on `n`
nodes is the set of edge-vectors whose incident-edge sum at every vertex is equal to `2`. -/
theorem affineSpan_travelingSalesmanPolytope_eq_degreeConstraintSet
    (n : ℕ) (hn : 3 ≤ n) :
    (affineSpan ℝ (travelingSalesmanPolytope n) : Set (complete_graph_edges n → ℝ)) =
      travelingSalesmanDegreeConstraintSet n := by
  -- Route correction: the old whole-slice-image proof has been removed. The remaining route is:
  -- prove tour vertices satisfy the degree equations, prove the completed path vertices are tour
  -- vertices, use `completePathToTourAffineMap_injective` for the lower bound, and compare that
  -- lower bound against the degree-map kernel dimension for the upper bound.
  have hm : 2 ≤ n - 1 := by
    omega
  have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  let A : AffineSubspace ℝ (complete_graph_edges n → ℝ) := affineSpan ℝ (travelingSalesmanPolytope n)
  let x₀ : complete_graph_edges n → ℝ := hamiltonian_tour_incidence_vector (Equiv.refl (Fin n))
  let B : AffineSubspace ℝ (complete_graph_edges n → ℝ) :=
    AffineSubspace.mk' x₀ (LinearMap.ker (travelingSalesmanDegreeMap n))
  have hx₀_mem_poly : x₀ ∈ travelingSalesmanPolytope n := by
    -- The identity permutation contributes one generating tour vertex.
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self (Equiv.refl (Fin n)))
  have hx₀_mem_A : x₀ ∈ A := by
    -- Every polytope vertex lies in its affine span.
    exact subset_affineSpan ℝ _ hx₀_mem_poly
  have hx₀_mem_degreeSlice : x₀ ∈ travelingSalesmanDegreeConstraintSet n := by
    -- The upper containment helper provides the common base point for the final affine equality.
    exact travelingSalesmanPolytope_subset_degreeConstraintSet n hn hx₀_mem_poly
  have hdegreeSlice_eq_B :
      travelingSalesmanDegreeConstraintSet n = (B : Set (complete_graph_edges n → ℝ)) := by
    -- After fixing one feasible tour vector, the degree slice becomes an affine translate of the
    -- degree-map kernel.
    simpa [B] using
      travelingSalesmanDegreeConstraintSet_eq_affineTranslate (n := n) hx₀_mem_degreeSlice
  have hx₀_mem_B : x₀ ∈ B := by
    -- The chosen base point is the origin point of the affine translate.
    rw [show B = AffineSubspace.mk' x₀ (LinearMap.ker (travelingSalesmanDegreeMap n)) by rfl]
    exact AffineSubspace.self_mem_mk' x₀ (LinearMap.ker (travelingSalesmanDegreeMap n))
  have hdegreeSliceFinrank :
      Module.finrank ℝ (LinearMap.ker (travelingSalesmanDegreeMap n)) = Nat.choose n 2 - n := by
    -- The upper-bound codimension is already reduced to the kernel finrank computation above.
    simpa using travelingSalesmanDegreeMap_ker_finrank n hn
  have himageFinrank :
      Module.finrank ℝ
          (affineSpan ℝ (completePathToTourAffineMap (n - 1) '' hamiltonian_path_polytope (n - 1))).direction =
        Nat.choose n 2 - n := by
    -- The completion map is injective on directions, so its image has the same dimension as the
    -- Hamiltonian-path affine hull.
    calc
      Module.finrank ℝ
          (affineSpan ℝ (completePathToTourAffineMap (n - 1) '' hamiltonian_path_polytope (n - 1))).direction =
          Module.finrank ℝ (affineSpan ℝ (hamiltonian_path_polytope (n - 1))).direction := by
            simpa using
              completePathToTourAffineMap_image_finrank_direction_affineSpan
                (m := n - 1) (s := hamiltonian_path_polytope (n - 1))
      _ = Nat.choose (n - 1) 2 - 1 := by
            simpa using hamiltonian_path_polytope_finrank_direction_affineSpan (n - 1)
      _ = Nat.choose n 2 - n := by
            have hchoose : Nat.choose n 2 = Nat.choose (n - 1) 2 + (n - 1) := by
              rw [← hn_sub, Nat.choose_succ_succ, Nat.choose_one_right]
              simpa [Nat.add_comm]
            calc
              Nat.choose (n - 1) 2 - 1 = Nat.choose (n - 1) 2 + (n - 1) - n := by
                omega
              _ = Nat.choose n 2 - n := by
                rw [hchoose]
  have hlower :
      Nat.choose n 2 - n ≤ Module.finrank ℝ A.direction := by
    -- The completed-path image sits inside the TSP polytope, so its affine-hull dimension is a
    -- lower bound for the TSP affine-hull dimension.
    have himageSubset :
        completePathToTourAffineMap (n - 1) '' hamiltonian_path_polytope (n - 1) ⊆
          travelingSalesmanPolytope ((n - 1) + 1) :=
      completePathToTourAffineMap_image_subset_travelingSalesmanPolytope (n - 1) hm
    have himageAff_le_raw :
        affineSpan ℝ (completePathToTourAffineMap (n - 1) '' hamiltonian_path_polytope (n - 1)) ≤
          affineSpan ℝ (travelingSalesmanPolytope ((n - 1) + 1)) := by
      exact affineSpan_mono ℝ himageSubset
    have hdir_le_raw :
        (affineSpan ℝ (completePathToTourAffineMap (n - 1) '' hamiltonian_path_polytope (n - 1))).direction ≤
          (affineSpan ℝ (travelingSalesmanPolytope ((n - 1) + 1))).direction := by
      exact AffineSubspace.direction_le himageAff_le_raw
    calc
      Nat.choose n 2 - n =
          Module.finrank ℝ
            (affineSpan ℝ
              (completePathToTourAffineMap (n - 1) '' hamiltonian_path_polytope (n - 1))).direction := by
            symm
            exact himageFinrank
      _ ≤ Module.finrank ℝ (affineSpan ℝ (travelingSalesmanPolytope ((n - 1) + 1))).direction := by
            exact Submodule.finrank_mono hdir_le_raw
      _ = Module.finrank ℝ A.direction := by
            unfold A
            rw [hn_sub]
  have hupper :
      Module.finrank ℝ A.direction ≤ Nat.choose n 2 - n := by
    -- The TSP affine hull lies in the affine translate of the degree-map kernel.
    have hpoly_subset_B : travelingSalesmanPolytope n ⊆ (B : Set (complete_graph_edges n → ℝ)) := by
      simpa [hdegreeSlice_eq_B] using travelingSalesmanPolytope_subset_degreeConstraintSet n hn
    have hA_le_B : A ≤ B := by
      exact affineSpan_le.2 hpoly_subset_B
    calc
      Module.finrank ℝ A.direction ≤ Module.finrank ℝ B.direction := by
        exact Submodule.finrank_mono (AffineSubspace.direction_le hA_le_B)
      _ = Module.finrank ℝ (LinearMap.ker (travelingSalesmanDegreeMap n)) := by
        rw [show B = AffineSubspace.mk' x₀ (LinearMap.ker (travelingSalesmanDegreeMap n)) by rfl,
          AffineSubspace.direction_mk']
      _ = Nat.choose n 2 - n := hdegreeSliceFinrank
  have hdimA :
      Module.finrank ℝ A.direction = Nat.choose n 2 - n := by
    exact le_antisymm hupper hlower
  have hA_le_B : A ≤ B := by
    -- Reuse the upper containment at the affine-subspace level for the final equality.
    have hpoly_subset_B : travelingSalesmanPolytope n ⊆ (B : Set (complete_graph_edges n → ℝ)) := by
      simpa [hdegreeSlice_eq_B] using travelingSalesmanPolytope_subset_degreeConstraintSet n hn
    exact affineSpan_le.2 hpoly_subset_B
  have hdir_eq : A.direction = B.direction := by
    -- Equal lower and upper dimension bounds force the directions to coincide.
    apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hA_le_B)
    calc
      Module.finrank ℝ A.direction = Nat.choose n 2 - n := hdimA
      _ = Module.finrank ℝ (LinearMap.ker (travelingSalesmanDegreeMap n)) := hdegreeSliceFinrank.symm
      _ = Module.finrank ℝ B.direction := by
        rw [show B = AffineSubspace.mk' x₀ (LinearMap.ker (travelingSalesmanDegreeMap n)) by rfl,
          AffineSubspace.direction_mk']
  have hA_eq_B : A = B := by
    -- The common identity-tour base point upgrades the direction equality to affine-space equality.
    exact (AffineSubspace.eq_iff_direction_eq_of_mem hx₀_mem_A hx₀_mem_B).2 hdir_eq
  calc
    (A : Set (complete_graph_edges n → ℝ)) = (B : Set (complete_graph_edges n → ℝ)) := by
      simpa using congrArg
        (fun S : AffineSubspace ℝ (complete_graph_edges n → ℝ) =>
          (S : Set (complete_graph_edges n → ℝ))) hA_eq_B
    _ = travelingSalesmanDegreeConstraintSet n := by
      exact hdegreeSlice_eq_B.symm

/-- Theorem 7.18 (2). For `n ≥ 3`, the traveling salesman polytope on `n` nodes has dimension
`n.choose 2 - n`. -/
theorem finrank_direction_affineSpan_travelingSalesmanPolytope
    (n : ℕ) (hn : 3 ≤ n) :
    Module.finrank ℝ (affineSpan ℝ (travelingSalesmanPolytope n)).direction =
      Nat.choose n 2 - n := by
  let x₀ : complete_graph_edges n → ℝ := hamiltonian_tour_incidence_vector (Equiv.refl (Fin n))
  let B : AffineSubspace ℝ (complete_graph_edges n → ℝ) :=
    AffineSubspace.mk' x₀ (LinearMap.ker (travelingSalesmanDegreeMap n))
  have hx₀_mem_poly : x₀ ∈ travelingSalesmanPolytope n := by
    -- The identity tour is one of the convex-hull generators.
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self (Equiv.refl (Fin n)))
  have hx₀_mem_degreeSlice : x₀ ∈ travelingSalesmanDegreeConstraintSet n := by
    -- Reuse the remaining upper-containment helper to place the base point in the degree slice.
    exact travelingSalesmanPolytope_subset_degreeConstraintSet n hn hx₀_mem_poly
  have hdegreeSlice_eq_B :
      travelingSalesmanDegreeConstraintSet n = (B : Set (complete_graph_edges n → ℝ)) := by
    -- This is the same affine-translate description used in part (1).
    simpa [B] using
      travelingSalesmanDegreeConstraintSet_eq_affineTranslate (n := n) hx₀_mem_degreeSlice
  have hA_eq_B : affineSpan ℝ (travelingSalesmanPolytope n) = B := by
    -- Part (1) identifies the affine hull with the degree slice, and the previous lemma packages
    -- that slice as an affine translate of the kernel.
    apply SetLike.coe_injective
    calc
      ((affineSpan ℝ (travelingSalesmanPolytope n) :
          AffineSubspace ℝ (complete_graph_edges n → ℝ)) : Set (complete_graph_edges n → ℝ)) =
          travelingSalesmanDegreeConstraintSet n := by
            simpa using affineSpan_travelingSalesmanPolytope_eq_degreeConstraintSet n hn
      _ = (B : Set (complete_graph_edges n → ℝ)) := hdegreeSlice_eq_B
  -- With the affine hull identified as an affine translate of the kernel, the dimension is the
  -- kernel finrank computed earlier.
  rw [hA_eq_B]
  rw [show B = AffineSubspace.mk' x₀ (LinearMap.ker (travelingSalesmanDegreeMap n)) by rfl,
    AffineSubspace.direction_mk']
  simpa using travelingSalesmanDegreeMap_ker_finrank n hn
