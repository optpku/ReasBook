/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_corollary_3_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_1.ch3_sec3_4_1_definition_3_4_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_24
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_34
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_corollary_3_41

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators symmDiff

attribute [local instance] Classical.propDecidable

-- Primary domain: finite graph matchings and matching polytopes.
-- Core/canonical owners reused below: `SimpleGraph.Subgraph.IsMatching`,
-- `SimpleGraph.subgraphIncidenceVector`, `SimpleGraph.matchingPolytope`,
-- and the Chapter 3 edge/skeleton owners `IsEdgeOf` and `polytope_skeleton`.

universe u

namespace SimpleGraph

/-- The `0,1` incidence vector of a subgraph of `G`, viewed in the edge coordinates of `G` with
values in `R`. -/
def subgraphIncidenceVector {V : Type u} (G : SimpleGraph V) (R : Type*) [Zero R] [One R]
    (M : G.Subgraph) : G.edgeSet → R :=
  fun e ↦ if e.1 ∈ M.edgeSet then 1 else 0

/-- The matching polytope of `G`, defined as the convex hull of the incidence vectors of the
matchings of `G`. -/
def matchingPolytope {V : Type u} (G : SimpleGraph V) : Set (G.edgeSet → ℝ) :=
  convexHull ℝ {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = G.subgraphIncidenceVector ℝ M}

/-- A graph is a cycle or a path when it is exactly the spanning coercion of the subgraph traced by
some cycle walk, or exactly the spanning coercion of the subgraph traced by some nontrivial path
walk. -/
def IsCycleOrPath {V : Type u} (H : SimpleGraph V) : Prop :=
  (∃ v, ∃ p : H.Walk v v, p.IsCycle ∧ p.toSubgraph.spanningCoe = H) ∨
    ∃ u v, u ≠ v ∧ ∃ p : H.Walk u v, p.IsPath ∧ p.toSubgraph.spanningCoe = H

end SimpleGraph

section EdgeOwners

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Helper for Exercise 4.27: an edge of `P` is a one-dimensional convex extreme subset of `P`. -/
@[mk_iff]
class IsEdgeOf (P F : Set E) : Prop where
  /-- The carrier of an edge is convex. -/
  convex : Convex ℝ F
  /-- The subset `F` is extreme in `P`. -/
  isExtreme : IsExtreme ℝ P F
  /-- The direction of the affine span of `F` is one-dimensional. -/
  finrank_direction_eq_one : Module.finrank ℝ (affineSpan ℝ F).direction = 1

/-- Helper for Exercise 4.27: an edge is in particular an extreme subset. -/
instance instIsExtremeOfIsEdgeOf {P F : Set E} [h : IsEdgeOf P F] : IsExtreme ℝ P F :=
  h.isExtreme

/-- Helper for Exercise 4.27: a nondegenerate extreme segment is exactly an edge segment. -/
theorem isEdgeOf_segment_iff {P : Set E} {v w : E} (hvw : v ≠ w) :
    IsEdgeOf P (segment ℝ v w) ↔ IsExtreme ℝ P (segment ℝ v w) := by
  constructor
  · intro h
    -- Every edge is extreme by definition.
    exact h.isExtreme
  · intro h
    -- The affine span of a nondegenerate segment is one-dimensional.
    refine ⟨convex_segment _ _, h, ?_⟩
    rw [direction_affineSpan, vectorSpan_segment]
    simpa using finrank_span_singleton (vsub_ne_zero.2 hvw.symm)

/-- Helper for Exercise 4.27: the edge condition on a segment is symmetric in its endpoints. -/
theorem isEdgeOf_segment_symm {P : Set E} {v w : E} :
    IsEdgeOf P (segment ℝ v w) ↔ IsEdgeOf P (segment ℝ w v) := by
  by_cases hvw : v = w
  · subst hvw
    rfl
  · rw [isEdgeOf_segment_iff hvw, isEdgeOf_segment_iff (Ne.symm hvw)]
    simp [segment_symm]

/-- Helper for Exercise 4.27: the skeleton of `P` is the graph on its extreme points whose edges
are the edge segments of `P`. -/
def polytope_skeleton (P : Set E) : SimpleGraph (P.extremePoints ℝ) :=
  SimpleGraph.fromRel fun v w ↦ IsEdgeOf P (segment ℝ (v : E) (w : E))

/-- Helper for Exercise 4.27: adjacency in the skeleton means distinct vertices joined by an edge
segment of `P`. -/
theorem polytope_skeleton_adj_iff {P : Set E} {v w : P.extremePoints ℝ} :
    (polytope_skeleton P).Adj v w ↔
      v ≠ w ∧ IsEdgeOf P (segment ℝ (v : E) (w : E)) := by
  -- Unfold the graph relation and normalize the endpoint symmetry once.
  simp [polytope_skeleton, isEdgeOf_segment_symm]

end EdgeOwners

private abbrev componentGraph {V : Type u} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : SimpleGraph c.supp :=
  c.toSimpleGraph

private abbrev componentEdgeNonempty {V : Type u} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : Prop :=
  (componentGraph c).edgeSet.Nonempty

private abbrev componentSpanningGraph {V : Type u} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : SimpleGraph V :=
  (componentGraph c).spanningCoe

private abbrev componentSpanningEdgeSet {V : Type u} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : Set (Sym2 V) :=
  (componentSpanningGraph c).edgeSet

private abbrev walkSpanningGraph {V : Type u} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : SimpleGraph V :=
  p.toSubgraph.spanningCoe

section Exercise_4_27

variable {V : Type u}
variable (G : SimpleGraph V)

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel G.Adj

lemma polyhedron_le_set_convex
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  -- Each defining inequality is preserved by convex combinations, so the whole feasible region is.
  intro x hx y hy a c ha hc hac
  intro i
  have hx_i : (Matrix.mulVec A x) i ≤ b i := hx i
  have hy_i : (Matrix.mulVec A y) i ≤ b i := hy i
  calc
    (Matrix.mulVec A (a • x + c • y)) i = a * (Matrix.mulVec A x) i + c * (Matrix.mulVec A y) i := by
      calc
        ∑ j, A i j * (a * x j + c * y j)
            = ∑ j, (a * (A i j * x j) + c * (A i j * y j)) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                ring
        _ = (∑ j, a * (A i j * x j)) + ∑ j, c * (A i j * y j) := by
              rw [Finset.sum_add_distrib]
        _ = a * (Matrix.mulVec A x) i + c * (Matrix.mulVec A y) i := by
              simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ ≤ a * b i + c * b i := by
      exact add_le_add (mul_le_mul_of_nonneg_left hx_i ha) (mul_le_mul_of_nonneg_left hy_i hc)
    _ = b i := by
      rw [← add_mul, hac, one_mul]

/-- Helper for Exercise 4.27: every polyhedron is convex. -/
lemma convex_of_is_polyhedron
    {n : ℕ} {P : Set (Fin n → ℝ)} (hP : is_polyhedron P) :
    Convex ℝ P := by
  -- Unfold the polyhedral presentation and apply the matrix-inequality convexity lemma.
  rcases hP with ⟨m, A, b, rfl⟩
  exact polyhedron_le_set_convex A b

/-- Helper for Exercise 4.27: an extreme segment cannot have its midpoint on a chord whose
endpoints both lie in `P` outside that segment. -/
lemma midpoint_not_mem_segment_of_points_outside_of_isExtreme_segment
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w : Fin n → ℝ}
    (hExtreme : IsExtreme ℝ P (segment ℝ v w)) :
    ∀ x ∈ P \ segment ℝ v w, ∀ y ∈ P \ segment ℝ v w, midpoint ℝ v w ∉ segment ℝ x y := by
  intro x hx y hy hmid_xy
  rcases hx with ⟨hxP, hxOutside⟩
  rcases hy with ⟨hyP, hyOutside⟩
  have hmid_seg : midpoint ℝ v w ∈ segment ℝ v w := midpoint_mem_segment (𝕜 := ℝ) v w
  have hx_ne : x ≠ midpoint ℝ v w := by
    intro hx_mid
    exact hxOutside (hx_mid ▸ hmid_seg)
  have hy_ne : y ≠ midpoint ℝ v w := by
    intro hy_mid
    exact hyOutside (hy_mid ▸ hmid_seg)
  -- The midpoint lies strictly between `x` and `y`, so extremality forces `x` into the segment.
  have hmid_open : midpoint ℝ v w ∈ openSegment ℝ x y :=
    mem_openSegment_of_ne_left_right hx_ne hy_ne hmid_xy
  have hx_seg : x ∈ segment ℝ v w :=
    hExtreme.left_mem_of_mem_openSegment hxP hyP hmid_seg hmid_open
  exact hxOutside hx_seg

/-- Helper for Exercise 4.27: among `r` and `1 - r`, one lies across `1 / 2` from `t`, so the
midpoint parameter `1 / 2` belongs to the scalar segment from `t` to that chosen coefficient. -/
lemma midpoint_parameter_of_open_segment_coefficients
    {r t : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ q s : ℝ, (q = r ∨ q = 1 - r) ∧ s ∈ Set.Icc (0 : ℝ) 1 ∧
      AffineMap.lineMap t q s = (1 / 2 : ℝ) := by
  rcases hr with ⟨hr0, hr1⟩
  rcases ht with ⟨ht0, ht1⟩
  -- Choose whichever of `r` or `1 - r` puts `1 / 2` in the unordered interval with `t`.
  by_cases ht_half : t ≤ (1 / 2 : ℝ)
  · by_cases hr_half : (1 / 2 : ℝ) ≤ r
    · have hmid_seg : (1 / 2 : ℝ) ∈ segment ℝ t r := by
        rw [segment_eq_uIcc]
        exact Set.mem_uIcc_of_le ht_half hr_half
      rw [segment_eq_image_lineMap (𝕜 := ℝ) t r] at hmid_seg
      rcases hmid_seg with ⟨s, hs, hs_eq⟩
      exact ⟨r, s, Or.inl rfl, hs, hs_eq⟩
    · have hr_half' : r < (1 / 2 : ℝ) := lt_of_not_ge hr_half
      have hhalf_one_sub : (1 / 2 : ℝ) ≤ 1 - r := by linarith
      have hmid_seg : (1 / 2 : ℝ) ∈ segment ℝ t (1 - r) := by
        rw [segment_eq_uIcc]
        exact Set.mem_uIcc_of_le ht_half hhalf_one_sub
      rw [segment_eq_image_lineMap (𝕜 := ℝ) t (1 - r)] at hmid_seg
      rcases hmid_seg with ⟨s, hs, hs_eq⟩
      exact ⟨1 - r, s, Or.inr rfl, hs, hs_eq⟩
  · have ht_half' : (1 / 2 : ℝ) < t := lt_of_not_ge ht_half
    by_cases hr_half : r ≤ (1 / 2 : ℝ)
    · have hmid_seg : (1 / 2 : ℝ) ∈ segment ℝ t r := by
        rw [segment_eq_uIcc]
        exact Set.mem_uIcc_of_ge hr_half ht_half'.le
      rw [segment_eq_image_lineMap (𝕜 := ℝ) t r] at hmid_seg
      rcases hmid_seg with ⟨s, hs, hs_eq⟩
      exact ⟨r, s, Or.inl rfl, hs, hs_eq⟩
    · have hr_half' : (1 / 2 : ℝ) < r := lt_of_not_ge hr_half
      have hone_sub_le : 1 - r ≤ (1 / 2 : ℝ) := by linarith
      have hmid_seg : (1 / 2 : ℝ) ∈ segment ℝ t (1 - r) := by
        rw [segment_eq_uIcc]
        exact Set.mem_uIcc_of_ge hone_sub_le ht_half'.le
      rw [segment_eq_image_lineMap (𝕜 := ℝ) t (1 - r)] at hmid_seg
      rcases hmid_seg with ⟨s, hs, hs_eq⟩
      exact ⟨1 - r, s, Or.inr rfl, hs, hs_eq⟩

/-- Helper for Exercise 4.27: sliding both endpoints of a chord toward the same target commutes
with taking the same chord parameter. -/
lemma lineMap_lineMap_same_target
    {n : ℕ} (x y a : Fin n → ℝ) (r s : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap x a s) (AffineMap.lineMap y a s) r =
      AffineMap.lineMap (AffineMap.lineMap x y r) a s := by
  -- Reassociate the affine combinations so the common target `a` is factored out.
  ext i
  simp [AffineMap.lineMap_apply_module]
  ring

/-- Helper for Exercise 4.27: an extreme edge has no further points of `P` on the extension of
its supporting line beyond either endpoint. -/
lemma extreme_endpoints_forbid_outside_collinear_point
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w u : Fin n → ℝ}
    (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) (hvw : v ≠ w)
    (huP : u ∈ P) {a : ℝ} (hu : u = AffineMap.lineMap v w a) (ha : a < 0 ∨ 1 < a) :
    False := by
  rcases ha with ha | ha
  · -- A negative coefficient puts `v` strictly between `u` and `w`, contradicting extremality.
    have hs : -a / (1 - a) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · have hden : 0 < 1 - a := by linarith
        exact div_pos (by linarith) hden
      · have hden : 0 < 1 - a := by linarith
        have hne : 1 - a ≠ 0 := ne_of_gt hden
        have hlt : -a / (1 - a) < 1 := by
          field_simp [hne]
          linarith
        exact hlt
    have hv_open : v ∈ openSegment ℝ u w := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨-a / (1 - a), hs, ?_⟩
      rw [hu, AffineMap.lineMap_lineMap_left]
      have hne : 1 - a ≠ 0 := by linarith
      have hparam : 1 - (1 - -a / (1 - a)) * (1 - a) = (0 : ℝ) := by
        field_simp [hne]
        ring
      rw [hparam, AffineMap.lineMap_apply_zero]
    have hu_eq_v : u = v := (mem_extremePoints_iff_left.mp hv).2 u huP w hw.1 hv_open
    have hu_line_eq : AffineMap.lineMap v w a = v := by
      rw [← hu, hu_eq_v]
    have ha_zero : a = 0 :=
      (AffineMap.lineMap_eq_left_iff.mp hu_line_eq).resolve_left hvw
    linarith
  · -- A coefficient beyond `1` puts `w` strictly between `v` and `u`, contradicting extremality.
    have hs : 1 / a ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · have ha_pos : 0 < a := by linarith
        exact one_div_pos.mpr ha_pos
      · have ha_pos : 0 < a := by linarith
        have hlt : 1 / a < 1 := by
          field_simp [ha_pos.ne']
          linarith
        exact hlt
    have hw_open : w ∈ openSegment ℝ v u := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨1 / a, hs, ?_⟩
      rw [hu, AffineMap.lineMap_lineMap_right]
      have hne : a ≠ 0 := by linarith
      have hparam : (1 / a) * a = (1 : ℝ) := by
        field_simp [hne]
      rw [hparam, AffineMap.lineMap_apply_one]
    have hv_eq_w : v = w := (mem_extremePoints_iff_left.mp hw).2 v hv.1 u huP hw_open
    exact hvw hv_eq_w

/-- Helper for Exercise 4.27: a point of `P` outside the edge segment is not collinear with the
edge, so together with the edge direction it forms a linearly independent pair. -/
lemma outside_point_linearIndependent_with_edge
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w u : Fin n → ℝ}
    (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) (hvw : v ≠ w)
    (huP : u ∈ P) (huOutside : u ∉ segment ℝ v w) :
    LinearIndependent ℝ ![u - v, w - v] := by
  -- Route correction: instead of unfolding a large intersection argument immediately, first rule
  -- out every collinear outside point by extremality and then package the result as linear
  -- independence.
  have hpair : LinearIndependent ℝ ![w - v, u - v] := by
    apply (LinearIndependent.pair_iff' (by simpa using sub_ne_zero.mpr hvw.symm)).2
    intro a ha
    have hu_line : u = AffineMap.lineMap v w a := by
      ext i
      have hai := congrArg (fun p => p i) ha
      simp [AffineMap.lineMap_apply_module] at hai ⊢
      linarith
    have haOutside : a < 0 ∨ 1 < a := by
      by_contra haIcc
      have haIcc' : a ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · by_contra ha0
          exact haIcc (Or.inl (lt_of_not_ge ha0))
        · by_contra ha1
          exact haIcc (Or.inr (lt_of_not_ge ha1))
      exact huOutside (hu_line ▸ lineMap_mem_segment (𝕜 := ℝ) v w haIcc')
    exact
      (extreme_endpoints_forbid_outside_collinear_point
        hv hw hvw huP hu_line haOutside).elim
  simpa using (LinearIndependent.pair_symm_iff.mp hpair)

/-- Helper for Exercise 4.27: a strict slide from an outside point toward an endpoint of the edge
cannot land back on the edge in the transverse case. -/
lemma slid_endpoint_outside_segment_of_transverse_point
    {n : ℕ} {v w u : Fin n → ℝ} (huOutside : u ∉ segment ℝ v w)
    (hlin : LinearIndependent ℝ ![u - v, w - v]) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    AffineMap.lineMap u v s ∉ segment ℝ v w := by
  intro hSeg
  -- The slid point lies on both segments `[v, u]` and `[v, w]`, so linear independence forces it
  -- to be the common endpoint `v`.
  have huv_seg : AffineMap.lineMap u v s ∈ segment ℝ v u := by
    simpa [segment_symm] using
      (openSegment_subset_segment (𝕜 := ℝ) u v
        (lineMap_mem_openSegment (𝕜 := ℝ) u v hs))
  have hmem :
      AffineMap.lineMap u v s ∈ segment ℝ v u ∩ segment ℝ v w := ⟨huv_seg, hSeg⟩
  have hEq : AffineMap.lineMap u v s = v := by
    have hInter :
        segment ℝ v u ∩ segment ℝ v w = ({v} : Set (Fin n → ℝ)) :=
      segment_inter_eq_endpoint_of_linearIndependent_sub (𝕜 := ℝ) (c := v) (x := u) (y := w) hlin
    have hsingleton : AffineMap.lineMap u v s ∈ ({v} : Set (Fin n → ℝ)) := by
      simpa [hInter] using hmem
    simpa using hsingleton
  have hu_ne_v : u ≠ v := by
    intro hu_eq
    exact huOutside (hu_eq ▸ left_mem_segment ℝ v w)
  have hs_one : s = 1 := (AffineMap.lineMap_eq_right_iff.mp hEq).resolve_left hu_ne_v
  exact hs.2.ne hs_one

/-- Helper for Exercise 4.27: if an interior chord of `P` meets the edge at an interior point and
one endpoint lies outside the edge segment, then the other endpoint must lie outside as well. -/
lemma other_endpoint_outside_segment_of_interior_chord
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w x y z : Fin n → ℝ}
    (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) (hvw : v ≠ w)
    (hzSeg : z ∈ openSegment ℝ v w) (hzChord : z ∈ openSegment ℝ x y)
    (hxP : x ∈ P) (hyP : y ∈ P) (hxOutside : x ∉ segment ℝ v w) :
    y ∉ segment ℝ v w := by
  intro hySeg
  -- If `y` were on the edge, then the chord equality would force `x` onto the same line, which
  -- the extreme-point obstruction forbids.
  rw [openSegment_eq_image_lineMap] at hzSeg hzChord
  rw [segment_eq_image_lineMap] at hySeg
  rcases hzSeg with ⟨t, ht, hzvw⟩
  rcases hzChord with ⟨r, hr, hzxy⟩
  rcases hySeg with ⟨b, hb, hyLine⟩
  have hr_ne : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hr.2))
  let a : ℝ := (t - r * b) / (1 - r)
  have hxLine : x = AffineMap.lineMap v w a := by
    ext i
    have hzvw_i : (1 - t) * v i + t * w i = z i := by
      simpa [AffineMap.lineMap_apply_module] using congrArg (fun p => p i) hzvw
    have hzxy_i : (1 - r) * x i + r * y i = z i := by
      simpa [AffineMap.lineMap_apply_module] using congrArg (fun p => p i) hzxy
    have hy_i : y i = (1 - b) * v i + b * w i := by
      simpa [AffineMap.lineMap_apply_module] using (congrArg (fun p => p i) hyLine).symm
    have hz_eq :
        (1 - r) * x i + r * ((1 - b) * v i + b * w i) = (1 - t) * v i + t * w i := by
      calc
        (1 - r) * x i + r * ((1 - b) * v i + b * w i)
            = (1 - r) * x i + r * y i := by rw [hy_i]
        _ = z i := hzxy_i
        _ = (1 - t) * v i + t * w i := hzvw_i.symm
    have hMul :
        (1 - r) * x i = ((1 - r) - (t - r * b)) * v i + (t - r * b) * w i := by
      nlinarith [hz_eq]
    have hLineMul :
        (AffineMap.lineMap v w a) i * (1 - r) =
          ((1 - r) - (t - r * b)) * v i + (t - r * b) * w i := by
      simp [AffineMap.lineMap_apply_module, a]
      field_simp [a, hr_ne]
    have hEqMul : x i * (1 - r) = (AffineMap.lineMap v w a) i * (1 - r) := by
      calc
        x i * (1 - r) = ((1 - r) - (t - r * b)) * v i + (t - r * b) * w i := by
          simpa [mul_comm] using hMul
        _ = (AffineMap.lineMap v w a) i * (1 - r) := hLineMul.symm
    have hEqMulLeft : (1 - r) * x i = (1 - r) * (AffineMap.lineMap v w a) i := by
      simpa [mul_comm] using hEqMul
    exact (mul_right_inj' hr_ne).mp hEqMulLeft
  have haOutside : a < 0 ∨ 1 < a := by
    by_contra haIcc
    have haIcc' : a ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · by_contra ha0
        exact haIcc (Or.inl (lt_of_not_ge ha0))
      · by_contra ha1
        exact haIcc (Or.inr (lt_of_not_ge ha1))
    exact hxOutside (hxLine ▸ lineMap_mem_segment (𝕜 := ℝ) v w haIcc')
  exact
    extreme_endpoints_forbid_outside_collinear_point
      hv hw hvw hxP hxLine haOutside

/-- Helper for Exercise 4.27: an interior witness chord can be slid toward the appropriate edge
endpoint until it passes through the midpoint, while the new endpoints remain outside the edge. -/
lemma midpoint_witness_of_interior_chord
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w x y z : Fin n → ℝ}
    (hconvexP : Convex ℝ P) (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ)
    (hvw : v ≠ w) (hzSeg : z ∈ openSegment ℝ v w) (hzChord : z ∈ openSegment ℝ x y)
    (hxP : x ∈ P) (hyP : y ∈ P) (hxOutside : x ∉ segment ℝ v w) (hyOutside : y ∉ segment ℝ v w) :
    ∃ x' y', x' ∈ P \ segment ℝ v w ∧ y' ∈ P \ segment ℝ v w ∧
      midpoint ℝ v w ∈ segment ℝ x' y' := by
  rw [openSegment_eq_image_lineMap] at hzSeg hzChord
  rcases hzSeg with ⟨t, ht, hzvw⟩
  rcases hzChord with ⟨r, hr, hzxy⟩
  by_cases ht_half : t = (1 / 2 : ℝ)
  · -- If `z` is already the midpoint of the edge, the original outside chord is enough.
    refine ⟨x, y, ⟨hxP, hxOutside⟩, ⟨hyP, hyOutside⟩, ?_⟩
    have hhalf : (⅟2 : ℝ) = (1 / 2 : ℝ) := by norm_num
    have hmid_eq : midpoint ℝ v w = z := by
      simpa [midpoint, hhalf, ht_half] using hzvw
    rw [hmid_eq]
    rw [segment_eq_image_lineMap]
    exact ⟨r, ⟨hr.1.le, hr.2.le⟩, hzxy⟩
  · have ht_lt_or_gt : t < (1 / 2 : ℝ) ∨ (1 / 2 : ℝ) < t := lt_or_gt_of_ne ht_half
    rcases ht_lt_or_gt with ht_lt | ht_gt
    · -- Slide both endpoints toward `w`, because the midpoint lies strictly between `z` and `w`.
      have hhalf_open : (1 / 2 : ℝ) ∈ openSegment ℝ t 1 := by
        rw [openSegment_eq_Ioo ht.2]
        exact ⟨ht_lt, by norm_num⟩
      rw [openSegment_eq_image_lineMap] at hhalf_open
      rcases hhalf_open with ⟨s, hs, hs_eq⟩
      let x' : Fin n → ℝ := AffineMap.lineMap x w s
      let y' : Fin n → ℝ := AffineMap.lineMap y w s
      have hmid_eq : midpoint ℝ v w = AffineMap.lineMap z w s := by
        have hhalf : (⅟2 : ℝ) = (1 / 2 : ℝ) := by norm_num
        have hs_map := congrArg (AffineMap.lineMap v w) hs_eq
        simpa [midpoint, hhalf, hzvw] using hs_map.symm
      have hx'P : x' ∈ P := by
        exact hconvexP.segment_subset hxP hw.1
          (lineMap_mem_segment (𝕜 := ℝ) x w ⟨hs.1.le, hs.2.le⟩)
      have hy'P : y' ∈ P := by
        exact hconvexP.segment_subset hyP hw.1
          (lineMap_mem_segment (𝕜 := ℝ) y w ⟨hs.1.le, hs.2.le⟩)
      have hxLin :
          LinearIndependent ℝ ![x - w, v - w] := by
        simpa [segment_symm] using
          (outside_point_linearIndependent_with_edge
            (v := w) (w := v) hw hv (Ne.symm hvw) hxP (by simpa [segment_symm] using hxOutside))
      have hyLin :
          LinearIndependent ℝ ![y - w, v - w] := by
        simpa [segment_symm] using
          (outside_point_linearIndependent_with_edge
            (v := w) (w := v) hw hv (Ne.symm hvw) hyP (by simpa [segment_symm] using hyOutside))
      have hx'Outside : x' ∉ segment ℝ v w := by
        have hx'Outside' :
            x' ∉ segment ℝ w v :=
          slid_endpoint_outside_segment_of_transverse_point
            (v := w) (w := v) (u := x) (by simpa [segment_symm] using hxOutside) hxLin hs
        simpa [segment_symm, x'] using hx'Outside'
      have hy'Outside : y' ∉ segment ℝ v w := by
        have hy'Outside' :
            y' ∉ segment ℝ w v :=
          slid_endpoint_outside_segment_of_transverse_point
            (v := w) (w := v) (u := y) (by simpa [segment_symm] using hyOutside) hyLin hs
        simpa [segment_symm, y'] using hy'Outside'
      refine ⟨x', y', ⟨hx'P, hx'Outside⟩, ⟨hy'P, hy'Outside⟩, ?_⟩
      rw [segment_eq_image_lineMap]
      refine ⟨r, ⟨hr.1.le, hr.2.le⟩, ?_⟩
      calc
        AffineMap.lineMap x' y' r = AffineMap.lineMap z w s := by
          simpa [x', y', hzxy] using (lineMap_lineMap_same_target x y w r s)
        _ = midpoint ℝ v w := hmid_eq.symm
    · -- Slide both endpoints toward `v`, because the midpoint lies strictly between `z` and `v`.
      have hhalf_open : (1 / 2 : ℝ) ∈ openSegment ℝ t 0 := by
        rw [openSegment_symm, openSegment_eq_Ioo ht.1]
        exact ⟨by norm_num, ht_gt⟩
      rw [openSegment_eq_image_lineMap] at hhalf_open
      rcases hhalf_open with ⟨s, hs, hs_eq⟩
      let x' : Fin n → ℝ := AffineMap.lineMap x v s
      let y' : Fin n → ℝ := AffineMap.lineMap y v s
      have hmid_eq : midpoint ℝ v w = AffineMap.lineMap z v s := by
        have hhalf : (⅟2 : ℝ) = (1 / 2 : ℝ) := by norm_num
        have hs_map := congrArg (AffineMap.lineMap v w) hs_eq
        simpa [midpoint, hhalf, hzvw] using hs_map.symm
      have hx'P : x' ∈ P := by
        exact hconvexP.segment_subset hxP hv.1
          (lineMap_mem_segment (𝕜 := ℝ) x v ⟨hs.1.le, hs.2.le⟩)
      have hy'P : y' ∈ P := by
        exact hconvexP.segment_subset hyP hv.1
          (lineMap_mem_segment (𝕜 := ℝ) y v ⟨hs.1.le, hs.2.le⟩)
      have hxLin :
          LinearIndependent ℝ ![x - v, w - v] :=
        outside_point_linearIndependent_with_edge hv hw hvw hxP hxOutside
      have hyLin :
          LinearIndependent ℝ ![y - v, w - v] :=
        outside_point_linearIndependent_with_edge hv hw hvw hyP hyOutside
      have hx'Outside : x' ∉ segment ℝ v w := by
        simpa [x'] using
          (slid_endpoint_outside_segment_of_transverse_point
            (v := v) (w := w) (u := x) hxOutside hxLin hs)
      have hy'Outside : y' ∉ segment ℝ v w := by
        simpa [y'] using
          (slid_endpoint_outside_segment_of_transverse_point
            (v := v) (w := w) (u := y) hyOutside hyLin hs)
      refine ⟨x', y', ⟨hx'P, hx'Outside⟩, ⟨hy'P, hy'Outside⟩, ?_⟩
      rw [segment_eq_image_lineMap]
      refine ⟨r, ⟨hr.1.le, hr.2.le⟩, ?_⟩
      calc
        AffineMap.lineMap x' y' r = AffineMap.lineMap z v s := by
          simpa [x', y', hzxy] using (lineMap_lineMap_same_target x y v r s)
        _ = midpoint ℝ v w := hmid_eq.symm

/-- Helper for Exercise 4.27: for the segment joining two distinct vertices of a convex set,
extremality implies the midpoint obstruction, and the converse reduces to the source proof's
interior-chord reparameterization step. -/
lemma isExtreme_segment_iff_midpoint_not_mem_segment_of_points_outside_segment
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w : Fin n → ℝ}
    (hconvexP : Convex ℝ P) (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ)
    (hvw : v ≠ w) :
    IsExtreme ℝ P (segment ℝ v w) ↔
      ∀ x ∈ P \ segment ℝ v w, ∀ y ∈ P \ segment ℝ v w, midpoint ℝ v w ∉ segment ℝ x y := by
  constructor
  · intro hExtreme
    -- The forward implication is the direct extremality contradiction at the midpoint.
    exact midpoint_not_mem_segment_of_points_outside_of_isExtreme_segment hExtreme
  · intro hmidpoint
    refine ⟨hconvexP.segment_subset hv.1 hw.1, ?_⟩
    intro x hxP y hyP z hzSeg hzOpen
    rw [← insert_endpoints_openSegment (𝕜 := ℝ) v w, Set.mem_insert_iff, Set.mem_insert_iff] at hzSeg
    rcases hzSeg with hzv | hzSeg
    · -- If the witness point is `v`, extremality of the vertex forces the left endpoint to be `v`.
      subst z
      have hx_eq : x = v := (mem_extremePoints_iff_left.mp hv).2 x hxP y hyP <| by
        simpa using hzOpen
      simpa [hx_eq] using left_mem_segment (𝕜 := ℝ) v w
    rcases hzSeg with hzw | hzInterior
    · -- The symmetric endpoint case is handled by the same extreme-point criterion at `w`.
      subst z
      have hx_eq : x = w := (mem_extremePoints_iff_left.mp hw).2 x hxP y hyP <| by
        simpa using hzOpen
      simpa [hx_eq, segment_symm] using left_mem_segment (𝕜 := ℝ) w v
    · -- Parameterize the two open segments by `lineMap`, use the interior witness point to
      -- build a new outside chord through the midpoint, then contradict the midpoint obstruction.
      -- Route correction: the failing earlier route bundled all geometric cases into one slide.
      -- Here we first show the second endpoint is outside, then slide both endpoints toward the
      -- appropriate edge endpoint according to the position of `z`.
      by_contra hxOutside
      have hyOutside :
          y ∉ segment ℝ v w :=
        other_endpoint_outside_segment_of_interior_chord
          hv hw hvw hzInterior hzOpen hxP hyP hxOutside
      rcases
          midpoint_witness_of_interior_chord
            hconvexP hv hw hvw hzInterior hzOpen hxP hyP hxOutside hyOutside with
        ⟨x', y', hx', hy', hmid⟩
      exact hmidpoint x' hx' y' hy' hmid

/-- Exercise 3.28. Two distinct vertices `v` and `w` of a polyhedron `P` are adjacent if and only
if the midpoint of `v` and `w` is not contained in any segment joining two points of `P` that
both lie outside the segment joining `v` and `w`. -/
theorem adjacent_vertices_iff_midpoint_not_mem_segment_of_points_outside_segment
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w : Fin n → ℝ} (hP : is_polyhedron P)
    (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) (hvw : v ≠ w) :
    (polytope_skeleton P).Adj ⟨v, hv⟩ ⟨w, hw⟩ ↔
      ∀ x ∈ P \ segment ℝ v w, ∀ y ∈ P \ segment ℝ v w, midpoint ℝ v w ∉ segment ℝ x y := by
  have hconvexP : Convex ℝ P := convex_of_is_polyhedron hP
  rw [polytope_skeleton_adj_iff]
  constructor
  · rintro ⟨_, hEdge⟩
    -- Rewrite adjacency to an extreme-segment statement, then apply the midpoint obstruction.
    have hExtreme : IsExtreme ℝ P (segment ℝ v w) := (isEdgeOf_segment_iff hvw).1 hEdge
    exact
      (isExtreme_segment_iff_midpoint_not_mem_segment_of_points_outside_segment
        hconvexP hv hw hvw).1 hExtreme
  · intro hmidpoint
    -- The converse uses the packaged midpoint-obstruction-to-extremality implication.
    refine ⟨?_, ?_⟩
    · intro hEq
      exact hvw (congrArg Subtype.val hEq)
    · have hExtreme : IsExtreme ℝ P (segment ℝ v w) :=
        (isExtreme_segment_iff_midpoint_not_mem_segment_of_points_outside_segment
          hconvexP hv hw hvw).2 hmidpoint
      exact (isEdgeOf_segment_iff hvw).2 hExtreme
private lemma exists_nonzero_coordinate_of_ne_zero
    {n : ℕ} {x : Fin n → ℝ}
    (hx : x ≠ 0) :
    ∃ j : Fin n, x j ≠ 0 := by
  -- Coordinatewise extensionality forces a vector with only zero coordinates to vanish.
  by_contra h
  apply hx
  ext j
  by_contra hj
  exact h ⟨j, hj⟩

/-- Helper for Exercise 4.27: any non-auxiliary row of `Fin (m + 2)` is a tail row. -/
private lemma exists_tail_index_of_ne_auxiliary_slice_row
    {m : ℕ}
    {p : Fin (m + 2)}
    (hp0 : p ≠ 0)
    (hp1 : p ≠ 1) :
    ∃ i : Fin m, p = i.succ.succ := by
  -- A row index is either one of the two auxiliary rows or an original row shifted by two.
  rcases p with ⟨k, hk⟩
  cases k with
  | zero =>
      exact False.elim (hp0 rfl)
  | succ k =>
      cases k with
      | zero =>
          exact False.elim (hp1 rfl)
      | succ k =>
          refine ⟨⟨k, by omega⟩, rfl⟩

/-- Helper for Exercise 4.27: a one-dimensional submodule is the span of any nonzero vector it
contains. -/
private lemma submodule_eq_span_singleton_of_finrank_eq_one
    {n : ℕ}
    {D : Submodule ℝ (Fin n → ℝ)}
    {r : Fin n → ℝ}
    (hrD : r ∈ D)
    (hr_ne_zero : r ≠ 0)
    (hfinrank : Module.finrank ℝ D = 1) :
    D = ℝ ∙ r := by
  have hle : ℝ ∙ r ≤ D :=
    (Submodule.span_singleton_le_iff_mem r D).2 hrD
  -- Comparing finranks upgrades the inclusion to equality.
  symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [hfinrank]
  simpa using finrank_span_singleton hr_ne_zero

/-- Helper for Exercise 4.27: if `n - 1` linearly independent selected rows of `A` annihilate
both `r` and `s`, then `s` lies on the line spanned by the nonzero vector `r`. -/
private lemma selectedRowsZero_mem_spanSingleton
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {r s : Fin n → ℝ}
    (hr_ne_zero : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), Matrix.mulVec A r (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    (hs_zero : ∀ i : Fin (n - 1), Matrix.mulVec A s (I i) = 0) :
    s ∈ Submodule.span ℝ ({r} : Set (Fin n → ℝ)) := by
  have hn_pos : 0 < n := by
    -- A nonzero vector cannot live in the zero-dimensional ambient space.
    by_contra hn
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    apply hr_ne_zero
    ext i
    exact Fin.elim0 i
  let B : Matrix (Fin (n - 1)) (Fin n) ℝ := fun i j ↦ A (I i) j
  have hB_rows : LinearIndependent ℝ B.row := by
    -- The selected rows of `A` become the row family of the submatrix `B`.
    simpa [B, Matrix.row] using hI_linearIndependent
  have hB_rank : B.rank = n - 1 := by
    -- Full row rank records that the chosen active rows stay independent.
    simpa [B] using LinearIndependent.rank_matrix hB_rows
  have hker_finrank : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 1 := by
    -- The kernel of an `(n - 1) × n` full-row-rank matrix is one-dimensional.
    calc
      Module.finrank ℝ (LinearMap.ker B.mulVecLin) = n - B.rank := by
        simpa using finrank_matrix_kernel_eq_ambient_sub_rank B
      _ = n - (n - 1) := by rw [hB_rank]
      _ = 1 := by omega
  have hr_ker : r ∈ LinearMap.ker B.mulVecLin := by
    -- The reference direction `r` is annihilated by every selected row.
    change Matrix.mulVec B r = 0
    ext i
    simpa [B, Matrix.mulVec] using hI_active i
  have hs_ker : s ∈ LinearMap.ker B.mulVecLin := by
    -- The candidate direction `s` satisfies the same selected-row equalities.
    change Matrix.mulVec B s = 0
    ext i
    simpa [B, Matrix.mulVec] using hs_zero i
  have hker_eq :
      LinearMap.ker B.mulVecLin = ℝ ∙ r :=
    submodule_eq_span_singleton_of_finrank_eq_one hr_ker hr_ne_zero hker_finrank
  -- Once the selected-row kernel is identified with `ℝ ∙ r`, `s` lies on that line.
  simpa [hker_eq] using hs_ker

section Exercise_4_27

variable {V : Type u}
variable (G : SimpleGraph V)

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel G.Adj

section FinitePart_1

variable [Finite V]
local instance : Fintype V := Fintype.ofFinite V

/-- The incidence vector of a matching is a vertex of the matching polytope. -/
theorem subgraphIncidenceVector_mem_extremePoints_matchingPolytope
    {M : G.Subgraph} (hM : M.IsMatching) :
    G.subgraphIncidenceVector ℝ M ∈ (G.matchingPolytope).extremePoints ℝ := by
  classical
  let e : G.edgeSet ≃ Fin (Nat.card G.edgeSet) := Finite.equivFin G.edgeSet
  let L : (G.edgeSet → ℝ) ≃ₗ[ℝ] (Fin (Nat.card G.edgeSet) → ℝ) :=
    (LinearEquiv.funCongrLeft ℝ ℝ e).symm
  let S : Set (Fin (Nat.card G.edgeSet) → ℝ) :=
    L '' {x : G.edgeSet → ℝ | ∃ H : G.Subgraph, H.IsMatching ∧
      x = G.subgraphIncidenceVector ℝ H}
  have hL_apply (x : G.edgeSet → ℝ) (j : Fin (Nat.card G.edgeSet)) :
      L x j = x (e.symm j) := by
    -- This is the inverse evaluation formula for the canonical coordinate reindexing.
    change (LinearEquiv.funCongrLeft ℝ ℝ e).symm x j = x (e.symm j)
    rw [LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  have hS_zero_one : S ⊆ zero_one_cube (Nat.card G.edgeSet) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨H, hH, rfl⟩
    -- Every reindexed matching-incidence vector is still coordinatewise `0` or `1`.
    rw [mem_zero_one_cube_iff]
    intro j
    by_cases hj : ((e.symm j).1 : Sym2 V) ∈ H.edgeSet
    · right
      rw [hL_apply]
      exact dif_pos hj
    · left
      rw [hL_apply]
      exact dif_neg hj
  have hvertex_fin :
      L (G.subgraphIncidenceVector ℝ M) ∈ (convexHull ℝ S).extremePoints ℝ := by
    -- The Chapter 3 `0/1`-vertex theorem identifies the reindexed incidence vector as a vertex.
    rw [← zero_one_set_eq_extremePoints_convexHull hS_zero_one]
    exact ⟨G.subgraphIncidenceVector ℝ M, ⟨M, hM, rfl⟩, rfl⟩
  have himage_matchingPolytope :
      L '' G.matchingPolytope = convexHull ℝ S := by
    -- Linear reindexing commutes with convex hull.
    rw [SimpleGraph.matchingPolytope]
    simpa [S] using
      L.toLinearMap.image_convexHull
        ({x : G.edgeSet → ℝ | ∃ H : G.Subgraph, H.IsMatching ∧
          x = G.subgraphIncidenceVector ℝ H} : Set (G.edgeSet → ℝ))
  have himage_extreme :
      L '' (G.matchingPolytope).extremePoints ℝ = (convexHull ℝ S).extremePoints ℝ := by
    -- Extreme points are preserved by the coordinate reindexing equivalence.
    rw [image_extremePoints, himage_matchingPolytope]
  have himage_mem :
      L (G.subgraphIncidenceVector ℝ M) ∈ L '' (G.matchingPolytope).extremePoints ℝ := by
    rw [himage_extreme]
    exact hvertex_fin
  rcases himage_mem with ⟨x, hx, hx_eq⟩
  -- Injectivity of the reindexing equivalence brings the vertex statement back to `G.edgeSet`.
  have hx_native : x = G.subgraphIncidenceVector ℝ M := L.injective hx_eq
  simpa [hx_native] using hx

omit [Finite V] in
/-- Helper for Exercise 4.27: an edge belongs to `M.spanningCoe ∆ N.spanningCoe` exactly when it
lies in exactly one of the two matchings. -/
private lemma memSymmDiffSpanningCoe_iff {M N : G.Subgraph} {v w : V} :
    s(v, w) ∈ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet ↔
      (M.Adj v w ∨ N.Adj v w) ∧ ¬ (M.Adj v w ∧ N.Adj v w) := by
  -- Expand the symmetric-difference predicate to the xor description used in the source proof.
  constructor
  · intro h
    simp [symmDiff_def, SimpleGraph.Subgraph.mem_edgeSet] at h
    rcases h with ⟨hMvw, hNvw⟩ | ⟨hNvw, hMvw⟩
    · exact ⟨Or.inl hMvw, fun hBoth ↦ hNvw hBoth.2⟩
    · exact ⟨Or.inr hNvw, fun hBoth ↦ hMvw hBoth.1⟩
  · intro h
    rcases h.1 with hMvw | hNvw
    · exact Or.inl ⟨hMvw, fun hNvw ↦ h.2 ⟨hMvw, hNvw⟩⟩
    · exact Or.inr ⟨hNvw, fun hMvw ↦ h.2 ⟨hMvw, hNvw⟩⟩

omit [Finite V] in
/-- Helper for Exercise 4.27: the symmetric difference of two matchings alternates with respect to
the first matching. -/
private lemma matchingSymmDiff_isAlternating {M N : G.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching) :
    (M.spanningCoe ∆ N.spanningCoe).IsAlternating M.spanningCoe := by
  intro v w w' hww' hvw hvw'
  -- Two distinct symmetric-difference neighbors of one vertex cannot both come from the same
  -- matching, because each matching uses at most one edge at that vertex.
  have hxor : (M.Adj v w ∨ N.Adj v w) ∧ ¬ (M.Adj v w ∧ N.Adj v w) := by
    simpa [SimpleGraph.Subgraph.mem_edgeSet] using
      (memSymmDiffSpanningCoe_iff G).mp hvw
  have hxor' : (M.Adj v w' ∨ N.Adj v w') ∧ ¬ (M.Adj v w' ∧ N.Adj v w') := by
    simpa [SimpleGraph.Subgraph.mem_edgeSet] using
      (memSymmDiffSpanningCoe_iff G).mp hvw'
  have hM_iff : M.Adj v w ↔ ¬ M.Adj v w' := by
    constructor
    · intro hMv
      intro hMw'
      exact hww' (hM.eq_of_adj_left hMv hMw')
    · intro hnot
      rcases hxor.1 with hMv | hNv
      · exact hMv
      · exfalso
        have hNw' : ¬ N.Adj v w' := by
          intro hNw'
          exact hww' (hN.eq_of_adj_left hNv hNw')
        rcases hxor'.1 with hMw' | hNalt
        · exact hnot hMw'
        · exact hNw' hNalt
  -- Rewrite the conclusion back into the spanning-coercion graph.
  simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hM_iff

/-- Helper for Exercise 4.27: every vertex of the symmetric difference of two matchings has at
most two neighbors. -/
private lemma matchingSymmDiff_neighborSet_ncard_le_two {M N : G.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching) (v : V) :
    ((M.spanningCoe ∆ N.spanningCoe).neighborSet v).ncard ≤ 2 := by
  classical
  by_contra hgt
  have hthree : 2 < ((M.spanningCoe ∆ N.spanningCoe).neighborSet v).ncard := by
    exact lt_of_not_ge hgt
  obtain ⟨w, hw, w', hw', z, hz, hww', hwz, hw'z⟩ :=
    (Set.two_lt_ncard).mp hthree
  have halt : (M.spanningCoe ∆ N.spanningCoe).IsAlternating M.spanningCoe :=
    matchingSymmDiff_isAlternating G hM hN
  have hmww' : M.spanningCoe.Adj v w ↔ ¬ M.spanningCoe.Adj v w' := halt hww' hw hw'
  have hmwz : M.spanningCoe.Adj v w ↔ ¬ M.spanningCoe.Adj v z := halt hwz hw hz
  have hmw'z : M.spanningCoe.Adj v w' ↔ ¬ M.spanningCoe.Adj v z := halt hw'z hw' hz
  by_cases hMw : M.spanningCoe.Adj v w
  · have hMw' : ¬ M.spanningCoe.Adj v w' := hmww'.mp hMw
    have hMz : ¬ M.spanningCoe.Adj v z := hmwz.mp hMw
    have hMw'' : M.spanningCoe.Adj v w' := hmw'z.mpr hMz
    exact hMw' hMw''
  · have hMw' : M.spanningCoe.Adj v w' := by
      by_contra hMw''
      exact hMw (hmww'.mpr hMw'')
    have hMz : M.spanningCoe.Adj v z := by
      by_contra hMz'
      exact hMw (hmwz.mpr hMz')
    exact hw'z (hM.eq_of_adj_left hMw' hMz)

/-- Helper for Exercise 4.27: a finite connected graph with a nonempty edge set and vertex degree
at most `2` is either a union of cycles or a tree. -/
private lemma connectedIsCycles_or_isTree_of_neighborSet_ncard_le_two {W : Type*}
    [Finite W] (K : SimpleGraph W) [DecidableRel K.Adj]
    (hconn : K.Connected) (hnon : K.edgeSet.Nonempty)
    (hdeg : ∀ v : W, (K.neighborSet v).ncard ≤ 2) :
    K.IsCycles ∨ K.IsTree := by
  classical
  let _ : Fintype W := Fintype.ofFinite W
  by_cases hcyc : K.IsCycles
  · exact Or.inl hcyc
  · right
    have hleaf : ∃ v : W, K.degree v = 1 := by
      by_contra hnoLeaf
      have hcyc' : K.IsCycles := by
        intro v hv
        have hvle : (K.neighborSet v).ncard ≤ 2 := hdeg v
        have hvne : (K.neighborSet v).ncard ≠ 1 := by
          intro hvone
          have hvone' : Fintype.card (K.neighborSet v) = 1 := by
            rcases Set.ncard_eq_one.mp hvone with ⟨a, ha⟩
            simpa [ha]
          exact hnoLeaf ⟨v, by
            calc
              K.degree v = Fintype.card (K.neighborSet v) := by
                rw [SimpleGraph.card_neighborSet_eq_degree]
              _ = 1 := hvone'⟩
        have hvpos : 0 < (K.neighborSet v).ncard := by
          exact (Set.ncard_pos).2 hv
        omega
      exact hcyc hcyc'
    obtain ⟨v, hvdeg⟩ := hleaf
    have hdeg_le_two : ∀ w : W, K.degree w ≤ 2 := by
      intro w
      calc
        K.degree w = Fintype.card (K.neighborSet w) := by
          rw [SimpleGraph.card_neighborSet_eq_degree]
        _ = (K.neighborSet w).ncard := by rw [Set.fintypeCard_eq_ncard]
        _ ≤ 2 := hdeg w
    have hsum_lt : ∑ w : W, K.degree w < ∑ _ : W, 2 := by
      -- The degree-`1` vertex forces a strict inequality in the handshaking sum.
      exact Finset.sum_lt_sum (fun w _ ↦ hdeg_le_two w) ⟨v, Finset.mem_univ _, by omega⟩
    have hedge_lt : Nat.card K.edgeSet < Nat.card W := by
      -- The degree sum is strictly below `2 * |V|`, so the edge count is strictly below `|V|`.
      have hsum :
          ∑ w : W, K.degree w = 2 * Fintype.card K.edgeSet := by
        simpa [SimpleGraph.edgeFinset_card] using K.sum_degrees_eq_twice_card_edges
      rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum_lt
      have hsum_lt' : 2 * Nat.card K.edgeSet < 2 * Nat.card W := by
        simpa [Nat.card_eq_fintype_card, Nat.mul_comm] using hsum_lt
      have hedge_lt' : Fintype.card K.edgeSet < Fintype.card W := by
        have : Nat.card K.edgeSet < Nat.card W := by
          omega
        simpa [Nat.card_eq_fintype_card] using this
      simpa [Nat.card_eq_fintype_card] using hedge_lt'
    have hedge_card : Nat.card K.edgeSet + 1 = Nat.card W := by
      -- Connected graphs satisfy `|V| ≤ |E| + 1`, and the strict upper bound gives the reverse
      -- inequality.
      exact le_antisymm (Nat.succ_le_of_lt hedge_lt)
        (SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hconn)
    have htreeK : K.IsTree :=
      (SimpleGraph.isTree_iff_connected_and_card).2 ⟨hconn, hedge_card⟩
    exact htreeK

/-- Helper for Exercise 4.27: in the connected `IsCycles` branch, mathlib's cycle API already
produces a cycle walk whose spanning graph is the whole component. -/
private lemma connectedIsCycles_isCycleOrPath {W : Type*}
    [Finite W] (K : SimpleGraph W) [DecidableEq W] [DecidableRel K.Adj]
    (hconn : K.Connected) (hnon : K.edgeSet.Nonempty) (hcyc : K.IsCycles) :
    K.IsCycleOrPath := by
  classical
  let _ : Fintype W := Fintype.ofFinite W
  rcases hnon with ⟨e, he⟩
  induction e using Sym2.ind with
  | h v w =>
      let c : K.ConnectedComponent := K.connectedComponentMk v
      have hv : v ∈ c.supp := by
        simpa [c] using (K.connectedComponentMk_mem : v ∈ K.connectedComponentMk v)
      have hneigh : (K.neighborSet v).Nonempty := ⟨w, by simpa using he⟩
      have hc_supp : c.supp = Set.univ := by
        -- Connectedness collapses the chosen connected component to the whole vertex set.
        ext x
        constructor
        · intro _
          simp
        · intro _
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
          simpa [c] using (SimpleGraph.ConnectedComponent.sound (hconn x v))
      obtain ⟨p, hpCycle, hpVerts⟩ :=
        SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
          hcyc hv hneigh
      refine Or.inl ⟨v, p, hpCycle, ?_⟩
      have hpVertsUniv : p.toSubgraph.verts = Set.univ := by
        simpa [hc_supp] using hpVerts
      -- Once the cycle walk visits every vertex, its spanning coercion recovers all adjacencies of
      -- `K`, because `IsCycles` forbids extra edges through a visited vertex.
      ext x y
      constructor
      · intro hxy
        have hx : x ∈ p.toSubgraph.verts := by
          rw [hpVertsUniv]
          simp
        exact
          (hpCycle.adj_toSubgraph_iff_of_isCycles hcyc hx y).1
            (by simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hxy)
      · intro hxy
        have hx : x ∈ p.toSubgraph.verts := by
          rw [hpVertsUniv]
          simp
        exact
          (by
            simpa [SimpleGraph.Subgraph.spanningCoe_adj] using
              (hpCycle.adj_toSubgraph_iff_of_isCycles hcyc hx y).2 hxy)

/-- Helper for Exercise 4.27: a maximal path in a graph of degree at most `2` already contains
every neighbor of every support vertex. -/
private lemma maximalPath_support_closed_under_adj_of_neighborSet_ncard_le_two {W : Type*}
    [Finite W] (K : SimpleGraph W) [DecidableEq W] [DecidableRel K.Adj]
    (hdeg : ∀ v : W, (K.neighborSet v).ncard ≤ 2)
    {u v : W} {p : K.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (u' v' : W) (p' : K.Walk u' v'), p'.IsPath → p'.length ≤ p.length)
    {x y : W} (hx : x ∈ p.support) (hxy : K.Adj x y) :
    y ∈ p.support := by
  -- Route correction: the intended proof splits support vertices into start/end/internal cases.
  -- Endpoints contradict maximality by extending `p`; internal vertices contradict the degree
  -- bound because `p` already contributes two distinct neighbors there.
  classical
  by_cases hy : y ∈ p.support
  · exact hy
  obtain ⟨i, hix, hi_len⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  by_cases hi0 : i = 0
  · -- An outside neighbor of the startpoint extends the path by one edge.
    have hxu : x = u := by simpa [hi0] using hix.symm
    subst hxu
    have hp' : (p.cons hxy.symm).IsPath := hp.cons hy
    have hlen := hmax y v (p.cons hxy.symm) hp'
    rw [SimpleGraph.Walk.length_cons] at hlen
    omega
  by_cases hiv : i = p.length
  · -- An outside neighbor of the endpoint also extends the path by one edge.
    have hxv : x = v := by simpa [hiv] using hix.symm
    subst hxv
    have hp' : (p.concat hxy).IsPath := hp.concat hy hxy
    have hlen := hmax u y (p.concat hxy) hp'
    rw [SimpleGraph.Walk.length_concat] at hlen
    omega
  · -- Any third neighbor of an internal support vertex violates the degree-`≤ 2` bound.
    have hi_lt : i < p.length := by omega
    have hsub : p.toSubgraph.neighborSet x ⊂ K.neighborSet x := by
      refine ⟨p.toSubgraph.neighborSet_subset x, ?_⟩
      intro hrev
      have hySub : y ∈ p.toSubgraph.neighborSet x := hrev hxy
      exact hy <| p.mem_verts_toSubgraph.mp <| p.toSubgraph.edge_vert hySub.symm
    have hcard_path : (p.toSubgraph.neighborSet x).ncard = 2 := by
      simpa [hix] using hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hi_lt
    have hlt : 2 < (K.neighborSet x).ncard := by
      rw [← hcard_path]
      exact Set.ncard_lt_ncard hsub
    exfalso
    exact (not_lt_of_ge (hdeg x)) hlt

/-- Helper for Exercise 4.27: a connected finite tree with a nonempty edge set and degree at most
`2` is spanned by a nontrivial path. -/
private lemma connectedIsTree_isPath_of_neighborSet_ncard_le_two {W : Type*}
    [Finite W] (K : SimpleGraph W) [DecidableEq W] [DecidableRel K.Adj]
    (htree : K.IsTree) (hnon : K.edgeSet.Nonempty)
    (hdeg : ∀ v : W, (K.neighborSet v).ncard ≤ 2) :
    ∃ u v, u ≠ v ∧ ∃ p : K.Walk u v, p.IsPath ∧ p.toSubgraph.spanningCoe = K := by
  -- Choose a longest path `p`, prove its support is adjacency-closed using the preceding
  -- helper, show every vertex of the connected tree lies in that support, and conclude by minimal
  -- connectedness that `p.toSubgraph.spanningCoe = K`.
  classical
  let _ : Nonempty W := htree.connected.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length K
  have hsupport_closed :
      ∀ ⦃x y : W⦄, x ∈ p.support → K.Adj x y → y ∈ p.support := by
    intro x y hx hxy
    exact maximalPath_support_closed_under_adj_of_neighborSet_ncard_le_two
      K hdeg hp hmax hx hxy
  let S : K.Subgraph := (⊤ : K.Subgraph).induce {w : W | w ∈ p.support}
  have hSconn : S.Connected := by
    -- The walk support is connected inside the induced support subgraph.
    refine SimpleGraph.Subgraph.connected_iff'.2 ?_
    simpa [S, SimpleGraph.induce_eq_coe_induce_top] using p.connected_induce_support
  have hSadj :
      ∀ x ∈ S.verts, ∀ y, K.Adj x y → S.Adj x y := by
    intro x hx y hxy
    refine ⟨hx, hsupport_closed (by simpa [S] using hx) hxy, ?_⟩
    simpa [S] using hxy
  obtain ⟨c, hc⟩ :=
    SimpleGraph.Subgraph.Connected.exists_verts_eq_connectedComponentSupp
      hSconn hSadj
  have huS : u ∈ S.verts := by
    simpa [S] using p.start_mem_support
  have huC : u ∈ c.supp := by
    rw [← hc]
    exact huS
  have hcu : K.connectedComponentMk u = c := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp huC
  have hc_univ : c.supp = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.sound (htree.connected x u)).trans hcu
  have hsupport_univ : {w : W | w ∈ p.support} = Set.univ := by
    calc
      {w : W | w ∈ p.support} = S.verts := by rfl
      _ = c.supp := hc
      _ = Set.univ := hc_univ
  have hspan : p.toSubgraph.IsSpanning := by
    rw [SimpleGraph.Subgraph.isSpanning_iff]
    simpa [SimpleGraph.Walk.verts_toSubgraph] using hsupport_univ
  have hpconn : p.toSubgraph.spanningCoe.Connected := by
    -- Once the path visits every vertex, connectedness transfers through the spanning-coercion
    -- graph equivalence.
    exact
      (p.toSubgraph.spanningCoeEquivCoeOfSpanning hspan).connected_iff.mpr
        (show p.toSubgraph.coe.Connected from p.toSubgraph_connected)
  have hp_eq : p.toSubgraph.spanningCoe = K := by
    -- Trees are minimally connected, so any connected spanning subgraph already contains every
    -- ambient edge, hence it must coincide with the whole tree.
    have hminimal : Minimal SimpleGraph.Connected K :=
      (SimpleGraph.isTree_iff_minimal_connected).mp htree
    exact hminimal.eq_of_le hpconn p.toSubgraph.spanningCoe_le
  have hlen_pos : 0 < p.length := by
    rcases hnon with ⟨e, he⟩
    induction e using Sym2.ind with
    | h a b =>
        have hpEdge : he.toWalk.IsPath := SimpleGraph.Walk.IsPath.of_adj he
        have hlen := hmax a b he.toWalk hpEdge
        simpa using hlen
  have huv : u ≠ v := by
    intro huv
    subst huv
    have hpnil : p = .nil := (SimpleGraph.Walk.isPath_iff_eq_nil p).mp hp
    simpa [hpnil] using hlen_pos
  exact ⟨u, v, huv, p, hp, hp_eq⟩

/-- Helper for Exercise 4.27: a connected finite graph with a nonempty edge set and degree at
most `2` is a cycle or a path. -/
private lemma connectedIsCycleOrPath_of_neighborSet_ncard_le_two {W : Type*}
    [Finite W] (K : SimpleGraph W) [DecidableEq W] [DecidableRel K.Adj]
    (hconn : K.Connected) (hnon : K.edgeSet.Nonempty)
    (hdeg : ∀ v : W, (K.neighborSet v).ncard ≤ 2) :
    K.IsCycleOrPath := by
  classical
  rcases connectedIsCycles_or_isTree_of_neighborSet_ncard_le_two
      K hconn hnon hdeg with hcyc | htree
  · exact connectedIsCycles_isCycleOrPath K hconn hnon hcyc
  · -- The tree branch is reduced to the generic maximal-path argument above.
    rcases connectedIsTree_isPath_of_neighborSet_ncard_le_two
        K htree hnon hdeg with ⟨u, v, huv, p, hp, hpSpan⟩
    exact Or.inr ⟨u, v, huv, p, hp, hpSpan⟩

/-- Helper for Exercise 4.27: the neighbor set of a vertex inside a connected component has the
same cardinality as its ambient neighbor set. -/
private lemma connectedComponentNeighborSet_ncard_eq_ambient {W : Type*}
    [Finite W] (K : SimpleGraph W) [DecidableRel K.Adj]
    (c : K.ConnectedComponent) (v : c.supp) :
    (c.toSimpleGraph.neighborSet v).ncard = (K.neighborSet v.1).ncard := by
  classical
  let e : c.toSimpleGraph.neighborSet v ≃ K.neighborSet v.1 := by
    refine
      { toFun := fun w ↦
          ⟨w.1.1, (c.toSimpleGraph_adj v.property w.1.property).1 w.2⟩
        invFun := fun w ↦ by
          let hw : w.1 ∈ c.supp := (c.mem_supp_congr_adj w.2).mp v.property
          exact ⟨⟨w.1, hw⟩, (c.toSimpleGraph_adj v.property hw).2 w.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro w
      ext
      rfl
    · intro w
      ext
      rfl
  -- Compare the two finite neighbor sets through the explicit adjacency-preserving equivalence.
  calc
    (c.toSimpleGraph.neighborSet v).ncard = Fintype.card (c.toSimpleGraph.neighborSet v) := by
      rw [Set.fintypeCard_eq_ncard]
    _ = Fintype.card (K.neighborSet v.1) := Fintype.card_congr e
    _ = (K.neighborSet v.1).ncard := by
      rw [Set.fintypeCard_eq_ncard]

/-- Helper for Exercise 4.27: every nonempty connected component of the symmetric difference of
two matchings is either a union of cycles or a tree. -/
private lemma symmDiffConnectedComponent_isCycles_or_isTree {M N : G.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching)
    (c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent)
    (hc : c.toSimpleGraph.edgeSet.Nonempty) :
    c.toSimpleGraph.IsCycles ∨ c.toSimpleGraph.IsTree := by
  classical
  have hdeg_component : ∀ v : c.supp, (c.toSimpleGraph.neighborSet v).ncard ≤ 2 := by
    intro v
    rw [connectedComponentNeighborSet_ncard_eq_ambient (M.spanningCoe ∆ N.spanningCoe) c v]
    simpa using matchingSymmDiff_neighborSet_ncard_le_two
      G hM hN v.1
  -- The component inherits connectedness and the ambient degree bound, so the generic split
  -- applies verbatim on the subtype graph.
  exact connectedIsCycles_or_isTree_of_neighborSet_ncard_le_two
    c.toSimpleGraph c.connected_toSimpleGraph hc hdeg_component

/-- Helper for Exercise 4.27: every nonempty connected component of the symmetric difference of
two matchings is a cycle or a path. -/
private lemma symmDiffConnectedComponent_isCycleOrPath {M N : G.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching)
    (c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent)
    (hc : c.toSimpleGraph.edgeSet.Nonempty) :
    c.toSimpleGraph.IsCycleOrPath := by
  -- Componentwise degree transport reduces this directly to the previous path/cycle classifier.
  have hdeg_component : ∀ v : c.supp, (c.toSimpleGraph.neighborSet v).ncard ≤ 2 := by
    intro v
    rw [connectedComponentNeighborSet_ncard_eq_ambient (M.spanningCoe ∆ N.spanningCoe) c v]
    simpa using matchingSymmDiff_neighborSet_ncard_le_two
      G hM hN v.1
  -- The generic connected degree-`≤ 2` classifier now applies directly to the component graph.
  exact connectedIsCycleOrPath_of_neighborSet_ncard_le_two
    c.toSimpleGraph c.connected_toSimpleGraph hc hdeg_component

/-- Helper for Exercise 4.27: if a connected component is the unique edge-nonempty component of
`H`, then its spanning coercion already recovers all edges of `H`. -/
private lemma spanningCoe_eq_of_uniqueEdgeNonemptyConnectedComponent {H : SimpleGraph V}
    [DecidableEq V] [DecidableRel H.Adj] (c : H.ConnectedComponent)
    (hc : c.toSimpleGraph.edgeSet.Nonempty)
    (hunique : ∀ d : H.ConnectedComponent, d.toSimpleGraph.edgeSet.Nonempty → d = c) :
    c.toSimpleGraph.spanningCoe = H := by
  ext v w
  constructor
  · intro h
    -- Every edge of the component spanning coercion is already an ambient edge of `H`.
    exact (SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph c).1 h |>.2
  · intro h
    let d : H.ConnectedComponent := H.connectedComponentMk v
    have hdv : v ∈ d.supp := by
      simpa [d] using (H.connectedComponentMk_mem : v ∈ H.connectedComponentMk v)
    have hdw : w ∈ d.supp := (d.mem_supp_congr_adj h).mp hdv
    have hdnon : d.toSimpleGraph.edgeSet.Nonempty := by
      -- The ambient edge `vw` witnesses that the component of `v` is edge-nonempty.
      refine ⟨s(⟨v, hdv⟩, ⟨w, hdw⟩), ?_⟩
      simpa [d.toSimpleGraph_adj hdv hdw] using h
    have hd : d = c := hunique d hdnon
    have hvc : v ∈ c.supp := by
      simpa [hd] using hdv
    -- The spanning-coercion adjacency test now reduces the goal to ambient adjacency.
    exact (SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph c).2 ⟨hvc, h⟩

/-- Helper for Exercise 4.27: if a walk spans an edge-nonempty connected component after applying
`spanningCoe`, then it already uses every edge and vertex of that component. -/
private lemma walkToSubgraph_eq_top_of_spanningCoe_eq_connectedComponent
    {H : SimpleGraph V} [DecidableEq V] [DecidableRel H.Adj] (c : H.ConnectedComponent)
    (hc : c.toSimpleGraph.edgeSet.Nonempty)
    {u v : c.supp} {p : c.toSimpleGraph.Walk u v}
    (hspan : p.toSubgraph.spanningCoe = c.toSimpleGraph) :
    p.toSubgraph = ⊤ := by
  apply le_antisymm le_top
  refine ⟨?_, ?_⟩
  · intro x _
    have hclosed :
        ∀ z ∈ p.toSubgraph.verts, ∀ y, c.toSimpleGraph.Adj z y → p.toSubgraph.Adj z y := by
      intro z hz y hzy
      -- The spanning-coercion equality turns each ambient component edge back into a walk edge.
      have hzy' : p.toSubgraph.spanningCoe.Adj z y := by
        rwa [hspan]
      simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hzy'
    have hu : u ∈ p.toSubgraph.verts := p.start_mem_verts_toSubgraph
    -- Reachability inside the connected component forces every vertex into the walk support.
    exact (c.connected_toSimpleGraph u x).mem_subgraphVerts hclosed hu
  · intro x y hxy
    -- Every top-subgraph edge of the component belongs to the walk by the spanning hypothesis.
    have hxy' : p.toSubgraph.spanningCoe.Adj x y := by
      rwa [hspan]
    simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hxy'

/-- Helper for Exercise 4.27: after a spanning walk fills a connected component, mapping the walk
back to the ambient graph recovers that component as a spanning subgraph. -/
private lemma mapWalk_spanningCoe_eq_connectedComponent
    {H : SimpleGraph V} [DecidableEq V] [DecidableRel H.Adj] (c : H.ConnectedComponent)
    {u v : c.supp} {p : c.toSimpleGraph.Walk u v}
    (hpTop : p.toSubgraph = ⊤) :
    (p.map c.toSimpleGraph_hom).toSubgraph.spanningCoe = c.toSimpleGraph.spanningCoe := by
  -- After the walk fills the component, the mapped top subgraph is exactly the component
  -- subgraph inside the ambient graph.
  rw [SimpleGraph.Walk.toSubgraph_map, hpTop]
  ext x y
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact
      (SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph c).2
        ⟨a.property, hab⟩
  · intro h
    rcases
        (SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph c).1 h with
      ⟨hx, hxy⟩
    have hy : y ∈ c.supp := (c.mem_supp_congr_adj hxy).mp hx
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, (c.toSimpleGraph_adj hx hy).2 hxy, rfl, rfl⟩

/-- Helper for Exercise 4.27: a graph with exactly one edge-nonempty connected component is a
cycle or a path as soon as that component is. -/
private lemma isCycleOrPath_of_uniqueEdgeNonemptyConnectedComponent {H : SimpleGraph V}
    [DecidableEq V] [DecidableRel H.Adj] (c : H.ConnectedComponent)
    (hc : c.toSimpleGraph.edgeSet.Nonempty)
    (hunique : ∀ d : H.ConnectedComponent, d.toSimpleGraph.edgeSet.Nonempty → d = c)
    (hcyp : c.toSimpleGraph.IsCycleOrPath) :
    H.IsCycleOrPath := by
  have hspan :
      c.toSimpleGraph.spanningCoe = H :=
    spanningCoe_eq_of_uniqueEdgeNonemptyConnectedComponent
      c hc hunique
  have hhom_injective : Function.Injective c.toSimpleGraph_hom := by
    intro x y hxy
    exact Subtype.ext hxy
  rcases hcyp with ⟨v, p, hpCycle, hpSpan⟩ | ⟨u, v, huv, p, hpPath, hpSpan⟩
  · have hpTop : p.toSubgraph = ⊤ :=
      walkToSubgraph_eq_top_of_spanningCoe_eq_connectedComponent
        c hc hpSpan
    refine Or.inl ⟨v.1, p.map c.toSimpleGraph_hom, hpCycle.map hhom_injective, ?_⟩
    -- The mapped cycle walk spans the whole ambient graph because `c` is the only nontrivial
    -- connected component.
    calc
      (p.map c.toSimpleGraph_hom).toSubgraph.spanningCoe = c.toSimpleGraph.spanningCoe := by
        exact mapWalk_spanningCoe_eq_connectedComponent c hpTop
      _ = H := hspan
  · have hpTop : p.toSubgraph = ⊤ :=
      walkToSubgraph_eq_top_of_spanningCoe_eq_connectedComponent
        c hc hpSpan
    have huv_val : u.1 ≠ v.1 := by
      intro huv'
      exact huv (Subtype.ext huv')
    refine Or.inr
      ⟨u.1, v.1, huv_val, p.map c.toSimpleGraph_hom,
        SimpleGraph.Walk.map_isPath_of_injective hhom_injective hpPath, ?_⟩
    -- The same mapped-walk computation handles the spanning equality in the path case.
    calc
      (p.map c.toSimpleGraph_hom).toSubgraph.spanningCoe = c.toSimpleGraph.spanningCoe := by
        exact mapWalk_spanningCoe_eq_connectedComponent c hpTop
      _ = H := hspan

/-- Helper for Exercise 4.27: if a walk spans `H` after applying `spanningCoe`, then the walk
support is exactly the support of one connected component of `H`. -/
private lemma walkSupport_eq_connectedComponentSupp_of_spanningCoe_eq {H : SimpleGraph V}
    [DecidableEq V] [DecidableRel H.Adj] {u v : V} {p : H.Walk u v}
    (hspan : p.toSubgraph.spanningCoe = H) :
    ∃ c : H.ConnectedComponent, {w : V | w ∈ p.support} = c.supp := by
  have hclosed :
      ∀ x ∈ p.toSubgraph.verts, ∀ y, H.Adj x y → p.toSubgraph.Adj x y := by
    intro x hx y hxy
    -- Any ambient edge of `H` adjacent to the walk support already lies in the walk subgraph.
    have hxy' : p.toSubgraph.spanningCoe.Adj x y := by
      rwa [hspan]
    simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hxy'
  -- The walk-support subgraph is connected and adjacency-closed, so it is one connected component.
  obtain ⟨c, hc⟩ :=
    p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hclosed
  exact ⟨c, by simpa [SimpleGraph.Walk.verts_toSubgraph] using hc⟩

/-- Helper for Exercise 4.27: a graph that is a single spanning cycle or path has only one
edge-nonempty connected component. -/
private lemma isCycleOrPath_has_uniqueEdgeNonemptyConnectedComponent {H : SimpleGraph V}
    [DecidableEq V] [DecidableRel H.Adj] (hH : H.IsCycleOrPath) :
    ∃ c : H.ConnectedComponent, ∀ d : H.ConnectedComponent, d.toSimpleGraph.edgeSet.Nonempty → d = c := by
  rcases hH with ⟨v, p, _hpCycle, hpSpan⟩ | ⟨u, v, _huv, p, _hpPath, hpSpan⟩
  · obtain ⟨c, hc⟩ := walkSupport_eq_connectedComponentSupp_of_spanningCoe_eq hpSpan
    refine ⟨c, ?_⟩
    intro d hdnon
    rcases hdnon with ⟨e, he⟩
    induction e using Sym2.ind with
    | h x y =>
        have hxySub : p.toSubgraph.Adj x.1 y.1 := by
          have hxySpan : p.toSubgraph.spanningCoe.Adj x.1 y.1 := by
            rw [hpSpan]
            exact (d.toSimpleGraph_adj x.property y.property).1 (by simpa using he)
          simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hxySpan
        have hxc : x.1 ∈ c.supp := by
          rw [← hc]
          simpa using p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hxySub)
        exact
          (SimpleGraph.ConnectedComponent.eq_of_common_vertex
            (c' := d) hxc x.property).symm
  · obtain ⟨c, hc⟩ := walkSupport_eq_connectedComponentSupp_of_spanningCoe_eq hpSpan
    refine ⟨c, ?_⟩
    intro d hdnon
    rcases hdnon with ⟨e, he⟩
    induction e using Sym2.ind with
    | h x y =>
        have hxySub : p.toSubgraph.Adj x.1 y.1 := by
          have hxySpan : p.toSubgraph.spanningCoe.Adj x.1 y.1 := by
            rw [hpSpan]
            exact (d.toSimpleGraph_adj x.property y.property).1 (by simpa using he)
          simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hxySpan
        have hxc : x.1 ∈ c.supp := by
          rw [← hc]
          simpa using p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hxySub)
        exact
          (SimpleGraph.ConnectedComponent.eq_of_common_vertex
            (c' := d) hxc x.property).symm

/-- Helper for Exercise 4.27: if the symmetric difference of two matchings is not a single cycle
or path, then it has at least two distinct edge-nonempty connected components. -/
private lemma existsTwoEdgeNonemptySymmDiffComponents_of_not_isCycleOrPath
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching) (hMN : M ≠ N)
    (hnot : ¬ (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath) :
    ∃ c d : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent,
      c ≠ d ∧ c.toSimpleGraph.edgeSet.Nonempty ∧ d.toSimpleGraph.edgeSet.Nonempty := by
  have hedge_ne : M.edgeSet ≠ N.edgeSet := by
    intro hEdge
    exact hMN <| SimpleGraph.Subgraph.IsMatching.injOn_edgeSet hM hN hEdge
  have hsymm_nonempty : (M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hEmpty
    exact hedge_ne <| (Set.symmDiff_eq_empty.mp hEmpty)
  obtain ⟨e, he⟩ := hsymm_nonempty
  induction e using Sym2.ind with
  | h v w =>
      have hAdj : (M.spanningCoe ∆ N.spanningCoe).Adj v w := by
        simpa [SimpleGraph.Subgraph.mem_edgeSet] using he
      let c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent :=
        (M.spanningCoe ∆ N.spanningCoe).connectedComponentMk v
      have hc : c.toSimpleGraph.edgeSet.Nonempty := by
        have hv : v ∈ c.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        have hw : w ∈ c.supp := (c.mem_supp_congr_adj hAdj).mp hv
        have hAdjC : c.toSimpleGraph.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
          exact (c.toSimpleGraph_adj hv hw).2 hAdj
        exact ⟨s(⟨v, hv⟩, ⟨w, hw⟩), by simpa using hAdjC⟩
      by_contra hNoPair
      have hunique : ∀ d : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent,
          d.toSimpleGraph.edgeSet.Nonempty → d = c := by
        intro d hd
        by_contra hdc
        have hcd : c ≠ d := by
          intro hcd'
          exact hdc hcd'.symm
        exact hNoPair ⟨c, d, hcd, hc, hd⟩
      have hcyc :
          (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath :=
        isCycleOrPath_of_uniqueEdgeNonemptyConnectedComponent
          c hc hunique
          (symmDiffConnectedComponent_isCycleOrPath
            G hM hN c hc)
      exact hnot hcyc

/-- Helper for Exercise 4.27: every subgraph incidence coordinate is a `0/1` value. -/
private lemma subgraphIncidenceVector_eq_zero_or_one {H : G.Subgraph} (e : G.edgeSet) :
    G.subgraphIncidenceVector ℝ H e = 0 ∨ G.subgraphIncidenceVector ℝ H e = 1 := by
  -- Expand the incidence coordinate into its defining indicator function.
  by_cases he : (e : Sym2 V) ∈ H.edgeSet
  · right
    simp [SimpleGraph.subgraphIncidenceVector, he]
  · left
    simp [SimpleGraph.subgraphIncidenceVector, he]

/-- Helper for Exercise 4.27: two `0/1` numbers summing to twice a third `0/1` number must both
equal that third value. -/
private lemma zeroOne_pair_eq_double {a b c : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hsum : b + c = a + a) :
    b = a ∧ c = a := by
  -- A short case split on the three possible `0/1` coordinates leaves only the compatible sums.
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · rcases hc with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · norm_num at hsum
    · rcases hc with rfl | rfl
      · norm_num at hsum
      · norm_num at hsum
  · rcases hb with rfl | rfl
    · rcases hc with rfl | rfl
      · norm_num at hsum
      · norm_num at hsum
    · rcases hc with rfl | rfl
      · norm_num at hsum
      · exact ⟨rfl, rfl⟩

/-- Helper for Exercise 4.27: two `0/1` numbers summing to `1` are complementary. -/
private lemma zeroOne_pair_sum_eq_one {a b : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hsum : a + b = 1) :
    (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  -- The only admissible `0/1` pairs with total sum `1` are `(1,0)` and `(0,1)`.
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · norm_num at hsum
    · exact Or.inr ⟨rfl, rfl⟩
  · rcases hb with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · norm_num at hsum

/-- Helper for Exercise 4.27: if two incidence-vector pairs have the same sum, then every edge
outside `M △ N` is fixed in both midpoint components. -/
private lemma subgraphIncidenceVector_agrees_off_symmDiff_of_add_eq
    {M N K L : G.Subgraph}
    (hadd :
      G.subgraphIncidenceVector ℝ M + G.subgraphIncidenceVector ℝ N =
        G.subgraphIncidenceVector ℝ K + G.subgraphIncidenceVector ℝ L)
    {e : G.edgeSet}
    (he : (e : Sym2 V) ∉ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet) :
    G.subgraphIncidenceVector ℝ K e = G.subgraphIncidenceVector ℝ M e ∧
      G.subgraphIncidenceVector ℝ L e = G.subgraphIncidenceVector ℝ M e := by
  have hMN_mem : ((e : Sym2 V) ∈ M.edgeSet) ↔ ((e : Sym2 V) ∈ N.edgeSet) := by
    -- Outside the symmetric difference, the two endpoint matchings make the same edge decision.
    by_cases hMe : (e : Sym2 V) ∈ M.edgeSet <;> by_cases hNe : (e : Sym2 V) ∈ N.edgeSet <;>
      simp [symmDiff_def, SimpleGraph.Subgraph.mem_edgeSet, hMe, hNe] at he ⊢
  have hMN :
      G.subgraphIncidenceVector ℝ M e = G.subgraphIncidenceVector ℝ N e := by
    -- Rewrite the shared edge decision into equality of the two `0/1` coordinates.
    by_cases hMe : (e : Sym2 V) ∈ M.edgeSet
    · simp [SimpleGraph.subgraphIncidenceVector, hMe, hMN_mem.mp hMe]
    · have hNe : (e : Sym2 V) ∉ N.edgeSet := by
        intro hNe
        exact hMe (hMN_mem.mpr hNe)
      simp [SimpleGraph.subgraphIncidenceVector, hMe, hNe]
  have hsume :
      G.subgraphIncidenceVector ℝ K e + G.subgraphIncidenceVector ℝ L e =
        G.subgraphIncidenceVector ℝ M e + G.subgraphIncidenceVector ℝ M e := by
    -- Evaluate the vector identity at the chosen edge coordinate.
    simpa [Pi.add_apply, hMN, add_comm] using congrArg (fun x : G.edgeSet → ℝ ↦ x e) hadd |>.symm
  exact zeroOne_pair_eq_double
    (subgraphIncidenceVector_eq_zero_or_one G e)
    (subgraphIncidenceVector_eq_zero_or_one G e)
    (subgraphIncidenceVector_eq_zero_or_one G e)
    hsume

/-- Helper for Exercise 4.27: if two incidence-vector pairs have the same sum, then every edge
of `M △ N` is split complementary between the two midpoint components. -/
private lemma subgraphIncidenceVector_complementary_on_symmDiff_of_add_eq
    {M N K L : G.Subgraph}
    (hadd :
      G.subgraphIncidenceVector ℝ M + G.subgraphIncidenceVector ℝ N =
        G.subgraphIncidenceVector ℝ K + G.subgraphIncidenceVector ℝ L)
    {e : G.edgeSet}
    (he : (e : Sym2 V) ∈ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet) :
    (G.subgraphIncidenceVector ℝ K e = 1 ∧ G.subgraphIncidenceVector ℝ L e = 0) ∨
      (G.subgraphIncidenceVector ℝ K e = 0 ∧ G.subgraphIncidenceVector ℝ L e = 1) := by
  have hxor :
      (((e : Sym2 V) ∈ M.edgeSet) ∧ (e : Sym2 V) ∉ N.edgeSet) ∨
        (((e : Sym2 V) ∈ N.edgeSet) ∧ (e : Sym2 V) ∉ M.edgeSet) := by
    -- Membership in the symmetric difference is the xor condition on the two endpoint matchings.
    simpa [symmDiff_def] using he
  have hMN :
      G.subgraphIncidenceVector ℝ M e + G.subgraphIncidenceVector ℝ N e = 1 := by
    -- Exactly one endpoint matching contributes the chosen edge.
    rcases hxor with ⟨hMe, hNnot⟩ | ⟨hNe, hMnot⟩
    ·
      simp [SimpleGraph.subgraphIncidenceVector, hMe, hNnot]
    ·
      simp [SimpleGraph.subgraphIncidenceVector, hMnot, hNe]
  have hsume :
      G.subgraphIncidenceVector ℝ K e + G.subgraphIncidenceVector ℝ L e = 1 := by
    -- Evaluate the vector identity at the chosen edge coordinate and rewrite the source sum.
    calc
      G.subgraphIncidenceVector ℝ K e + G.subgraphIncidenceVector ℝ L e =
          G.subgraphIncidenceVector ℝ M e + G.subgraphIncidenceVector ℝ N e := by
            simpa [Pi.add_apply, add_comm] using congrArg (fun x : G.edgeSet → ℝ ↦ x e) hadd |>.symm
      _ = 1 := hMN
  exact zeroOne_pair_sum_eq_one
    (subgraphIncidenceVector_eq_zero_or_one G e)
    (subgraphIncidenceVector_eq_zero_or_one G e)
    hsume

/-- Helper for Exercise 4.27: the edge set obtained by keeping the edges of `A` off `S` and the
edges of `B` on `S` is still a subgraph of `G`. -/
private lemma swapEdgeSet_subset
    (A B : G.Subgraph) (S : Set (Sym2 V)) :
    (A.edgeSet \ S) ∪ (B.edgeSet ∩ S) ⊆ G.edgeSet := by
  intro e he
  rcases he with hA | hB
  · exact A.edgeSet_subset hA.1
  · exact B.edgeSet_subset hB.1

/-- Helper for Exercise 4.27: the adjacency relation obtained by swapping two subgraphs on `S` is
supported by the ambient graph. -/
private lemma swapEdgeSubgraph_adj_sub
    (A B : G.Subgraph) (S : Set (Sym2 V)) :
    ∀ {v w : V},
      s(v, w) ∈ (A.edgeSet \ S) ∪ (B.edgeSet ∩ S) → G.Adj v w := by
  intro v w h
  exact G.mem_edgeSet.1 (swapEdgeSet_subset G A B S h)

/-- Helper for Exercise 4.27: the adjacency relation obtained by swapping two subgraphs on `S` is
symmetric. -/
private lemma swapEdgeSubgraph_symm
    (A B : G.Subgraph) (S : Set (Sym2 V)) :
    Symmetric fun v w ↦ s(v, w) ∈ (A.edgeSet \ S) ∪ (B.edgeSet ∩ S) := by
  intro v w h
  rcases h with hA | hB
  · left
    exact ⟨by simpa [Sym2.eq_swap] using hA.1,
      by simpa [Sym2.eq_swap] using hA.2⟩
  · right
    exact ⟨by simpa [Sym2.eq_swap] using hB.1,
      by simpa [Sym2.eq_swap] using hB.2⟩

/-- Helper for Exercise 4.27: each edge of a swapped subgraph is supported at both of its
endpoints. -/
private lemma swapEdgeSubgraph_edge_vert
    (A B : G.Subgraph) (S : Set (Sym2 V)) :
    ∀ {v w : V}, s(v, w) ∈ (A.edgeSet \ S) ∪ (B.edgeSet ∩ S) →
      v ∈ {u : V | ∃ z, s(u, z) ∈ (A.edgeSet \ S) ∪ (B.edgeSet ∩ S)} := by
  intro v w h
  exact ⟨w, h⟩

/-- Helper for Exercise 4.27: replacing the edges of `A` by those of `B` on a chosen edge set
`S` gives the corresponding swapped subgraph of `G`. -/
private def swapEdgeSubgraph
    (A B : G.Subgraph) (S : Set (Sym2 V)) : G.Subgraph :=
  { verts := {v | ∃ w, s(v, w) ∈ (A.edgeSet \ S) ∪ (B.edgeSet ∩ S)}
    Adj := fun v w ↦ s(v, w) ∈ (A.edgeSet \ S) ∪ (B.edgeSet ∩ S)
    adj_sub := swapEdgeSubgraph_adj_sub G A B S
    edge_vert := swapEdgeSubgraph_edge_vert G A B S
    symm := swapEdgeSubgraph_symm G A B S }

/-- Helper for Exercise 4.27: an ambient edge belongs to `swapEdgeSubgraph G G A B S` exactly when
it comes from `A` off `S` or from `B` on `S`. -/
private lemma swapEdgeSubgraph_edgeSet_iff
    {A B : G.Subgraph} {S : Set (Sym2 V)} {e : G.edgeSet} :
    (e : Sym2 V) ∈ (swapEdgeSubgraph G A B S).edgeSet ↔
      ((e : Sym2 V) ∈ A.edgeSet ∧ (e : Sym2 V) ∉ S) ∨
        ((e : Sym2 V) ∈ B.edgeSet ∧ (e : Sym2 V) ∈ S) := by
  rcases e with ⟨e, heG⟩
  induction e using Sym2.ind with
  | h v w =>
      -- Unfold the swapped subgraph on the chosen ambient edge coordinate.
      rw [SimpleGraph.Subgraph.mem_edgeSet]
      rfl

/-- Helper for Exercise 4.27: on an edge outside the swap set, the swapped incidence vector
agrees with the left input subgraph. -/
private lemma subgraphIncidenceVector_swapEdgeSubgraph_apply_of_not_mem
    {A B : G.Subgraph} {S : Set (Sym2 V)} {e : G.edgeSet}
    (he : (e : Sym2 V) ∉ S) :
    G.subgraphIncidenceVector ℝ (swapEdgeSubgraph G A B S) e =
      G.subgraphIncidenceVector ℝ A e := by
  -- Rewrite the swapped edge-membership test into the ambient `A/B` split.
  rw [SimpleGraph.subgraphIncidenceVector, SimpleGraph.subgraphIncidenceVector]
  rw [swapEdgeSubgraph_edgeSet_iff ]
  simp [he]

/-- Helper for Exercise 4.27: on an edge inside the swap set, the swapped incidence vector agrees
with the right input subgraph. -/
private lemma subgraphIncidenceVector_swapEdgeSubgraph_apply_of_mem
    {A B : G.Subgraph} {S : Set (Sym2 V)} {e : G.edgeSet}
    (he : (e : Sym2 V) ∈ S) :
    G.subgraphIncidenceVector ℝ (swapEdgeSubgraph G A B S) e =
      G.subgraphIncidenceVector ℝ B e := by
  -- Rewrite the swapped edge-membership test into the ambient `A/B` split.
  rw [SimpleGraph.subgraphIncidenceVector, SimpleGraph.subgraphIncidenceVector]
  rw [swapEdgeSubgraph_edgeSet_iff ]
  simp [he]

/-- Helper for Exercise 4.27: swapping two subgraphs on the same edge set preserves the total
incidence-vector sum. -/
private lemma swapEdgeSubgraph_incidence_add_eq
    {A B : G.Subgraph} (S : Set (Sym2 V)) :
    G.subgraphIncidenceVector ℝ (swapEdgeSubgraph G A B S) +
        G.subgraphIncidenceVector ℝ (swapEdgeSubgraph G B A S) =
      G.subgraphIncidenceVector ℝ A + G.subgraphIncidenceVector ℝ B := by
  ext e
  by_cases he : (e : Sym2 V) ∈ S
  · -- On the swap set, the two swapped coordinates exchange the `A` and `B` values.
    rw [Pi.add_apply, Pi.add_apply]
    rw [subgraphIncidenceVector_swapEdgeSubgraph_apply_of_mem
      G he]
    rw [subgraphIncidenceVector_swapEdgeSubgraph_apply_of_mem
      G he]
    simpa [add_comm]
  · -- Off the swap set, both swapped subgraphs keep their original coordinates.
    rw [Pi.add_apply, Pi.add_apply]
    rw [subgraphIncidenceVector_swapEdgeSubgraph_apply_of_not_mem
      G he]
    rw [subgraphIncidenceVector_swapEdgeSubgraph_apply_of_not_mem
      G he]

/-- Helper for Exercise 4.27: an ambient edge lies in the spanning coercion of a connected
component exactly when it is an ambient edge with both endpoints in that component. -/
private lemma connectedComponentSpanningCoe_edgeSet_iff {H : SimpleGraph V}
    [DecidableEq V] [DecidableRel H.Adj] (c : H.ConnectedComponent) {v w : V} :
    s(v, w) ∈ c.toSimpleGraph.spanningCoe.edgeSet ↔ H.Adj v w ∧ v ∈ c.supp ∧ w ∈ c.supp := by
  constructor
  · intro h
    have hAdj : c.toSimpleGraph.spanningCoe.Adj v w := by
      simpa [SimpleGraph.Subgraph.mem_edgeSet] using h
    rcases (SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph c).1 hAdj with
      ⟨hv, hvw⟩
    exact ⟨hvw, hv, (c.mem_supp_congr_adj hvw).mp hv⟩
  · rintro ⟨hvw, hv, _hw⟩
    -- The spanning-coercion adjacency criterion packages the component-membership condition.
    have hAdj : c.toSimpleGraph.spanningCoe.Adj v w := by
      exact (SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph c).2 ⟨hv, hvw⟩
    simpa [SimpleGraph.Subgraph.mem_edgeSet] using hAdj

/-- Helper for Exercise 4.27: swapping `M` and `N` on one connected component of
`M.spanningCoe ∆ N.spanningCoe` preserves the total incidence-vector sum. -/
private lemma componentSwapIncidence_add_eq_of_connectedComponent
    {M N : G.Subgraph}
    (c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent) :
    let C : Set (Sym2 V) := c.toSimpleGraph.spanningCoe.edgeSet
    let K : G.Subgraph := swapEdgeSubgraph G M N C
    let L : G.Subgraph := swapEdgeSubgraph G N M C
    G.subgraphIncidenceVector ℝ K + G.subgraphIncidenceVector ℝ L =
      G.subgraphIncidenceVector ℝ M + G.subgraphIncidenceVector ℝ N := by
  -- This is the generic swap identity specialized to the connected-component edge set.
  simp [swapEdgeSubgraph_incidence_add_eq]

/-- Helper for Exercise 4.27: distinct connected components have disjoint spanning edge sets. -/
private lemma spanningCoe_edgeSet_disjoint_of_ne_connectedComponent {H : SimpleGraph V}
    [DecidableEq V] [DecidableRel H.Adj]
    {c d : H.ConnectedComponent} (hcd : c ≠ d) :
    Disjoint c.toSimpleGraph.spanningCoe.edgeSet d.toSimpleGraph.spanningCoe.edgeSet := by
  rw [Set.disjoint_left]
  intro e hc hd
  induction e using Sym2.ind with
  | h v w =>
      have hcv : v ∈ c.supp :=
        (connectedComponentSpanningCoe_edgeSet_iff c).1 hc |>.2.1
      have hdv : v ∈ d.supp :=
        (connectedComponentSpanningCoe_edgeSet_iff d).1 hd |>.2.1
      exact hcd <| SimpleGraph.ConnectedComponent.eq_of_common_vertex hcv hdv

/-- Helper for Exercise 4.27: every edge of a nonempty connected component can be viewed as an
ambient edge coordinate of `G`. -/
private lemma existsAmbientEdgeCoord_of_component_nonempty {M N : G.Subgraph}
    (c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent)
    (hc : c.toSimpleGraph.edgeSet.Nonempty) :
    ∃ e : G.edgeSet,
      (e : Sym2 V) ∈ c.toSimpleGraph.spanningCoe.edgeSet ∧
        (e : Sym2 V) ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
  -- Expand one component edge to its ambient endpoints, then reuse the xor description to recover
  -- the corresponding ambient edge coordinate of `G`.
  rcases hc with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      have huv : c.toSimpleGraph.Adj u v := by
        simpa using he
      have huvDiff : (M.spanningCoe ∆ N.spanningCoe).Adj u.1 v.1 :=
        (c.toSimpleGraph_adj u.property v.property).1 huv
      have heDiff : s(u.1, v.1) ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
        simpa using huvDiff
      have hGAdj : G.Adj u.1 v.1 := by
        rcases
            (memSymmDiffSpanningCoe_iff G).mp
              heDiff with
          ⟨huvM | huvN, _⟩
        · exact huvM.adj_sub
        · exact huvN.adj_sub
      refine ⟨⟨s(u.1, v.1), hGAdj⟩, ?_, heDiff⟩
      change s(u.1, v.1) ∈ c.toSimpleGraph.spanningCoe.edgeSet
      simpa using he

/-- Helper for Exercise 4.27: a symmetric-difference edge touching a chosen connected component
already belongs to that component. -/
private lemma symmDiffEdge_mem_component_of_incidentVertex {M N : G.Subgraph}
    (c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent)
    {v w : V} (hv : v ∈ c.supp)
    (he : s(v, w) ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet) :
    s(v, w) ∈ c.toSimpleGraph.spanningCoe.edgeSet := by
  have hAdj : (M.spanningCoe ∆ N.spanningCoe).Adj v w := by
    simpa [SimpleGraph.Subgraph.mem_edgeSet] using he
  have hw : w ∈ c.supp := (c.mem_supp_congr_adj hAdj).mp hv
  -- A symmetric-difference edge with one endpoint in `c` has both endpoints in `c`.
  exact (connectedComponentSpanningCoe_edgeSet_iff c).2 ⟨hAdj, hv, hw⟩

/-- Helper for Exercise 4.27: on the support of the chosen component, the swapped subgraph
`swapEdgeSubgraph G M N C` has exactly the `N`-edges. -/
private lemma swapEdgeSubgraph_adj_iff_right_of_mem_component {M N : G.Subgraph}
    (c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent)
    {v w : V} (hv : v ∈ c.supp) :
    (swapEdgeSubgraph G M N c.toSimpleGraph.spanningCoe.edgeSet).Adj v w ↔ N.Adj v w := by
  constructor
  · intro hswap
    change
      s(v, w) ∈
        (M.edgeSet \ c.toSimpleGraph.spanningCoe.edgeSet) ∪
          (N.edgeSet ∩ c.toSimpleGraph.spanningCoe.edgeSet) at hswap
    rcases hswap with ⟨hM, hnotC⟩ | ⟨hN, hC⟩
    · have hMAdj : M.Adj v w := by simpa using hM
      by_contra hNAdj
      have hsymm :
          s(v, w) ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
        exact
          (memSymmDiffSpanningCoe_iff G).2
            ⟨Or.inl hMAdj, fun hBoth ↦ hNAdj hBoth.2⟩
      exact hnotC <|
        symmDiffEdge_mem_component_of_incidentVertex G c hv hsymm
    · simpa using hN
  · intro hNAdj
    change
      s(v, w) ∈
        (M.edgeSet \ c.toSimpleGraph.spanningCoe.edgeSet) ∪
          (N.edgeSet ∩ c.toSimpleGraph.spanningCoe.edgeSet)
    by_cases hC : s(v, w) ∈ c.toSimpleGraph.spanningCoe.edgeSet
    · exact Or.inr ⟨by simpa using hNAdj, hC⟩
    · have hMAdj : M.Adj v w := by
        by_contra hMAdj
        have hsymm :
            s(v, w) ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
          exact
            (memSymmDiffSpanningCoe_iff G).2
              ⟨Or.inr hNAdj, fun hBoth ↦ hMAdj hBoth.1⟩
        exact hC <|
          symmDiffEdge_mem_component_of_incidentVertex G c hv hsymm
      exact Or.inl ⟨by simpa using hMAdj, hC⟩

/-- Helper for Exercise 4.27: away from the chosen component support, the swapped subgraph
`swapEdgeSubgraph G M N C` keeps exactly the `M`-edges. -/
private lemma swapEdgeSubgraph_adj_iff_left_of_not_mem_component {M N : G.Subgraph}
    (c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent)
    {v w : V} (hv : v ∉ c.supp) :
    (swapEdgeSubgraph G M N c.toSimpleGraph.spanningCoe.edgeSet).Adj v w ↔ M.Adj v w := by
  constructor
  · intro hswap
    change
      s(v, w) ∈
        (M.edgeSet \ c.toSimpleGraph.spanningCoe.edgeSet) ∪
          (N.edgeSet ∩ c.toSimpleGraph.spanningCoe.edgeSet) at hswap
    rcases hswap with ⟨hM, _hnotC⟩ | ⟨_hN, hC⟩
    · simpa using hM
    · exfalso
      exact hv <| (connectedComponentSpanningCoe_edgeSet_iff c).1 hC |>.2.1
  · intro hMAdj
    change
      s(v, w) ∈
        (M.edgeSet \ c.toSimpleGraph.spanningCoe.edgeSet) ∪
          (N.edgeSet ∩ c.toSimpleGraph.spanningCoe.edgeSet)
    by_cases hC : s(v, w) ∈ c.toSimpleGraph.spanningCoe.edgeSet
    · exfalso
      exact hv <| (connectedComponentSpanningCoe_edgeSet_iff c).1 hC |>.2.1
    · exact Or.inl ⟨by simpa using hMAdj, hC⟩

/-- Helper for Exercise 4.27: on the support of the chosen component, the swapped subgraph
`swapEdgeSubgraph G N M C` has exactly the `M`-edges. -/
private lemma swapEdgeSubgraph_adj_iff_left_of_mem_component {M N : G.Subgraph}
    (c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent)
    {v w : V} (hv : v ∈ c.supp) :
    (swapEdgeSubgraph G N M c.toSimpleGraph.spanningCoe.edgeSet).Adj v w ↔ M.Adj v w := by
  constructor
  · intro hswap
    change
      s(v, w) ∈
        (N.edgeSet \ c.toSimpleGraph.spanningCoe.edgeSet) ∪
          (M.edgeSet ∩ c.toSimpleGraph.spanningCoe.edgeSet) at hswap
    rcases hswap with ⟨hN, hnotC⟩ | ⟨hM, hC⟩
    · have hNAdj : N.Adj v w := by simpa using hN
      by_contra hMAdj
      have hsymm :
          s(v, w) ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
        exact
          (memSymmDiffSpanningCoe_iff G).2
            ⟨Or.inr hNAdj, fun hBoth ↦ hMAdj hBoth.1⟩
      exact hnotC <|
        symmDiffEdge_mem_component_of_incidentVertex G c hv hsymm
    · simpa using hM
  · intro hMAdj
    change
      s(v, w) ∈
        (N.edgeSet \ c.toSimpleGraph.spanningCoe.edgeSet) ∪
          (M.edgeSet ∩ c.toSimpleGraph.spanningCoe.edgeSet)
    by_cases hC : s(v, w) ∈ c.toSimpleGraph.spanningCoe.edgeSet
    · exact Or.inr ⟨by simpa using hMAdj, hC⟩
    · have hNAdj : N.Adj v w := by
        by_contra hNAdj
        have hsymm :
            s(v, w) ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
          exact
            (memSymmDiffSpanningCoe_iff G).2
              ⟨Or.inl hMAdj, fun hBoth ↦ hNAdj hBoth.2⟩
        exact hC <|
          symmDiffEdge_mem_component_of_incidentVertex G c hv hsymm
      exact Or.inl ⟨by simpa using hNAdj, hC⟩

/-- Helper for Exercise 4.27: away from the chosen component support, the swapped subgraph
`swapEdgeSubgraph G N M C` keeps exactly the `N`-edges. -/
private lemma swapEdgeSubgraph_adj_iff_right_of_not_mem_component {M N : G.Subgraph}
    (c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent)
    {v w : V} (hv : v ∉ c.supp) :
    (swapEdgeSubgraph G N M c.toSimpleGraph.spanningCoe.edgeSet).Adj v w ↔ N.Adj v w := by
  constructor
  · intro hswap
    change
      s(v, w) ∈
        (N.edgeSet \ c.toSimpleGraph.spanningCoe.edgeSet) ∪
          (M.edgeSet ∩ c.toSimpleGraph.spanningCoe.edgeSet) at hswap
    rcases hswap with ⟨hN, _hnotC⟩ | ⟨_hM, hC⟩
    · simpa using hN
    · exfalso
      exact hv <| (connectedComponentSpanningCoe_edgeSet_iff c).1 hC |>.2.1
  · intro hNAdj
    change
      s(v, w) ∈
        (N.edgeSet \ c.toSimpleGraph.spanningCoe.edgeSet) ∪
          (M.edgeSet ∩ c.toSimpleGraph.spanningCoe.edgeSet)
    by_cases hC : s(v, w) ∈ c.toSimpleGraph.spanningCoe.edgeSet
    · exfalso
      exact hv <| (connectedComponentSpanningCoe_edgeSet_iff c).1 hC |>.2.1
    · exact Or.inl ⟨by simpa using hNAdj, hC⟩

/-- Helper for Exercise 4.27: swapping the two endpoint matchings on one connected component of
`M.spanningCoe ∆ N.spanningCoe` again yields two matchings. -/
private lemma componentSwapIsMatching_of_connectedComponent
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching)
    (c : (M.spanningCoe ∆ N.spanningCoe).ConnectedComponent) :
    let C : Set (Sym2 V) := c.toSimpleGraph.spanningCoe.edgeSet
    let K : G.Subgraph := swapEdgeSubgraph G M N C
    let L : G.Subgraph := swapEdgeSubgraph G N M C
    K.IsMatching ∧ L.IsMatching := by
  classical
  constructor
  · intro v hvK
    rcases hvK with ⟨w₀, hK₀⟩
    by_cases hv : v ∈ c.supp
    · have hN₀ :
          N.Adj v w₀ :=
        (swapEdgeSubgraph_adj_iff_right_of_mem_component
          G c hv).1 hK₀
      have hvN : v ∈ N.verts := N.edge_vert hN₀
      obtain ⟨w, hw, huniqw⟩ := hN hvN
      refine ⟨w, ?_, ?_⟩
      · exact
          (swapEdgeSubgraph_adj_iff_right_of_mem_component
            G c hv).2 hw
      · intro w' hw'
        exact huniqw w' <|
          (swapEdgeSubgraph_adj_iff_right_of_mem_component
            G c hv).1 hw'
    · have hM₀ :
          M.Adj v w₀ :=
        (swapEdgeSubgraph_adj_iff_left_of_not_mem_component
          G c hv).1 hK₀
      have hvM : v ∈ M.verts := M.edge_vert hM₀
      obtain ⟨w, hw, huniqw⟩ := hM hvM
      refine ⟨w, ?_, ?_⟩
      · exact
          (swapEdgeSubgraph_adj_iff_left_of_not_mem_component
            G c hv).2 hw
      · intro w' hw'
        exact huniqw w' <|
          (swapEdgeSubgraph_adj_iff_left_of_not_mem_component
            G c hv).1 hw'
  · intro v hvL
    rcases hvL with ⟨w₀, hL₀⟩
    by_cases hv : v ∈ c.supp
    · have hM₀ :
          M.Adj v w₀ :=
        (swapEdgeSubgraph_adj_iff_left_of_mem_component
          G c hv).1 hL₀
      have hvM : v ∈ M.verts := M.edge_vert hM₀
      obtain ⟨w, hw, huniqw⟩ := hM hvM
      refine ⟨w, ?_, ?_⟩
      · exact
          (swapEdgeSubgraph_adj_iff_left_of_mem_component
            G c hv).2 hw
      · intro w' hw'
        exact huniqw w' <|
          (swapEdgeSubgraph_adj_iff_left_of_mem_component
            G c hv).1 hw'
    · have hN₀ :
          N.Adj v w₀ :=
        (swapEdgeSubgraph_adj_iff_right_of_not_mem_component
          G c hv).1 hL₀
      have hvN : v ∈ N.verts := N.edge_vert hN₀
      obtain ⟨w, hw, huniqw⟩ := hN hvN
      refine ⟨w, ?_, ?_⟩
      · exact
          (swapEdgeSubgraph_adj_iff_right_of_not_mem_component
            G c hv).2 hw
      · intro w' hw'
        exact huniqw w' <|
          (swapEdgeSubgraph_adj_iff_right_of_not_mem_component
            G c hv).1 hw'

/-- Helper for Exercise 4.27: a sharp valid separator identifies its equality set with the
corresponding exposed face. -/
private lemma separatorEqualitySet_eq_toExposed_of_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {P : Set E} {l : StrongDual ℝ E} {β : ℝ} {x₀ : E}
    (hvalid : ∀ x ∈ P, l x ≤ β)
    (hx₀P : x₀ ∈ P) (hx₀ : l x₀ = β) :
    {x : E | x ∈ P ∧ l x = β} = l.toExposed P := by
  ext x
  constructor
  · rintro ⟨hxP, hxEq⟩
    -- Equality points maximize `l` because the same upper bound is valid on the whole set.
    refine ⟨hxP, fun y hyP ↦ ?_⟩
    calc
      l y ≤ β := hvalid y hyP
      _ = l x := by simp [hxEq]
  · intro hx
    -- Any maximizer must attain the witness value where the bound is already sharp.
    refine ⟨hx.1, ?_⟩
    have hx₀_le : l x₀ ≤ l x := hx.2 x₀ hx₀P
    have hx_le : l x ≤ l x₀ := by
      calc
        l x ≤ β := hvalid x hx.1
        _ = l x₀ := hx₀.symm
    have hx_eq : l x = l x₀ := le_antisymm hx_le hx₀_le
    simpa [hx₀] using hx_eq

/-- Helper for Exercise 4.27: any linear upper bound checked on every matching-incidence generator
is valid on the whole matching polytope. -/
private lemma matchingPolytope_le_of_generatorBound
    {l : StrongDual ℝ (G.edgeSet → ℝ)} {β : ℝ}
    (hgen : ∀ M : G.Subgraph, M.IsMatching → l (G.subgraphIncidenceVector ℝ M) ≤ β) :
    ∀ x ∈ G.matchingPolytope, l x ≤ β := by
  intro x hx
  rw [SimpleGraph.matchingPolytope] at hx
  have hsubset :
      convexHull ℝ {y : G.edgeSet → ℝ | ∃ M : G.Subgraph, M.IsMatching ∧
        y = G.subgraphIncidenceVector ℝ M} ⊆ {y : G.edgeSet → ℝ | l y ≤ β} := by
    -- Convexity propagates a generator-wise inequality to the defining convex hull.
    refine convexHull_min ?_ ?_
    · intro y hy
      rcases hy with ⟨M, hM, rfl⟩
      exact hgen M hM
    · exact (convex_Iic β).linear_preimage l.toLinearMap
  exact hsubset hx

/-- Helper for Exercise 4.27: if a convex combination of scalar terms bounded above by `c`
already has value `c`, then every positive-weight term is itself equal to `c`. -/
private lemma eq_of_weightedSumEq_of_nonneg_of_le
    {ι : Type*}
    (t : Finset ι)
    (w f : ι → ℝ)
    (c : ℝ)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hf : ∀ i ∈ t, f i ≤ c)
    (hsum : ∑ i ∈ t, w i * f i = c) :
    ∀ i ∈ t, w i ≠ 0 → f i = c := by
  intro i hi hwi
  -- Compare the weighted sum with the upper bound via the nonnegative deficits `c - f i`.
  have hsum_zero : ∑ j ∈ t, w j * (c - f j) = 0 := by
    calc
      ∑ j ∈ t, w j * (c - f j)
          = ∑ j ∈ t, (w j * c - w j * f j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = (∑ j ∈ t, w j * c) - ∑ j ∈ t, w j * f j := by
            rw [Finset.sum_sub_distrib]
      _ = c - c := by
            rw [← Finset.sum_mul, hw₁, one_mul, hsum]
      _ = 0 := by ring
  have hterm_zero :
      ∀ j ∈ t, w j * (c - f j) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum_zero
    intro j hj
    exact mul_nonneg (hw₀ j hj) (sub_nonneg.mpr (hf j hj))
  have hfactor_zero : c - f i = 0 := by
    rcases mul_eq_zero.mp (hterm_zero i hi) with hwi_zero | hfactor_zero
    · exact False.elim (hwi hwi_zero)
    · exact hfactor_zero
  linarith

/-- Helper for Exercise 4.27: if a boundary point of `convexHull ℝ A` is written as a convex
combination of generators in `A`, then every positive-weight generator already lies on the same
supporting hyperplane. -/
private lemma support_mem_hyperplane_of_centerMass_eq
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {ι : Type*}
    (A : Set E)
    (gamma : E →ₗ[ℝ] ℝ)
    (gamma0 : ℝ)
    (hA : A ⊆ gamma ⁻¹' Set.Iic gamma0)
    (t : Finset ι)
    (w : ι → ℝ)
    (z : ι → E)
    (x : E)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ A)
    (hx : ∑ i ∈ t, w i • z i = x)
    (hxH : gamma x = gamma0) :
    ∀ i ∈ {i ∈ t | w i ≠ 0}, z i ∈ A ∩ gamma ⁻¹' {gamma0} := by
  classical
  -- Applying `gamma` to the barycentric identity reduces the face condition to a scalar equality.
  have hle : ∀ i ∈ t, gamma (z i) ≤ gamma0 := by
    intro i hi
    simpa using hA (hz i hi)
  have hgamma_sum : ∑ i ∈ t, w i * gamma (z i) = gamma0 := by
    have hx_gamma : gamma (∑ i ∈ t, w i • z i) = gamma0 := by
      simpa [hx] using hxH
    simpa using hx_gamma
  have hboundary :
      ∀ i ∈ t, w i ≠ 0 → gamma (z i) = gamma0 :=
    eq_of_weightedSumEq_of_nonneg_of_le t w (fun i ↦ gamma (z i)) gamma0 hw₀ hw₁ hle hgamma_sum
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hit, hwi⟩
  -- Positive-weight generators stay in `A`, and the scalar equality places them on the boundary.
  refine ⟨hz i hit, ?_⟩
  simp [hboundary i hit hwi]

/-- Helper for Exercise 4.27: when a generating family `A` lies in the closed halfspace
`gamma ≤ gamma0`, the boundary slice of `convexHull ℝ A` is exactly the convex hull of the
generators already lying on `gamma = gamma0`. -/
private lemma convexHull_inter_hyperplane_eq
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (A : Set E)
    (gamma : E →ₗ[ℝ] ℝ)
    (gamma0 : ℝ)
    (hA : A ⊆ gamma ⁻¹' Set.Iic gamma0) :
    convexHull ℝ A ∩ gamma ⁻¹' {gamma0} =
      convexHull ℝ (A ∩ gamma ⁻¹' {gamma0}) := by
  classical
  letI : AddCommGroup E := Module.addCommMonoidToAddCommGroup ℝ
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rcases hx with ⟨hxHull, hxH⟩
    -- Rewrite the convex-hull membership as a finite center-of-mass representation.
    rw [_root_.convexHull_eq] at hxHull ⊢
    rcases hxHull with ⟨ι, t, w, z, hw₀, hw₁, hz, hcenter⟩
    refine ⟨ι, {i ∈ t | w i ≠ 0}, w, z, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact hw₀ i (Finset.mem_filter.mp hi).1
    · -- Removing zero-weight generators keeps the barycentric normalization unchanged.
      rw [Finset.sum_filter_ne_zero]
      exact hw₁
    · -- Every positive-weight generator lies on the same supporting hyperplane.
      have hx_eq : gamma x = gamma0 := by
        simpa using hxH
      have hsum_eq : ∑ i ∈ t, w i • z i = x := by
        calc
          ∑ i ∈ t, w i • z i = t.centerMass w z := by
            rw [Finset.centerMass_eq_of_sum_1 (t := t) (w := w) (z := z) hw₁]
          _ = x := hcenter
      exact support_mem_hyperplane_of_centerMass_eq A gamma gamma0 hA t w z x hw₀ hw₁ hz
        hsum_eq hx_eq
    · -- Filtering away zero coefficients does not change the center of mass.
      calc
        {i ∈ t | w i ≠ 0}.centerMass w z = t.centerMass w z := by
          simpa using
            (Finset.centerMass_filter_ne_zero (t := t) (w := w) (z := z))
        _ = x := hcenter
  · -- The boundary slice is convex and already contains every boundary generator.
    refine convexHull_min ?_ ?_
    · intro x hx
      exact ⟨subset_convexHull ℝ A hx.1, hx.2⟩
    · exact (convex_convexHull ℝ A).inter ((convex_singleton gamma0).linear_preimage gamma)

/-- Helper for Exercise 4.27: if all generators of a convex hull lie on one of two points, then
the whole convex hull lies on the segment joining those two points. -/
private lemma convexHull_subset_segment_of_subset_pair
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {A : Set E} {a b : E}
    (hA : A ⊆ ({a, b} : Set E)) :
    convexHull ℝ A ⊆ segment ℝ a b := by
  -- The segment is convex and already contains both candidate generators.
  refine convexHull_min ?_ (convex_segment a b)
  intro x hx
  rcases hA hx with rfl | rfl
  · exact left_mem_segment ℝ _ _
  · exact right_mem_segment ℝ _ _

/-- Helper for Exercise 4.27: a convex hull whose generators are all contained in `{a, b}` and
which still contains both `a` and `b` is exactly the segment `segment ℝ a b`. -/
private lemma convexHull_eq_segment_of_subset_pair
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {A : Set E} {a b : E}
    (hA : A ⊆ ({a, b} : Set E))
    (ha : a ∈ convexHull ℝ A)
    (hb : b ∈ convexHull ℝ A) :
    convexHull ℝ A = segment ℝ a b := by
  refine Set.Subset.antisymm ?_ ?_
  · exact convexHull_subset_segment_of_subset_pair hA
  · -- The ambient convex hull is convex and already contains both endpoints.
    exact (convex_convexHull ℝ A).segment_subset ha hb

/-- Helper for Exercise 4.27: a finite center of mass supported only on two endpoints lies on the
segment joining those endpoints. -/
private lemma centerMass_mem_segment_of_posSupport_eq_endpoints
    {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (t : Finset ι) (w : ι → ℝ) (z : ι → E) {x y : E}
    (hw_nonneg : ∀ i ∈ t, 0 ≤ w i)
    (hw_sum : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, w i ≠ 0 → z i = x ∨ z i = y) :
    t.centerMass w z ∈ segment ℝ x y := by
  classical
  -- Filter away the zero-weight generators before applying the finite convex-hull criterion.
  rw [← Finset.centerMass_filter_ne_zero (t := t) (w := w) (z := z)]
  rw [← convexHull_pair]
  refine Finset.centerMass_mem_convexHull {i ∈ t | w i ≠ 0} ?_ ?_ ?_
  · intro i hi
    exact hw_nonneg i (Finset.mem_filter.mp hi).1
  · -- The positive-weight support still has total mass `1`, so the center of mass is defined.
    have hw_sum_filter : ∑ i ∈ {i ∈ t | w i ≠ 0}, w i = 1 := by
      rw [Finset.sum_filter_ne_zero]
      exact hw_sum
    simp [hw_sum_filter]
  · intro i hi
    -- Every positive-weight support point is one of the two designated endpoints.
    rcases hz i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2 with rfl | rfl <;> simp

/-- Helper for Exercise 4.27: the incident-coordinate functional at `v` sums the ambient edge
coordinates incident to `v`. -/
private def incidentCoordinateSumFunctional (v : V) :
    StrongDual ℝ (G.edgeSet → ℝ) :=
  Finset.sum
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v)
    fun e ↦ (ContinuousLinearMap.proj e : StrongDual ℝ (G.edgeSet → ℝ))

/-- Helper for Exercise 4.27: evaluating the incident-coordinate functional rewrites to the
expected incident-edge coordinate sum. -/
private lemma incidentCoordinateSumFunctional_apply (v : V) (x : G.edgeSet → ℝ) :
    incidentCoordinateSumFunctional G v x =
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x := by
  -- Expand the finite sum of coordinate projections at the chosen vertex.
  simp [incidentCoordinateSumFunctional]

/-- Helper for Exercise 4.27: if a vertex is not covered by a subgraph, then its incident-edge
coordinate sum in the subgraph incidence vector is `0`. -/
private lemma subgraphIncidenceSum_eq_zero_of_notMem_verts
    {M : G.Subgraph} {v : V} (hv : v ∉ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 0 := by
  -- Every nonzero incident coordinate would force `v` into `M.verts`.
  refine Finset.sum_eq_zero ?_
  intro e he
  have hv_mem : v ∈ (e : Sym2 V) := by
    have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
    simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] using he_inc
  by_cases heM : e.1 ∈ M.edgeSet
  · exact (hv (SimpleGraph.Subgraph.mem_verts_of_mem_edge heM hv_mem)).elim
  · simp [SimpleGraph.subgraphIncidenceVector, heM]

/-- Helper for Exercise 4.27: a matching contributes exactly one incident edge at every covered
vertex. -/
private lemma matchingIncidenceSum_eq_one_of_mem_verts
    {M : G.Subgraph} (hM : M.IsMatching) {v : V} (hv : v ∈ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  obtain ⟨w, hvw, huniq⟩ := hM hv
  let e₀ : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
  have he₀_mem :
      e₀ ∈ Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v := by
    -- The unique matching edge through `v` lies in the ambient incidence filter.
    simp [e₀, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  have he₀_val : G.subgraphIncidenceVector ℝ M e₀ = 1 := by
    have he₀_edge : e₀.1 ∈ M.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.2 hvw
    simp [SimpleGraph.subgraphIncidenceVector, he₀_edge]
  -- The matching property kills every other term in the incident-edge sum.
  calc
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = G.subgraphIncidenceVector ℝ M e₀ := by
          refine Finset.sum_eq_single_of_mem e₀ he₀_mem ?_
          intro e he he_ne
          by_cases heM : e.1 ∈ M.edgeSet
          · have hv_e : v ∈ (e : Sym2 V) := by
              have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
              simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
                using he_inc
            have hAdj_e : M.Adj v (Sym2.Mem.other hv_e) := by
              exact SimpleGraph.Subgraph.mem_edgeSet.1
                (by simpa [Sym2.other_spec hv_e] using heM)
            have he_eq : e.1 = e₀.1 := by
              calc
                e.1 = s(v, Sym2.Mem.other hv_e) := by
                  symm
                  exact Sym2.other_spec hv_e
                _ = s(v, w) := by rw [huniq _ hAdj_e]
                _ = e₀.1 := rfl
            exact (he_ne (Subtype.ext he_eq)).elim
          · simp [SimpleGraph.subgraphIncidenceVector, heM]
    _ = 1 := he₀_val

/-- Helper for Exercise 4.27: every matching incidence vector satisfies the incident-edge upper
bound `≤ 1` at each ambient vertex. -/
private lemma matchingIncidenceSum_le_one
    {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) ≤ 1 := by
  -- Covered vertices contribute exactly one edge, and uncovered vertices contribute none.
  by_cases hv : v ∈ M.verts
  · have hsum_eq_one := matchingIncidenceSum_eq_one_of_mem_verts G hM hv
    linarith
  · rw [subgraphIncidenceSum_eq_zero_of_notMem_verts G hv]
    norm_num

/-- Helper for Exercise 4.27: every point of `G.matchingPolytope` satisfies the incident-edge
degree inequality at each vertex. -/
private lemma matchingPolytopeIncidentSum_le_one
    {x : G.edgeSet → ℝ} (hx : x ∈ G.matchingPolytope) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x ≤ 1 := by
  -- Lift the generator-wise matching inequality through the defining convex hull of the polytope.
  have hle :
      incidentCoordinateSumFunctional G v x ≤ 1 := by
    have hgen :
        ∀ M : G.Subgraph,
          M.IsMatching →
            incidentCoordinateSumFunctional G v (G.subgraphIncidenceVector ℝ M) ≤ 1 := by
      intro M hM
      rw [incidentCoordinateSumFunctional_apply G]
      exact matchingIncidenceSum_le_one G hM v
    exact matchingPolytope_le_of_generatorBound G hgen x hx
  rw [incidentCoordinateSumFunctional_apply G] at hle
  exact hle

/-- Helper for Exercise 4.27: every coordinate of a point of the matching polytope lies in
`[0,1]`. -/
private lemma matchingPolytope_coordinateBounds {x : G.edgeSet → ℝ}
    (hx : x ∈ G.matchingPolytope) (e : G.edgeSet) :
    0 ≤ x e ∧ x e ≤ 1 := by
  have hlower :
      (-ContinuousLinearMap.proj e : StrongDual ℝ (G.edgeSet → ℝ)) x ≤ 0 := by
    -- Nonnegativity is enough to make the negative coordinate functional valid with bound `0`.
    have hgen :
        ∀ M : G.Subgraph,
          M.IsMatching →
            (-ContinuousLinearMap.proj e : StrongDual ℝ (G.edgeSet → ℝ))
              (G.subgraphIncidenceVector ℝ M) ≤ 0 := by
      intro M _hM
      rcases subgraphIncidenceVector_eq_zero_or_one (G := G) (H := M) e with h0 | h1
      · simpa [h0]
      · simpa [h1]
    exact matchingPolytope_le_of_generatorBound G hgen x hx
  have hupper :
      (ContinuousLinearMap.proj e : StrongDual ℝ (G.edgeSet → ℝ)) x ≤ 1 := by
    -- The same generator check gives the ambient `1` upper bound on each coordinate.
    have hgen :
        ∀ M : G.Subgraph,
          M.IsMatching →
            (ContinuousLinearMap.proj e : StrongDual ℝ (G.edgeSet → ℝ))
              (G.subgraphIncidenceVector ℝ M) ≤ 1 := by
      intro M _hM
      rcases subgraphIncidenceVector_eq_zero_or_one (G := G) (H := M) e with h0 | h1
      · simpa [h0]
      · simpa [h1]
    exact matchingPolytope_le_of_generatorBound G hgen x hx
  exact ⟨by
    have hneg : -(x e) ≤ 0 := by
      simpa using hlower
    linarith, by simpa using hupper⟩

/-- Helper for Exercise 4.27: every adjacency of `M.spanningCoe ∆ N.spanningCoe` is already an
ambient adjacency of `G`. -/
private lemma ambientAdj_of_symmDiff_adj
    {M N : G.Subgraph} {v w : V}
    (hvw : (M.spanningCoe ∆ N.spanningCoe).Adj v w) :
    G.Adj v w := by
  have hmem : s(v, w) ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
    simpa [SimpleGraph.Subgraph.mem_edgeSet] using hvw
  rcases (memSymmDiffSpanningCoe_iff G).mp hmem with
    ⟨hMvw | hNvw, _⟩
  · exact hMvw.adj_sub
  · exact hNvw.adj_sub

/-- Helper for Exercise 4.27: two distinct ambient edges incident to the same vertex have
coordinate sum at most `1` at every point of `G.matchingPolytope`. -/
private lemma matchingPolytope_edgePairSum_le_one
    {x : G.edgeSet → ℝ} (hx : x ∈ G.matchingPolytope)
    {v w z : V} (hvw : G.Adj v w) (hvz : G.Adj v z) (hwz : w ≠ z) :
    x ⟨s(v, w), G.mem_edgeSet.2 hvw⟩ + x ⟨s(v, z), G.mem_edgeSet.2 hvz⟩ ≤ 1 := by
  let I : Finset G.edgeSet :=
    Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v
  let ew : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.2 hvw⟩
  let ez : G.edgeSet := ⟨s(v, z), G.mem_edgeSet.2 hvz⟩
  have hew_mem : ew ∈ I := by
    simp [I, ew, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  have hez_mem : ez ∈ I := by
    simp [I, ez, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  have he_ne : ew ≠ ez := by
    intro heq
    apply hwz
    have hs : s(v, w) = s(v, z) := by
      simpa [ew, ez] using congrArg Subtype.val heq
    exact Sym2.congr_right.mp hs
  have hcoord_nonneg : ∀ e : G.edgeSet, 0 ≤ x e := by
    intro e
    exact (matchingPolytope_coordinateBounds G hx e).1
  have hez_le : x ez ≤ (I.erase ew).sum x := by
    exact
      Finset.single_le_sum (fun e _ ↦ hcoord_nonneg e)
        (by
          refine Finset.mem_erase.mpr ?_
          exact ⟨fun h ↦ he_ne h.symm, hez_mem⟩)
  calc
    x ew + x ez ≤ x ew + (I.erase ew).sum x := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hez_le (x ew)
    _ = I.sum x := by
          exact Finset.add_sum_erase I x hew_mem
    _ = (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x := by
          rfl
    _ ≤ 1 := matchingPolytopeIncidentSum_le_one G hx v

/-- Helper for Exercise 4.27: if the symmetric difference of two matchings has at least two
edge-nonempty connected components, swapping on one component yields two matching-incidence
vectors with the same midpoint as the endpoints but lying outside the endpoint segment. -/
private lemma existsComponentSwapMidpointCounterexample
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching) (hMN : M ≠ N)
    (hnot : ¬ (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath) :
    ∃ K L : G.Subgraph,
      K.IsMatching ∧
      L.IsMatching ∧
      G.subgraphIncidenceVector ℝ K + G.subgraphIncidenceVector ℝ L =
        G.subgraphIncidenceVector ℝ M + G.subgraphIncidenceVector ℝ N ∧
      G.subgraphIncidenceVector ℝ K ∉
        segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) ∧
      G.subgraphIncidenceVector ℝ L ∉
        segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
  classical
  obtain ⟨c, d, hcd, hc, hd⟩ :=
    existsTwoEdgeNonemptySymmDiffComponents_of_not_isCycleOrPath G
      hM hN hMN hnot
  let C : Set (Sym2 V) := c.toSimpleGraph.spanningCoe.edgeSet
  let K : G.Subgraph := swapEdgeSubgraph G M N C
  let L : G.Subgraph := swapEdgeSubgraph G N M C
  have hKLmatching :
      K.IsMatching ∧ L.IsMatching := by
    -- Swapping on one symmetric-difference component preserves the matching condition.
    simpa [C, K, L] using
      componentSwapIsMatching_of_connectedComponent G hM hN c
  have hadd :
      G.subgraphIncidenceVector ℝ K + G.subgraphIncidenceVector ℝ L =
        G.subgraphIncidenceVector ℝ M + G.subgraphIncidenceVector ℝ N := by
    -- The swapped pair keeps the same total incidence vector as the original pair.
    simpa [C, K, L] using
      componentSwapIncidence_add_eq_of_connectedComponent G c
  obtain ⟨eC, heC_mem, heC_diff⟩ :=
    existsAmbientEdgeCoord_of_component_nonempty G c hc
  obtain ⟨eD, heD_mem, heD_diff⟩ :=
    existsAmbientEdgeCoord_of_component_nonempty G d hd
  have hdisj :
      Disjoint C d.toSimpleGraph.spanningCoe.edgeSet := by
    -- Distinct connected components have disjoint ambient edge supports.
    simpa [C] using
      spanningCoe_edgeSet_disjoint_of_ne_connectedComponent
        hcd
  have heD_not_mem : (eD : Sym2 V) ∉ C := by
    -- An edge from the untouched component cannot lie in the chosen swap component.
    intro heD_in
    exact (Set.disjoint_left.mp hdisj) heD_in heD_mem
  have heC_xor :
      (((eC : Sym2 V) ∈ M.edgeSet) ∧ (eC : Sym2 V) ∉ N.edgeSet) ∨
        (((eC : Sym2 V) ∈ N.edgeSet) ∧ (eC : Sym2 V) ∉ M.edgeSet) := by
    -- A symmetric-difference edge belongs to exactly one of the two endpoint matchings.
    simpa [symmDiff_def, SimpleGraph.Subgraph.edgeSet_spanningCoe] using heC_diff
  have heD_xor :
      (((eD : Sym2 V) ∈ M.edgeSet) ∧ (eD : Sym2 V) ∉ N.edgeSet) ∨
        (((eD : Sym2 V) ∈ N.edgeSet) ∧ (eD : Sym2 V) ∉ M.edgeSet) := by
    -- The same xor description holds on the untouched component edge.
    simpa [symmDiff_def, SimpleGraph.Subgraph.edgeSet_spanningCoe] using heD_diff
  have hK_out :
      G.subgraphIncidenceVector ℝ K ∉
        segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
    intro hKseg
    rw [segment_eq_image_lineMap] at hKseg
    rcases hKseg with ⟨t, ht, hKt⟩
    have hKeC :
        G.subgraphIncidenceVector ℝ K eC = G.subgraphIncidenceVector ℝ N eC := by
      -- On the chosen component, the first swapped subgraph agrees with `N`.
      simpa [C, K] using
        subgraphIncidenceVector_swapEdgeSubgraph_apply_of_mem
          G heC_mem
    have hKeD :
        G.subgraphIncidenceVector ℝ K eD = G.subgraphIncidenceVector ℝ M eD := by
      -- Off that component, the first swapped subgraph still agrees with `M`.
      simpa [C, K] using
        subgraphIncidenceVector_swapEdgeSubgraph_apply_of_not_mem
          G heD_not_mem
    have ht_one : t = 1 := by
      -- The coordinate on the swapped component forces the segment parameter to be `1`.
      have hcoord :
          (AffineMap.lineMap (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) t) eC =
            G.subgraphIncidenceVector ℝ N eC := by
        calc
          (AffineMap.lineMap (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) t) eC =
              G.subgraphIncidenceVector ℝ K eC := by
                simpa using congrArg (fun x : G.edgeSet → ℝ ↦ x eC) hKt
          _ = G.subgraphIncidenceVector ℝ N eC := hKeC
      rcases heC_xor with ⟨heCM, heCN⟩ | ⟨heCN, heCM⟩
      · simp [AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          SimpleGraph.subgraphIncidenceVector, heCM, heCN] at hcoord
        linarith
      · simp [AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          SimpleGraph.subgraphIncidenceVector, heCM, heCN] at hcoord
        linarith
    have ht_zero : t = 0 := by
      -- The coordinate on the untouched component forces the same parameter to be `0`.
      have hcoord :
          (AffineMap.lineMap (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) t) eD =
            G.subgraphIncidenceVector ℝ M eD := by
        calc
          (AffineMap.lineMap (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) t) eD =
              G.subgraphIncidenceVector ℝ K eD := by
                simpa using congrArg (fun x : G.edgeSet → ℝ ↦ x eD) hKt
          _ = G.subgraphIncidenceVector ℝ M eD := hKeD
      rcases heD_xor with ⟨heDM, heDN⟩ | ⟨heDN, heDM⟩
      · simp [AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          SimpleGraph.subgraphIncidenceVector, heDM, heDN] at hcoord
        linarith
      · simp [AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          SimpleGraph.subgraphIncidenceVector, heDM, heDN] at hcoord
        linarith
    linarith
  have hL_out :
      G.subgraphIncidenceVector ℝ L ∉
        segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
    intro hLseg
    rw [segment_eq_image_lineMap] at hLseg
    rcases hLseg with ⟨t, ht, hLt⟩
    have hLeC :
        G.subgraphIncidenceVector ℝ L eC = G.subgraphIncidenceVector ℝ M eC := by
      -- On the chosen component, the second swapped subgraph agrees with `M`.
      simpa [C, L] using
        subgraphIncidenceVector_swapEdgeSubgraph_apply_of_mem
          G heC_mem
    have hLeD :
        G.subgraphIncidenceVector ℝ L eD = G.subgraphIncidenceVector ℝ N eD := by
      -- Away from that component, the second swapped subgraph keeps the `N`-coordinate.
      simpa [C, L] using
        subgraphIncidenceVector_swapEdgeSubgraph_apply_of_not_mem
          G heD_not_mem
    have ht_zero : t = 0 := by
      -- The chosen component now forces the segment parameter to be `0`.
      have hcoord :
          (AffineMap.lineMap (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) t) eC =
            G.subgraphIncidenceVector ℝ M eC := by
        calc
          (AffineMap.lineMap (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) t) eC =
              G.subgraphIncidenceVector ℝ L eC := by
                simpa using congrArg (fun x : G.edgeSet → ℝ ↦ x eC) hLt
          _ = G.subgraphIncidenceVector ℝ M eC := hLeC
      rcases heC_xor with ⟨heCM, heCN⟩ | ⟨heCN, heCM⟩
      · simp [AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          SimpleGraph.subgraphIncidenceVector, heCM, heCN] at hcoord
        linarith
      · simp [AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          SimpleGraph.subgraphIncidenceVector, heCM, heCN] at hcoord
        linarith
    have ht_one : t = 1 := by
      -- The untouched component forces the same parameter to be `1`.
      have hcoord :
          (AffineMap.lineMap (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) t) eD =
            G.subgraphIncidenceVector ℝ N eD := by
        calc
          (AffineMap.lineMap (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) t) eD =
              G.subgraphIncidenceVector ℝ L eD := by
                simpa using congrArg (fun x : G.edgeSet → ℝ ↦ x eD) hLt
          _ = G.subgraphIncidenceVector ℝ N eD := hLeD
      rcases heD_xor with ⟨heDM, heDN⟩ | ⟨heDN, heDM⟩
      · simp [AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          SimpleGraph.subgraphIncidenceVector, heDM, heDN] at hcoord
        linarith
      · simp [AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          SimpleGraph.subgraphIncidenceVector, heDM, heDN] at hcoord
        linarith
    linarith
  exact ⟨K, L, hKLmatching.1, hKLmatching.2, hadd, hK_out, hL_out⟩

/-- Helper for Exercise 4.27: a graph that is a spanning cycle or path has a nonempty edge set. -/
private lemma isCycleOrPath_edgeSet_nonempty {H : SimpleGraph V} (hH : H.IsCycleOrPath) :
    H.edgeSet.Nonempty := by
  rcases hH with ⟨v, p, hpCycle, hpSpan⟩ | ⟨u, v, huv, p, hpPath, hpSpan⟩
  · rcases SimpleGraph.Walk.not_nil_iff.mp hpCycle.not_nil with ⟨w, hvw, q, hpCons⟩
    refine ⟨s(v, w), ?_⟩
    have hAdjSub : p.toSubgraph.Adj v w := by
      simpa [hpCons] using hvw
    have hAdj : H.Adj v w := by
      have hAdjSpan : p.toSubgraph.spanningCoe.Adj v w := by
        simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hAdjSub
      simpa [hpSpan] using hAdjSpan
    simpa [SimpleGraph.mem_edgeSet] using hAdj
  · have hpNotNil : ¬ p.Nil := p.not_nil_of_ne huv
    rcases SimpleGraph.Walk.not_nil_iff.mp hpNotNil with ⟨w, huw, q, hpCons⟩
    refine ⟨s(u, w), ?_⟩
    have hAdjSub : p.toSubgraph.Adj u w := by
      simpa [hpCons] using huw
    have hAdj : H.Adj u w := by
      have hAdjSpan : p.toSubgraph.spanningCoe.Adj u w := by
        simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hAdjSub
      simpa [hpSpan] using hAdjSpan
    simpa [SimpleGraph.mem_edgeSet] using hAdj

/-- Helper for Exercise 4.27: equality of subgraph incidence vectors forces equality of the
underlying ambient edge sets. -/
private lemma edgeSet_eq_of_subgraphIncidenceVector_eq {M N : G.Subgraph}
    (hMN :
      G.subgraphIncidenceVector ℝ M = G.subgraphIncidenceVector ℝ N) :
    M.edgeSet = N.edgeSet := by
  ext e
  constructor
  · intro heM
    by_cases heN : e ∈ N.edgeSet
    · exact heN
    · have hcoord :=
        congrArg (fun x : G.edgeSet → ℝ ↦ x ⟨e, M.edgeSet_subset heM⟩) hMN
      simp [SimpleGraph.subgraphIncidenceVector, heM, heN] at hcoord
  · intro heN
    by_cases heM : e ∈ M.edgeSet
    · exact heM
    · have hcoord :=
        congrArg (fun x : G.edgeSet → ℝ ↦ x ⟨e, N.edgeSet_subset heN⟩) hMN
      simp [SimpleGraph.subgraphIncidenceVector, heM, heN] at hcoord

/-- Helper for Exercise 4.27: in any midpoint barycentric decomposition, every positive-weight
generator agrees with the endpoint matchings on edges outside `M.spanningCoe ∆ N.spanningCoe`. -/
private lemma midpointCenterMass_generator_eq_endpoint_off_symmDiff
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {K : ι → G.Subgraph}
    {M N : G.Subgraph}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hmid :
      t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N))
    {e : G.edgeSet}
    (he : (e : Sym2 V) ∉ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet) :
    ∀ i ∈ t, w i ≠ 0 →
      G.subgraphIncidenceVector ℝ (K i) e = G.subgraphIncidenceVector ℝ M e := by
  have hsum :
      ∑ j ∈ t, w j • G.subgraphIncidenceVector ℝ (K j) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
    -- Rewrite the center of mass as the normalized weighted sum used by the scalar helper lemmas.
    calc
      ∑ j ∈ t, w j • G.subgraphIncidenceVector ℝ (K j) =
          t.centerMass w (fun j ↦ G.subgraphIncidenceVector ℝ (K j)) := by
            rw [Finset.centerMass_eq_of_sum_1
              (t := t) (w := w) (z := fun j ↦ G.subgraphIncidenceVector ℝ (K j)) hw₁]
      _ = midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := hmid
  have hcoord_sum :
      ∑ j ∈ t, w j * G.subgraphIncidenceVector ℝ (K j) e =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) e := by
    -- Evaluate the barycentric identity at the chosen ambient edge coordinate.
    simpa [Pi.smul_apply, smul_eq_mul] using
      congrArg (fun x : G.edgeSet → ℝ ↦ x e) hsum
  have hMN :
      G.subgraphIncidenceVector ℝ M e = G.subgraphIncidenceVector ℝ N e := by
    -- Outside the symmetric difference, the two endpoint matchings make the same edge decision.
    by_cases hMe : (e : Sym2 V) ∈ M.edgeSet
    · have hNe : (e : Sym2 V) ∈ N.edgeSet := by
        by_contra hNe
        exact he (by simp [symmDiff_def, hMe, hNe])
      simp [SimpleGraph.subgraphIncidenceVector, hMe, hNe]
    · have hNe : (e : Sym2 V) ∉ N.edgeSet := by
        intro hNe
        exact he (by simp [symmDiff_def, hMe, hNe])
      simp [SimpleGraph.subgraphIncidenceVector, hMe, hNe]
  intro i hi hwi
  rcases subgraphIncidenceVector_eq_zero_or_one G e with hMe0 | hMe1
  · have hmidpoint_zero :
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) e = 0 := by
      -- If the shared endpoint coordinate is `0`, then the midpoint coordinate is also `0`.
      have hNe0 : G.subgraphIncidenceVector ℝ N e = 0 := by
        rw [← hMN]
        exact hMe0
      simpa [midpoint_eq_smul_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hMe0, hNe0]
    have hcoord_zero :
        ∑ j ∈ t, w j * G.subgraphIncidenceVector ℝ (K j) e = 0 := by
      calc
        ∑ j ∈ t, w j * G.subgraphIncidenceVector ℝ (K j) e =
            midpoint ℝ (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) e := hcoord_sum
        _ = 0 := hmidpoint_zero
    have hle_zero :
        ∀ j ∈ t, -(G.subgraphIncidenceVector ℝ (K j) e) ≤ 0 := by
      intro j hj
      rcases subgraphIncidenceVector_eq_zero_or_one (G := G) (H := K j) e with hKe0 | hKe1
      · simpa [hKe0]
      · simpa [hKe1]
    have hsum_neg :
        ∑ j ∈ t, w j * (-(G.subgraphIncidenceVector ℝ (K j) e)) = 0 := by
      -- Negating the vanishing coordinate sum puts the problem into the helper's `≤ c` format.
      calc
        ∑ j ∈ t, w j * (-(G.subgraphIncidenceVector ℝ (K j) e)) =
            ∑ j ∈ t, -(w j * G.subgraphIncidenceVector ℝ (K j) e) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
        _ = -∑ j ∈ t, w j * G.subgraphIncidenceVector ℝ (K j) e := by
              rw [Finset.sum_neg_distrib]
        _ = 0 := by rw [hcoord_zero]; norm_num
    have hneg_eq_zero :
        -(G.subgraphIncidenceVector ℝ (K i) e) = 0 :=
      eq_of_weightedSumEq_of_nonneg_of_le t w
        (fun j ↦ -(G.subgraphIncidenceVector ℝ (K j) e)) 0 hw₀ hw₁ hle_zero hsum_neg
        i hi hwi
    linarith
  · have hmidpoint_one :
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) e = 1 := by
      -- If the shared endpoint coordinate is `1`, then the midpoint coordinate is also `1`.
      have hNe1 : G.subgraphIncidenceVector ℝ N e = 1 := by
        rw [← hMN]
        exact hMe1
      simpa [midpoint_eq_smul_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hMe1, hNe1]
    have hcoord_one :
        ∑ j ∈ t, w j * G.subgraphIncidenceVector ℝ (K j) e = 1 := by
      calc
        ∑ j ∈ t, w j * G.subgraphIncidenceVector ℝ (K j) e =
            midpoint ℝ (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) e := hcoord_sum
        _ = 1 := hmidpoint_one
    have hle_one :
        ∀ j ∈ t, G.subgraphIncidenceVector ℝ (K j) e ≤ 1 := by
      intro j hj
      rcases subgraphIncidenceVector_eq_zero_or_one (G := G) (H := K j) e with hKe0 | hKe1
      · simpa [hKe0]
      · simpa [hKe1]
    simpa [hMe1] using
      eq_of_weightedSumEq_of_nonneg_of_le t w
        (fun j ↦ G.subgraphIncidenceVector ℝ (K j) e) 1 hw₀ hw₁ hle_one hcoord_one
        i hi hwi

/-- Helper for Exercise 4.27: in any midpoint barycentric decomposition, every positive-weight
generator saturates each incident-sum constraint that is already tight at the midpoint. -/
private lemma midpointCenterMass_generator_incidentSum_eq_one
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {K : ι → G.Subgraph}
    {M N : G.Subgraph}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hK : ∀ i ∈ t, (K i).IsMatching)
    (hmid :
      t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N))
    {v : V}
    (hv :
      incidentCoordinateSumFunctional G v
        (midpoint ℝ (G.subgraphIncidenceVector ℝ M)
          (G.subgraphIncidenceVector ℝ N)) = 1) :
    ∀ i ∈ t, w i ≠ 0 →
      incidentCoordinateSumFunctional G v
        (G.subgraphIncidenceVector ℝ (K i)) = 1 := by
  have hsum :
      ∑ j ∈ t, w j • G.subgraphIncidenceVector ℝ (K j) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
    -- Rewrite the center of mass as the weighted sum so the linear functional sees a scalar sum.
    calc
      ∑ j ∈ t, w j • G.subgraphIncidenceVector ℝ (K j) =
          t.centerMass w (fun j ↦ G.subgraphIncidenceVector ℝ (K j)) := by
            rw [Finset.centerMass_eq_of_sum_1
              (t := t) (w := w) (z := fun j ↦ G.subgraphIncidenceVector ℝ (K j)) hw₁]
      _ = midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := hmid
  have hsum_eval :
      ∑ j ∈ t, w j *
          incidentCoordinateSumFunctional G v
            (G.subgraphIncidenceVector ℝ (K j)) = 1 := by
    -- Apply the incident-sum functional to the barycentric identity at the tight vertex.
    have happly :
        incidentCoordinateSumFunctional G v
            (∑ j ∈ t, w j • G.subgraphIncidenceVector ℝ (K j)) = 1 := by
      simpa [hsum] using hv
    simpa [map_sum, map_smul, smul_eq_mul] using happly
  have hle :
      ∀ j ∈ t,
        incidentCoordinateSumFunctional G v
          (G.subgraphIncidenceVector ℝ (K j)) ≤ 1 := by
    intro j hj
    -- Each matching generator satisfies the standard degree inequality at every ambient vertex.
    rw [incidentCoordinateSumFunctional_apply]
    exact matchingIncidenceSum_le_one G (hK j hj) v
  intro i hi hwi
  exact
    eq_of_weightedSumEq_of_nonneg_of_le t w
      (fun j ↦ incidentCoordinateSumFunctional G v
        (G.subgraphIncidenceVector ℝ (K j))) 1 hw₀ hw₁ hle hsum_eval
      i hi hwi

/-- Helper for Exercise 4.27: if two distinct symmetric-difference edges meet at `v`, then the
midpoint of the two endpoint incidence vectors is tight for the incident-sum inequality at `v`. -/
private lemma midpoint_incidentSum_eq_one_of_symmDiff_adjPair
    {M N : G.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching)
    {v w w' : V} (hww' : w ≠ w')
    (hvw : (M.spanningCoe ∆ N.spanningCoe).Adj v w)
    (hvw' : (M.spanningCoe ∆ N.spanningCoe).Adj v w') :
    incidentCoordinateSumFunctional G v
      (midpoint ℝ (G.subgraphIncidenceVector ℝ M)
        (G.subgraphIncidenceVector ℝ N)) = 1 := by
  have haltM : (M.spanningCoe ∆ N.spanningCoe).IsAlternating M.spanningCoe :=
    matchingSymmDiff_isAlternating G hM hN
  have haltN : (M.spanningCoe ∆ N.spanningCoe).IsAlternating N.spanningCoe := by
    have haltN' : (N.spanningCoe ∆ M.spanningCoe).IsAlternating N.spanningCoe :=
      matchingSymmDiff_isAlternating G hN hM
    simpa [symmDiff_comm] using
      haltN'
  have hMiff : M.Adj v w ↔ ¬ M.Adj v w' := by
    -- The alternating property forces `M` to choose exactly one of the two support edges.
    simpa [SimpleGraph.Subgraph.spanningCoe_adj] using haltM hww' hvw hvw'
  have hNiff : N.Adj v w ↔ ¬ N.Adj v w' := by
    -- The same alternation statement holds with the roles of `M` and `N` reversed.
    simpa [SimpleGraph.Subgraph.spanningCoe_adj] using haltN hww' hvw hvw'
  have hxor_w : (M.Adj v w ∨ N.Adj v w) ∧ ¬ (M.Adj v w ∧ N.Adj v w) := by
    have hmem :
        s(v, w) ∈ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet := by
      simpa [SimpleGraph.Subgraph.mem_edgeSet] using hvw
    exact (memSymmDiffSpanningCoe_iff G).mp hmem
  have hxor_w' : (M.Adj v w' ∨ N.Adj v w') ∧ ¬ (M.Adj v w' ∧ N.Adj v w') := by
    have hmem :
        s(v, w') ∈ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet := by
      simpa [SimpleGraph.Subgraph.mem_edgeSet] using hvw'
    exact (memSymmDiffSpanningCoe_iff G).mp hmem
  have hvM : v ∈ M.verts := by
    -- One of the two support edges must belong to `M`, so `v` is covered in `M`.
    rcases hxor_w.1 with hMvw | hNvw
    · exact M.edge_vert hMvw
    · have hnotMvw : ¬ M.Adj v w := fun h ↦ hxor_w.2 ⟨h, hNvw⟩
      have hMvw' : M.Adj v w' := by
        by_contra hnotMvw'
        exact hnotMvw (hMiff.mpr hnotMvw')
      exact M.edge_vert hMvw'
  have hvN : v ∈ N.verts := by
    -- Reversing the same argument shows that `v` is also covered in `N`.
    rcases hxor_w.1 with hMvw | hNvw
    · have hnotNvw : ¬ N.Adj v w := fun h ↦ hxor_w.2 ⟨hMvw, h⟩
      have hNvw' : N.Adj v w' := by
        by_contra hnotNvw'
        exact hnotNvw (hNiff.mpr hnotNvw')
      exact N.edge_vert hNvw'
    · exact N.edge_vert hNvw
  have hMsum :
      incidentCoordinateSumFunctional G v
        (G.subgraphIncidenceVector ℝ M) = 1 := by
    -- A matching covers a vertex with exactly one incident edge.
    rw [incidentCoordinateSumFunctional_apply G]
    exact matchingIncidenceSum_eq_one_of_mem_verts G hM hvM
  have hNsum :
      incidentCoordinateSumFunctional G v
        (G.subgraphIncidenceVector ℝ N) = 1 := by
    -- The same incident-sum normalization holds for `N`.
    rw [incidentCoordinateSumFunctional_apply G]
    exact matchingIncidenceSum_eq_one_of_mem_verts G hN hvN
  -- Linearity of the incident-sum functional turns the midpoint into the average of the two
  -- tight endpoint sums.
  calc
    incidentCoordinateSumFunctional G v
        (midpoint ℝ (G.subgraphIncidenceVector ℝ M)
          (G.subgraphIncidenceVector ℝ N)) =
      incidentCoordinateSumFunctional G v
        ((1 / 2 : ℝ) • G.subgraphIncidenceVector ℝ M +
          (1 / 2 : ℝ) • G.subgraphIncidenceVector ℝ N) := by
            simp [midpoint_eq_smul_add]
    _ =
        (1 / 2 : ℝ) *
            incidentCoordinateSumFunctional G v
              (G.subgraphIncidenceVector ℝ M) +
          (1 / 2 : ℝ) *
            incidentCoordinateSumFunctional G v
              (G.subgraphIncidenceVector ℝ N) := by
            simp [map_add, map_smul, smul_eq_mul]
    _ = 1 := by rw [hMsum, hNsum]; ring

/-- Helper for Exercise 4.27: in a midpoint center-of-mass decomposition, every positive-weight
generator inherits the tight incident-sum equality from any symmetric-difference adjacent pair. -/
private lemma midpointCenterMass_generator_incidentSum_eq_one_of_symmDiff_adjPair
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {K : ι → G.Subgraph}
    {M N : G.Subgraph}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hK : ∀ i ∈ t, (K i).IsMatching)
    (hmid :
      t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N))
    (hM : M.IsMatching) (hN : N.IsMatching)
    {v w₁ w₂ : V} (hw12 : w₁ ≠ w₂)
    (hvw₁ : (M.spanningCoe ∆ N.spanningCoe).Adj v w₁)
    (hvw₂ : (M.spanningCoe ∆ N.spanningCoe).Adj v w₂) :
    ∀ i ∈ t, w i ≠ 0 →
      incidentCoordinateSumFunctional G v
        (G.subgraphIncidenceVector ℝ (K i)) = 1 := by
  -- Route correction: use the concrete symmetric-difference adjacent pair to certify the midpoint
  -- equality first, then inherit that tightness through the existing center-of-mass lemma.
  exact midpointCenterMass_generator_incidentSum_eq_one
    G hw₀ hw₁ hK hmid
    (midpoint_incidentSum_eq_one_of_symmDiff_adjPair
      G hM hN hw12 hvw₁ hvw₂)

/-- Helper for Exercise 4.27: every positive-weight midpoint generator chooses exactly one edge
from a symmetric-difference adjacent pair through a common vertex. -/
private lemma matchingGenerator_edgePairSum_eq_one_of_symmDiff_adjPair
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {K : ι → G.Subgraph}
    {M N : G.Subgraph}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hK : ∀ i ∈ t, (K i).IsMatching)
    (hmid :
      t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N))
    (hM : M.IsMatching) (hN : N.IsMatching)
    {v w₁ w₂ : V} (hw12 : w₁ ≠ w₂)
    (hvw₁ : (M.spanningCoe ∆ N.spanningCoe).Adj v w₁)
    (hvw₂ : (M.spanningCoe ∆ N.spanningCoe).Adj v w₂) :
    ∀ i ∈ t, w i ≠ 0 →
      let e₁ : G.edgeSet := ⟨s(v, w₁), G.mem_edgeSet.2 <|
        ambientAdj_of_symmDiff_adj G hvw₁⟩
      let e₂ : G.edgeSet := ⟨s(v, w₂), G.mem_edgeSet.2 <|
        ambientAdj_of_symmDiff_adj G hvw₂⟩
      G.subgraphIncidenceVector ℝ (K i) e₁ +
        G.subgraphIncidenceVector ℝ (K i) e₂ = 1 := by
  intro i hi hwi
  let e₁ : G.edgeSet := ⟨s(v, w₁), G.mem_edgeSet.2 <|
    ambientAdj_of_symmDiff_adj G hvw₁⟩
  let e₂ : G.edgeSet := ⟨s(v, w₂), G.mem_edgeSet.2 <|
    ambientAdj_of_symmDiff_adj G hvw₂⟩
  have hsum :
      incidentCoordinateSumFunctional G v
        (G.subgraphIncidenceVector ℝ (K i)) = 1 :=
    midpointCenterMass_generator_incidentSum_eq_one_of_symmDiff_adjPair
      G hw₀ hw₁ hK hmid hM hN hw12 hvw₁ hvw₂ i hi hwi
  have hvK : v ∈ (K i).verts := by
    -- The tight incident-sum equality forces `K i` to cover `v`.
    by_contra hvK
    have hzero :
        incidentCoordinateSumFunctional G v
          (G.subgraphIncidenceVector ℝ (K i)) = 0 := by
      rw [incidentCoordinateSumFunctional_apply]
      exact subgraphIncidenceSum_eq_zero_of_notMem_verts G hvK
    linarith
  obtain ⟨u, hu, huuniq⟩ := hK i hi hvK
  have hMpair : M.Adj v w₁ ∨ M.Adj v w₂ := by
    -- The alternating symmetric difference forces `M` to use exactly one of the two support
    -- edges through `v`.
    have hmem :
        s(v, w₁) ∈ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet := by
      simpa [SimpleGraph.Subgraph.mem_edgeSet] using hvw₁
    have hmem' :
        s(v, w₂) ∈ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet := by
      simpa [SimpleGraph.Subgraph.mem_edgeSet] using hvw₂
    have hxor :=
      (memSymmDiffSpanningCoe_iff G).mp hmem
    have hxor' :=
      (memSymmDiffSpanningCoe_iff G).mp hmem'
    rcases hxor.1 with hMw₁ | hNw₁
    · exact Or.inl hMw₁
    · rcases hxor'.1 with hMw₂ | hNw₂
      · exact Or.inr hMw₂
      · exact (hw12 (hN.eq_of_adj_left hNw₁ hNw₂)).elim
  have hu_pair : u = w₁ ∨ u = w₂ := by
    -- A positive-weight generator cannot match `v` to an off-support edge, because it agrees with
    -- `M` off the symmetric difference and `M` already uses one support edge at `v`.
    by_contra hu_pair
    have huw₁ : u ≠ w₁ := fun h ↦ hu_pair (Or.inl h)
    have huw₂ : u ≠ w₂ := fun h ↦ hu_pair (Or.inr h)
    have hmem_u :
        s(v, u) ∉ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
      intro hmem_u
      have hvu : (M.spanningCoe ∆ N.spanningCoe).Adj v u := by
        simpa [SimpleGraph.Subgraph.mem_edgeSet] using hmem_u
      have hneighbor_finite :
          ((M.spanningCoe ∆ N.spanningCoe).neighborSet v).Finite :=
        Set.finite_of_ncard_pos <|
          (show ((M.spanningCoe ∆ N.spanningCoe).neighborSet v).Nonempty from
            ⟨w₁, by simpa using hvw₁⟩).ncard_pos
      have hthree :
          2 < ((M.spanningCoe ∆ N.spanningCoe).neighborSet v).ncard := by
        refine (Set.two_lt_ncard hneighbor_finite).2 ?_
        refine ⟨w₁, ?_, w₂, ?_, u, ?_, hw12, huw₁.symm, huw₂.symm⟩
        · simpa using hvw₁
        · simpa using hvw₂
        · simpa using hvu
      have hdeg :
          ((M.spanningCoe ∆ N.spanningCoe).neighborSet v).ncard ≤ 2 :=
        matchingSymmDiff_neighborSet_ncard_le_two G hM hN v
      omega
    let eu : G.edgeSet := ⟨s(v, u), G.mem_edgeSet.2 hu.adj_sub⟩
    have heuK : (eu : Sym2 V) ∈ (K i).edgeSet := by
      simpa [eu, SimpleGraph.Subgraph.mem_edgeSet] using hu
    have hKu :
        G.subgraphIncidenceVector ℝ (K i) eu = 1 := by
      simp [SimpleGraph.subgraphIncidenceVector, eu, heuK]
    have hMu :
        G.subgraphIncidenceVector ℝ (K i) eu =
          G.subgraphIncidenceVector ℝ M eu := by
      have hmem_u' :
          (eu : Sym2 V) ∉ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet := by
        simpa [eu, symmDiff_def, SimpleGraph.Subgraph.edgeSet_spanningCoe] using hmem_u
      exact
        midpointCenterMass_generator_eq_endpoint_off_symmDiff
          G hw₀ hw₁ hmid hmem_u' i hi hwi
    have heuM : (eu : Sym2 V) ∈ M.edgeSet := by
      by_contra heuM
      have hMu_zero :
          G.subgraphIncidenceVector ℝ M eu = 0 := by
        simp [SimpleGraph.subgraphIncidenceVector, eu, heuM]
      rw [hMu_zero] at hMu
      linarith
    have hMu_adj : M.Adj v u := by
      simpa [eu, SimpleGraph.Subgraph.mem_edgeSet] using heuM
    rcases hMpair with hMw₁ | hMw₂
    · exact huw₁ (hM.eq_of_adj_left hMu_adj hMw₁)
    · exact huw₂ (hM.eq_of_adj_left hMu_adj hMw₂)
  rcases hu_pair with rfl | rfl
  · -- If `K i` uses the first edge, matching uniqueness forces the second coordinate to vanish.
    have he₁ : G.subgraphIncidenceVector ℝ (K i) e₁ = 1 := by
      have he₁_mem : (e₁ : Sym2 V) ∈ (K i).edgeSet := by
        simpa [e₁, SimpleGraph.Subgraph.mem_edgeSet] using hu
      simp [SimpleGraph.subgraphIncidenceVector, e₁, he₁_mem]
    have he₂ : G.subgraphIncidenceVector ℝ (K i) e₂ = 0 := by
      have he₂_not_mem : (e₂ : Sym2 V) ∉ (K i).edgeSet := by
        intro he₂_mem
        have hAdj₂ : (K i).Adj v w₂ := by
          simpa [e₂, SimpleGraph.Subgraph.mem_edgeSet] using he₂_mem
        exact hw12 (huuniq w₂ hAdj₂).symm
      simp [SimpleGraph.subgraphIncidenceVector, e₂, he₂_not_mem]
    linarith
  · -- The symmetric case swaps the roles of the two support edges.
    have he₁ : G.subgraphIncidenceVector ℝ (K i) e₁ = 0 := by
      have he₁_not_mem : (e₁ : Sym2 V) ∉ (K i).edgeSet := by
        intro he₁_mem
        have hAdj₁ : (K i).Adj v w₁ := by
          simpa [e₁, SimpleGraph.Subgraph.mem_edgeSet] using he₁_mem
        exact hw12.symm (huuniq w₁ hAdj₁).symm
      simp [SimpleGraph.subgraphIncidenceVector, e₁, he₁_not_mem]
    have he₂ : G.subgraphIncidenceVector ℝ (K i) e₂ = 1 := by
      have he₂_mem : (e₂ : Sym2 V) ∈ (K i).edgeSet := by
        simpa [e₂, SimpleGraph.Subgraph.mem_edgeSet] using hu
      simp [SimpleGraph.subgraphIncidenceVector, e₂, he₂_mem]
    linarith

/-- Helper for Exercise 4.27: on a symmetric-difference adjacent pair, a positive-weight midpoint
generator uses the first edge exactly when it avoids the second. -/
private lemma matchingGenerator_adj_iff_not_adj_of_symmDiff_adjPair
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {K : ι → G.Subgraph}
    {M N : G.Subgraph}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hK : ∀ i ∈ t, (K i).IsMatching)
    (hmid :
      t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N))
    (hM : M.IsMatching) (hN : N.IsMatching)
    {v w₁ w₂ : V} (hw12 : w₁ ≠ w₂)
    (hvw₁ : (M.spanningCoe ∆ N.spanningCoe).Adj v w₁)
    (hvw₂ : (M.spanningCoe ∆ N.spanningCoe).Adj v w₂) :
    ∀ i ∈ t, w i ≠ 0 → ((K i).Adj v w₁ ↔ ¬ (K i).Adj v w₂) := by
  intro i hi hwi
  let e₁ : G.edgeSet := ⟨s(v, w₁), G.mem_edgeSet.2 <|
    ambientAdj_of_symmDiff_adj G hvw₁⟩
  let e₂ : G.edgeSet := ⟨s(v, w₂), G.mem_edgeSet.2 <|
    ambientAdj_of_symmDiff_adj G hvw₂⟩
  have hpair :
      G.subgraphIncidenceVector ℝ (K i) e₁ +
        G.subgraphIncidenceVector ℝ (K i) e₂ = 1 :=
    matchingGenerator_edgePairSum_eq_one_of_symmDiff_adjPair
      G hw₀ hw₁ hK hmid hM hN hw12 hvw₁ hvw₂ i hi hwi
  constructor
  · intro hAdj₁ hAdj₂
    have hvK : v ∈ (K i).verts := (K i).edge_vert hAdj₁
    obtain ⟨u, hu, huuniq⟩ := hK i hi hvK
    exact hw12.symm ((huuniq w₂ hAdj₂).trans (huuniq w₁ hAdj₁).symm)
  · intro hNotAdj₂
    by_contra hNotAdj₁
    have he₁_not_mem : (e₁ : Sym2 V) ∉ (K i).edgeSet := by
      simpa [e₁, SimpleGraph.Subgraph.mem_edgeSet] using hNotAdj₁
    have he₂_not_mem : (e₂ : Sym2 V) ∉ (K i).edgeSet := by
      simpa [e₂, SimpleGraph.Subgraph.mem_edgeSet] using hNotAdj₂
    have he₁_zero : G.subgraphIncidenceVector ℝ (K i) e₁ = 0 := by
      simp [SimpleGraph.subgraphIncidenceVector, e₁, he₁_not_mem]
    have he₂_zero : G.subgraphIncidenceVector ℝ (K i) e₂ = 0 := by
      simp [SimpleGraph.subgraphIncidenceVector, e₂, he₂_not_mem]
    linarith

/-- Helper for Exercise 4.27: the two endpoint incidence vectors agree on every ambient edge
outside `M.spanningCoe ∆ N.spanningCoe`. -/
private lemma endpointIncidence_eq_of_not_mem_symmDiff
    {M N : G.Subgraph} {e : G.edgeSet}
    (he : (e : Sym2 V) ∉ (M.spanningCoe ∆ N.spanningCoe).edgeSet) :
    G.subgraphIncidenceVector ℝ M e = G.subgraphIncidenceVector ℝ N e := by
  -- Outside the symmetric difference, `M` and `N` make the same edge-membership decision.
  by_cases hMe : (e : Sym2 V) ∈ M.edgeSet
  · have hNe : (e : Sym2 V) ∈ N.edgeSet := by
      by_contra hNe
      exact he (by simp [symmDiff_def, hMe, hNe])
    simp [SimpleGraph.subgraphIncidenceVector, hMe, hNe]
  · have hNe : (e : Sym2 V) ∉ N.edgeSet := by
      intro hNe
      exact he (by simp [symmDiff_def, hMe, hNe])
    simp [SimpleGraph.subgraphIncidenceVector, hMe, hNe]

/-- Helper for Exercise 4.27: once a positive-weight midpoint generator agrees with one endpoint
matching on the first edge of a spanning walk witness, the local alternation constraints force it
to equal that endpoint incidence vector on the whole symmetric-difference support. -/
private lemma matching_eq_endpoints_of_walkWitnessSeed
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {K : ι → G.Subgraph}
    {M N : G.Subgraph}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hK : ∀ i ∈ t, (K i).IsMatching)
    (hmid :
      t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N))
    (hM : M.IsMatching) (hN : N.IsMatching)
    {u v : V} {p : (M.spanningCoe ∆ N.spanningCoe).Walk u v}
    (hpos : 0 < p.length)
    (hstepNe : ∀ j, j + 1 < p.length → p.getVert j ≠ p.getVert (j + 2))
    (hspan : p.toSubgraph.spanningCoe = M.spanningCoe ∆ N.spanningCoe) :
    ∀ i ∈ t, w i ≠ 0 →
      G.subgraphIncidenceVector ℝ (K i) = G.subgraphIncidenceVector ℝ M ∨
        G.subgraphIncidenceVector ℝ (K i) = G.subgraphIncidenceVector ℝ N := by
  intro i hi hwi
  let H : SimpleGraph V := M.spanningCoe ∆ N.spanningCoe
  have hHedge : ∀ j, j < p.length → H.Adj (p.getVert j) (p.getVert (j + 1)) := by
    intro j hj
    have hpAdj : p.toSubgraph.Adj (p.getVert j) (p.getVert (j + 1)) :=
      p.toSubgraph_adj_getVert hj
    have hpAdj' : p.toSubgraph.spanningCoe.Adj (p.getVert j) (p.getVert (j + 1)) := by
      simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hpAdj
    simpa [H, hspan] using hpAdj'
  have hAltM : H.IsAlternating M.spanningCoe := by
    simpa [H] using matchingSymmDiff_isAlternating (G := G) hM hN
  have hAltN : H.IsAlternating N.spanningCoe := by
    simpa [H, symmDiff_comm] using
      (matchingSymmDiff_isAlternating (G := G) (M := N) (N := M) hN hM)
  have hOffMCoord :
      ∀ {e : G.edgeSet}, (e : Sym2 V) ∉ (M.spanningCoe ∆ N.spanningCoe).edgeSet →
        G.subgraphIncidenceVector ℝ (K i) e = G.subgraphIncidenceVector ℝ M e := by
    intro e heSymm
    have heSymm' : (e : Sym2 V) ∉ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet := by
      simpa [symmDiff_def, SimpleGraph.Subgraph.edgeSet_spanningCoe] using heSymm
    exact
      midpointCenterMass_generator_eq_endpoint_off_symmDiff
        (G := G) (t := t) (w := w) (K := K) (M := M) (N := N)
        hw₀ hw₁ hmid (e := e) heSymm' i hi hwi
  have hEndpointFromSeed :
      ∀ {A : G.Subgraph},
        H.IsAlternating A.spanningCoe →
        (∀ {e : G.edgeSet}, (e : Sym2 V) ∉ H.edgeSet →
          G.subgraphIncidenceVector ℝ (K i) e = G.subgraphIncidenceVector ℝ A e) →
        ((K i).Adj (p.getVert 0) (p.getVert 1) ↔ A.Adj (p.getVert 0) (p.getVert 1)) →
        G.subgraphIncidenceVector ℝ (K i) = G.subgraphIncidenceVector ℝ A := by
    intro A hAalt hOff hSeed
    have hEdgeAgree :
        ∀ j, j < p.length →
          ((K i).Adj (p.getVert j) (p.getVert (j + 1)) ↔
            A.Adj (p.getVert j) (p.getVert (j + 1))) := by
      intro j hj
      induction j with
      | zero =>
          simpa using hSeed
      | succ j ih =>
          have hjPrev : j < p.length := by
            omega
          have hPrev := ih hjPrev
          have hPrevH : H.Adj (p.getVert (j + 1)) (p.getVert j) := by
            simpa using (hHedge j hjPrev).symm
          have hNextH : H.Adj (p.getVert (j + 1)) (p.getVert (j + 2)) := by
            simpa [Nat.add_assoc] using hHedge (j + 1) hj
          have hKswitch :
              (K i).Adj (p.getVert j) (p.getVert (j + 1)) ↔
                ¬ (K i).Adj (p.getVert (j + 1)) (p.getVert (j + 2)) := by
            simpa [(K i).adj_comm] using
              (matchingGenerator_adj_iff_not_adj_of_symmDiff_adjPair
                (G := G) (t := t) (w := w) (K := K) (M := M) (N := N)
                hw₀ hw₁ hK hmid hM hN
                (v := p.getVert (j + 1)) (w₁ := p.getVert j) (w₂ := p.getVert (j + 2))
                (hstepNe j hj) hPrevH hNextH i hi hwi)
          have hAswitch :
              A.Adj (p.getVert j) (p.getVert (j + 1)) ↔
                ¬ A.Adj (p.getVert (j + 1)) (p.getVert (j + 2)) := by
            simpa [A.adj_comm, SimpleGraph.Subgraph.spanningCoe_adj] using
              hAalt (hstepNe j hj) hPrevH hNextH
          have hKnext :
              (K i).Adj (p.getVert (j + 1)) (p.getVert (j + 2)) ↔
                ¬ (K i).Adj (p.getVert j) (p.getVert (j + 1)) := by
            constructor
            · intro hNext hPrevK
              exact (hKswitch.mp hPrevK) hNext
            · intro hNotPrev
              by_contra hNotNext
              exact hNotPrev (hKswitch.mpr hNotNext)
          have hAnext :
              A.Adj (p.getVert (j + 1)) (p.getVert (j + 2)) ↔
                ¬ A.Adj (p.getVert j) (p.getVert (j + 1)) := by
            constructor
            · intro hNext hPrevA
              exact (hAswitch.mp hPrevA) hNext
            · intro hNotPrev
              by_contra hNotNext
              exact hNotPrev (hAswitch.mpr hNotNext)
          exact hKnext.trans ((not_congr hPrev).trans hAnext.symm)
    -- The final extensionality split separates support edges, controlled by the witness walk, from
    -- off-support edges, where the midpoint decomposition already forces endpoint agreement.
    ext e
    by_cases he : (e : Sym2 V) ∈ H.edgeSet
    · have hAdjH : H.Adj e.1.out.1 e.1.out.2 := by
        exact H.mem_edgeSet.mp (by simpa [e.1.out_eq] using he)
      have hAdjWalk : p.toSubgraph.Adj e.1.out.1 e.1.out.2 := by
        have hAdjWalk' : p.toSubgraph.spanningCoe.Adj e.1.out.1 e.1.out.2 := by
          simpa [H, hspan] using hAdjH
        simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hAdjWalk'
      obtain ⟨j, hs, hj⟩ := p.toSubgraph_adj_iff.mp hAdjWalk
      have hHj : H.Adj (p.getVert j) (p.getVert (j + 1)) := hHedge j hj
      let ej : G.edgeSet := ⟨s(p.getVert j, p.getVert (j + 1)), G.mem_edgeSet.2 <|
        ambientAdj_of_symmDiff_adj (G := G) (M := M) (N := N) hHj⟩
      have hej : ej = e := by
        apply Subtype.ext
        simpa [ej, e.1.out_eq] using hs
      have hCoord :
          G.subgraphIncidenceVector ℝ (K i) ej =
            G.subgraphIncidenceVector ℝ A ej := by
        by_cases hAedge : A.Adj (p.getVert j) (p.getVert (j + 1))
        · have hKedge : (K i).Adj (p.getVert j) (p.getVert (j + 1)) :=
            (hEdgeAgree j hj).2 hAedge
          have hejA : (ej : Sym2 V) ∈ A.edgeSet := by
            simpa [ej, SimpleGraph.Subgraph.mem_edgeSet] using hAedge
          have hejK : (ej : Sym2 V) ∈ (K i).edgeSet := by
            simpa [ej, SimpleGraph.Subgraph.mem_edgeSet] using hKedge
          simp [SimpleGraph.subgraphIncidenceVector, ej, hejA, hejK]
        · have hKedge : ¬ (K i).Adj (p.getVert j) (p.getVert (j + 1)) := by
            intro hKedge
            exact hAedge ((hEdgeAgree j hj).1 hKedge)
          have hejA : (ej : Sym2 V) ∉ A.edgeSet := by
            simpa [ej, SimpleGraph.Subgraph.mem_edgeSet] using hAedge
          have hejK : (ej : Sym2 V) ∉ (K i).edgeSet := by
            simpa [ej, SimpleGraph.Subgraph.mem_edgeSet] using hKedge
          simp [SimpleGraph.subgraphIncidenceVector, ej, hejA, hejK]
      simpa [hej] using hCoord
    · exact hOff he
  have hFirst : H.Adj (p.getVert 0) (p.getVert 1) := hHedge 0 hpos
  have hFirstMem :
      s(p.getVert 0, p.getVert 1) ∈ H.edgeSet := by
    simpa [SimpleGraph.mem_edgeSet] using hFirst
  have hxorFirst :
      (M.Adj (p.getVert 0) (p.getVert 1) ∨ N.Adj (p.getVert 0) (p.getVert 1)) ∧
        ¬ (M.Adj (p.getVert 0) (p.getVert 1) ∧ N.Adj (p.getVert 0) (p.getVert 1)) := by
    simpa [H] using
      (memSymmDiffSpanningCoe_iff (G := G) (M := M) (N := N)
        (v := p.getVert 0) (w := p.getVert 1)).mp hFirstMem
  by_cases hKFirst : (K i).Adj (p.getVert 0) (p.getVert 1)
  · by_cases hMFirst : M.Adj (p.getVert 0) (p.getVert 1)
    · left
      have hOffM :
          ∀ {e : G.edgeSet}, (e : Sym2 V) ∉ H.edgeSet →
            G.subgraphIncidenceVector ℝ (K i) e = G.subgraphIncidenceVector ℝ M e := by
        intro e heH
        have heSymm : (e : Sym2 V) ∉ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
          simpa [H] using heH
        exact hOffMCoord heSymm
      have hSeedM : (K i).Adj (p.getVert 0) (p.getVert 1) ↔
          M.Adj (p.getVert 0) (p.getVert 1) := by
        constructor
        · intro _
          exact hMFirst
        · intro _
          exact hKFirst
      exact hEndpointFromSeed hAltM hOffM hSeedM
    · have hNFirst : N.Adj (p.getVert 0) (p.getVert 1) := by
        rcases hxorFirst.1 with hM' | hN'
        · exact (hMFirst hM').elim
        · exact hN'
      right
      have hOffN :
          ∀ {e : G.edgeSet}, (e : Sym2 V) ∉ H.edgeSet →
            G.subgraphIncidenceVector ℝ (K i) e = G.subgraphIncidenceVector ℝ N e := by
        intro e heH
        have heSymm : (e : Sym2 V) ∉ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
          simpa [H] using heH
        calc
          G.subgraphIncidenceVector ℝ (K i) e =
              G.subgraphIncidenceVector ℝ M e := hOffMCoord heSymm
          _ = G.subgraphIncidenceVector ℝ N e := by
                simpa using
                  (endpointIncidence_eq_of_not_mem_symmDiff
                    (G := G) (M := M) (N := N) (e := e) heSymm)
      have hSeedN : (K i).Adj (p.getVert 0) (p.getVert 1) ↔
          N.Adj (p.getVert 0) (p.getVert 1) := by
        constructor
        · intro _
          exact hNFirst
        · intro _
          exact hKFirst
      exact hEndpointFromSeed hAltN hOffN hSeedN
  · by_cases hMFirst : M.Adj (p.getVert 0) (p.getVert 1)
    · have hNFirst : ¬ N.Adj (p.getVert 0) (p.getVert 1) := by
        intro hNFirst
        exact hxorFirst.2 ⟨hMFirst, hNFirst⟩
      right
      have hOffN :
          ∀ {e : G.edgeSet}, (e : Sym2 V) ∉ H.edgeSet →
            G.subgraphIncidenceVector ℝ (K i) e = G.subgraphIncidenceVector ℝ N e := by
        intro e heH
        have heSymm : (e : Sym2 V) ∉ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
          simpa [H] using heH
        calc
          G.subgraphIncidenceVector ℝ (K i) e =
              G.subgraphIncidenceVector ℝ M e := hOffMCoord heSymm
          _ = G.subgraphIncidenceVector ℝ N e := by
                simpa using
                  (endpointIncidence_eq_of_not_mem_symmDiff
                    (G := G) (M := M) (N := N) (e := e) heSymm)
      have hSeedN : (K i).Adj (p.getVert 0) (p.getVert 1) ↔
          N.Adj (p.getVert 0) (p.getVert 1) := by
        constructor
        · intro h
          exact (hKFirst h).elim
        · intro h
          exact (hNFirst h).elim
      exact hEndpointFromSeed hAltN hOffN hSeedN
    · have hMFirstFalse : ¬ M.Adj (p.getVert 0) (p.getVert 1) := hMFirst
      left
      have hOffM :
          ∀ {e : G.edgeSet}, (e : Sym2 V) ∉ H.edgeSet →
            G.subgraphIncidenceVector ℝ (K i) e = G.subgraphIncidenceVector ℝ M e := by
        intro e heH
        have heSymm : (e : Sym2 V) ∉ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
          simpa [H] using heH
        exact hOffMCoord heSymm
      have hSeedM : (K i).Adj (p.getVert 0) (p.getVert 1) ↔
          M.Adj (p.getVert 0) (p.getVert 1) := by
        constructor
        · intro h
          exact (hKFirst h).elim
        · intro h
          exact (hMFirstFalse h).elim
      exact hEndpointFromSeed hAltM hOffM hSeedM

/-- Helper for Exercise 4.27: along a fixed spanning path witness of
`M.spanningCoe ∆ N.spanningCoe`, a positive-weight midpoint generator is forced to equal one of
the two endpoint incidence vectors. -/
private lemma matching_eq_endpoints_of_pathWitnessSeed
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {K : ι → G.Subgraph}
    {M N : G.Subgraph}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hK : ∀ i ∈ t, (K i).IsMatching)
    (hmid :
      t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N))
    (hM : M.IsMatching) (hN : N.IsMatching)
    {u v : V} {p : (M.spanningCoe ∆ N.spanningCoe).Walk u v}
    (huv : u ≠ v)
    (hp : p.IsPath)
    (hspan : p.toSubgraph.spanningCoe = M.spanningCoe ∆ N.spanningCoe) :
    ∀ i ∈ t, w i ≠ 0 →
      G.subgraphIncidenceVector ℝ (K i) = G.subgraphIncidenceVector ℝ M ∨
        G.subgraphIncidenceVector ℝ (K i) = G.subgraphIncidenceVector ℝ N := by
  have hpos : 0 < p.length := by
    exact SimpleGraph.Walk.not_nil_iff_lt_length.mp (p.not_nil_of_ne huv)
  have hstepNe : ∀ j, j + 1 < p.length → p.getVert j ≠ p.getVert (j + 2) := by
    intro j hj
    intro hEq
    have hEq' := hp.getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hEq
    omega
  -- Route correction: the path branch now delegates all propagation to the generic witness-seed
  -- helper, so the theorem body only supplies the path-specific local injectivity input.
  exact matching_eq_endpoints_of_walkWitnessSeed
    (G := G) hw₀ hw₁ hK hmid hM hN hpos hstepNe hspan

/-- Helper for Exercise 4.27: in a midpoint center-of-mass decomposition over a single
path/cycle symmetric difference, every positive-weight matching generator is already one of the
two endpoint incidence vectors. -/
private lemma matchingGenerator_eq_endpoints_of_midpointCenterMass
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {K : ι → G.Subgraph}
    {M N : G.Subgraph}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ t, w i = 1)
    (hK : ∀ i ∈ t, (K i).IsMatching)
    (hmid :
      t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N))
    (hM : M.IsMatching) (hN : N.IsMatching)
    (hH : (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath) :
    ∀ i ∈ t, w i ≠ 0 →
      G.subgraphIncidenceVector ℝ (K i) = G.subgraphIncidenceVector ℝ M ∨
        G.subgraphIncidenceVector ℝ (K i) = G.subgraphIncidenceVector ℝ N := by
  rcases hH with ⟨v, p, hpCycle, hpSpan⟩ | ⟨u, v, huv, p, hpPath, hpSpan⟩
  · have hpos : 0 < p.length := by
      have hlen : 3 ≤ p.length := hpCycle.three_le_length
      omega
    have hstepNe : ∀ j, j + 1 < p.length → p.getVert j ≠ p.getVert (j + 2) := by
      intro j hj
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        (hpCycle.getVert_sub_one_ne_getVert_add_one (i := j + 1) (by omega))
    -- Route correction: the cycle case uses the same seeded walk propagation as the path case;
    -- the only extra input is the cycle-specific non-backtracking fact on consecutive triples.
    exact matching_eq_endpoints_of_walkWitnessSeed
      (G := G) hw₀ hw₁ hK hmid hM hN hpos hstepNe hpSpan
  · -- Route correction: the path branch is now isolated behind a dedicated witness-local helper.
    exact matching_eq_endpoints_of_pathWitnessSeed
      (G := G) hw₀ hw₁ hK hmid hM hN huv hpPath hpSpan

/-- Helper for Exercise 4.27: on a single path/cycle symmetric-difference support, the midpoint
of the two endpoint incidence vectors should not lie on a chord whose endpoints are both outside
the endpoint segment. -/
private lemma matchingMidpoint_not_mem_segment_of_points_outside_of_symmDiff_isCycleOrPath
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching)
    (hH : (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath)
    {x y : G.edgeSet → ℝ}
    (hx :
      x ∈ G.matchingPolytope \
        segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N))
    (hy :
      y ∈ G.matchingPolytope \
        segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) :
    midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) ∉
      segment ℝ x y := by
  classical
  intro hmidSeg
  rw [segment_eq_image_lineMap] at hmidSeg
  rcases hmidSeg with ⟨s, hs, hsMid⟩
  have hmid_mem :
      midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) ∈
        segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
    -- The midpoint of the endpoint segment lies on that endpoint segment.
    exact midpoint_mem_segment _ _
  have hs_left : s ≠ 0 := by
    -- If `s = 0`, then the left chord endpoint would literally be the midpoint, contradicting
    -- that `x` lies outside the endpoint segment.
    intro hs0
    have hxEq :
        x = midpoint ℝ (G.subgraphIncidenceVector ℝ M)
          (G.subgraphIncidenceVector ℝ N) := by
      simpa [hs0] using hsMid
    exact hx.2 (hxEq.symm ▸ hmid_mem)
  have hs_right : s ≠ 1 := by
    -- The symmetric endpoint case forces `y` to be the midpoint, again contradicting
    -- `y ∉ segment ℝ χ_M χ_N`.
    intro hs1
    have hyEq :
        y = midpoint ℝ (G.subgraphIncidenceVector ℝ M)
          (G.subgraphIncidenceVector ℝ N) := by
      simpa [hs1] using hsMid
    exact hy.2 (hyEq.symm ▸ hmid_mem)
  have hs_open : s ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨lt_of_le_of_ne hs.1 hs_left.symm, lt_of_le_of_ne hs.2 hs_right⟩
  rw [SimpleGraph.matchingPolytope, _root_.convexHull_eq] at hx hy
  rcases hx.1 with ⟨ιx, tx, wx, zx, hwx₀, hwx₁, hxz, hxcenter⟩
  rcases hy.1 with ⟨ιy, ty, wy, zy, hwy₀, hwy₁, hyz, hycenter⟩
  let Kx : ιx → G.Subgraph := fun i ↦
    if hi : i ∈ tx then Classical.choose (hxz i hi) else M
  let Ky : ιy → G.Subgraph := fun i ↦
    if hi : i ∈ ty then Classical.choose (hyz i hi) else M
  have hxcenter' :
      tx.centerMass wx (fun i ↦ G.subgraphIncidenceVector ℝ (Kx i)) = x := by
    -- Replace the abstract generators in the convex-hull decomposition of `x` with the chosen
    -- matching witnesses.
    calc
      tx.centerMass wx (fun i ↦ G.subgraphIncidenceVector ℝ (Kx i)) =
          tx.centerMass wx zx := by
            apply tx.centerMass_congr_fun
            intro i hi hwi
            simp [Kx, hi]
            exact (Classical.choose_spec (hxz i hi)).2.symm
      _ = x := hxcenter
  have hycenter' :
      ty.centerMass wy (fun i ↦ G.subgraphIncidenceVector ℝ (Ky i)) = y := by
    -- The same witness replacement works for the right chord endpoint.
    calc
      ty.centerMass wy (fun i ↦ G.subgraphIncidenceVector ℝ (Ky i)) =
          ty.centerMass wy zy := by
            apply ty.centerMass_congr_fun
            intro i hi hwi
            simp [Ky, hi]
            exact (Classical.choose_spec (hyz i hi)).2.symm
      _ = y := hycenter
  let t : Finset (ιx ⊕ ιy) := tx.disjSum ty
  let w : ιx ⊕ ιy → ℝ := Sum.elim (fun i ↦ (1 - s) * wx i) (fun j ↦ s * wy j)
  let K : ιx ⊕ ιy → G.Subgraph := Sum.elim Kx Ky
  have hw₀ : ∀ i ∈ t, 0 ≤ w i := by
    intro i hi
    rcases Finset.mem_disjSum.mp hi with (⟨i', hi', rfl⟩ | ⟨j', hj', rfl⟩)
    · -- The left half of the combined decomposition keeps the nonnegative `x`-weights.
      exact mul_nonneg (sub_nonneg.mpr hs.2) (hwx₀ _ hi')
    · -- The right half keeps the nonnegative `y`-weights.
      exact mul_nonneg hs.1 (hwy₀ _ hj')
  have hw₁ : ∑ i ∈ t, w i = 1 := by
    -- The midpoint is the convex combination of the two chord endpoints with weights `1 - s`
    -- and `s`.
    calc
      ∑ i ∈ t, w i =
          ∑ i ∈ tx, (1 - s) * wx i + ∑ j ∈ ty, s * wy j := by
            simp [t, w, Finset.sum_disjSum]
      _ = (1 - s) * (∑ i ∈ tx, wx i) + s * (∑ j ∈ ty, wy j) := by
            rw [Finset.mul_sum, Finset.mul_sum]
      _ = (1 - s) * 1 + s * 1 := by rw [hwx₁, hwy₁]
      _ = 1 := by ring
  have hKmatch : ∀ i ∈ t, (K i).IsMatching := by
    intro i hi
    rcases Finset.mem_disjSum.mp hi with (⟨i', hi', rfl⟩ | ⟨j', hj', rfl⟩)
    · -- Every generator coming from `x` is a matching by construction.
      simp [K, Kx, hi']
      exact (Classical.choose_spec (hxz i' hi')).1
    · -- The same holds for the generators coming from `y`.
      simp [K, Ky, hj']
      exact (Classical.choose_spec (hyz j' hj')).1
  have hmidCenter :
      t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
    have hKfun :
        (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
          Sum.elim (fun i ↦ G.subgraphIncidenceVector ℝ (Kx i))
            (fun j ↦ G.subgraphIncidenceVector ℝ (Ky j)) := by
      funext i
      cases i <;> rfl
    have hcombine :
        (1 - s) • tx.centerMass wx (fun i ↦ G.subgraphIncidenceVector ℝ (Kx i)) +
            s • ty.centerMass wy (fun i ↦ G.subgraphIncidenceVector ℝ (Ky i)) =
          t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) := by
      -- A convex combination of two centers of mass is the center of mass on the disjoint union.
      rw [hKfun]
      simpa [t, w, K] using
        (Finset.centerMass_segment' tx ty wx
          (fun i ↦ G.subgraphIncidenceVector ℝ (Kx i))
          wy (fun i ↦ G.subgraphIncidenceVector ℝ (Ky i))
          hwx₁ hwy₁ (1 - s) s (by ring))
    calc
      t.centerMass w (fun i ↦ G.subgraphIncidenceVector ℝ (K i)) =
          (1 - s) • tx.centerMass wx (fun i ↦ G.subgraphIncidenceVector ℝ (Kx i)) +
            s • ty.centerMass wy (fun i ↦ G.subgraphIncidenceVector ℝ (Ky i)) := by
              exact hcombine.symm
      _ = (1 - s) • x + s • y := by rw [hxcenter', hycenter']
      _ = AffineMap.lineMap x y s := by
            simp [AffineMap.lineMap_apply_module]
      _ = midpoint ℝ (G.subgraphIncidenceVector ℝ M)
            (G.subgraphIncidenceVector ℝ N) := hsMid
  have hendpoint :
      ∀ i ∈ t, w i ≠ 0 →
        G.subgraphIncidenceVector ℝ (K i) = G.subgraphIncidenceVector ℝ M ∨
          G.subgraphIncidenceVector ℝ (K i) = G.subgraphIncidenceVector ℝ N :=
    matchingGenerator_eq_endpoints_of_midpointCenterMass
      (G := G) hw₀ hw₁ hKmatch hmidCenter hM hN hH
  have hxSeg :
      x ∈ segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
    -- Every positive-weight generator in the decomposition of `x` is one endpoint incidence
    -- vector, so `x` itself lies on the endpoint segment.
    simpa [hxcenter'] using
      (centerMass_mem_segment_of_posSupport_eq_endpoints tx wx
        (fun i ↦ G.subgraphIncidenceVector ℝ (Kx i)) hwx₀ hwx₁
        (by
          intro i hi hwi
          have hwi' : w (.inl i) ≠ 0 := by
            exact mul_ne_zero (sub_ne_zero.mpr hs_right.symm) hwi
          simpa [t, K, Kx, hi] using hendpoint (.inl i) (by simpa [t] using hi) hwi'))
  exact hx.2 hxSeg

/-- Exercise 4.27 (1). Two matching incidence vectors span an edge of the matching polytope
exactly when the symmetric difference of the matchings is a path or a cycle. -/
-- The local xor/alternation/degree-`≤ 2` API reduces the argument to connected components of
-- `M.spanningCoe ∆ N.spanningCoe`; those components supply the midpoint obstruction and the
-- uniqueness of the supporting matching generators.
theorem matchingIncidenceVector_segment_isEdgeOf_iff_symmDiff_isCycleOrPath
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching) :
    IsEdgeOf G.matchingPolytope
      (segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) ↔
      (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath := by
  constructor
  · intro hEdge
    by_contra hnot
    have hvec_ne :
        G.subgraphIncidenceVector ℝ M ≠ G.subgraphIncidenceVector ℝ N := by
      -- An edge segment cannot collapse to a singleton because its affine direction is
      -- one-dimensional.
      intro hEq
      have hdim := hEdge.finrank_direction_eq_one
      rw [direction_affineSpan, vectorSpan_segment, hEq, vsub_self] at hdim
      have hzero : Module.finrank ℝ ↥(ℝ ∙ (0 : G.edgeSet → ℝ)) = 0 := by
        simp
      linarith
    have hMN : M ≠ N := by
      intro hEq
      exact hvec_ne (by simpa [hEq])
    obtain ⟨K, L, hKmatch, hLmatch, hadd, hKout, _hLout⟩ :=
      existsComponentSwapMidpointCounterexample
        G hM hN hMN hnot
    have hExtreme :
        IsExtreme ℝ G.matchingPolytope
          (segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) :=
      (isEdgeOf_segment_iff hvec_ne).1 hEdge
    have hKpoly :
        G.subgraphIncidenceVector ℝ K ∈ G.matchingPolytope := by
      -- Matching-incidence vectors are generators of the matching polytope.
      rw [SimpleGraph.matchingPolytope]
      exact subset_convexHull ℝ _ ⟨K, hKmatch, rfl⟩
    have hLpoly :
        G.subgraphIncidenceVector ℝ L ∈ G.matchingPolytope := by
      -- The same generator description applies to the second swapped matching.
      rw [SimpleGraph.matchingPolytope]
      exact subset_convexHull ℝ _ ⟨L, hLmatch, rfl⟩
    have hmid_mem :
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) ∈
          segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
      -- The midpoint of the endpoint segment is still on that segment.
      exact midpoint_mem_segment _ _
    have hmid_eq :
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) =
          midpoint ℝ (G.subgraphIncidenceVector ℝ K) (G.subgraphIncidenceVector ℝ L) := by
      -- Equal total sums give equal midpoints after scaling by `1 / 2`.
      rw [midpoint_eq_smul_add, midpoint_eq_smul_add, hadd]
    have hmid_open :
        midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) ∈
          openSegment ℝ (G.subgraphIncidenceVector ℝ K) (G.subgraphIncidenceVector ℝ L) := by
      -- The swapped midpoint lies strictly between the two swapped endpoints.
      rw [hmid_eq]
      exact midpoint_mem_openSegment _ _
    have hKin :
        G.subgraphIncidenceVector ℝ K ∈
          segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) :=
      hExtreme.left_mem_of_mem_openSegment hKpoly hLpoly hmid_mem hmid_open
    exact hKout hKin
  · intro hSymm
    let e : G.edgeSet ≃ Fin (Nat.card G.edgeSet) := Finite.equivFin G.edgeSet
    let L : (G.edgeSet → ℝ) ≃ₗ[ℝ] (Fin (Nat.card G.edgeSet) → ℝ) :=
      (LinearEquiv.funCongrLeft ℝ ℝ e).symm
    have hL_segment (x y : G.edgeSet → ℝ) :
        L '' segment ℝ x y = segment ℝ (L x) (L y) := by
      -- The coordinate reindexing equivalence preserves closed segments.
      simpa using image_segment ℝ (L.toLinearMap.toAffineMap) x y
    have hL_openSegment (x y : G.edgeSet → ℝ) :
        L '' openSegment ℝ x y = openSegment ℝ (L x) (L y) := by
      -- The same coordinate reindexing equivalence preserves open segments.
      simpa using image_openSegment ℝ (L.toLinearMap.toAffineMap) x y
    have hL_midpoint (x y : G.edgeSet → ℝ) :
        L (midpoint ℝ x y) = midpoint ℝ (L x) (L y) := by
      -- Midpoints are linear on vector spaces, so reindexing commutes with midpoint formation.
      ext i
      rw [midpoint_eq_smul_add, midpoint_eq_smul_add, map_smul, map_add]
    have hmatchingConvex : Convex ℝ G.matchingPolytope := by
      -- The matching polytope is a convex hull by definition.
      rw [SimpleGraph.matchingPolytope]
      exact convex_convexHull ℝ _
    have hMpoly : G.subgraphIncidenceVector ℝ M ∈ G.matchingPolytope := by
      -- Matching-incidence vectors are defining generators of the matching polytope.
      rw [SimpleGraph.matchingPolytope]
      exact subset_convexHull ℝ _ ⟨M, hM, rfl⟩
    have hNpoly : G.subgraphIncidenceVector ℝ N ∈ G.matchingPolytope := by
      -- The same generator description applies to the right endpoint.
      rw [SimpleGraph.matchingPolytope]
      exact subset_convexHull ℝ _ ⟨N, hN, rfl⟩
    have hvec_ne :
        G.subgraphIncidenceVector ℝ M ≠ G.subgraphIncidenceVector ℝ N := by
      -- A single path/cycle symmetric difference has a nonempty edge set, so the endpoint
      -- incidence vectors cannot coincide.
      intro hEq
      have hEdgeEq : M.edgeSet = N.edgeSet :=
        edgeSet_eq_of_subgraphIncidenceVector_eq G hEq
      have hSpanningEq : M.spanningCoe.edgeSet = N.spanningCoe.edgeSet := by
        simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using hEdgeEq
      have hEmpty : (M.spanningCoe ∆ N.spanningCoe).edgeSet = ∅ := by
        ext e
        simp [symmDiff_def, hSpanningEq]
      exact (isCycleOrPath_edgeSet_nonempty (H := M.spanningCoe ∆ N.spanningCoe) hSymm).ne_empty
        hEmpty
    have hMvtxImage :
        L (G.subgraphIncidenceVector ℝ M) ∈
          (L '' G.matchingPolytope).extremePoints ℝ := by
      -- Extreme points are preserved by the coordinate reindexing equivalence.
      rw [← image_extremePoints]
      exact ⟨_, subgraphIncidenceVector_mem_extremePoints_matchingPolytope G hM, rfl⟩
    have hNvtxImage :
        L (G.subgraphIncidenceVector ℝ N) ∈
          (L '' G.matchingPolytope).extremePoints ℝ := by
      -- The same transport applies to the right endpoint.
      rw [← image_extremePoints]
      exact ⟨_, subgraphIncidenceVector_mem_extremePoints_matchingPolytope G hN, rfl⟩
    have hmidImage :
        ∀ x ∈
            (L '' G.matchingPolytope) \
              segment ℝ (L (G.subgraphIncidenceVector ℝ M))
                (L (G.subgraphIncidenceVector ℝ N)),
          ∀ y ∈
              (L '' G.matchingPolytope) \
                segment ℝ (L (G.subgraphIncidenceVector ℝ M))
                  (L (G.subgraphIncidenceVector ℝ N)),
            midpoint ℝ (L (G.subgraphIncidenceVector ℝ M))
                (L (G.subgraphIncidenceVector ℝ N)) ∉
              segment ℝ x y := by
      intro x hx y hy hmidSeg
      rcases hx.1 with ⟨x₀, hx₀poly, rfl⟩
      rcases hy.1 with ⟨y₀, hy₀poly, rfl⟩
      have hx₀_out :
          x₀ ∉ segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
        intro hx₀Seg
        have hx₀SegImage :
            L x₀ ∈ L '' segment ℝ (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) := ⟨x₀, hx₀Seg, rfl⟩
        have hx₀SegImage' :
            L x₀ ∈ segment ℝ (L (G.subgraphIncidenceVector ℝ M))
              (L (G.subgraphIncidenceVector ℝ N)) := by
          rw [← hL_segment]
          exact hx₀SegImage
        exact hx.2 hx₀SegImage'
      have hy₀_out :
          y₀ ∉ segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
        intro hy₀Seg
        have hy₀SegImage :
            L y₀ ∈ L '' segment ℝ (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) := ⟨y₀, hy₀Seg, rfl⟩
        have hy₀SegImage' :
            L y₀ ∈ segment ℝ (L (G.subgraphIncidenceVector ℝ M))
              (L (G.subgraphIncidenceVector ℝ N)) := by
          rw [← hL_segment]
          exact hy₀SegImage
        exact hy.2 hy₀SegImage'
      have hmidSegNative :
          midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) ∈
            segment ℝ x₀ y₀ := by
        have hmidSegImage :
            midpoint ℝ (L (G.subgraphIncidenceVector ℝ M))
                (L (G.subgraphIncidenceVector ℝ N)) ∈
              L '' segment ℝ x₀ y₀ := by
          rw [hL_segment x₀ y₀]
          exact hmidSeg
        have hmidSegImage' :
            L (midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) ∈
              L '' segment ℝ x₀ y₀ := by
          simpa [hL_midpoint] using hmidSegImage
        rcases hmidSegImage' with ⟨z, hzSeg, hzEq⟩
        have hz :
            z = midpoint ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) :=
          L.injective (by simpa [hL_midpoint] using hzEq)
        simpa [hz] using hzSeg
      exact
        matchingMidpoint_not_mem_segment_of_points_outside_of_symmDiff_isCycleOrPath
          G hM hN hSymm
          ⟨hx₀poly, hx₀_out⟩ ⟨hy₀poly, hy₀_out⟩ hmidSegNative
    have hExtremeImage :
        IsExtreme ℝ (L '' G.matchingPolytope)
          (segment ℝ (L (G.subgraphIncidenceVector ℝ M))
            (L (G.subgraphIncidenceVector ℝ N))) := by
      -- The Chapter 3 midpoint criterion applies after one finite coordinate reindexing.
      refine
        (isExtreme_segment_iff_midpoint_not_mem_segment_of_points_outside_segment
          (hmatchingConvex.linear_image L.toLinearMap)
          hMvtxImage hNvtxImage (fun hEq ↦ hvec_ne (L.injective hEq))).2 hmidImage
    have hExtreme :
        IsExtreme ℝ G.matchingPolytope
          (segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) := by
      refine ⟨hmatchingConvex.segment_subset hMpoly hNpoly, ?_⟩
      intro x hxP y hyP z hzSeg hzOpen
      have hzSegImage :
          L z ∈
            segment ℝ (L (G.subgraphIncidenceVector ℝ M))
              (L (G.subgraphIncidenceVector ℝ N)) := by
        have hzSegImage' :
            L z ∈ L '' segment ℝ (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) := ⟨z, hzSeg, rfl⟩
        rw [← hL_segment]
        exact hzSegImage'
      have hzOpenImage :
          L z ∈ openSegment ℝ (L x) (L y) := by
        have hzOpenImage' : L z ∈ L '' openSegment ℝ x y := ⟨z, hzOpen, rfl⟩
        rw [← hL_openSegment]
        exact hzOpenImage'
      have hxSegImage :
          L x ∈
            segment ℝ (L (G.subgraphIncidenceVector ℝ M))
              (L (G.subgraphIncidenceVector ℝ N)) :=
        hExtremeImage.left_mem_of_mem_openSegment
          ⟨x, hxP, rfl⟩ ⟨y, hyP, rfl⟩ hzSegImage hzOpenImage
      have hxSegImage' :
          L x ∈ L '' segment ℝ (G.subgraphIncidenceVector ℝ M)
            (G.subgraphIncidenceVector ℝ N) := by
        rw [hL_segment]
        exact hxSegImage
      rcases hxSegImage' with ⟨x', hx'Seg, hx'Eq⟩
      have hx' : x' = x := L.injective (by simpa using hx'Eq)
      simpa [hx'] using hx'Seg
    exact (isEdgeOf_segment_iff hvec_ne).2 hExtreme

/-- For Exercise 4.27 (1), two matchings `M` and `N` in `G` have adjacent incidence-vector
vertices of the matching polytope if and only if `M △ N` consists of a cycle or a path. -/
theorem matchingIncidenceVector_adjacent_vertices_iff_symmDiff_isCycleOrPath
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching) :
    (polytope_skeleton G.matchingPolytope).Adj
        ⟨G.subgraphIncidenceVector ℝ M,
          subgraphIncidenceVector_mem_extremePoints_matchingPolytope G hM⟩
        ⟨G.subgraphIncidenceVector ℝ N,
          subgraphIncidenceVector_mem_extremePoints_matchingPolytope G hN⟩ ↔
      (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath := by
  rw [polytope_skeleton_adj_iff]
  constructor
  · rintro ⟨_hne, hEdge⟩
    -- The public adjacency statement is just the segment-edge criterion on the same endpoints.
    exact
      (matchingIncidenceVector_segment_isEdgeOf_iff_symmDiff_isCycleOrPath
        G hM hN).1 hEdge
  · intro hSymm
    refine ⟨?_, ?_⟩
    · intro hEq
      -- Route correction: endpoint distinctness is established from the nonempty symmetric
      -- difference, not by re-running the whole edge argument.
      have hInc :
          G.subgraphIncidenceVector ℝ M = G.subgraphIncidenceVector ℝ N :=
        congrArg Subtype.val hEq
      have hEdgeEq : M.edgeSet = N.edgeSet :=
        edgeSet_eq_of_subgraphIncidenceVector_eq G hInc
      have hSpanningEq : M.spanningCoe.edgeSet = N.spanningCoe.edgeSet := by
        simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using hEdgeEq
      have hEmpty : (M.spanningCoe ∆ N.spanningCoe).edgeSet = ∅ := by
        ext e
        simp [symmDiff_def, hSpanningEq]
      exact (isCycleOrPath_edgeSet_nonempty (H := M.spanningCoe ∆ N.spanningCoe) hSymm).ne_empty
        hEmpty
    · -- The remaining work is exactly the source-facing segment-edge criterion proved above.
      exact
        (matchingIncidenceVector_segment_isEdgeOf_iff_symmDiff_isCycleOrPath
          G hM hN).2 hSymm

end FinitePart_1

/-- Helper for Exercise 4.27: summing a subgraph incidence vector over all edge coordinates counts
the edges of the subgraph. -/
lemma matchingIncidenceVector_total_sum_eq_card_edgeSet
    [Fintype V] (M : G.Subgraph) :
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ M e) = (Fintype.card M.edgeSet : ℝ) := by
  classical
  have hfilter :
      ((Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ M.edgeSet).card : ℝ) =
        Fintype.card M.edgeSet := by
    calc
      ((Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ M.edgeSet).card : ℝ) =
          (Fintype.card {e : G.edgeSet // e.1 ∈ M.edgeSet} : ℝ) := by
            exact congrArg (fun n : ℕ ↦ (n : ℝ))
              ((Fintype.card_of_subtype
                (Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ M.edgeSet)
                (by
                  intro e
                  simp)).symm)
      _ = Fintype.card M.edgeSet := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) <| Fintype.card_congr
            { toFun := fun e ↦ ⟨e.1.1, e.2⟩
              invFun := fun e ↦ ⟨⟨e.1, M.edgeSet_subset e.2⟩, e.2⟩
              left_inv := by
                intro e
                cases e
                rfl
              right_inv := by
                intro e
                cases e
                rfl }
  -- The coordinate sum is the sum of a `0/1` indicator function over `G.edgeSet`.
  calc
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ M e) =
        (∑ e : G.edgeSet, if e.1 ∈ M.edgeSet then (1 : ℝ) else 0) := by
          simp [SimpleGraph.subgraphIncidenceVector]
    _ = ((Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ M.edgeSet).card : ℝ) := by
          simpa using
            (Finset.sum_boole (fun e : G.edgeSet ↦ e.1 ∈ M.edgeSet) Finset.univ : _)
    _ = Fintype.card M.edgeSet := hfilter

/-- Helper for Exercise 4.27: the total sum of a matching-incidence vector is also the `ncard` of
the matching edge set. -/
private lemma matchingIncidenceVector_total_sum_eq_ncard_edgeSet
    [Fintype V] (M : G.Subgraph) :
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ M e) = (M.edgeSet.ncard : ℝ) := by
  -- Rewrite the already established `Fintype.card` formula through `Set.ncard`.
  calc
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ M e) = (Fintype.card M.edgeSet : ℝ) := by
      simpa using matchingIncidenceVector_total_sum_eq_card_edgeSet (G := G) M
    _ = (M.edgeSet.ncard : ℝ) := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- The incidence vectors of the matchings of `G` with exactly `k` edges. -/
def cardinalityKMatchingIncidenceSet (k : ℕ) : Set (G.edgeSet → ℝ) :=
  {x | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k ∧ x = G.subgraphIncidenceVector ℝ M}

/-- Membership in `cardinalityKMatchingIncidenceSet G k` means being the incidence vector of a
matching of `G` with cardinality `k`. -/
lemma mem_cardinalityKMatchingIncidenceSet_iff {k : ℕ} {x : G.edgeSet → ℝ} :
    x ∈ cardinalityKMatchingIncidenceSet G k ↔
      ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k ∧ x = G.subgraphIncidenceVector ℝ M := by
  rfl
/-- Helper for Exercise 4.27: the incidence vector of a size-`k` matching already lies in the
`k`-slice of the matching polytope. -/
lemma subgraphIncidenceVector_mem_matchingPolytope_inter_cardinality_hyperplane
    [Fintype V] {k : ℕ} {M : G.Subgraph} (hM : M.IsMatching) (hcard : M.edgeSet.ncard = k) :
    G.subgraphIncidenceVector ℝ M ∈
      G.matchingPolytope ∩ {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)} := by
  constructor
  · -- The defining generators of `matchingPolytope` are exactly the matching-incidence vectors.
    rw [SimpleGraph.matchingPolytope]
    exact subset_convexHull ℝ _ ⟨M, hM, rfl⟩
  · -- Convert the total edge-coordinate sum into the matching cardinality.
    have hnat : Fintype.card M.edgeSet = M.edgeSet.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hcard' : Fintype.card M.edgeSet = k := by
      rw [hnat]
      exact hcard
    calc
      ∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ M e = (Fintype.card M.edgeSet : ℝ) := by
        simpa using matchingIncidenceVector_total_sum_eq_card_edgeSet (G := G) M
      _ = (k : ℝ) := by
        exact_mod_cast hcard'

/-- Helper for Exercise 4.27: the convex hull generated by the size-`k` matchings is contained in
the `k`-slice of the matching polytope. -/
lemma convexHull_cardinality_k_matchings_subset_matchingPolytope_inter_cardinality_hyperplane
    [Fintype V] (k : ℕ) :
    convexHull ℝ (cardinalityKMatchingIncidenceSet G k) ⊆
      G.matchingPolytope ∩ {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)} := by
  refine convexHull_min ?_ ?_
  · intro x hx
    rw [mem_cardinalityKMatchingIncidenceSet_iff] at hx
    rcases hx with ⟨M, hM, hcard, rfl⟩
    -- Each generator already satisfies both the matching-polytope and cardinality conditions.
    exact
      subgraphIncidenceVector_mem_matchingPolytope_inter_cardinality_hyperplane
        (G := G) hM hcard
  · -- The target slice is an intersection of two convex sets.
    have hmatching_convex : Convex ℝ G.matchingPolytope := by
      rw [SimpleGraph.matchingPolytope]
      exact convex_convexHull ℝ _
    have hhyper_convex :
        Convex ℝ {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)} := by
      let totalMap : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun x ↦ ∑ e : G.edgeSet, x e
          map_add' := by
            intro x y
            simp [Finset.sum_add_distrib]
          map_smul' := by
            intro a x
            simp [smul_eq_mul, Finset.mul_sum] }
      have hpre :
          {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)} =
            totalMap ⁻¹' ({(k : ℝ)} : Set ℝ) := by
        ext x
        simp [totalMap]
      rw [hpre]
      exact (convex_singleton (k : ℝ)).linear_preimage totalMap
    exact hmatching_convex.inter hhyper_convex

/-- Helper for Exercise 4.27: the family of matching-incidence generators is finite. -/
private lemma finiteMatchingIncidenceGenerators [Fintype V] :
    (Set.range fun M : {M : G.Subgraph // M.IsMatching} ↦
      G.subgraphIncidenceVector ℝ M.1).Finite := by
  -- The subtype of matchings is finite, so its image under the incidence-vector map is finite.
  exact Set.finite_range _

/-- Helper for Exercise 4.27: the matching polytope is compact because it is the convex hull of
the finite family of matching-incidence generators. -/
lemma matchingPolytope_isCompact [Fintype V] :
    IsCompact G.matchingPolytope := by
  let matchingGenerators : Set (G.edgeSet → ℝ) :=
    Set.range fun M : {M : G.Subgraph // M.IsMatching} ↦ G.subgraphIncidenceVector ℝ M.1
  have hgenerators :
      {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = G.subgraphIncidenceVector ℝ M} =
        matchingGenerators := by
    ext x
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact ⟨⟨M, hM⟩, rfl⟩
    · rintro ⟨M, rfl⟩
      exact ⟨M.1, M.2, rfl⟩
  -- Rewrite `matchingPolytope` as the convex hull of a finite range of generators.
  rw [SimpleGraph.matchingPolytope, hgenerators]
  simpa [matchingGenerators] using
    (finiteMatchingIncidenceGenerators (G := G)).isCompact_convexHull ℝ

/-- Helper for Exercise 4.27: the total-edge-cardinality hyperplane is closed. -/
lemma cardinalityHyperplane_isClosed [Fintype V] (k : ℕ) :
    IsClosed {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)} := by
  let totalMap : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ ∑ e : G.edgeSet, x e
      map_add' := by
        intro x y
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        simp [smul_eq_mul, Finset.mul_sum] }
  have hpre :
      {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)} =
        totalMap ⁻¹' ({(k : ℝ)} : Set ℝ) := by
    ext x
    simp [totalMap]
  -- The hyperplane is the preimage of a singleton under the total-sum linear map.
  rw [hpre]
  exact isClosed_singleton.preimage totalMap.continuous_of_finiteDimensional

/-- Helper for Exercise 4.27: the total-edge-cardinality hyperplane is convex. -/
lemma cardinalityHyperplane_convex [Fintype V] (k : ℕ) :
    Convex ℝ {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)} := by
  let totalMap : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ ∑ e : G.edgeSet, x e
      map_add' := by
        intro x y
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        simp [smul_eq_mul, Finset.mul_sum] }
  have hpre :
      {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)} =
        totalMap ⁻¹' ({(k : ℝ)} : Set ℝ) := by
    ext x
    simp [totalMap]
  -- Equality to a fixed total sum is a linear-preimage of a singleton.
  rw [hpre]
  exact (convex_singleton (k : ℝ)).linear_preimage totalMap

/-- Helper for Exercise 4.27: the cardinality slice of the matching polytope is compact. -/
lemma matchingPolytope_inter_cardinality_hyperplane_isCompact [Fintype V] (k : ℕ) :
    IsCompact (G.matchingPolytope ∩ {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)}) := by
  -- Intersect the compact matching polytope with the closed total-sum hyperplane.
  exact (matchingPolytope_isCompact (G := G)).inter_right
    (cardinalityHyperplane_isClosed (G := G) k)

/-- Helper for Exercise 4.27: the cardinality slice of the matching polytope is convex. -/
lemma matchingPolytope_inter_cardinality_hyperplane_convex [Fintype V] (k : ℕ) :
    Convex ℝ (G.matchingPolytope ∩ {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)}) := by
  have hmatching_convex : Convex ℝ G.matchingPolytope := by
    rw [SimpleGraph.matchingPolytope]
    exact convex_convexHull ℝ _
  -- Intersect the ambient polytope with the affine total-sum hyperplane.
  exact hmatching_convex.inter (cardinalityHyperplane_convex (G := G) k)

/-- Helper for Exercise 4.27: an ambient extreme point of `G.matchingPolytope` lying on the
cardinality-`k` hyperplane is already the incidence vector of a size-`k` matching. -/
private lemma mem_cardinality_k_matching_generators_of_mem_extremePoints_matchingPolytope
    [Fintype V] {x : G.edgeSet → ℝ} {k : ℕ}
    (hx : x ∈ (G.matchingPolytope).extremePoints ℝ)
    (hxsum : ∑ e, x e = (k : ℝ)) :
    x ∈ cardinalityKMatchingIncidenceSet G k := by
  rw [SimpleGraph.matchingPolytope] at hx
  rcases extremePoints_convexHull_subset hx with ⟨M, hM, rfl⟩
  -- Extreme points of the convex hull are actual matching generators.
  refine ⟨M, hM, ?_, rfl⟩
  have hnat : Fintype.card M.edgeSet = M.edgeSet.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcard : Fintype.card M.edgeSet = k := by
    -- The total coordinate sum computes the matching cardinality.
    have hsum_card :
        (Fintype.card M.edgeSet : ℝ) = (k : ℝ) := by
      calc
        (Fintype.card M.edgeSet : ℝ) =
            ∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ M e := by
              simpa using (matchingIncidenceVector_total_sum_eq_card_edgeSet (G := G) M).symm
        _ = (k : ℝ) := hxsum
    exact_mod_cast hsum_card
  exact hnat ▸ hcard

/-- Helper for Exercise 4.27: the size-`k` matching-incidence generators form a finite subset of
the ambient edge-coordinate space. -/
private lemma finite_cardinality_k_matching_generators [Fintype V] (k : ℕ) :
    (cardinalityKMatchingIncidenceSet G k).Finite := by
  -- The size-`k` generators are a subset of the finite range of all matching-incidence vectors.
  refine (Set.finite_range fun M : G.Subgraph ↦ G.subgraphIncidenceVector ℝ M).subset ?_
  intro y hy
  rw [mem_cardinalityKMatchingIncidenceSet_iff] at hy
  rcases hy with ⟨M, _, _, rfl⟩
  exact ⟨M, rfl⟩

/-- Helper for Exercise 4.27: every matching-incidence vector is already an integral edge
coordinate vector. -/
private lemma subgraphIncidenceVector_mem_integerRange {M : G.Subgraph} :
    G.subgraphIncidenceVector ℝ M ∈
      Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z) := by
  -- Each matching-incidence coordinate is literally the cast of the corresponding `0/1`
  -- integer indicator on the ambient edge set.
  refine ⟨fun e ↦ if e.1 ∈ M.edgeSet then 1 else 0, ?_⟩
  funext e
  by_cases he : e.1 ∈ M.edgeSet
  · simp [SimpleGraph.subgraphIncidenceVector, he]
  · simp [SimpleGraph.subgraphIncidenceVector, he]

/-- Helper for Exercise 4.27: the whole matching polytope lies in the convex hull of the integral
ambient edge-coordinate vectors. -/
private lemma matchingPolytope_subset_convexHull_integerRange :
    G.matchingPolytope ⊆
      convexHull ℝ (Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) := by
  rw [SimpleGraph.matchingPolytope]
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro x hx
  rcases hx with ⟨M, _hM, rfl⟩
  -- Every generator of the matching polytope is already an integral `0/1` point.
  exact subset_convexHull ℝ _ (subgraphIncidenceVector_mem_integerRange (G := G))

/-- Helper for Exercise 4.27: every integral point of the matching polytope is already the
incidence vector of a matching. -/
private lemma edgeCoordinate_eq_zero_or_one_of_mem_matchingPolytope_of_integerRange
    [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ G.matchingPolytope)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (e : G.edgeSet) :
    x e = 0 ∨ x e = 1 := by
  rcases hxInt with ⟨z, rfl⟩
  have hz_nonneg : (0 : ℤ) ≤ z e := by
    have hreal : (0 : ℝ) ≤ (z e : ℝ) := (matchingPolytope_coordinateBounds G hx e).1
    exact_mod_cast hreal
  have hz_le_one : z e ≤ 1 := by
    have hreal : ((z e : ℝ) ≤ 1) := (matchingPolytope_coordinateBounds G hx e).2
    exact_mod_cast hreal
  -- Integer coordinates inside `[0,1]` can only be `0` or `1`.
  have hz_cases : z e = 0 ∨ z e = 1 := by
    omega
  rcases hz_cases with hzero | hone
  · left
    simpa using congrArg (fun n : ℤ ↦ (n : ℝ)) hzero
  · right
    simpa using congrArg (fun n : ℤ ↦ (n : ℝ)) hone

/-- Helper for Exercise 4.27: the support adjacency relation of an integral edge vector records
exactly the ambient edges whose coordinate equals `1`. -/
private def integralSupportSubgraphAdj (x : G.edgeSet → ℝ) (v w : V) : Prop :=
  ∃ h : G.Adj v w, x ⟨s(v, w), G.mem_edgeSet.2 h⟩ = 1

/-- Helper for Exercise 4.27: the support adjacency relation is contained in the ambient graph. -/
private lemma integralSupportSubgraphAdj_sub (x : G.edgeSet → ℝ) {v w : V} :
    integralSupportSubgraphAdj G x v w → G.Adj v w := by
  intro h
  exact h.1

/-- Helper for Exercise 4.27: every support edge contributes its left endpoint to the support
vertex set. -/
private lemma integralSupportSubgraphAdj_edge_vert (x : G.edgeSet → ℝ) {v w : V}
    (h : integralSupportSubgraphAdj G x v w) :
    v ∈ {u : V | ∃ z, integralSupportSubgraphAdj G x u z} := by
  exact ⟨w, h⟩

/-- Helper for Exercise 4.27: the support adjacency relation is symmetric. -/
private lemma integralSupportSubgraphAdj_symm (x : G.edgeSet → ℝ) :
    Symmetric (integralSupportSubgraphAdj G x) := by
  intro v w h
  rcases h with ⟨hvw, hxvw⟩
  refine ⟨hvw.symm, ?_⟩
  simpa [Sym2.eq_swap] using hxvw

/-- Helper for Exercise 4.27: the ambient edges with coordinate `1` form a subgraph of `G`. -/
private def integralSupportSubgraph (x : G.edgeSet → ℝ) : G.Subgraph :=
  { verts := {v : V | ∃ w, integralSupportSubgraphAdj G x v w}
    Adj := integralSupportSubgraphAdj G x
    adj_sub := integralSupportSubgraphAdj_sub G x
    edge_vert := integralSupportSubgraphAdj_edge_vert G x
    symm := integralSupportSubgraphAdj_symm G x }

/-- Helper for Exercise 4.27: adjacency in the support subgraph means that the corresponding edge
coordinate is `1`. -/
private lemma integralSupportSubgraph_adj_iff (x : G.edgeSet → ℝ) {u v : V} :
    (integralSupportSubgraph G x).Adj u v ↔
      ∃ h : G.Adj u v, x ⟨s(u, v), G.mem_edgeSet.2 h⟩ = 1 := by
  -- Unfold the support subgraph once so the adjacency field reduces to the defining relation.
  change integralSupportSubgraphAdj G x u v ↔
    ∃ h : G.Adj u v, x ⟨s(u, v), G.mem_edgeSet.2 h⟩ = 1
  rfl

/-- Helper for Exercise 4.27: an ambient edge lies in the support subgraph exactly when its
coordinate equals `1`. -/
private lemma integralSupportSubgraph_mem_edgeSet_iff
    (x : G.edgeSet → ℝ) (e : G.edgeSet) :
    e.1 ∈ (integralSupportSubgraph G x).edgeSet ↔ x e = 1 := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    rw [← G.mem_edgeSet]
    simpa [e.1.out_eq] using e.2
  rw [← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet,
    integralSupportSubgraph_adj_iff (G := G) (x := x)]
  constructor
  · rintro ⟨hG, hx⟩
    have hSubtype :
        (⟨s(e.1.out.1, e.1.out.2), G.mem_edgeSet.2 hG⟩ : G.edgeSet) = e := by
      apply Subtype.ext
      exact e.1.out_eq
    simpa [hSubtype] using hx
  · intro hx
    refine ⟨hadj, ?_⟩
    have hSubtype :
        (⟨s(e.1.out.1, e.1.out.2), G.mem_edgeSet.2 hadj⟩ : G.edgeSet) = e := by
      apply Subtype.ext
      exact e.1.out_eq
    simpa [hSubtype] using hx

/-- Helper for Exercise 4.27: every covered vertex of an integral point of `G.matchingPolytope`
has a unique support neighbor. -/
private lemma existsUnique_supportNeighbor_of_mem_matchingPolytope_of_integerRange
    [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ G.matchingPolytope)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    {v : V} (hv : v ∈ (integralSupportSubgraph G x).verts) :
    ∃! w : V, (integralSupportSubgraph G x).Adj v w := by
  let _ : Fintype V := Fintype.ofFinite V
  -- Unfold the support-vertex predicate so the witness edge can be extracted explicitly.
  change ∃ w, integralSupportSubgraphAdj G x v w at hv
  rcases hv with ⟨w, hAdj_vw⟩
  rcases hAdj_vw with ⟨hvw, hxe⟩
  let I : Finset G.edgeSet :=
    Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset v
  let e : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.2 hvw⟩
  have heI : e ∈ I := by
    simp [I, e, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  have hincident_le :
      (Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset v).sum x ≤ 1 :=
    matchingPolytopeIncidentSum_le_one G hx v
  have hsum_le : x e + (I.erase e).sum x ≤ 1 := by
    calc
      x e + (I.erase e).sum x = I.sum x := by
        exact Finset.add_sum_erase I x heI
      _ =
          (Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset v).sum x := by
            rfl
      _ ≤ 1 := by
        exact hincident_le
  have hxe_one : x e = 1 := by
    simpa [e] using hxe
  refine ⟨w, ⟨hvw, hxe⟩, ?_⟩
  intro u hu
  rcases hu with ⟨hvu, hxf⟩
  let f : G.edgeSet := ⟨s(v, u), G.mem_edgeSet.2 hvu⟩
  have hfI : f ∈ I := by
    simp [I, f, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  by_contra hwu
  have hfe : f ≠ e := by
    intro hfeEq
    apply hwu
    have hs : s(v, u) = s(v, w) := by
      simpa [f, e] using congrArg Subtype.val hfeEq
    exact Sym2.congr_right.mp hs
  have hf_erase : f ∈ I.erase e := Finset.mem_erase.mpr ⟨hfe, hfI⟩
  have hsum_erase_ge_one : 1 ≤ (I.erase e).sum x := by
    have hcoord_nonneg : ∀ g : G.edgeSet, 0 ≤ x g := by
      intro g
      exact (matchingPolytope_coordinateBounds G hx g).1
    have hsingle : x f ≤ (I.erase e).sum x := by
      exact Finset.single_le_sum (fun g _ ↦ hcoord_nonneg g) hf_erase
    calc
      1 = x f := by simpa [f] using hxf.symm
      _ ≤ (I.erase e).sum x := hsingle
  linarith

/-- Helper for Exercise 4.27: the support subgraph of an integral point of `G.matchingPolytope`
is a matching. -/
private lemma integralSupportSubgraph_isMatching_of_mem_matchingPolytope_of_integerRange
    [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ G.matchingPolytope)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    (integralSupportSubgraph G x).IsMatching := by
  intro v hv
  -- The matching API asks for a unique support neighbor at each covered vertex.
  exact existsUnique_supportNeighbor_of_mem_matchingPolytope_of_integerRange
    (G := G) hx hxInt hv

/-- Helper for Exercise 4.27: an integral point of `G.matchingPolytope` is the incidence vector
of its support matching. -/
private lemma integerPoint_eq_subgraphIncidenceVector_of_mem_matchingPolytope
    [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ G.matchingPolytope)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    ∃ M : G.Subgraph, M.IsMatching ∧ x = G.subgraphIncidenceVector ℝ M := by
  let M : G.Subgraph := integralSupportSubgraph G x
  have hM : M.IsMatching :=
    integralSupportSubgraph_isMatching_of_mem_matchingPolytope_of_integerRange
      (G := G) hx hxInt
  refine ⟨M, hM, ?_⟩
  funext e
  by_cases he : x e = 1
  · have heM : e.1 ∈ M.edgeSet := by
      simpa [M] using (integralSupportSubgraph_mem_edgeSet_iff (G := G) x e).2 he
    -- On the support, both the reconstructed incidence vector and `x` equal `1`.
    simp [M, SimpleGraph.subgraphIncidenceVector, heM, he]
  · have hx0 : x e = 0 := by
      rcases edgeCoordinate_eq_zero_or_one_of_mem_matchingPolytope_of_integerRange
          G hx hxInt e with hzero | hone
      · exact hzero
      · exact (he hone).elim
    have heM : e.1 ∉ M.edgeSet := by
      intro heM
      exact he ((integralSupportSubgraph_mem_edgeSet_iff (G := G) x e).1 (by simpa [M] using heM))
    -- Outside the support, both the reconstructed incidence vector and `x` vanish.
    simp [M, SimpleGraph.subgraphIncidenceVector, heM, hx0]

/-- Helper for Exercise 4.27: every integral point of the matching polytope is already the
incidence vector of a matching. -/
private lemma mem_matching_generators_of_mem_matchingPolytope_of_mem_integerRange
    [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ G.matchingPolytope)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    x ∈ {y | ∃ M : G.Subgraph, M.IsMatching ∧ y = G.subgraphIncidenceVector ℝ M} := by
  rcases integerPoint_eq_subgraphIncidenceVector_of_mem_matchingPolytope
      (G := G) hx hxInt with ⟨M, hM, rfl⟩
  -- The reconstructed support subgraph is one of the defining matching generators.
  exact ⟨M, hM, rfl⟩

/-- Helper for Exercise 4.27: summing the coordinates of an affine line map commutes with taking
the affine line map of the endpoint sums. -/
private lemma totalEdgeSum_lineMap [Fintype V]
    (x y : G.edgeSet → ℝ) (t : ℝ) :
    (∑ e, AffineMap.lineMap x y t e) =
      AffineMap.lineMap (∑ e, x e) (∑ e, y e) t := by
  -- Expand `lineMap` coordinatewise and move the scalar coefficients outside the finite sum.
  simp [AffineMap.lineMap_apply_module, Finset.sum_add_distrib, Finset.mul_sum,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul]

/-- Helper for Exercise 4.27: a strict convex combination of consecutive integers cannot equal the
smaller endpoint. -/
private lemma lineMap_consecutive_nat_ne_left
    {m : ℕ} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    AffineMap.lineMap (m : ℝ) (m + 1 : ℝ) t ≠ (m : ℝ) := by
  -- The line-map value is strictly larger than the left endpoint when the parameter is in `(0,1)`.
  intro h
  have ht_pos : 0 < t := ht.1
  have ht_lt : t < 1 := ht.2
  simp [AffineMap.lineMap_apply_module] at h
  nlinarith

/-- Helper for Exercise 4.27: a one-dimensional affine direction is generated by any nonzero chord
inside the face. -/
private lemma selectedFace_direction_eq_spanChord
    {n : ℕ} {F : Set (Fin n → ℝ)} {u v : Fin n → ℝ}
    (hu : u ∈ F) (hv : v ∈ F) (huv : u ≠ v)
    (hfinrank : Module.finrank ℝ (affineSpan ℝ F).direction = 1) :
    (affineSpan ℝ F).direction = ℝ ∙ (v - u) := by
  -- Any nontrivial chord of a one-dimensional affine hull spans the full direction space.
  have huv_dir : v - u ∈ (affineSpan ℝ F).direction := by
    simpa using
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hv) (mem_affineSpan ℝ hu)
  have huv_ne_zero : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  exact
    submodule_eq_span_singleton_of_finrank_eq_one
      (D := (affineSpan ℝ F).direction) huv_dir huv_ne_zero hfinrank

/-- Helper for Exercise 4.27: a compact face admits points minimizing and maximizing any fixed
coordinate. -/
private lemma selectedFace_coordinateExtrema
    {n : ℕ} {F : Set (Fin n → ℝ)} {j : Fin n}
    (hF_nonempty : F.Nonempty) (hF_compact : IsCompact F) :
    ∃ y z, y ∈ F ∧ z ∈ F ∧ ∀ w ∈ F, y j ≤ w j ∧ w j ≤ z j := by
  -- Minimize and maximize the chosen coordinate on the compact face.
  let coord : (Fin n → ℝ) → ℝ := fun x ↦ x j
  have hcoord_compact : IsCompact (coord '' F) := hF_compact.image (continuous_apply j)
  obtain ⟨ycoord, hycoord_min⟩ :=
    hcoord_compact.exists_isLeast (hF_nonempty.image coord)
  obtain ⟨zcoord, hzcoord_max⟩ :=
    hcoord_compact.exists_isGreatest (hF_nonempty.image coord)
  rcases hycoord_min with ⟨hycoord_mem, hycoord_min⟩
  rcases hzcoord_max with ⟨hzcoord_mem, hzcoord_max⟩
  rcases hycoord_mem with ⟨y, hyF, rfl⟩
  rcases hzcoord_mem with ⟨z, hzF, rfl⟩
  refine ⟨y, z, hyF, hzF, ?_⟩
  intro w hwF
  constructor
  · exact hycoord_min ⟨w, hwF, rfl⟩
  · exact hzcoord_max ⟨w, hwF, rfl⟩

/-- Helper for Exercise 4.27: once one coordinate sees the one-dimensional affine direction,
coordinate bounds force the whole face into the segment between its extremizers. -/
private lemma selectedFace_subset_segment_of_coordinateExtrema
    {n : ℕ} {F : Set (Fin n → ℝ)} {r y z : Fin n → ℝ} {j : Fin n}
    (hyF : y ∈ F) (hzF : z ∈ F)
    (hcoord : ∀ w ∈ F, y j ≤ w j ∧ w j ≤ z j)
    (hyz : y j < z j)
    (hrj : r j ≠ 0)
    (hdir : (affineSpan ℝ F).direction = ℝ ∙ r) :
    F ⊆ segment ℝ y z := by
  intro w hwF
  -- Rewrite both displacements from `y` along the unique direction `r`.
  have hwy_dir : w - y ∈ (affineSpan ℝ F).direction := by
    simpa using
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hwF) (mem_affineSpan ℝ hyF)
  have hzy_dir : z - y ∈ (affineSpan ℝ F).direction := by
    simpa using
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hzF) (mem_affineSpan ℝ hyF)
  have hwy_span : w - y ∈ ℝ ∙ r := by simpa [hdir] using hwy_dir
  have hzy_span : z - y ∈ ℝ ∙ r := by simpa [hdir] using hzy_dir
  rw [Submodule.mem_span_singleton] at hwy_span hzy_span
  rcases hwy_span with ⟨a, hwy_eq⟩
  rcases hzy_span with ⟨b, hzy_eq⟩
  have hb_ne : b ≠ 0 := by
    intro hb_zero
    have hzjy : z j - y j = 0 := by
      have hcoord_eq := congrArg (fun v ↦ v j) hzy_eq
      simpa [hb_zero] using hcoord_eq.symm
    exact (sub_ne_zero.mpr (ne_of_gt hyz)) hzjy
  have hwj_line :
      w j = AffineMap.lineMap (y j) (z j) (a / b) := by
    have hwy_j : w j - y j = a * r j := by
      simpa using (congrArg (fun v ↦ v j) hwy_eq).symm
    have hzy_j : z j - y j = b * r j := by
      simpa using (congrArg (fun v ↦ v j) hzy_eq).symm
    have hwj_eq :
        w j = y j + (a / b) * (z j - y j) := by
      have hwj_sub : w j = y j + a * r j := by
        linarith
      rw [hwj_sub, hzy_j]
      field_simp [hb_ne]
    simpa [AffineMap.lineMap_apply_module, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_add, add_mul] using hwj_eq
  have hparam_left : 0 ≤ a / b := by
    have hyw : y j ≤ w j := (hcoord w hwF).1
    simp [AffineMap.lineMap_apply_module] at hwj_line
    nlinarith
  have hparam_right : a / b ≤ 1 := by
    have hwz : w j ≤ z j := (hcoord w hwF).2
    simp [AffineMap.lineMap_apply_module] at hwj_line
    nlinarith
  -- The coordinate parameter determines the whole point because every displacement is parallel to
  -- `r`.
  rw [segment_eq_image_lineMap]
  refine ⟨a / b, ⟨hparam_left, hparam_right⟩, ?_⟩
  ext i
  have hwy_i : w i - y i = a * r i := by
    simpa using (congrArg (fun v ↦ v i) hwy_eq).symm
  have hzy_i : z i - y i = b * r i := by
    simpa using (congrArg (fun v ↦ v i) hzy_eq).symm
  have hwi_eq :
      w i = y i + (a / b) * (z i - y i) := by
    have hwi_sub : w i = y i + a * r i := by
      linarith
    rw [hwi_sub, hzy_i]
    field_simp [hb_ne]
  simpa [AffineMap.lineMap_apply_module, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_add, add_mul] using hwi_eq.symm

/-- Helper for Exercise 4.27: a nonempty compact convex subset of `Fin n → ℝ` whose affine-span
direction is `ℝ ∙ r` with `r ≠ 0` is a segment. -/
private lemma eqSegment_of_isCompact_of_convex_of_direction_eq_spanSingleton
    {n : ℕ} {F : Set (Fin n → ℝ)} {r : Fin n → ℝ}
    (hF_nonempty : F.Nonempty) (hF_compact : IsCompact F) (hF_convex : Convex ℝ F)
    (hr_ne_zero : r ≠ 0)
    (hdir : (affineSpan ℝ F).direction = ℝ ∙ r) :
    ∃ y z, y ∈ F ∧ z ∈ F ∧ y ≠ z ∧ F = segment ℝ y z := by
  obtain ⟨j, hrj⟩ := exists_nonzero_coordinate_of_ne_zero hr_ne_zero
  obtain ⟨y, z, hyF, hzF, hcoord⟩ :=
    selectedFace_coordinateExtrema hF_nonempty hF_compact (j := j)
  have hyz : y j < z j := by
    have hy_le_z : y j ≤ z j := (hcoord z hzF).1
    by_contra hyz_not
    have hz_le_y : z j ≤ y j := le_of_not_gt hyz_not
    have hyz_eq : y j = z j := le_antisymm hy_le_z hz_le_y
    have hr_dir : r ∈ (affineSpan ℝ F).direction := by
      rw [hdir]
      exact Submodule.mem_span_singleton_self r
    have hr_dir' : r ∈ Submodule.span ℝ ((fun x : Fin n → ℝ ↦ x - y) '' F) := by
      have hr_vec : r ∈ vectorSpan ℝ F := by
        simpa [direction_affineSpan] using hr_dir
      simpa [vsub_eq_sub] using
        (show r ∈ Submodule.span ℝ ((fun x : Fin n → ℝ ↦ x -ᵥ y) '' F) by
          rw [← vectorSpan_eq_span_vsub_set_right ℝ hyF]
          exact hr_vec)
    have hspan_zero :
        Submodule.span ℝ ((fun x : Fin n → ℝ ↦ x - y) '' F) ≤
          LinearMap.ker (LinearMap.proj j) := by
      rw [Submodule.span_le]
      intro v hv
      rcases hv with ⟨w, hwF, rfl⟩
      have hyw : y j ≤ w j := (hcoord w hwF).1
      have hwz : w j ≤ z j := (hcoord w hwF).2
      have hw_eq : w j = y j := by
        nlinarith [hyw, hwz, hyz_eq]
      simpa [LinearMap.mem_ker, hw_eq]
    have hr_ker : r ∈ LinearMap.ker (LinearMap.proj j) := hspan_zero hr_dir'
    have : r j = 0 := by
      simpa [LinearMap.mem_ker] using hr_ker
    exact hrj this
  have hsubset :
      F ⊆ segment ℝ y z :=
    selectedFace_subset_segment_of_coordinateExtrema
      hyF hzF hcoord hyz hrj hdir
  have hsegment_subset : segment ℝ y z ⊆ F := hF_convex.segment_subset hyF hzF
  have hyz_ne : y ≠ z := by
    intro hyz_eq
    exact (ne_of_gt hyz) (by simpa [hyz_eq])
  exact ⟨y, z, hyF, hzF, hyz_ne, Set.Subset.antisymm hsubset hsegment_subset⟩

/-- Helper for Exercise 4.27: a nonvertex of a polyhedron cannot become a vertex of the
active-row face through that point, because the active-row face is exposed in the ambient
polyhedron. -/
private lemma not_mem_extremePoints_tightRowFace_of_not_mem_extremePoints
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {xbar : Fin n → ℝ}
    (hxNot : xbar ∉ (polyhedron_le_set A b).extremePoints ℝ) :
    let I : Set (Fin m) := {i | Matrix.mulVec A xbar i = b i}
    let F := active_constraint_face A b I
    xbar ∉ F.extremePoints ℝ := by
  intro I F hxF
  -- Extreme points of an exposed face remain extreme in the ambient polyhedron.
  have hF_exposed : IsExposed ℝ (polyhedron_le_set A b) F := by
    simpa [F, I] using active_constraint_face_isExposed A b I
  exact hxNot (hF_exposed.isExtreme.extremePoints_subset_extremePoints hxF)

/-- Helper for Exercise 4.27: the total-sum row on `Fin n` coordinates. -/
private def cardinalitySliceSumRow {n : ℕ} : Fin n → ℝ :=
  fun _ ↦ 1

/-- Helper for Exercise 4.27: augment `A *ᵥ x ≤ b` by the two total-sum rows enforcing
`∑ x = γ0`. -/
private def cardinalitySliceAugmentedMatrix
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (m + 2)) (Fin n) ℝ :=
  fun i ↦
    Fin.cases
      (cardinalitySliceSumRow)
      (fun i' ↦
        Fin.cases (-cardinalitySliceSumRow) (fun i'' ↦ A i'') i')
      i

/-- Helper for Exercise 4.27: the right-hand side for the augmented cardinality-slice system. -/
private def cardinalitySliceAugmentedRhs
    {m : ℕ} (b : Fin m → ℝ) (γ0 : ℝ) :
    Fin (m + 2) → ℝ :=
  fun i ↦
    Fin.cases γ0
      (fun i' ↦ Fin.cases (-γ0) (fun i'' ↦ b i'') i')
      i

/-- Helper for Exercise 4.27: after the two auxiliary cardinality rows, the augmented matrix is
literally the original matrix `A`. -/
private lemma cardinalitySliceAugmentedMatrix_tail_row
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    cardinalitySliceAugmentedMatrix A i.succ.succ = A i := by
  ext j
  simp [cardinalitySliceAugmentedMatrix]

/-- Helper for Exercise 4.27: after the two auxiliary cardinality rows, the augmented right-hand
side is literally the original right-hand side `b`. -/
private lemma cardinalitySliceAugmentedRhs_tail_row
    {m : ℕ} (b : Fin m → ℝ) (γ0 : ℝ) (i : Fin m) :
    cardinalitySliceAugmentedRhs b γ0 i.succ.succ = b i := by
  simp [cardinalitySliceAugmentedRhs]

/-- Helper for Exercise 4.27: the first augmented row is the all-ones cardinality row. -/
private lemma cardinalitySliceAugmentedMatrix_zero_row
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    cardinalitySliceAugmentedMatrix A 0 = cardinalitySliceSumRow := by
  ext j
  simp [cardinalitySliceAugmentedMatrix]

/-- Helper for Exercise 4.27: the second augmented row is the negated cardinality row. -/
private lemma cardinalitySliceAugmentedMatrix_one_row
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    cardinalitySliceAugmentedMatrix A 1 = -cardinalitySliceSumRow := by
  ext j
  change
    (Fin.cases
      (motive := fun _ : Fin (m + 2) ↦ Fin n → ℝ)
      cardinalitySliceSumRow
      (fun i' ↦ Fin.cases (motive := fun _ : Fin (m + 1) ↦ Fin n → ℝ)
        (-cardinalitySliceSumRow) (fun i'' ↦ A i'') i')
      ((0 : Fin (m + 1)).succ)) j =
      (-cardinalitySliceSumRow) j
  simp only [Fin.cases_succ, Fin.cases_zero]

/-- Helper for Exercise 4.27: the first augmented right-hand side is `γ0`. -/
private lemma cardinalitySliceAugmentedRhs_zero
    {m : ℕ} (b : Fin m → ℝ) (γ0 : ℝ) :
    cardinalitySliceAugmentedRhs b γ0 0 = γ0 := by
  simp [cardinalitySliceAugmentedRhs]

/-- Helper for Exercise 4.27: the second augmented right-hand side is `-γ0`. -/
private lemma cardinalitySliceAugmentedRhs_one
    {m : ℕ} (b : Fin m → ℝ) (γ0 : ℝ) :
    cardinalitySliceAugmentedRhs b γ0 1 = -γ0 := by
  change
    Fin.cases γ0
      (fun i' ↦ Fin.cases (motive := fun _ : Fin (m + 1) ↦ ℝ) (-γ0) (fun i'' ↦ b i'') i')
      ((0 : Fin (m + 1)).succ) =
      -γ0
  simp only [Fin.cases_succ, Fin.cases_zero]

/-- Helper for Exercise 4.27: the augmented cardinality-slice polyhedron is exactly the original
polyhedron intersected with the total-sum hyperplane. -/
private lemma mem_cardinalitySliceAugmentedPolyhedron_iff
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {γ0 : ℝ}
    {x : Fin n → ℝ} :
    x ∈ polyhedron_le_set (cardinalitySliceAugmentedMatrix A) (cardinalitySliceAugmentedRhs b γ0) ↔
      x ∈ polyhedron_le_set A b ∧ dotProduct cardinalitySliceSumRow x = γ0 := by
  constructor
  · intro hx
    have hx0 : dotProduct cardinalitySliceSumRow x ≤ γ0 := by
      simpa [Matrix.mulVec, dotProduct, cardinalitySliceAugmentedMatrix_zero_row,
        cardinalitySliceAugmentedRhs_zero] using hx 0
    have hx1neg : -dotProduct cardinalitySliceSumRow x ≤ -γ0 := by
      simpa [Matrix.mulVec, dotProduct, cardinalitySliceAugmentedMatrix_one_row,
        cardinalitySliceAugmentedRhs_one] using hx 1
    have hsum : dotProduct cardinalitySliceSumRow x = γ0 := by
      linarith
    refine ⟨?_, hsum⟩
    intro i
    have hi := hx i.succ.succ
    simpa [Matrix.mulVec, cardinalitySliceAugmentedMatrix_tail_row,
      cardinalitySliceAugmentedRhs_tail_row] using hi
  · rintro ⟨hx, hsum⟩
    intro i
    by_cases h0 : i = 0
    · subst h0
      simpa [Matrix.mulVec, dotProduct, cardinalitySliceAugmentedMatrix_zero_row,
        cardinalitySliceAugmentedRhs_zero, hsum] using (le_of_eq hsum)
    · by_cases h1 : i = 1
      · subst h1
        have hsum' : -dotProduct cardinalitySliceSumRow x = -γ0 := by
          linarith
        simpa [Matrix.mulVec, dotProduct, cardinalitySliceAugmentedMatrix_one_row,
          cardinalitySliceAugmentedRhs_one, hsum'] using (le_of_eq hsum')
      · obtain ⟨j, rfl⟩ := exists_tail_index_of_ne_auxiliary_slice_row h0 h1
        simpa [cardinalitySliceAugmentedMatrix_tail_row, cardinalitySliceAugmentedRhs_tail_row]
          using hx j

/-- Helper for Exercise 4.27: the two auxiliary cardinality rows are linearly dependent, so they
cannot both belong to an independent active family. -/
private lemma not_linearIndependent_cardinality_auxiliary_rows
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ¬ LinearIndependent ℝ
      (fun t : Fin 2 ↦ cardinalitySliceAugmentedMatrix A ⟨t, by omega⟩) := by
  rw [not_linearIndependent_iff]
  refine ⟨Finset.univ, fun _ ↦ (1 : ℝ), ?_, 0, by simp, by norm_num⟩
  ext j
  simp [Fin.sum_univ_two, cardinalitySliceAugmentedMatrix_zero_row,
    cardinalitySliceAugmentedMatrix_one_row, cardinalitySliceSumRow]

/-- Helper for Exercise 4.27: if `n` active rows of `A` are linearly independent at `xbar`, then
`xbar` is already an ambient extreme point of `polyhedron_le_set A b`. -/
private lemma mem_extremePoints_of_active_linearlyIndependent_rows
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ polyhedron_le_set A b)
    (I : Fin n ↪ Fin m)
    (hI_active : ∀ i : Fin n, Matrix.mulVec A xbar (I i) = b (I i))
    (hI_linearIndependent : LinearIndependent ℝ (fun i : Fin n ↦ A (I i))) :
    xbar ∈ (polyhedron_le_set A b).extremePoints ℝ := by
  exact
    (mem_extremePoints_iff_exists_active_linearlyIndependent_rows A b hxbar).2
      ⟨I, hI_active, hI_linearIndependent⟩

/-- Helper for Exercise 4.27: deleting the unique auxiliary cardinality row from an active
independent augmented family leaves `n - 1` original rows of `A` that stay active and linearly
independent. -/
private lemma augmentedSliceActiveRowsDropToOriginalRows
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {xbar : Fin n → ℝ} {γ0 : ℝ}
    (hxbar : xbar ∈ polyhedron_le_set A b)
    (hxbarNotAmbient : xbar ∉ (polyhedron_le_set A b).extremePoints ℝ)
    (J : Fin n ↪ Fin (m + 2))
    (hJ_active :
      ∀ i : Fin n,
        Matrix.mulVec (cardinalitySliceAugmentedMatrix A) xbar (J i) =
          cardinalitySliceAugmentedRhs b γ0 (J i))
    (hJ_linearIndependent :
      LinearIndependent ℝ (fun i : Fin n ↦ cardinalitySliceAugmentedMatrix A (J i))) :
    ∃ I : Fin (n - 1) ↪ Fin m,
      (∀ i : Fin (n - 1), Matrix.mulVec A xbar (I i) = b (I i)) ∧
        LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)) := by
  have haux_exists : ∃ kAux : Fin n, J kAux = 0 ∨ J kAux = 1 := by
    by_contra haux
    have hJ_nonaux : ∀ k : Fin n, J k ≠ 0 ∧ J k ≠ 1 := by
      intro k
      constructor
      · intro h0
        exact haux ⟨k, Or.inl h0⟩
      · intro h1
        exact haux ⟨k, Or.inr h1⟩
    let tail : Fin n → Fin m := fun k ↦
      Classical.choose
        (exists_tail_index_of_ne_auxiliary_slice_row (hJ_nonaux k).1 (hJ_nonaux k).2)
    have htail_eq : ∀ k : Fin n, J k = (tail k).succ.succ := by
      intro k
      exact
        Classical.choose_spec
          (exists_tail_index_of_ne_auxiliary_slice_row (hJ_nonaux k).1 (hJ_nonaux k).2)
    have htail_active : ∀ k : Fin n, Matrix.mulVec A xbar (tail k) = b (tail k) := by
      intro k
      have hk := hJ_active k
      rw [htail_eq k] at hk
      simpa [Matrix.mulVec, cardinalitySliceAugmentedMatrix_tail_row,
        cardinalitySliceAugmentedRhs_tail_row] using hk
    have htail_linearIndependent : LinearIndependent ℝ (fun k : Fin n ↦ A (tail k)) := by
      simpa [htail_eq, cardinalitySliceAugmentedMatrix_tail_row] using hJ_linearIndependent
    have hxbarExtreme :
        xbar ∈ (polyhedron_le_set A b).extremePoints ℝ :=
      mem_extremePoints_of_active_linearlyIndependent_rows hxbar
        ⟨tail, by
          intro i i' hij
          apply J.injective
          simpa [htail_eq i, htail_eq i', hij]⟩
        htail_active htail_linearIndependent
    exact hxbarNotAmbient hxbarExtreme
  obtain ⟨kAux, hkAux⟩ := haux_exists
  have hno_two_aux :
      ∀ {a b : Fin n}, a ≠ b → J a = 0 → J b = 1 → False := by
    intro a b hab hJa hJb
    let e : Fin 2 → Fin n := ![a, b]
    have he_inj : Function.Injective e := by
      intro u v huv
      fin_cases u <;> fin_cases v
      · rfl
      · have : a = b := by simpa [e] using huv
        exact False.elim (hab this)
      · have : a = b := by simpa [e] using huv.symm
        exact False.elim (hab this)
      · rfl
    have hpair_linearIndependent :
        LinearIndependent ℝ
          (fun t : Fin 2 ↦ cardinalitySliceAugmentedMatrix A (J (e t))) :=
      hJ_linearIndependent.comp e he_inj
    have hpair_eq :
        (fun t : Fin 2 ↦ cardinalitySliceAugmentedMatrix A (J (e t))) =
          (fun t : Fin 2 ↦ cardinalitySliceAugmentedMatrix A ⟨t, by omega⟩) := by
      funext t
      fin_cases t <;> simp [e, hJa, hJb]
    have hpair_linearIndependent' :
        LinearIndependent ℝ
          (fun t : Fin 2 ↦ cardinalitySliceAugmentedMatrix A ⟨t, by omega⟩) := by
      simpa [hpair_eq] using hpair_linearIndependent
    exact not_linearIndependent_cardinality_auxiliary_rows A hpair_linearIndependent'
  have hother_nonaux :
      ∀ {k : Fin n}, k ≠ kAux → J k ≠ 0 ∧ J k ≠ 1 := by
    intro k hk
    constructor
    · intro hk0
      cases hkAux with
      | inl hkAux0 =>
          exact hk (J.injective (hk0.trans hkAux0.symm))
      | inr hkAux1 =>
          exact False.elim (hno_two_aux hk hk0 hkAux1)
    · intro hk1
      cases hkAux with
      | inl hkAux0 =>
          have hkAux_ne_k : kAux ≠ k := fun h ↦ hk h.symm
          exact False.elim (hno_two_aux hkAux_ne_k hkAux0 hk1)
      | inr hkAux1 =>
          exact hk (J.injective (hk1.trans hkAux1.symm))
  have hn_pos : 0 < n := Fin.pos_iff_nonempty.mpr ⟨kAux⟩
  have hn_cast : (n - 1) + 1 = n := by
    omega
  let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm kAux
  let skip : Fin (n - 1) → Fin n := fun i ↦ Fin.cast hn_cast (pivot.succAboveEmb i)
  have hskip_ne_aux : ∀ i : Fin (n - 1), skip i ≠ kAux := by
    intro i
    intro hskip
    have :
        pivot.succAboveEmb i = pivot := by
      apply Fin.cast_injective hn_cast
      simpa [skip, pivot] using hskip
    exact Fin.succAbove_ne pivot i this
  let tail : Fin (n - 1) → Fin m := fun i ↦
    Classical.choose
      (exists_tail_index_of_ne_auxiliary_slice_row
        ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).1
        ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).2)
  have htail_eq :
      ∀ i : Fin (n - 1), J (skip i) = (tail i).succ.succ := by
    intro i
    exact
      Classical.choose_spec
        (exists_tail_index_of_ne_auxiliary_slice_row
          ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).1
          ((hother_nonaux (k := skip i)) (hskip_ne_aux i)).2)
  let I : Fin (n - 1) ↪ Fin m :=
    ⟨tail, by
      intro i i' hij
      apply pivot.succAboveEmb.inj'
      apply Fin.cast_injective hn_cast
      apply J.injective
      calc
        J (skip i) = (tail i).succ.succ := htail_eq i
        _ = (tail i').succ.succ := by simpa [hij]
        _ = J (skip i') := (htail_eq i').symm⟩
  refine ⟨I, ?_, ?_⟩
  · intro i
    have hi := hJ_active (skip i)
    rw [htail_eq i] at hi
    simpa [I, Matrix.mulVec, cardinalitySliceAugmentedMatrix_tail_row,
      cardinalitySliceAugmentedRhs_tail_row] using hi
  · have hskip_linearIndependent :
        LinearIndependent ℝ
          (fun i : Fin (n - 1) ↦ cardinalitySliceAugmentedMatrix A (J (skip i))) := by
      exact hJ_linearIndependent.comp skip (by
        intro i i' hij
        apply pivot.succAboveEmb.inj'
        apply Fin.cast_injective hn_cast
        exact hij)
    simpa [I, htail_eq, cardinalitySliceAugmentedMatrix_tail_row] using hskip_linearIndependent

/-- Helper for Exercise 4.27: the left endpoint of a nondegenerate segment in `Fin n → ℝ` is an
extreme point of that segment. -/
private lemma left_mem_extremePoints_segment_fin
    {n : ℕ} {x y : Fin n → ℝ} (hxy : x ≠ y) :
    x ∈ (segment ℝ x y).extremePoints ℝ := by
  rw [mem_extremePoints_iff_forall_segment]
  constructor
  · exact left_mem_segment ℝ x y
  · intro u hu v hv hxSeg
    rw [segment_eq_image_lineMap] at hu hv hxSeg
    rcases hu with ⟨a, ha, rfl⟩
    rcases hv with ⟨b, hb, rfl⟩
    rcases hxSeg with ⟨t, ht, hxt⟩
    have hparam :
        AffineMap.lineMap a b t = (0 : ℝ) := by
      obtain ⟨j, hj⟩ := exists_nonzero_coordinate_of_ne_zero (sub_ne_zero.mpr hxy.symm)
      have hxt' := congrArg (fun w ↦ w j) hxt
      have hlinej :
          AffineMap.lineMap (AffineMap.lineMap (x j) (y j) a)
            (AffineMap.lineMap (x j) (y j) b) t = x j := by
        simpa [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc, mul_add, add_mul] using hxt'
      have hrewrite :
          AffineMap.lineMap (AffineMap.lineMap (x j) (y j) a)
            (AffineMap.lineMap (x j) (y j) b) t =
              AffineMap.lineMap (x j) (y j) (AffineMap.lineMap a b t) := by
        simp [AffineMap.lineMap_apply_module]
        ring
      have hcoord :
          AffineMap.lineMap (x j) (y j) (AffineMap.lineMap a b t) = x j :=
        hrewrite.symm.trans hlinej
      have hxyj : x j ≠ y j := by
        intro hxyj
        exact hj (by simpa [sub_eq_zero] using hxyj.symm)
      exact (AffineMap.lineMap_eq_left_iff.mp hcoord).resolve_left hxyj
    by_cases ha0 : a = 0
    · left
      simp [ha0]
    · have hb0 : b = 0 := by
        by_contra hb0
        have ha_pos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
        have hparam_pos : 0 < AffineMap.lineMap a b t := by
          by_cases ht0 : t = 0
          · simp [AffineMap.lineMap_apply_module, ht0, ha_pos]
          · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
            have hline_ge : t * b ≤ AffineMap.lineMap a b t := by
              simp [AffineMap.lineMap_apply_module]
              nlinarith [ha.1, ht.2]
            have htb_pos : 0 < t * b := by positivity
            exact lt_of_lt_of_le htb_pos hline_ge
        exact (ne_of_gt hparam_pos) hparam
      right
      simp [hb0]

/-- Helper for Exercise 4.27: the right endpoint of a nondegenerate segment in `Fin n → ℝ` is an
extreme point of that segment. -/
private lemma right_mem_extremePoints_segment_fin
    {n : ℕ} {x y : Fin n → ℝ} (hxy : x ≠ y) :
    y ∈ (segment ℝ x y).extremePoints ℝ := by
  simpa [segment_symm] using left_mem_extremePoints_segment_fin hxy.symm

/-- Helper for Exercise 4.27: the cardinality distance between two matchings is exactly the
distance between their exclusive edge parts, because the common edges contribute equally to both
cardinalities. -/
private lemma matchingCardinalityDist_eq_dist_symmDiffParts [Finite V]
    {M N : G.Subgraph} :
    Nat.dist M.edgeSet.ncard N.edgeSet.ncard =
      Nat.dist (M.edgeSet \ N.edgeSet).ncard (N.edgeSet \ M.edgeSet).ncard := by
  have hM :
      M.edgeSet.ncard =
        (M.edgeSet \ N.edgeSet).ncard + (M.edgeSet ∩ N.edgeSet).ncard := by
    -- Split the left matching into its exclusive part and its common part with `N`.
    simpa [add_comm] using
      (Set.ncard_inter_add_ncard_diff_eq_ncard M.edgeSet N.edgeSet).symm
  have hN :
      N.edgeSet.ncard =
        (N.edgeSet \ M.edgeSet).ncard + (M.edgeSet ∩ N.edgeSet).ncard := by
    -- The same decomposition holds for `N`, with the same common intersection term.
    simpa [Set.inter_comm, add_comm] using
      (Set.ncard_inter_add_ncard_diff_eq_ncard N.edgeSet M.edgeSet).symm
  -- Cancel the shared intersection cardinality from both sides of the natural-number distance.
  rw [hM, hN]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    Nat.dist_add_add_right
      (M.edgeSet \ N.edgeSet).ncard
      (M.edgeSet ∩ N.edgeSet).ncard
      (N.edgeSet \ M.edgeSet).ncard

/-- Helper for Exercise 4.27: the `M`-edges supported on a walk `p`, viewed back inside the
ambient graph `G`. -/
private def walkMatchingPiece [Finite V] {H : SimpleGraph V} (M : G.Subgraph) {u v : V}
    (p : H.Walk u v) : G.Subgraph :=
  swapEdgeSubgraph G ⊥ M p.edgeSet

/-- Helper for Exercise 4.27: the walk-supported piece of `M` has exactly the ambient edges of
`M` that lie on the walk. -/
private lemma walkMatchingPiece_edgeSet [Finite V]
    {H : SimpleGraph V} {M : G.Subgraph} {u v : V} {p : H.Walk u v} :
    (walkMatchingPiece G M p).edgeSet = M.edgeSet ∩ p.edgeSet := by
  ext e
  constructor
  · intro he
    let eG : G.edgeSet := ⟨e, (walkMatchingPiece G M p).edgeSet_subset he⟩
    have he' : (eG : Sym2 V) ∈ (walkMatchingPiece G M p).edgeSet := by
      simpa [eG] using he
    have hswap :=
      (swapEdgeSubgraph_edgeSet_iff (G := G) (A := ⊥) (B := M) (S := p.edgeSet) (e := eG)).1 he'
    rcases hswap with hbot | hM
    · exfalso
      simpa using hbot.1
    · exact ⟨by simpa [eG] using hM.1, by simpa [eG] using hM.2⟩
  · rintro ⟨heM, hep⟩
    let eG : G.edgeSet := ⟨e, M.edgeSet_subset heM⟩
    have hswap :
        ((eG : Sym2 V) ∈ (⊥ : G.Subgraph).edgeSet \ p.edgeSet ∪ M.edgeSet ∩ p.edgeSet) := by
      exact Or.inr ⟨by simpa [eG] using heM, by simpa [eG] using hep⟩
    exact (swapEdgeSubgraph_edgeSet_iff (G := G) (A := ⊥) (B := M) (S := p.edgeSet) (e := eG)).2 hswap

/-- Helper for Exercise 4.27: adjacency in the walk-supported piece means adjacency in `M`
and on the walk support simultaneously. -/
private lemma walkMatchingPiece_adj_iff [Finite V]
    {H : SimpleGraph V} {M : G.Subgraph} {u v x y : V} {p : H.Walk u v} :
    (walkMatchingPiece G M p).Adj x y ↔ M.Adj x y ∧ p.toSubgraph.Adj x y := by
  constructor
  · intro hxy
    have he : s(x, y) ∈ (walkMatchingPiece G M p).edgeSet := by
      simpa [SimpleGraph.Subgraph.mem_edgeSet] using hxy
    rw [walkMatchingPiece_edgeSet] at he
    refine ⟨?_, ?_⟩
    · simpa [SimpleGraph.Subgraph.mem_edgeSet] using he.1
    · exact (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).2 he.2
  · rintro ⟨hMxy, hpxy⟩
    have he : s(x, y) ∈ (walkMatchingPiece G M p).edgeSet := by
      rw [walkMatchingPiece_edgeSet]
      refine ⟨?_, ?_⟩
      · simpa [SimpleGraph.Subgraph.mem_edgeSet] using hMxy
      · exact (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).1 hpxy
    simpa [SimpleGraph.Subgraph.mem_edgeSet] using he

/-- Helper for Exercise 4.27: restricting a matching to the edges of a walk leaves a matching. -/
private lemma walkMatchingPiece_isMatching [Finite V]
    {H : SimpleGraph V} {M : G.Subgraph} {u v : V} {p : H.Walk u v}
    (hM : M.IsMatching) :
    (walkMatchingPiece G M p).IsMatching := by
  intro x hx
  rcases (by simpa [walkMatchingPiece, swapEdgeSubgraph] using hx :
      ∃ y, (walkMatchingPiece G M p).Adj x y) with ⟨y, hxy⟩
  have hxM : x ∈ M.verts := M.edge_vert ((walkMatchingPiece_adj_iff G).mp hxy).1
  obtain ⟨yM, hyM, hyuniq⟩ := hM (v := x) hxM
  have hxyM : M.Adj x y := ((walkMatchingPiece_adj_iff G).mp hxy).1
  -- The walk-supported piece cannot create a second incident edge beyond the one already unique in
  -- the ambient matching `M`.
  refine ⟨y, hxy, ?_⟩
  intro z hxz
  have hyEq : y = yM := hyuniq y hxyM
  have hzEq : z = yM := hyuniq z ((walkMatchingPiece_adj_iff G).mp hxz).1
  exact hzEq.trans hyEq.symm

/-- Helper for Exercise 4.27: a matching covers exactly twice as many vertices as it has edges. -/
private lemma matchingVertsNcard_eq_twoMulEdgeSetNcard [Fintype V] {K : G.Subgraph}
    (hK : K.IsMatching) :
    K.verts.ncard = 2 * K.edgeSet.ncard := by
  classical
  have hdeg : ∀ x : V, K.spanningCoe.degree x = if x ∈ K.verts then 1 else 0 := by
    intro x
    by_cases hx : x ∈ K.verts
    · have hdegK : K.degree x = 1 :=
        (SimpleGraph.Subgraph.isMatching_iff_forall_degree (M := K)).mp hK x hx
      simp [hx, SimpleGraph.Subgraph.degree_spanningCoe, hdegK]
    · have hdegK : K.degree x = 0 := K.degree_of_notMem_verts hx
      simp [hx, SimpleGraph.Subgraph.degree_spanningCoe, hdegK]
  have hsum : Fintype.card K.verts = 2 * Fintype.card K.spanningCoe.edgeSet := by
    -- On a matching, covered vertices contribute degree `1` and uncovered vertices contribute `0`.
    calc
      Fintype.card K.verts = ∑ x : V, K.spanningCoe.degree x := by
        rw [Fintype.card_subtype, Finset.card_eq_sum_ones]
        simp [hdeg]
      _ = 2 * K.spanningCoe.edgeFinset.card := K.spanningCoe.sum_degrees_eq_twice_card_edges
      _ = 2 * Fintype.card K.spanningCoe.edgeSet := by
        simpa using congrArg (fun n : ℕ ↦ 2 * n) K.spanningCoe.edgeFinset_card
  have hsum' : Nat.card K.verts = 2 * Nat.card K.spanningCoe.edgeSet := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact hsum
  -- Convert the finite-cardinality identity back to `Set.ncard`.
  calc
    K.verts.ncard = Nat.card K.verts := by rw [Nat.card_coe_set_eq]
    _ = 2 * Nat.card K.spanningCoe.edgeSet := hsum'
    _ = 2 * K.spanningCoe.edgeSet.ncard := by rw [Nat.card_coe_set_eq]
    _ = 2 * K.edgeSet.ncard := by rw [SimpleGraph.Subgraph.edgeSet_spanningCoe]

/-- Helper for Exercise 4.27: a path vertex distinct from both endpoints occurs at an internal
index. -/
private lemma existsInternalIndex_of_mem_support_ne_endpoints
    {H : SimpleGraph V} {u v x : V} {p : H.Walk u v} (_hp : p.IsPath)
    (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    ∃ i, 0 < i ∧ i < p.length ∧ x = p.getVert i := by
  obtain ⟨i, hxi, hi_le⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  have hi0 : 0 < i := by
    have hi_ne_zero : i ≠ 0 := by
      intro hi_zero
      apply hxu
      calc
        x = p.getVert i := hxi.symm
        _ = p.getVert 0 := by simp [hi_zero]
        _ = u := p.getVert_zero
    exact Nat.pos_iff_ne_zero.mpr hi_ne_zero
  have hil : i < p.length := by
    have hi_ne_length : i ≠ p.length := by
      intro hi_length
      apply hxv
      calc
        x = p.getVert i := hxi.symm
        _ = p.getVert p.length := by simp [hi_length]
        _ = v := p.getVert_length
    exact lt_of_le_of_ne hi_le hi_ne_length
  exact ⟨i, hi0, hil, hxi.symm⟩

/-- Helper for Exercise 4.27: on a cycle witness, every support vertex is covered by both
walk-supported matching pieces. -/
private lemma cycleVertex_mem_walkMatchingPieces
    [Finite V] {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching)
    {v : V} {p : (M.spanningCoe ∆ N.spanningCoe).Walk v v}
    (hp : p.IsCycle) {x : V} (hx : x ∈ p.toSubgraph.verts) :
    x ∈ (walkMatchingPiece G M p).verts ∧ x ∈ (walkMatchingPiece G N p).verts := by
  classical
  have hAlt := matchingSymmDiff_isAlternating G hM hN
  have hxSupport : x ∈ p.support := p.mem_verts_toSubgraph.mp hx
  obtain ⟨w, w', hww, hneigh⟩ := Set.ncard_eq_two.mp (hp.ncard_neighborSet_toSubgraph_eq_two hxSupport)
  have hwMem : w ∈ p.toSubgraph.neighborSet x := by simpa [hneigh]
  have hw'Mem : w' ∈ p.toSubgraph.neighborSet x := by simpa [hneigh]
  have hw : p.toSubgraph.Adj x w := (p.toSubgraph.mem_neighborSet _ _).1 hwMem
  have hw' : p.toSubgraph.Adj x w' := (p.toSubgraph.mem_neighborSet _ _).1 hw'Mem
  have hDiffw : (M.spanningCoe ∆ N.spanningCoe).Adj x w := hw.adj_sub
  have hDiffw' : (M.spanningCoe ∆ N.spanningCoe).Adj x w' := hw'.adj_sub
  have hAltForward : M.Adj x w ↔ ¬ M.Adj x w' := by
    simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hAlt hww hDiffw hDiffw'
  have hAltBackward : M.Adj x w' ↔ ¬ M.Adj x w := by
    simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hAlt hww.symm hDiffw' hDiffw
  have hxorw : (M.Adj x w ∧ ¬ N.Adj x w) ∨ (N.Adj x w ∧ ¬ M.Adj x w) := by
    simpa [symmDiff_def, SimpleGraph.Subgraph.spanningCoe_adj] using hDiffw
  have hxorw' : (M.Adj x w' ∧ ¬ N.Adj x w') ∨ (N.Adj x w' ∧ ¬ M.Adj x w') := by
    simpa [symmDiff_def, SimpleGraph.Subgraph.spanningCoe_adj] using hDiffw'
  constructor
  · -- Alternation forces exactly one of the two cycle edges at `x` into `M`.
    rcases hxorw with hMw | hNw
    · exact (walkMatchingPiece G M p).edge_vert ((walkMatchingPiece_adj_iff G).2 ⟨hMw.1, hw⟩)
    · have hMw' : M.Adj x w' := hAltBackward.mpr hNw.2
      exact (walkMatchingPiece G M p).edge_vert ((walkMatchingPiece_adj_iff G).2 ⟨hMw', hw'⟩)
  · -- The other cycle edge must then belong to `N`.
    rcases hxorw with hMw | hNw
    · have hNotMw' : ¬ M.Adj x w' := hAltForward.mp hMw.1
      rcases hxorw' with hMw' | hNw'
      · exact False.elim (hNotMw' hMw'.1)
      · exact (walkMatchingPiece G N p).edge_vert ((walkMatchingPiece_adj_iff G).2 ⟨hNw'.1, hw'⟩)
    · exact (walkMatchingPiece G N p).edge_vert ((walkMatchingPiece_adj_iff G).2 ⟨hNw.1, hw⟩)

/-- Helper for Exercise 4.27: an internal vertex of a path witness is covered by both
walk-supported matching pieces. -/
private lemma internalVertex_mem_walkMatchingPieces
    [Finite V] {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching)
    {u v : V} {p : (M.spanningCoe ∆ N.spanningCoe).Walk u v}
    (hp : p.IsPath) {x : V} (hx : x ∈ p.toSubgraph.verts)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    x ∈ (walkMatchingPiece G M p).verts ∧ x ∈ (walkMatchingPiece G N p).verts := by
  classical
  have hAlt := matchingSymmDiff_isAlternating G hM hN
  have hxSupport : x ∈ p.support := p.mem_verts_toSubgraph.mp hx
  obtain ⟨i, hi0, hil, hxi⟩ :=
    existsInternalIndex_of_mem_support_ne_endpoints hp hxSupport hxu hxv
  have hprevMem : p.getVert (i - 1) ∈ p.toSubgraph.neighborSet x := by
    rw [hxi, hp.neighborSet_toSubgraph_internal (by omega) hil]
    simp
  have hnextMem : p.getVert (i + 1) ∈ p.toSubgraph.neighborSet x := by
    rw [hxi, hp.neighborSet_toSubgraph_internal (by omega) hil]
    simp
  have hprev : p.toSubgraph.Adj x (p.getVert (i - 1)) := (p.toSubgraph.mem_neighborSet _ _).1 hprevMem
  have hnext : p.toSubgraph.Adj x (p.getVert (i + 1)) := (p.toSubgraph.mem_neighborSet _ _).1 hnextMem
  have hprev_ne_next : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro hEq
    have := hp.getVert_injOn (by simp; omega) (by simp; omega) hEq
    omega
  have hDiffPrev : (M.spanningCoe ∆ N.spanningCoe).Adj x (p.getVert (i - 1)) := hprev.adj_sub
  have hDiffNext : (M.spanningCoe ∆ N.spanningCoe).Adj x (p.getVert (i + 1)) := hnext.adj_sub
  have hAltForward : M.Adj x (p.getVert (i - 1)) ↔ ¬ M.Adj x (p.getVert (i + 1)) := by
    simpa [SimpleGraph.Subgraph.spanningCoe_adj, hxi] using hAlt hprev_ne_next hDiffPrev hDiffNext
  have hAltBackward : M.Adj x (p.getVert (i + 1)) ↔ ¬ M.Adj x (p.getVert (i - 1)) := by
    simpa [SimpleGraph.Subgraph.spanningCoe_adj, hxi] using hAlt hprev_ne_next.symm hDiffNext hDiffPrev
  have hxorPrev :
      (M.Adj x (p.getVert (i - 1)) ∧ ¬ N.Adj x (p.getVert (i - 1))) ∨
        (N.Adj x (p.getVert (i - 1)) ∧ ¬ M.Adj x (p.getVert (i - 1))) := by
    simpa [symmDiff_def, SimpleGraph.Subgraph.spanningCoe_adj] using hDiffPrev
  have hxorNext :
      (M.Adj x (p.getVert (i + 1)) ∧ ¬ N.Adj x (p.getVert (i + 1))) ∨
        (N.Adj x (p.getVert (i + 1)) ∧ ¬ M.Adj x (p.getVert (i + 1))) := by
    simpa [symmDiff_def, SimpleGraph.Subgraph.spanningCoe_adj] using hDiffNext
  constructor
  · -- One of the two path edges at an internal vertex must be the `M`-edge.
    rcases hxorPrev with hMprev | hNprev
    · exact (walkMatchingPiece G M p).edge_vert
        ((walkMatchingPiece_adj_iff G).2 ⟨hMprev.1, hprev⟩)
    · have hMnext : M.Adj x (p.getVert (i + 1)) := hAltBackward.mpr hNprev.2
      exact (walkMatchingPiece G M p).edge_vert
        ((walkMatchingPiece_adj_iff G).2 ⟨hMnext, hnext⟩)
  · -- The alternating partner edge is then the `N`-edge.
    rcases hxorPrev with hMprev | hNprev
    · have hNotMnext : ¬ M.Adj x (p.getVert (i + 1)) := hAltForward.mp hMprev.1
      rcases hxorNext with hMnext | hNnext
      · exact False.elim (hNotMnext hMnext.1)
      · exact (walkMatchingPiece G N p).edge_vert
          ((walkMatchingPiece_adj_iff G).2 ⟨hNnext.1, hnext⟩)
    · exact (walkMatchingPiece G N p).edge_vert
        ((walkMatchingPiece_adj_iff G).2 ⟨hNprev.1, hprev⟩)

/-- Helper for Exercise 4.27: the cardinality distance between two finite sets depends only on
their exclusive parts. -/
private lemma ncardDist_eq_dist_diffParts [Fintype V] {A B : Set V} :
    Nat.dist A.ncard B.ncard = Nat.dist (A \ B).ncard (B \ A).ncard := by
  have hA :
      A.ncard = (A \ B).ncard + (A ∩ B).ncard := by
    simpa [add_comm] using (Set.ncard_inter_add_ncard_diff_eq_ncard A B).symm
  have hB :
      B.ncard = (B \ A).ncard + (A ∩ B).ncard := by
    simpa [Set.inter_comm, add_comm] using
      (Set.ncard_inter_add_ncard_diff_eq_ncard B A).symm
  -- The shared intersection contributes equally to both cardinalities.
  rw [hA, hB]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    Nat.dist_add_add_right (A \ B).ncard (A ∩ B).ncard (B \ A).ncard

/-- Helper for Exercise 4.27: on a cycle witness, the two walk-supported matching pieces have the
same number of edges. -/
private lemma cycleWitness_interEdgeDist_eq_zero
    [Fintype V]
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching)
    {v : V} {p : (M.spanningCoe ∆ N.spanningCoe).Walk v v}
    (hp : p.IsCycle) :
    Nat.dist (M.edgeSet ∩ p.edgeSet).ncard (N.edgeSet ∩ p.edgeSet).ncard = 0 := by
  classical
  let KM : G.Subgraph := walkMatchingPiece G M p
  let KN : G.Subgraph := walkMatchingPiece G N p
  have hKM : KM.IsMatching := by simpa [KM] using walkMatchingPiece_isMatching G hM
  have hKN : KN.IsMatching := by simpa [KN] using walkMatchingPiece_isMatching G hN
  have hKMVerts : KM.verts = p.toSubgraph.verts := by
    ext x
    constructor
    · intro hx
      have hx' : ∃ y, KM.Adj x y := by
        simpa [KM, walkMatchingPiece, swapEdgeSubgraph] using hx
      rcases hx' with ⟨y, hxy⟩
      have hxy' : M.Adj x y ∧ p.toSubgraph.Adj x y := by
        simpa [KM] using (walkMatchingPiece_adj_iff (G := G) (M := M) (p := p)).mp hxy
      exact p.toSubgraph.edge_vert hxy'.2
    · intro hx
      simpa [KM] using (cycleVertex_mem_walkMatchingPieces G hM hN hp hx).1
  have hKNVerts : KN.verts = p.toSubgraph.verts := by
    ext x
    constructor
    · intro hx
      have hx' : ∃ y, KN.Adj x y := by
        simpa [KN, walkMatchingPiece, swapEdgeSubgraph] using hx
      rcases hx' with ⟨y, hxy⟩
      have hxy' : N.Adj x y ∧ p.toSubgraph.Adj x y := by
        simpa [KN] using (walkMatchingPiece_adj_iff (G := G) (M := N) (p := p)).mp hxy
      exact p.toSubgraph.edge_vert hxy'.2
    · intro hx
      simpa [KN] using (cycleVertex_mem_walkMatchingPieces G hM hN hp hx).2
  have hKMCount : KM.verts.ncard = 2 * KM.edgeSet.ncard := matchingVertsNcard_eq_twoMulEdgeSetNcard G hKM
  have hKNCount : KN.verts.ncard = 2 * KN.edgeSet.ncard := matchingVertsNcard_eq_twoMulEdgeSetNcard G hKN
  have hVertsEq : KM.verts.ncard = KN.verts.ncard := by
    rw [hKMVerts, hKNVerts]
  have hDoubleEq : 2 * KM.edgeSet.ncard = 2 * KN.edgeSet.ncard := by
    simpa [hKMCount, hKNCount] using hVertsEq
  have hEdgeEq : KM.edgeSet.ncard = KN.edgeSet.ncard := by
    omega
  -- Equal covered-vertex counts force equal edge counts for the two restricted matchings.
  simpa [KM, KN, walkMatchingPiece_edgeSet, hEdgeEq] using Nat.dist_eq_zero hEdgeEq

/-- Helper for Exercise 4.27: on a path witness, the two walk-supported matching pieces have edge
counts whose distance is at most `1`. -/
private lemma pathWitness_interEdgeDist_le_one
    [Fintype V]
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching)
    {u v : V} (huv : u ≠ v)
    {p : (M.spanningCoe ∆ N.spanningCoe).Walk u v}
    (hp : p.IsPath) :
    Nat.dist (M.edgeSet ∩ p.edgeSet).ncard (N.edgeSet ∩ p.edgeSet).ncard ≤ 1 := by
  classical
  let KM : G.Subgraph := walkMatchingPiece G M p
  let KN : G.Subgraph := walkMatchingPiece G N p
  have hKM : KM.IsMatching := by simpa [KM] using walkMatchingPiece_isMatching G hM
  have hKN : KN.IsMatching := by simpa [KN] using walkMatchingPiece_isMatching G hN
  have hKMdiffSub : KM.verts \ KN.verts ⊆ ({u, v} : Set V) := by
    intro x hx
    have hxPath : x ∈ p.toSubgraph.verts := by
      have hxKM : x ∈ KM.verts := hx.1
      have hxKM' : ∃ y, KM.Adj x y := by
        simpa [KM, walkMatchingPiece, swapEdgeSubgraph] using hxKM
      rcases hxKM' with ⟨y, hxy⟩
      have hxy' : M.Adj x y ∧ p.toSubgraph.Adj x y := by
        simpa [KM] using (walkMatchingPiece_adj_iff (G := G) (M := M) (p := p)).mp hxy
      exact p.toSubgraph.edge_vert hxy'.2
    by_cases hxu : x = u
    · simpa [hxu]
    · by_cases hxv : x = v
      · simpa [hxv]
      · exact False.elim (hx.2 (internalVertex_mem_walkMatchingPieces G hM hN hp hxPath hxu hxv).2)
  have hKNdiffSub : KN.verts \ KM.verts ⊆ ({u, v} : Set V) := by
    intro x hx
    have hxPath : x ∈ p.toSubgraph.verts := by
      have hxKN : x ∈ KN.verts := hx.1
      have hxKN' : ∃ y, KN.Adj x y := by
        simpa [KN, walkMatchingPiece, swapEdgeSubgraph] using hxKN
      rcases hxKN' with ⟨y, hxy⟩
      have hxy' : N.Adj x y ∧ p.toSubgraph.Adj x y := by
        simpa [KN] using (walkMatchingPiece_adj_iff (G := G) (M := N) (p := p)).mp hxy
      exact p.toSubgraph.edge_vert hxy'.2
    by_cases hxu : x = u
    · simpa [hxu]
    · by_cases hxv : x = v
      · simpa [hxv]
      · exact False.elim (hx.2 (internalVertex_mem_walkMatchingPieces G hM hN hp hxPath hxu hxv).1)
  have hKMdiffLeTwo : (KM.verts \ KN.verts).ncard ≤ 2 := by
    exact le_trans (Set.ncard_mono hKMdiffSub) (by simpa using (Set.ncard_pair huv).le)
  have hKNdiffLeTwo : (KN.verts \ KM.verts).ncard ≤ 2 := by
    exact le_trans (Set.ncard_mono hKNdiffSub)
      (by simpa [Set.pair_comm] using (Set.ncard_pair huv).le)
  have hVertsDistLeTwo : Nat.dist KM.verts.ncard KN.verts.ncard ≤ 2 := by
    rw [ncardDist_eq_dist_diffParts]
    unfold Nat.dist
    omega
  have hKMCount : KM.verts.ncard = 2 * KM.edgeSet.ncard := matchingVertsNcard_eq_twoMulEdgeSetNcard G hKM
  have hKNCount : KN.verts.ncard = 2 * KN.edgeSet.ncard := matchingVertsNcard_eq_twoMulEdgeSetNcard G hKN
  have hDoubleDist : Nat.dist (2 * KM.edgeSet.ncard) (2 * KN.edgeSet.ncard) ≤ 2 := by
    simpa [hKMCount, hKNCount] using hVertsDistLeTwo
  have hEdgeDist : Nat.dist KM.edgeSet.ncard KN.edgeSet.ncard ≤ 1 := by
    -- Dividing the covered-vertex bound by `2` gives the desired edge-count bound.
    unfold Nat.dist at hDoubleDist ⊢
    omega
  simpa [KM, KN, walkMatchingPiece_edgeSet] using hEdgeDist

/-- Helper for Exercise 4.27: under a spanning walk witness of the symmetric difference, the
exclusive ambient edge sets are exactly the matching edge sets restricted to the walk support. -/
private lemma exclusiveEdgeSet_eq_inter_walkEdgeSet
    {M N : G.Subgraph} {u v : V}
    {p : (M.spanningCoe ∆ N.spanningCoe).Walk u v}
    (hspan : p.toSubgraph.spanningCoe = M.spanningCoe ∆ N.spanningCoe) :
    (M.edgeSet \ N.edgeSet) = M.edgeSet ∩ p.edgeSet ∧
      (N.edgeSet \ M.edgeSet) = N.edgeSet ∩ p.edgeSet := by
  constructor <;> ext e <;> constructor
  · intro he
    refine ⟨he.1, ?_⟩
    have heSymm : e ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
      -- Exclusive `M`-edges are, by definition, edges of the symmetric difference.
      simpa [symmDiff_def, SimpleGraph.Subgraph.edgeSet_spanningCoe, he.1, he.2]
    have heSpan : e ∈ p.toSubgraph.spanningCoe.edgeSet := by
      simpa [hspan] using heSymm
    have heSub : e ∈ p.toSubgraph.edgeSet := by
      simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using heSpan
    simpa [SimpleGraph.Walk.edgeSet_toSubgraph] using heSub
  · intro he
    refine ⟨he.1, ?_⟩
    intro heN
    have heSub : e ∈ p.toSubgraph.edgeSet := by
      simpa [SimpleGraph.Walk.edgeSet_toSubgraph] using he.2
    have heSpan : e ∈ p.toSubgraph.spanningCoe.edgeSet := by
      simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using heSub
    have heSymm : e ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
      simpa [hspan] using heSpan
    -- An edge on the witness walk cannot belong to both matchings, because the walk spans the
    -- symmetric difference itself.
    simpa [symmDiff_def, SimpleGraph.Subgraph.edgeSet_spanningCoe, he.1, heN] using heSymm
  · intro he
    refine ⟨he.1, ?_⟩
    have heSymm : e ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
      -- The same normalization applies with the roles of `M` and `N` reversed.
      simpa [symmDiff_def, SimpleGraph.Subgraph.edgeSet_spanningCoe, he.2, he.1]
    have heSpan : e ∈ p.toSubgraph.spanningCoe.edgeSet := by
      simpa [hspan] using heSymm
    have heSub : e ∈ p.toSubgraph.edgeSet := by
      simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using heSpan
    simpa [SimpleGraph.Walk.edgeSet_toSubgraph] using heSub
  · intro he
    refine ⟨he.1, ?_⟩
    intro heM
    have heSub : e ∈ p.toSubgraph.edgeSet := by
      simpa [SimpleGraph.Walk.edgeSet_toSubgraph] using he.2
    have heSpan : e ∈ p.toSubgraph.spanningCoe.edgeSet := by
      simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using heSub
    have heSymm : e ∈ (M.spanningCoe ∆ N.spanningCoe).edgeSet := by
      simpa [hspan] using heSpan
    -- Symmetric-difference edges are exclusive, so a witness edge already chosen by `N` cannot
    -- simultaneously belong to `M`.
    simpa [symmDiff_def, SimpleGraph.Subgraph.edgeSet_spanningCoe, heM, he.1] using heSymm

/-- Helper for Exercise 4.27: a single path/cycle witness for the symmetric difference forces the
exclusive edge counts of the two matchings to differ by at most one. -/
private lemma matchingExclusiveEdgeDist_le_one_of_symmDiff_isCycleOrPath
    [Fintype V]
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching)
    (hH : (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath) :
    Nat.dist (M.edgeSet \ N.edgeSet).ncard (N.edgeSet \ M.edgeSet).ncard ≤ 1 := by
  -- Route correction: keep the ambient normalization fixed and move the counting entirely onto the
  -- witness support. The cycle branch gives equal restricted edge counts, and the path branch
  -- bounds the restricted edge-count distance through the two endpoint exceptions.
  rcases hH with ⟨v, p, hpCycle, hpSpan⟩ | ⟨u, v, huv, p, hpPath, hpSpan⟩
  · obtain ⟨hMpart, hNpart⟩ := exclusiveEdgeSet_eq_inter_walkEdgeSet G hpSpan
    rw [hMpart, hNpart]
    have hdist : Nat.dist (M.edgeSet ∩ p.edgeSet).ncard (N.edgeSet ∩ p.edgeSet).ncard = 0 :=
      cycleWitness_interEdgeDist_eq_zero G hM hN hpCycle
    omega
  · obtain ⟨hMpart, hNpart⟩ := exclusiveEdgeSet_eq_inter_walkEdgeSet G hpSpan
    rw [hMpart, hNpart]
    exact pathWitness_interEdgeDist_le_one G hM hN huv hpPath

/-- Helper for Exercise 4.27: after the canonical finite reindexing of `G.edgeSet`, the image of
`G.matchingPolytope` is a polyhedron in `Fin (Nat.card G.edgeSet) → ℝ`. -/
private lemma matchingPolytope_reindexed_eq_polyhedron [Fintype V] :
    let e : G.edgeSet ≃ Fin (Nat.card G.edgeSet) := Finite.equivFin G.edgeSet
    let L : (G.edgeSet → ℝ) ≃ₗ[ℝ] (Fin (Nat.card G.edgeSet) → ℝ) :=
      (LinearEquiv.funCongrLeft ℝ ℝ e).symm
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin (Nat.card G.edgeSet)) ℝ, ∃ b : Fin m → ℝ,
      L '' G.matchingPolytope = polyhedron_le_set A b := by
  classical
  let e : G.edgeSet ≃ Fin (Nat.card G.edgeSet) := Finite.equivFin G.edgeSet
  let L : (G.edgeSet → ℝ) ≃ₗ[ℝ] (Fin (Nat.card G.edgeSet) → ℝ) :=
    (LinearEquiv.funCongrLeft ℝ ℝ e).symm
  let matchingGenerators : Set (Fin (Nat.card G.edgeSet) → ℝ) :=
    Set.range fun M : {M : G.Subgraph // M.IsMatching} ↦ L (G.subgraphIncidenceVector ℝ M.1)
  have hgenerators :
      L '' {x : G.edgeSet → ℝ | ∃ M : G.Subgraph, M.IsMatching ∧
        x = G.subgraphIncidenceVector ℝ M} = matchingGenerators := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨M, hM, rfl⟩
      exact ⟨⟨M, hM⟩, rfl⟩
    · rintro ⟨M, rfl⟩
      exact ⟨_, ⟨M.1, M.2, rfl⟩, rfl⟩
  have himage_matchingPolytope :
      L '' G.matchingPolytope = convexHull ℝ matchingGenerators := by
    -- The reindexing equivalence preserves the finite matching-generator hull.
    rw [SimpleGraph.matchingPolytope]
    calc
      L '' convexHull ℝ {x : G.edgeSet → ℝ | ∃ M : G.Subgraph, M.IsMatching ∧
          x = G.subgraphIncidenceVector ℝ M} =
          convexHull ℝ (L ''
            {x : G.edgeSet → ℝ | ∃ M : G.Subgraph, M.IsMatching ∧
              x = G.subgraphIncidenceVector ℝ M}) := by
              simpa using
                L.toLinearMap.image_convexHull
                  ({x : G.edgeSet → ℝ | ∃ M : G.Subgraph, M.IsMatching ∧
                    x = G.subgraphIncidenceVector ℝ M} : Set (G.edgeSet → ℝ))
      _ = convexHull ℝ matchingGenerators := by rw [hgenerators]
  have hpolytope : (L '' G.matchingPolytope).IsPolytope ℝ := by
    refine ⟨matchingGenerators, ?_, himage_matchingPolytope⟩
    simpa [matchingGenerators] using
      (Set.finite_range
        (fun M : {M : G.Subgraph // M.IsMatching} ↦
          L (G.subgraphIncidenceVector ℝ M.1)))
  have hpolyhedron : is_polyhedron (L '' G.matchingPolytope) :=
    (polytope_iff_bounded_polyhedron (L '' G.matchingPolytope)).1 hpolytope |>.1
  rcases is_polyhedron_iff.mp hpolyhedron with ⟨m, A, b, hEq⟩
  exact ⟨m, A, b, hEq⟩

private lemma existsMatchingEdgeThrough_nonambientSliceExtreme
    [Fintype V] {x : G.edgeSet → ℝ} {k : ℕ}
    (hx : x ∈
      (G.matchingPolytope ∩ {y : G.edgeSet → ℝ | ∑ e, y e = (k : ℝ)}).extremePoints ℝ)
    (hxNotAmbient : x ∉ (G.matchingPolytope).extremePoints ℝ) :
    ∃ M N : G.Subgraph,
      M.IsMatching ∧
      N.IsMatching ∧
      IsEdgeOf G.matchingPolytope
        (segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) ∧
      x ∈ openSegment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) ∧
      Nat.dist M.edgeSet.ncard N.edgeSet.ncard ≤ 1 := by
  classical
  let e : G.edgeSet ≃ Fin (Nat.card G.edgeSet) := Finite.equivFin G.edgeSet
  let L : (G.edgeSet → ℝ) ≃ₗ[ℝ] (Fin (Nat.card G.edgeSet) → ℝ) :=
    (LinearEquiv.funCongrLeft ℝ ℝ e).symm
  obtain ⟨m, A, b, hpolyhedron⟩ := matchingPolytope_reindexed_eq_polyhedron (G := G)
  let xbar : Fin (Nat.card G.edgeSet) → ℝ := L x
  let I : Set (Fin m) := {i | A.mulVec xbar i = b i}
  let F : Set (Fin (Nat.card G.edgeSet) → ℝ) := active_constraint_face A b I
  have hxSlice :
      x ∈ G.matchingPolytope ∩ {y : G.edgeSet → ℝ | ∑ e, y e = (k : ℝ)} :=
    (mem_extremePoints_iff_left.mp hx).1
  have hxPoly : x ∈ G.matchingPolytope := hxSlice.1
  have hxbarPoly : xbar ∈ polyhedron_le_set A b := by
    -- The reindexed image of `G.matchingPolytope` is exactly the ambient polyhedron `A * x ≤ b`.
    rw [← hpolyhedron]
    exact ⟨x, hxPoly, rfl⟩
  have hxbarFace : xbar ∈ F := by
    -- By construction, `F` is cut out by the rows active at `xbar`.
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      simpa [I, xbar] using hi
    · intro i hi
      simpa [I, xbar] using hxbarPoly i
  have hxbarNotAmbient :
      xbar ∉ (polyhedron_le_set A b).extremePoints ℝ := by
    intro hxbarExtreme
    have hxbarImage :
        xbar ∈ (L '' G.matchingPolytope).extremePoints ℝ := by
      rw [hpolyhedron]
      exact hxbarExtreme
    rw [← image_extremePoints] at hxbarImage
    rcases hxbarImage with ⟨y, hy, hyEq⟩
    have hyx : y = x := L.injective (by simpa [xbar] using hyEq)
    exact hxNotAmbient (hyx ▸ hy)
  have hxbarNotFaceExtreme :
      xbar ∉ F.extremePoints ℝ := by
    -- Route correction: the first geometric obstruction is now localized to the tight-row face.
    simpa [F, I, xbar] using
      not_mem_extremePoints_tightRowFace_of_not_mem_extremePoints
        (A := A) (b := b) (xbar := xbar) hxbarNotAmbient
  have hF_exposed : IsExposed ℝ (polyhedron_le_set A b) F := by
    -- The active-row face is exposed in the reindexed matching polytope.
    simpa [F, I] using active_constraint_face_isExposed A b I
  have hF_nonempty : F.Nonempty := ⟨xbar, hxbarFace⟩
  have hF_convex : Convex ℝ F := by
    -- Exposed faces inherit convexity from the ambient polyhedron.
    exact hF_exposed.convex (polyhedron_le_set_convex A b)
  have hL_apply (y : G.edgeSet → ℝ) (j : Fin (Nat.card G.edgeSet)) :
      L y j = y (e.symm j) := by
    -- This is the inverse evaluation formula for the canonical coordinate reindexing.
    change (LinearEquiv.funCongrLeft ℝ ℝ e).symm y j = y (e.symm j)
    rw [LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  have hsumRow_apply (y : G.edgeSet → ℝ) :
      dotProduct cardinalitySliceSumRow (L y) = ∑ e' : G.edgeSet, y e' := by
    -- Reindex the all-ones `Fin`-sum back to the original `G.edgeSet` coordinate sum exactly
    -- once, so the rest of the proof stays in the `Fin` normal form.
    change ∑ j : Fin (Nat.card G.edgeSet), cardinalitySliceSumRow j * L y j = ∑ e' : G.edgeSet, y e'
    rw [show (fun j : Fin (Nat.card G.edgeSet) ↦ cardinalitySliceSumRow j * L y j) =
        fun j ↦ y (e.symm j) by
      funext j
      simpa [cardinalitySliceSumRow] using hL_apply y j]
    simpa using (e.symm.sum_comp fun e' : G.edgeSet ↦ y e')
  have hsumRow :
      dotProduct cardinalitySliceSumRow xbar = ∑ e' : G.edgeSet, x e' := by
    simpa [xbar] using hsumRow_apply x
  let slice : Set (G.edgeSet → ℝ) :=
    G.matchingPolytope ∩ {y : G.edgeSet → ℝ | ∑ e, y e = (k : ℝ)}
  let augPoly : Set (Fin (Nat.card G.edgeSet) → ℝ) :=
    polyhedron_le_set (cardinalitySliceAugmentedMatrix A) (cardinalitySliceAugmentedRhs b (k : ℝ))
  have himageSlice : L '' slice = augPoly := by
    ext y
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      rcases hy₀ with ⟨hy₀Poly, hy₀Sum⟩
      rw [mem_cardinalitySliceAugmentedPolyhedron_iff]
      constructor
      · rw [← hpolyhedron]
        exact ⟨y₀, hy₀Poly, rfl⟩
      · calc
          dotProduct cardinalitySliceSumRow (L y₀) = ∑ e' : G.edgeSet, y₀ e' := by
              exact hsumRow_apply y₀
          _ = (k : ℝ) := hy₀Sum
    · intro hy
      rw [mem_cardinalitySliceAugmentedPolyhedron_iff] at hy
      rcases (show y ∈ L '' G.matchingPolytope by rw [hpolyhedron]; exact hy.1) with ⟨y₀, hy₀Poly, rfl⟩
      refine ⟨y₀, ⟨hy₀Poly, ?_⟩, rfl⟩
      calc
        ∑ e' : G.edgeSet, y₀ e' = dotProduct cardinalitySliceSumRow (L y₀) := by
            symm
            exact hsumRow_apply y₀
        _ = (k : ℝ) := hy.2
  have hxbarAug :
      xbar ∈ augPoly.extremePoints ℝ := by
    -- The slice-extreme hypothesis is transported once through the reindexing equivalence and the
    -- augmented-slice normal form.
    have himageExtreme :
        xbar ∈ (L '' slice).extremePoints ℝ := by
      rw [← image_extremePoints]
      exact ⟨x, hx, rfl⟩
    rw [← himageSlice]
    exact himageExtreme
  obtain ⟨J, hJ_active, hJ_linearIndependent⟩ :=
    (mem_extremePoints_iff_exists_active_linearlyIndependent_rows
      (cardinalitySliceAugmentedMatrix A)
      (cardinalitySliceAugmentedRhs b (k : ℝ))
      ((mem_cardinalitySliceAugmentedPolyhedron_iff).2 <|
        ⟨hxbarPoly, by
          calc
            dotProduct cardinalitySliceSumRow xbar = ∑ e' : G.edgeSet, x e' := hsumRow
            _ = (k : ℝ) := hxSlice.2⟩)).1 hxbarAug
  obtain ⟨I₀, hI₀_active, hI₀_linearIndependent⟩ :=
    augmentedSliceActiveRowsDropToOriginalRows
      (A := A) (b := b) (xbar := xbar) (γ0 := (k : ℝ))
      hxbarPoly hxbarNotAmbient J hJ_active hJ_linearIndependent
  have hI₀_mem : ∀ i : Fin (Nat.card G.edgeSet - 1), I₀ i ∈ I := by
    intro i
    exact hI₀_active i
  have hxbarChord :
      ∃ u₀ ∈ F, ∃ v₀ ∈ F, xbar ∈ openSegment ℝ u₀ v₀ ∧ u₀ ≠ xbar ∧ v₀ ≠ xbar := by
    -- Route correction: after isolating the active-row face, non-extremality there already gives
    -- the needed chord through `xbar`.
    rcases not_and_or.mp ((mem_extremePoints_iff_forall_segment).not.mp hxbarNotFaceExtreme) with
      hNotFace | hSeg
    · exact False.elim (hNotFace hxbarFace)
    · push_neg at hSeg
      rcases hSeg with ⟨u₀, hu₀, v₀, hv₀, hxbarSeg, hu₀ne, hv₀ne⟩
      exact ⟨u₀, hu₀, v₀, hv₀, mem_openSegment_of_ne_left_right hu₀ne hv₀ne hxbarSeg,
        hu₀ne, hv₀ne⟩
  rcases hxbarChord with ⟨u₀, hu₀, v₀, hv₀, hxbarOpen, hu₀ne, hv₀ne⟩
  have hu₀v₀_ne : u₀ ≠ v₀ := by
    intro hEq
    have hxbarOpenSame : xbar ∈ openSegment ℝ v₀ v₀ := by
      simpa [hEq] using hxbarOpen
    rw [openSegment_same] at hxbarOpenSame
    have hxbar_eq_v₀ : xbar = v₀ := by simpa using hxbarOpenSame
    exact hu₀ne (hEq.trans hxbar_eq_v₀.symm)
  have hr₀_ne_zero : v₀ - u₀ ≠ 0 := sub_ne_zero.mpr hu₀v₀_ne.symm
  have hI₀_r₀_zero :
      ∀ i : Fin (Nat.card G.edgeSet - 1), Matrix.mulVec A (v₀ - u₀) (I₀ i) = 0 := by
    intro i
    have hv₀_eq :
        Matrix.mulVec A v₀ (I₀ i) = b (I₀ i) :=
      (mem_active_constraint_face_iff.mp hv₀).1 (I₀ i) (hI₀_mem i)
    have hu₀_eq :
        Matrix.mulVec A u₀ (I₀ i) = b (I₀ i) :=
      (mem_active_constraint_face_iff.mp hu₀).1 (I₀ i) (hI₀_mem i)
    rw [Matrix.mulVec_sub, Pi.sub_apply, hv₀_eq, hu₀_eq]
    ring
  have hdir_le :
      (affineSpan ℝ F).direction ≤ ℝ ∙ (v₀ - u₀) := by
    have hspan_le :
        vectorSpan ℝ F ≤ ℝ ∙ (v₀ - u₀) := by
      rw [vectorSpan_eq_span_vsub_set_right ℝ hu₀]
      rw [Submodule.span_le]
      intro d hd
      rcases hd with ⟨w, hw, rfl⟩
      have hd_zero :
          ∀ i : Fin (Nat.card G.edgeSet - 1), Matrix.mulVec A (w - u₀) (I₀ i) = 0 := by
        intro i
        have hw_eq :
            Matrix.mulVec A w (I₀ i) = b (I₀ i) :=
          (mem_active_constraint_face_iff.mp hw).1 (I₀ i) (hI₀_mem i)
        have hu₀_eq :
            Matrix.mulVec A u₀ (I₀ i) = b (I₀ i) :=
          (mem_active_constraint_face_iff.mp hu₀).1 (I₀ i) (hI₀_mem i)
        rw [Matrix.mulVec_sub, Pi.sub_apply, hw_eq, hu₀_eq]
        ring
      exact
        selectedRowsZero_mem_spanSingleton
          A hr₀_ne_zero I₀ hI₀_r₀_zero hI₀_linearIndependent hd_zero
    simpa [direction_affineSpan] using hspan_le
  have hr₀_dir : v₀ - u₀ ∈ (affineSpan ℝ F).direction := by
    simpa using
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hv₀) (mem_affineSpan ℝ hu₀)
  have hdir_ge :
      ℝ ∙ (v₀ - u₀) ≤ (affineSpan ℝ F).direction :=
    (Submodule.span_singleton_le_iff_mem _ _).2 hr₀_dir
  have hfinrank_eq_one :
      Module.finrank ℝ (affineSpan ℝ F).direction = 1 := by
    have hfinrank_le_one :
        Module.finrank ℝ (affineSpan ℝ F).direction ≤ 1 := by
      calc
        Module.finrank ℝ (affineSpan ℝ F).direction ≤ Module.finrank ℝ ↥(ℝ ∙ (v₀ - u₀)) := by
          exact Submodule.finrank_mono hdir_le
        _ = 1 := finrank_span_singleton hr₀_ne_zero
    have hfinrank_ge_one :
        1 ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
      calc
        1 = Module.finrank ℝ ↥(ℝ ∙ (v₀ - u₀)) := (finrank_span_singleton hr₀_ne_zero).symm
        _ ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
          exact Submodule.finrank_mono hdir_ge
    exact le_antisymm hfinrank_le_one hfinrank_ge_one
  have hdir_eq :
      (affineSpan ℝ F).direction = ℝ ∙ (v₀ - u₀) :=
    selectedFace_direction_eq_spanChord hu₀ hv₀ hu₀v₀_ne hfinrank_eq_one
  have hpolyCompact : IsCompact (polyhedron_le_set A b) := by
    -- The reindexed polyhedron is a continuous image of the compact matching polytope.
    rw [← hpolyhedron]
    exact (matchingPolytope_isCompact (G := G)).image L.toContinuousLinearEquiv.continuous_toFun
  have hF_compact : IsCompact F := by
    -- The exposed face is closed inside the compact ambient polyhedron.
    exact hpolyCompact.of_isClosed_subset (hF_exposed.isClosed hpolyCompact.isClosed) hF_exposed.subset
  obtain ⟨y, z, hyF, hzF, hyz_ne, hF_eqSeg⟩ :=
    eqSegment_of_isCompact_of_convex_of_direction_eq_spanSingleton
      hF_nonempty hF_compact hF_convex hr₀_ne_zero hdir_eq
  have hyFaceExtreme : y ∈ F.extremePoints ℝ := by
    simpa [hF_eqSeg] using left_mem_extremePoints_segment_fin hyz_ne
  have hzFaceExtreme : z ∈ F.extremePoints ℝ := by
    simpa [hF_eqSeg] using right_mem_extremePoints_segment_fin hyz_ne
  have hySegExtreme : y ∈ (segment ℝ y z).extremePoints ℝ := by
    simpa using left_mem_extremePoints_segment_fin hyz_ne
  have hzSegExtreme : z ∈ (segment ℝ y z).extremePoints ℝ := by
    simpa using right_mem_extremePoints_segment_fin hyz_ne
  have hxbar_ne_y : xbar ≠ y := by
    intro hEq
    exact hxbarNotFaceExtreme (hEq ▸ hyFaceExtreme)
  have hxbar_ne_z : xbar ≠ z := by
    intro hEq
    exact hxbarNotFaceExtreme (hEq ▸ hzFaceExtreme)
  have hxbarSeg :
      xbar ∈ segment ℝ y z := by
    simpa [hF_eqSeg] using hxbarFace
  have hxbarOpenSeg :
      xbar ∈ openSegment ℝ y z :=
    mem_openSegment_of_ne_left_right hxbar_ne_y.symm hxbar_ne_z.symm hxbarSeg
  have hEdgeAmbient :
      IsEdgeOf (polyhedron_le_set A b) (segment ℝ y z) := by
    have hfinrank_seg :
        Module.finrank ℝ ↥(affineSpan ℝ (segment ℝ y z)).direction = 1 := by
      have hspan_eq : affineSpan ℝ (segment ℝ y z) = affineSpan ℝ F := by
        simpa [hF_eqSeg]
      rw [hspan_eq]
      exact hfinrank_eq_one
    refine ⟨convex_segment _ _, ?_, ?_⟩
    · simpa [hF_eqSeg] using hF_exposed.isExtreme
    · exact hfinrank_seg
  have hyAmbient :
      y ∈ (polyhedron_le_set A b).extremePoints ℝ := by
    exact hEdgeAmbient.isExtreme.extremePoints_subset_extremePoints hySegExtreme
  have hzAmbient :
      z ∈ (polyhedron_le_set A b).extremePoints ℝ := by
    exact hEdgeAmbient.isExtreme.extremePoints_subset_extremePoints hzSegExtreme
  obtain ⟨M, hM, hyEq⟩ :
      ∃ M : G.Subgraph, M.IsMatching ∧ y = L (G.subgraphIncidenceVector ℝ M) := by
    have hyImage : y ∈ (L '' G.matchingPolytope).extremePoints ℝ := by
      rw [hpolyhedron]
      exact hyAmbient
    rw [← image_extremePoints] at hyImage
    rcases hyImage with ⟨y₀, hy₀, rfl⟩
    rw [SimpleGraph.matchingPolytope] at hy₀
    rcases extremePoints_convexHull_subset hy₀ with ⟨M, hM, rfl⟩
    exact ⟨M, hM, rfl⟩
  obtain ⟨N, hN, hzEq⟩ :
      ∃ N : G.Subgraph, N.IsMatching ∧ z = L (G.subgraphIncidenceVector ℝ N) := by
    have hzImage : z ∈ (L '' G.matchingPolytope).extremePoints ℝ := by
      rw [hpolyhedron]
      exact hzAmbient
    rw [← image_extremePoints] at hzImage
    rcases hzImage with ⟨z₀, hz₀, rfl⟩
    rw [SimpleGraph.matchingPolytope] at hz₀
    rcases extremePoints_convexHull_subset hz₀ with ⟨N, hN, rfl⟩
    exact ⟨N, hN, rfl⟩
  have hvec_ne :
      G.subgraphIncidenceVector ℝ M ≠ G.subgraphIncidenceVector ℝ N := by
    intro hEq
    apply hyz_ne
    simpa [hyEq, hzEq, hEq]
  have hL_segment (x₁ y₁ : G.edgeSet → ℝ) :
      L '' segment ℝ x₁ y₁ = segment ℝ (L x₁) (L y₁) := by
    -- The coordinate reindexing equivalence preserves closed segments.
    simpa using image_segment ℝ (L.toLinearMap.toAffineMap) x₁ y₁
  have hL_openSegment (x₁ y₁ : G.edgeSet → ℝ) :
      L '' openSegment ℝ x₁ y₁ = openSegment ℝ (L x₁) (L y₁) := by
    -- The same coordinate reindexing equivalence preserves open segments.
    simpa using image_openSegment ℝ (L.toLinearMap.toAffineMap) x₁ y₁
  have hmatchingConvex : Convex ℝ G.matchingPolytope := by
    -- The matching polytope is a convex hull by definition.
    rw [SimpleGraph.matchingPolytope]
    exact convex_convexHull ℝ _
  have hMpoly : G.subgraphIncidenceVector ℝ M ∈ G.matchingPolytope := by
    -- Matching-incidence vectors are defining generators of the matching polytope.
    rw [SimpleGraph.matchingPolytope]
    exact subset_convexHull ℝ _ ⟨M, hM, rfl⟩
  have hNpoly : G.subgraphIncidenceVector ℝ N ∈ G.matchingPolytope := by
    -- The same generator description applies to the right endpoint.
    rw [SimpleGraph.matchingPolytope]
    exact subset_convexHull ℝ _ ⟨N, hN, rfl⟩
  have hExtremeImage :
      IsExtreme ℝ (L '' G.matchingPolytope)
        (segment ℝ (L (G.subgraphIncidenceVector ℝ M)) (L (G.subgraphIncidenceVector ℝ N))) := by
    rw [hpolyhedron]
    simpa [hyEq, hzEq] using hEdgeAmbient.isExtreme
  have hEdge :
      IsEdgeOf G.matchingPolytope
        (segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) := by
    have hExtreme :
        IsExtreme ℝ G.matchingPolytope
          (segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) := by
      refine ⟨hmatchingConvex.segment_subset hMpoly hNpoly, ?_⟩
      intro x₁ hx₁P y₁ hy₁P z₁ hz₁Seg hz₁Open
      have hz₁SegImage :
          L z₁ ∈
            segment ℝ (L (G.subgraphIncidenceVector ℝ M))
              (L (G.subgraphIncidenceVector ℝ N)) := by
        have hz₁SegImage' :
            L z₁ ∈
              L '' segment ℝ (G.subgraphIncidenceVector ℝ M)
                (G.subgraphIncidenceVector ℝ N) := ⟨z₁, hz₁Seg, rfl⟩
        rw [← hL_segment]
        exact hz₁SegImage'
      have hz₁OpenImage :
          L z₁ ∈ openSegment ℝ (L x₁) (L y₁) := by
        have hz₁OpenImage' : L z₁ ∈ L '' openSegment ℝ x₁ y₁ := ⟨z₁, hz₁Open, rfl⟩
        rw [← hL_openSegment]
        exact hz₁OpenImage'
      have hx₁SegImage :
          L x₁ ∈
            segment ℝ (L (G.subgraphIncidenceVector ℝ M))
              (L (G.subgraphIncidenceVector ℝ N)) :=
        hExtremeImage.left_mem_of_mem_openSegment
          ⟨x₁, hx₁P, rfl⟩ ⟨y₁, hy₁P, rfl⟩ hz₁SegImage hz₁OpenImage
      have hx₁SegImage' :
          L x₁ ∈
            L '' segment ℝ (G.subgraphIncidenceVector ℝ M)
              (G.subgraphIncidenceVector ℝ N) := by
        rw [hL_segment]
        exact hx₁SegImage
      rcases hx₁SegImage' with ⟨x₁', hx₁'Seg, hx₁'Eq⟩
      have hx₁' : x₁' = x₁ := L.injective (by simpa using hx₁'Eq)
      simpa [hx₁'] using hx₁'Seg
    exact (isEdgeOf_segment_iff hvec_ne).2 hExtreme
  have hxOpen :
      x ∈ openSegment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
    have hxOpenImage :
        L x ∈
          L '' openSegment ℝ (G.subgraphIncidenceVector ℝ M)
            (G.subgraphIncidenceVector ℝ N) := by
      rw [hL_openSegment]
      simpa [xbar, hyEq, hzEq] using hxbarOpenSeg
    rcases hxOpenImage with ⟨w, hwOpen, hwEq⟩
    have hwx : w = x := L.injective (by simpa [xbar] using hwEq)
    simpa [hwx] using hwOpen
  have hSymm :
      (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath :=
    (matchingIncidenceVector_segment_isEdgeOf_iff_symmDiff_isCycleOrPath
      (G := G) hM hN).1 hEdge
  have hdist :
      Nat.dist M.edgeSet.ncard N.edgeSet.ncard ≤ 1 := by
    -- Route correction: first cancel the common edges of `M` and `N`, so only the exclusive
    -- symmetric-difference path/cycle edges remain to be counted.
    rw [matchingCardinalityDist_eq_dist_symmDiffParts (G := G) (M := M) (N := N)]
    exact matchingExclusiveEdgeDist_le_one_of_symmDiff_isCycleOrPath (G := G) hM hN hSymm
  exact ⟨M, N, hM, hN, hEdge, hxOpen, hdist⟩

/-- Helper for Exercise 4.27: a slice-extreme point cannot lie in the open segment between two
distinct size-`k` matching-incidence vectors, because both endpoints already belong to the same
cardinality slice. -/
private lemma cardinalitySliceExtreme_not_mem_openSegment_of_equal_cardinality
    [Fintype V] {x : G.edgeSet → ℝ} {k : ℕ} {M N : G.Subgraph}
    (hx : x ∈
      (G.matchingPolytope ∩ {y : G.edgeSet → ℝ | ∑ e, y e = (k : ℝ)}).extremePoints ℝ)
    (hM : M.IsMatching) (hN : N.IsMatching)
    (hMk : M.edgeSet.ncard = k) (hNk : N.edgeSet.ncard = k)
    (hMN :
      G.subgraphIncidenceVector ℝ M ≠ G.subgraphIncidenceVector ℝ N)
    (hxOpen :
      x ∈ openSegment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) :
    False := by
  have hxExtreme :=
    (mem_extremePoints_iff_left.mp hx).2
  have hMmem :
      G.subgraphIncidenceVector ℝ M ∈
        G.matchingPolytope ∩ {y : G.edgeSet → ℝ | ∑ e, y e = (k : ℝ)} :=
    subgraphIncidenceVector_mem_matchingPolytope_inter_cardinality_hyperplane
      (G := G) hM hMk
  have hNmem :
      G.subgraphIncidenceVector ℝ N ∈
        G.matchingPolytope ∩ {y : G.edgeSet → ℝ | ∑ e, y e = (k : ℝ)} :=
    subgraphIncidenceVector_mem_matchingPolytope_inter_cardinality_hyperplane
      (G := G) hN hNk
  -- Extremality inside the slice forces the left endpoint of the open segment to equal `x`.
  have hxEq :
      G.subgraphIncidenceVector ℝ M = x :=
    hxExtreme _ hMmem _ hNmem hxOpen
  have hxOpen' :
      G.subgraphIncidenceVector ℝ M ∈
        openSegment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) := by
    simpa [hxEq] using hxOpen
  rw [openSegment_eq_image_lineMap] at hxOpen'
  rcases hxOpen' with ⟨t, ht, htEq⟩
  -- A strict interior point cannot coincide with the left endpoint when the two endpoints differ.
  have htZero :
      t = 0 := by
    exact (AffineMap.lineMap_eq_left_iff.mp htEq).resolve_left hMN
  exact ht.1.ne' htZero

/-- Helper for Exercise 4.27: an interior point of the segment between matchings of consecutive
cardinalities cannot satisfy any integer cardinality equation. -/
private lemma not_mem_cardinalitySlice_openSegment_of_consecutive_cardinality
    [Fintype V] {x : G.edgeSet → ℝ} {k m : ℕ} {M N : G.Subgraph}
    (hxsum : ∑ e, x e = (k : ℝ))
    (hM : M.IsMatching) (hN : N.IsMatching)
    (hMk : M.edgeSet.ncard = m) (hNk : N.edgeSet.ncard = m + 1)
    (hxOpen :
      x ∈ openSegment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) :
    False := by
  rw [openSegment_eq_image_lineMap] at hxOpen
  rcases hxOpen with ⟨t, ht, rfl⟩
  have hsumLine :
      (k : ℝ) =
        AffineMap.lineMap
          (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ M e)
          (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ N e) t := by
    -- Summing coordinates commutes with the affine line map along the matching segment.
    rw [← totalEdgeSum_lineMap (G := G)
      (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N) t]
    simpa using hxsum.symm
  have hnatM : Fintype.card M.edgeSet = m := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hMk]
  have hnatN : Fintype.card N.edgeSet = m + 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hNk]
  have hstrict :
      (m : ℝ) < (k : ℝ) ∧ (k : ℝ) < (m + 1 : ℝ) := by
    -- The total sum of an interior point on the segment lies strictly between the endpoint totals.
    rw [matchingIncidenceVector_total_sum_eq_card_edgeSet (G := G) M,
      matchingIncidenceVector_total_sum_eq_card_edgeSet (G := G) N, hnatM, hnatN] at hsumLine
    have hline :
        (k : ℝ) = AffineMap.lineMap (m : ℝ) (m + 1 : ℝ) t := by
      simpa using hsumLine
    have htPos : 0 < t := ht.1
    have htLt : t < 1 := ht.2
    simp [AffineMap.lineMap_apply_module] at hline
    constructor <;> nlinarith
  have hkNat : m < k := by
    exact_mod_cast hstrict.1
  have hkNat' : k < m + 1 := by
    exact_mod_cast hstrict.2
  omega

/-- Helper for Exercise 4.27: if a linear inequality from `A *ᵥ u ≤ b` is tight at an interior
point of a feasible segment, then it is already tight at both segment endpoints. -/
private lemma activeRow_tight_at_openSegment_endpoints
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {x y z : Fin n → ℝ} (hx : x ∈ polyhedron_le_set A b) (hy : y ∈ polyhedron_le_set A b)
    (hz : z ∈ openSegment ℝ x y) {i : Fin m} (hi : A.mulVec z i = b i) :
    A.mulVec x i = b i ∧ A.mulVec y i = b i := by
  rw [openSegment_eq_image_lineMap] at hz
  rcases hz with ⟨t, ht, rfl⟩
  have hxle : A.mulVec x i ≤ b i := hx i
  have hyle : A.mulVec y i ≤ b i := hy i
  have hline :
      AffineMap.lineMap (A.mulVec x i) (A.mulVec y i) t = b i := by
    -- Rewrite the row evaluation of the affine combination to a scalar line map.
    simpa [AffineMap.lineMap_apply_module, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct,
      Finset.mul_sum, Finset.sum_add_distrib, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_add, add_mul] using hi
  have hxge : b i ≤ A.mulVec x i := by
    by_contra hlt
    have hlt' : A.mulVec x i < b i := lt_of_not_ge hlt
    simp [AffineMap.lineMap_apply_module] at hline
    nlinarith [hlt', hyle, ht.1, ht.2]
  have hyge : b i ≤ A.mulVec y i := by
    by_contra hlt
    have hlt' : A.mulVec y i < b i := lt_of_not_ge hlt
    simp [AffineMap.lineMap_apply_module] at hline
    nlinarith [hxle, hlt', ht.1, ht.2]
  exact ⟨le_antisymm hxle hxge, le_antisymm hyle hyge⟩

/-- Helper for Exercise 4.27: a slice-extreme point should already be ambient-extreme in
`G.matchingPolytope`. -/
private lemma ambientExtreme_of_mem_extremePoints_cardinalitySlice
    [Fintype V] {x : G.edgeSet → ℝ} {k : ℕ}
    (hx : x ∈
      (G.matchingPolytope ∩ {y : G.edgeSet → ℝ | ∑ e, y e = (k : ℝ)}).extremePoints ℝ) :
    x ∈ (G.matchingPolytope).extremePoints ℝ := by
  -- A hypothetical nonambient slice-extreme point yields an ambient edge whose endpoints have
  -- equal or consecutive cardinality; the local arithmetic then contradicts slice extremality.
  by_contra hxNotAmbient
  have hxSlice :
      x ∈ G.matchingPolytope ∩ {y : G.edgeSet → ℝ | ∑ e, y e = (k : ℝ)} :=
    (mem_extremePoints_iff_left.mp hx).1
  have hxsum : ∑ e, x e = (k : ℝ) := hxSlice.2
  obtain ⟨M, N, hM, hN, hEdge, hxOpen, hdist⟩ :=
    existsMatchingEdgeThrough_nonambientSliceExtreme (G := G) hx hxNotAmbient
  have hvec_ne :
      G.subgraphIncidenceVector ℝ M ≠ G.subgraphIncidenceVector ℝ N := by
    -- An edge segment cannot collapse to a singleton because its direction has dimension `1`.
    intro hEq
    have hdim := hEdge.finrank_direction_eq_one
    rw [direction_affineSpan, vectorSpan_segment, hEq, vsub_self] at hdim
    have hzero : Module.finrank ℝ ↥(ℝ ∙ (0 : G.edgeSet → ℝ)) = 0 := by
      simp
    linarith
  by_cases hEqCard : M.edgeSet.ncard = N.edgeSet.ncard
  · -- Equal endpoint cardinalities force both endpoints into the same slice, contradicting
    -- extremality of `x` inside that slice.
    have hxOpen' := hxOpen
    rw [openSegment_eq_image_lineMap] at hxOpen'
    rcases hxOpen' with ⟨t, _ht, rfl⟩
    have hkCard :
        M.edgeSet.ncard = k := by
      -- Summing coordinates along the segment reduces the slice equation to the constant endpoint
      -- total.
      have hsumLine :
          (k : ℝ) =
            AffineMap.lineMap (M.edgeSet.ncard : ℝ) (N.edgeSet.ncard : ℝ) t := by
        calc
          (k : ℝ) =
              ∑ e : G.edgeSet,
                AffineMap.lineMap
                  (G.subgraphIncidenceVector ℝ M)
                  (G.subgraphIncidenceVector ℝ N) t e := by
                simpa using hxsum.symm
          _ =
              AffineMap.lineMap
                (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ M e)
                (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ N e) t := by
                exact totalEdgeSum_lineMap (G := G)
                  (G.subgraphIncidenceVector ℝ M)
                  (G.subgraphIncidenceVector ℝ N) t
          _ =
              AffineMap.lineMap (M.edgeSet.ncard : ℝ) (N.edgeSet.ncard : ℝ) t := by
                rw [matchingIncidenceVector_total_sum_eq_ncard_edgeSet (G := G) M,
                  matchingIncidenceVector_total_sum_eq_ncard_edgeSet (G := G) N]
      have hkReal : (k : ℝ) = (M.edgeSet.ncard : ℝ) := by
        simpa [hEqCard, AffineMap.lineMap_apply_module] using hsumLine
      exact_mod_cast hkReal.symm
    have hNk : N.edgeSet.ncard = k := by simpa [hEqCard] using hkCard
    exact
      cardinalitySliceExtreme_not_mem_openSegment_of_equal_cardinality
        (G := G) hx hM hN hkCard hNk hvec_ne hxOpen
  · -- If the endpoint cardinalities differ, the edge-gap bound forces them to be consecutive, and
    -- an interior point on that segment cannot satisfy the integer slice equation.
    have hsucc :
        M.edgeSet.ncard + 1 = N.edgeSet.ncard ∨
          N.edgeSet.ncard + 1 = M.edgeSet.ncard := by
      by_cases hMNle : M.edgeSet.ncard ≤ N.edgeSet.ncard
      · left
        have hsub :
            N.edgeSet.ncard - M.edgeSet.ncard ≤ 1 := by
          simpa [Nat.dist_eq_sub_of_le hMNle] using hdist
        omega
      · right
        have hNMle : N.edgeSet.ncard ≤ M.edgeSet.ncard := Nat.le_of_not_ge hMNle
        have hsub :
            M.edgeSet.ncard - N.edgeSet.ncard ≤ 1 := by
          simpa [Nat.dist_eq_sub_of_le_right hNMle] using hdist
        omega
    rcases hsucc with hMNsucc | hNMsucc
    · exact
        not_mem_cardinalitySlice_openSegment_of_consecutive_cardinality
          (G := G) (x := x) (k := k) (m := M.edgeSet.ncard)
          hxsum hM hN rfl hMNsucc.symm hxOpen
    · have hxOpenSymm :
        x ∈ openSegment ℝ
          (G.subgraphIncidenceVector ℝ N)
          (G.subgraphIncidenceVector ℝ M) := by
        simpa [openSegment_symm] using hxOpen
      exact
        not_mem_cardinalitySlice_openSegment_of_consecutive_cardinality
          (G := G) (x := x) (k := k) (m := N.edgeSet.ncard)
          hxsum hN hM rfl hNMsucc.symm hxOpenSymm

/-- Helper for Exercise 4.27: every extreme point of the cardinality slice is a size-`k` matching
incidence vector. -/
private lemma mem_cardinality_k_matching_generators_of_mem_extremePoints_slice
    [Fintype V] {x : G.edgeSet → ℝ} {k : ℕ}
    (hx : x ∈
      (G.matchingPolytope ∩ {y : G.edgeSet → ℝ | ∑ e, y e = (k : ℝ)}).extremePoints ℝ) :
    x ∈ cardinalityKMatchingIncidenceSet G k := by
  have hxSlice :
      x ∈ G.matchingPolytope ∩ {y : G.edgeSet → ℝ | ∑ e, y e = (k : ℝ)} :=
    (mem_extremePoints_iff_left.mp hx).1
  have hxsum : ∑ e, x e = (k : ℝ) := hxSlice.2
  have hxAmbient :
      x ∈ (G.matchingPolytope).extremePoints ℝ :=
    ambientExtreme_of_mem_extremePoints_cardinalitySlice (G := G) hx
  -- Once the slice vertex is known to be ambient-extreme, the existing ambient classification
  -- identifies it as a size-`k` matching incidence vector.
  exact
    mem_cardinality_k_matching_generators_of_mem_extremePoints_matchingPolytope
      G hxAmbient hxsum

/-- Exercise 4.27 (2). For `k = 1, …, |V|`, the slice of the matching polytope by the
hyperplane `∑ e∈E, x e = k` is the convex hull of the incidence vectors of the matchings of
cardinality `k`. -/
-- The ambient extreme-point bookkeeping and slice-vertex classification are both available, so
-- compact convex reconstruction from the finite generator hull closes the equality.
theorem matchingPolytope_inter_cardinality_hyperplane_eq_convexHull
    [Fintype V]
    (k : ℕ) (hk_pos : 1 ≤ k) (hk_le_card : k ≤ Fintype.card V) :
    G.matchingPolytope ∩ {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)} =
      convexHull ℝ (cardinalityKMatchingIncidenceSet G k) := by
  refine Set.Subset.antisymm ?_ ?_
  · let slice : Set (G.edgeSet → ℝ) :=
        G.matchingPolytope ∩ {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)}
    let generators : Set (G.edgeSet → ℝ) := cardinalityKMatchingIncidenceSet G k
    have hcompact : IsCompact slice :=
      matchingPolytope_inter_cardinality_hyperplane_isCompact G k
    have hconvex : Convex ℝ slice :=
      matchingPolytope_inter_cardinality_hyperplane_convex G k
    have hclosure :
        closure (convexHull ℝ (slice.extremePoints ℝ)) = slice :=
      closure_convexHull_extremePoints hcompact hconvex
    have hgenFinite : generators.Finite :=
      finite_cardinality_k_matching_generators G k
    have hHullClosed : IsClosed (convexHull ℝ generators) :=
      by
        simpa using (hgenFinite.isCompact_convexHull (𝕜 := ℝ)).isClosed
    have hExtremeSubset : slice.extremePoints ℝ ⊆ generators := by
      intro x hx
      -- The slice-extreme-point classification identifies every vertex as a size-`k` generator.
      exact mem_cardinality_k_matching_generators_of_mem_extremePoints_slice G hx
    have hHullSubset :
        convexHull ℝ (slice.extremePoints ℝ) ⊆ convexHull ℝ generators := by
      -- Once every slice extreme point is a size-`k` generator, convexity absorbs their hull.
      refine convexHull_min ?_ (convex_convexHull ℝ generators)
      intro x hx
      exact subset_convexHull ℝ generators (hExtremeSubset hx)
    -- Krein-Milman reconstructs the compact convex slice from its extreme points, and the finite
    -- generator family makes the target hull closed.
    have hclosureSubset :
        closure (convexHull ℝ (slice.extremePoints ℝ)) ⊆ convexHull ℝ generators :=
      closure_minimal hHullSubset hHullClosed
    have hsliceSubset : slice ⊆ convexHull ℝ generators := by
      calc
        slice = closure (convexHull ℝ (slice.extremePoints ℝ)) := hclosure.symm
        _ ⊆ convexHull ℝ generators := hclosureSubset
    simpa [slice] using hsliceSubset
  · -- The easy inclusion is already handled by the generator-membership lemma.
    exact
      convexHull_cardinality_k_matchings_subset_matchingPolytope_inter_cardinality_hyperplane
        G k

end Exercise_4_27

#print axioms subgraphIncidenceVector_mem_extremePoints_matchingPolytope
#print axioms matchingIncidenceVector_segment_isEdgeOf_iff_symmDiff_isCycleOrPath
#print axioms matchingIncidenceVector_adjacent_vertices_iff_symmDiff_isCycleOrPath
#print axioms mem_cardinalityKMatchingIncidenceSet_iff
#print axioms matchingPolytope_inter_cardinality_hyperplane_eq_convexHull
