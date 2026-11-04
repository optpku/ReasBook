/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_example_3_36
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

/-- The symmetric correlation-coordinate space on `Fin n`, viewed as the canonical linear
subspace of real symmetric matrices. -/
abbrev correlationSpace (n : ℕ) :=
  ↥(selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ))

/-- Correlation-space points act as their underlying symmetric matrices. -/
instance {n : ℕ} : CoeFun (correlationSpace n) fun _ ↦ Fin n → Fin n → ℝ :=
  ⟨fun x ↦ x.1⟩

namespace correlationSpace

/-- The ambient symmetric matrix underlying a correlation-space point. -/
def toMatrix {n : ℕ} (x : correlationSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  x.1

end correlationSpace

/-- The ambient symmetric matrix attached to a subset of `Fin n`. -/
def correlation_vertex_matrix {n : ℕ} (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (if i ∈ S then (1 : ℝ) else 0) * (if j ∈ S then (1 : ℝ) else 0)

/-- The ambient matrix attached to a correlation vertex is symmetric. -/
theorem correlation_vertex_matrix_isSymm {n : ℕ} (S : Finset (Fin n)) :
    (correlation_vertex_matrix S).IsSymm := by
  -- Swapping the two indices only swaps the two indicator factors.
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  simp [correlation_vertex_matrix, mul_comm]

/-- The ambient matrix attached to a correlation vertex belongs to the symmetric correlation
space. -/
theorem correlation_vertex_matrix_mem_correlationSpace {n : ℕ} (S : Finset (Fin n)) :
    correlation_vertex_matrix S ∈
      selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ) := by
  -- Membership in the self-adjoint submodule is exactly symmetry over `ℝ`.
  rw [mem_selfAdjointMatricesSubmodule]
  simpa [Matrix.IsSelfAdjoint, Matrix.IsAdjointPair] using
    correlation_vertex_matrix_isSymm S

/-- The `0/1` rank-one correlation vertex attached to a subset of `Fin n`. -/
def correlation_vertex {n : ℕ} (S : Finset (Fin n)) : correlationSpace n :=
  ⟨correlation_vertex_matrix S, correlation_vertex_matrix_mem_correlationSpace S⟩

/-- The `0/1` rank-one vertices spanning the correlation polytope on `n` vertices. -/
def correlationVertices (n : ℕ) : Set (correlationSpace n) :=
  Set.range fun S : Finset (Fin n) ↦ correlation_vertex S

/-- The correlation polytope on `n` vertices is the convex hull of the `0/1` rank-one symmetric
correlation vertices attached to subsets of `Fin n`. -/
def correlationPolytope (n : ℕ) : Set (correlationSpace n) :=
  convexHull ℝ (correlationVertices n)

/-- The correlation polytope is defined as the convex hull of the `0/1` rank-one symmetric
correlation vertices coming from subsets of `Fin n`. -/
theorem correlationPolytope_eq_convexHull (n : ℕ) :
    correlationPolytope n = convexHull ℝ (correlationVertices n) := by
  rfl

/-- Helper for Lemma 4.55: every point of `correlationSpace n` is a symmetric matrix. -/
theorem correlationSpace_isSymm {n : ℕ} (x : correlationSpace n) : x.1.IsSymm := by
  -- The subtype condition is exactly self-adjointness, which over `ℝ` is symmetry.
  have hx := x.2
  rw [mem_selfAdjointMatricesSubmodule] at hx
  simpa [Matrix.IsSelfAdjoint, Matrix.IsAdjointPair] using hx

/-- The unordered pair joining `i.castSucc` to the last vertex of `Fin (n + 1)` is not diagonal.
-/
theorem edge_to_last_not_isDiag (n : ℕ) (i : Fin n) :
    ¬ (s(i.castSucc, Fin.last n) : Sym2 (Fin (n + 1))).IsDiag := by
  -- The last vertex is never in the image of `Fin.castSucc`.
  simpa [Sym2.mk_isDiag_iff] using Fin.castSucc_ne_last i

/-- The edge of the complete graph on `Fin (n + 1)` joining `i.castSucc` to `Fin.last n`. -/
def edge_to_last (n : ℕ) (i : Fin n) : complete_graph_edges (n + 1) :=
  ⟨s(i.castSucc, Fin.last n), edge_to_last_not_isDiag n i⟩

/-- Distinct vertices of `Fin n` determine a non-diagonal edge in the complete graph on
`Fin (n + 1)`. -/
theorem internal_edge_not_isDiag {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ¬ (s(i.castSucc, j.castSucc) : Sym2 (Fin (n + 1))).IsDiag := by
  -- Injectivity of `Fin.castSucc` transports non-equality to the larger complete graph.
  simpa [Sym2.mk_isDiag_iff] using hij

/-- The edge of the complete graph on `Fin (n + 1)` joining the distinct vertices `i.castSucc`
and `j.castSucc`. -/
def internal_edge {n : ℕ} (i j : Fin n) (hij : i ≠ j) : complete_graph_edges (n + 1) :=
  ⟨s(i.castSucc, j.castSucc), internal_edge_not_isDiag hij⟩

/-- Helper for Lemma 4.55: swapping the two endpoints of an internal edge does not change the
edge coordinate. -/
theorem internal_edge_swap {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    internal_edge i j hij = internal_edge j i hij.symm := by
  -- The two subtype values agree because `Sym2` forgets endpoint order.
  apply Subtype.ext
  exact Sym2.eq_swap

/-- Helper for Lemma 4.55: every non-diagonal edge of `K_{n+1}` is either incident to the last
vertex or lies entirely inside the first `n` vertices. -/
theorem complete_graph_edge_cases {n : ℕ} (e : complete_graph_edges (n + 1)) :
    (∃ i : Fin n, e = edge_to_last n i) ∨
      ∃ i j : Fin n, ∃ hij : i ≠ j, e = internal_edge i j hij := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      rcases Fin.eq_castSucc_or_eq_last u with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last v with ⟨j, rfl⟩ | rfl
        · by_cases hij : i = j
          · exfalso
            exact he (by simpa [Sym2.mk_isDiag_iff, hij])
          · right
            exact ⟨i, j, hij, by rfl⟩
        · left
          exact ⟨i, by rfl⟩
      · rcases Fin.eq_castSucc_or_eq_last v with ⟨j, rfl⟩ | rfl
        · left
          exact ⟨j, by
            apply Subtype.ext
            exact Sym2.eq_swap⟩
        · exfalso
          exact he (by simp [Sym2.mk_isDiag_iff])

/-- Helper for Lemma 4.55: the textbook forward coordinate formula on ordered vertex pairs. -/
def correlation_cut_forward_coord {n : ℕ} (x : correlationSpace n) (u v : Fin (n + 1)) : ℝ :=
  if hu : u = Fin.last n then
    if hv : v = Fin.last n then
      0
    else
      x (v.castPred hv) (v.castPred hv)
  else if hv : v = Fin.last n then
    x (u.castPred hu) (u.castPred hu)
  else
    x (u.castPred hu) (u.castPred hu) + x (v.castPred hv) (v.castPred hv) -
      2 * x (u.castPred hu) (v.castPred hv)

/-- Helper for Lemma 4.55: the forward coordinate formula is symmetric in the two endpoints. -/
theorem correlation_cut_forward_coord_symm {n : ℕ} (x : correlationSpace n) :
    ∀ u v : Fin (n + 1),
      correlation_cut_forward_coord x u v = correlation_cut_forward_coord x v u := by
  intro u v
  by_cases hu : u = Fin.last n
  · by_cases hv : v = Fin.last n
    · -- When both endpoints are the last vertex, both sides are the diagonal fallback value.
      simp [correlation_cut_forward_coord, hu, hv]
    · -- If only `u` is the last vertex, both orientations read the diagonal entry of `v`.
      simp [correlation_cut_forward_coord, hu, hv]
  · by_cases hv : v = Fin.last n
    · -- If only `v` is the last vertex, symmetry is again immediate from the branch choice.
      simp [correlation_cut_forward_coord, hu, hv]
    · -- For two internal vertices, symmetry comes from symmetry of the underlying matrix.
      have hxSymm := correlationSpace_isSymm x
      have hsym :
          x (u.castPred hu) (v.castPred hv) = x (v.castPred hv) (u.castPred hu) := by
        have hentry :=
          congrFun (congrFun hxSymm (u.castPred hu)) (v.castPred hv)
        simpa using hentry.symm
      simp [correlation_cut_forward_coord, hu, hv, hsym, add_comm, add_left_comm, add_assoc]

/-- Helper for Lemma 4.55: the forward map from correlation coordinates to cut coordinates. -/
def correlation_cut_forward (n : ℕ) (x : correlationSpace n) :
    complete_graph_edges (n + 1) → ℝ :=
  fun e ↦ Sym2.lift ⟨correlation_cut_forward_coord x, correlation_cut_forward_coord_symm x⟩ e.1

/-- Helper for Lemma 4.55: the forward map sends the edge from `i` to the last vertex to the
diagonal entry `xᵢᵢ`. -/
theorem correlation_cut_forward_edge_to_last (n : ℕ) (x : correlationSpace n) (i : Fin n) :
    correlation_cut_forward n x (edge_to_last n i) = x i i := by
  -- Evaluating on the edge `(i.castSucc, last)` lands in the branch recording the diagonal entry.
  simp [correlation_cut_forward, correlation_cut_forward_coord, edge_to_last]

/-- Helper for Lemma 4.55: the forward map sends the internal edge `{i,j}` to
`xᵢᵢ + xⱼⱼ - 2 xᵢⱼ`. -/
theorem correlation_cut_forward_internal_edge {n : ℕ} (x : correlationSpace n)
    (i j : Fin n) (hij : i ≠ j) :
    correlation_cut_forward n x (internal_edge i j hij) = x i i + x j j - 2 * x i j := by
  -- On internal edges, both endpoints lie in the first `n` vertices, so the affine expression is
  -- the final branch of the coordinate formula.
  simp [correlation_cut_forward, correlation_cut_forward_coord, internal_edge]

/-- Helper for Lemma 4.55: the textbook inverse matrix reconstructed from cut coordinates. -/
noncomputable def correlation_cut_inverse_matrix (n : ℕ) (y : complete_graph_edges (n + 1) → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    if hij : i = j then
      y (edge_to_last n i)
    else
      (1 / 2 : ℝ) *
        (y (edge_to_last n i) + y (edge_to_last n j) - y (internal_edge i j hij))

/-- Helper for Lemma 4.55: the inverse matrix is symmetric. -/
theorem correlation_cut_inverse_matrix_isSymm (n : ℕ) (y : complete_graph_edges (n + 1) → ℝ) :
    (correlation_cut_inverse_matrix n y).IsSymm := by
  -- The diagonal branch is obvious, and the off-diagonal branch is symmetric because internal
  -- edges are unordered.
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  by_cases hij : i = j
  · subst hij
    simp [correlation_cut_inverse_matrix]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [correlation_cut_inverse_matrix, hij, hji, internal_edge_swap hij, add_comm, add_left_comm,
      add_assoc]

/-- Helper for Lemma 4.55: the inverse matrix belongs to the symmetric correlation-coordinate
space. -/
theorem correlation_cut_inverse_matrix_mem_correlationSpace (n : ℕ)
    (y : complete_graph_edges (n + 1) → ℝ) :
    correlation_cut_inverse_matrix n y ∈
      selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ) := by
  -- Over `ℝ`, symmetry is exactly the self-adjoint condition.
  rw [mem_selfAdjointMatricesSubmodule]
  simpa [Matrix.IsSelfAdjoint, Matrix.IsAdjointPair] using
    correlation_cut_inverse_matrix_isSymm n y

/-- Helper for Lemma 4.55: the inverse map from cut coordinates back to correlation coordinates.
-/
noncomputable def correlation_cut_inverse (n : ℕ) (y : complete_graph_edges (n + 1) → ℝ) :
    correlationSpace n :=
  ⟨correlation_cut_inverse_matrix n y, correlation_cut_inverse_matrix_mem_correlationSpace n y⟩

/-- Helper for Lemma 4.55: the inverse map recovers diagonal entries from edges to the last
vertex. -/
theorem correlation_cut_inverse_diag (n : ℕ) (y : complete_graph_edges (n + 1) → ℝ)
    (i : Fin n) :
    correlation_cut_inverse n y i i = y (edge_to_last n i) := by
  -- The diagonal branch of the inverse formula is exactly the edge-to-last coordinate.
  simp [correlation_cut_inverse, correlation_cut_inverse_matrix]

/-- Helper for Lemma 4.55: the inverse map recovers off-diagonal entries by the textbook
averaging formula. -/
theorem correlation_cut_inverse_offdiag (n : ℕ) (y : complete_graph_edges (n + 1) → ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    correlation_cut_inverse n y i j =
      (1 / 2 : ℝ) *
        (y (edge_to_last n i) + y (edge_to_last n j) - y (internal_edge i j hij)) := by
  -- Off the diagonal, the inverse map uses the affine reconstruction formula directly.
  simp [correlation_cut_inverse, correlation_cut_inverse_matrix, hij]

/-- Helper for Lemma 4.55: the forward map is additive. -/
theorem correlation_cut_forward_map_add (n : ℕ) (x z : correlationSpace n) :
    correlation_cut_forward n (x + z) = correlation_cut_forward n x + correlation_cut_forward n z := by
  -- Every edge coordinate is either diagonal-to-last or internal, so the pointwise formula is
  -- linear on each case.
  ext e
  rcases complete_graph_edge_cases (n := n) e with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · rw [Pi.add_apply, correlation_cut_forward_edge_to_last, correlation_cut_forward_edge_to_last,
      correlation_cut_forward_edge_to_last]
    rfl
  · rw [Pi.add_apply, correlation_cut_forward_internal_edge, correlation_cut_forward_internal_edge,
      correlation_cut_forward_internal_edge]
    simp
    ring_nf

/-- Helper for Lemma 4.55: the forward map commutes with scalar multiplication. -/
theorem correlation_cut_forward_map_smul (n : ℕ) (a : ℝ) (x : correlationSpace n) :
    correlation_cut_forward n (a • x) = a • correlation_cut_forward n x := by
  -- The same edge-by-edge coordinate formulas are homogeneous.
  ext e
  rcases complete_graph_edge_cases (n := n) e with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · rw [Pi.smul_apply, correlation_cut_forward_edge_to_last, correlation_cut_forward_edge_to_last]
    rfl
  · rw [Pi.smul_apply, correlation_cut_forward_internal_edge, correlation_cut_forward_internal_edge]
    simp
    ring_nf

/-- Helper for Lemma 4.55: applying the inverse after the forward map returns the original
correlation matrix. -/
theorem correlation_cut_left_inv (n : ℕ) :
    Function.LeftInverse (correlation_cut_inverse n) (correlation_cut_forward n) := by
  intro x
  -- We recover the original matrix entrywise from the diagonal and internal-edge formulas.
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [correlation_cut_inverse_diag, correlation_cut_forward_edge_to_last]
  · rw [correlation_cut_inverse_offdiag n (correlation_cut_forward n x) i j hij]
    rw [correlation_cut_forward_edge_to_last, correlation_cut_forward_edge_to_last,
      correlation_cut_forward_internal_edge]
    ring

/-- Helper for Lemma 4.55: applying the forward map after the inverse map returns the original
cut-coordinate vector. -/
theorem correlation_cut_right_inv (n : ℕ) :
    Function.RightInverse (correlation_cut_inverse n) (correlation_cut_forward n) := by
  intro y
  -- Every edge coordinate is reconstructed from the inverse matrix by the same textbook formulas.
  funext e
  rcases complete_graph_edge_cases (n := n) e with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · rw [correlation_cut_forward_edge_to_last, correlation_cut_inverse_diag]
  · rw [correlation_cut_forward_internal_edge, correlation_cut_inverse_diag,
      correlation_cut_inverse_diag, correlation_cut_inverse_offdiag n y i j hij]
    ring

/-- Helper for Lemma 4.55: the explicit linear equivalence between correlation coordinates and cut
coordinates. -/
noncomputable def correlation_cut_linear_equiv (n : ℕ) :
    correlationSpace n ≃ₗ[ℝ] (complete_graph_edges (n + 1) → ℝ) where
  toFun := correlation_cut_forward n
  invFun := correlation_cut_inverse n
  left_inv := correlation_cut_left_inv n
  right_inv := correlation_cut_right_inv n
  map_add' := correlation_cut_forward_map_add n
  map_smul' := correlation_cut_forward_map_smul n

/-- Helper for Lemma 4.55: the explicit linear equivalence sends the edge to the last vertex to
the corresponding diagonal matrix entry. -/
theorem correlation_cut_linear_equiv_apply_edge_to_last (n : ℕ) (x : correlationSpace n)
    (i : Fin n) :
    correlation_cut_linear_equiv n x (edge_to_last n i) = x i i := by
  -- This is exactly the forward edge-to-last coordinate formula.
  exact correlation_cut_forward_edge_to_last n x i

/-- Helper for Lemma 4.55: the explicit linear equivalence sends an internal edge to
`xᵢᵢ + xⱼⱼ - 2 xᵢⱼ`. -/
theorem correlation_cut_linear_equiv_apply_internal_edge {n : ℕ} (x : correlationSpace n)
    (i j : Fin n) (hij : i ≠ j) :
    correlation_cut_linear_equiv n x (internal_edge i j hij) = x i i + x j j - 2 * x i j := by
  -- This is exactly the forward internal-edge coordinate formula.
  exact correlation_cut_forward_internal_edge x i j hij

/-- Helper for Lemma 4.55: the inverse linear equivalence reads the diagonal from edges to the
last vertex. -/
theorem correlation_cut_linear_equiv_symm_apply_diag (n : ℕ)
    (y : complete_graph_edges (n + 1) → ℝ) (i : Fin n) :
    (correlation_cut_linear_equiv n).symm y i i = y (edge_to_last n i) := by
  -- The inverse equivalence is definitionally the inverse reconstruction map.
  exact correlation_cut_inverse_diag n y i

/-- Helper for Lemma 4.55: the inverse linear equivalence uses the textbook off-diagonal
averaging formula. -/
theorem correlation_cut_linear_equiv_symm_apply_offdiag (n : ℕ)
    (y : complete_graph_edges (n + 1) → ℝ) (i j : Fin n) (hij : i ≠ j) :
    (correlation_cut_linear_equiv n).symm y i j =
      (1 / 2 : ℝ) *
        (y (edge_to_last n i) + y (edge_to_last n j) - y (internal_edge i j hij)) := by
  -- The inverse equivalence is definitionally the inverse reconstruction map.
  exact correlation_cut_inverse_offdiag n y i j hij

/-- Helper for Lemma 4.55: the diagonal entries of a correlation vertex are its membership
indicators. -/
theorem correlation_vertex_apply_diag {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    correlation_vertex S i i = if i ∈ S then (1 : ℝ) else 0 := by
  -- On the diagonal, the rank-one matrix is the square of a `0/1` indicator, hence unchanged.
  by_cases hi : i ∈ S
  · simp [correlation_vertex, correlation_vertex_matrix, hi]
  · simp [correlation_vertex, correlation_vertex_matrix, hi]

/-- Helper for Lemma 4.55: the off-diagonal entries of a correlation vertex are products of the
two endpoint indicators. -/
theorem correlation_vertex_apply_offdiag {n : ℕ} (S : Finset (Fin n)) (i j : Fin n) :
    correlation_vertex S i j =
      (if i ∈ S then (1 : ℝ) else 0) * (if j ∈ S then (1 : ℝ) else 0) := by
  -- This is the definition of the ambient rank-one correlation vertex matrix.
  rfl

/-- Helper for Lemma 4.55: the explicit equivalence sends every correlation vertex to a cut
vertex and reaches every cut vertex. -/
theorem correlation_cut_linear_equiv_image_correlationVertices (n : ℕ) :
    correlation_cut_linear_equiv n '' correlationVertices n = cutVertices (n + 1) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨S, rfl⟩
    -- The forward direction uses the lifted subset `S.map Fin.castSuccEmb`.
    refine ⟨S.map Fin.castSuccEmb, ?_⟩
    ext e
    rcases complete_graph_edge_cases (n := n) e with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
    · rw [correlation_cut_linear_equiv_apply_edge_to_last]
      have hedge :
          cutIncidenceVector (S.map Fin.castSuccEmb) (edge_to_last n i) =
            if (i.castSucc ∈ S.map Fin.castSuccEmb) = (Fin.last n ∈ S.map Fin.castSuccEmb) then
              0
            else
              1 := by
        simpa [edge_to_last] using
          (cutIncidenceVector_apply_pair (S.map Fin.castSuccEmb) i.castSucc (Fin.last n)
            (edge_to_last_not_isDiag n i))
      rw [correlation_vertex_apply_diag]
      calc
        (fun W ↦ cutIncidenceVector W) (S.map Fin.castSuccEmb) (edge_to_last n i)
            = if (i.castSucc ∈ S.map Fin.castSuccEmb) = (Fin.last n ∈ S.map Fin.castSuccEmb) then
                0
              else
                1 := by
                  simpa using hedge
        _ = if i ∈ S then (1 : ℝ) else 0 := by
              by_cases hi : i ∈ S
              · simp [hi]
              · simp [hi]
    · rw [correlation_cut_linear_equiv_apply_internal_edge]
      have hinter :
          cutIncidenceVector (S.map Fin.castSuccEmb) (internal_edge i j hij) =
            if (i.castSucc ∈ S.map Fin.castSuccEmb) = (j.castSucc ∈ S.map Fin.castSuccEmb) then
              0
            else
              1 := by
        simpa [internal_edge] using
          (cutIncidenceVector_apply_pair (S.map Fin.castSuccEmb) i.castSucc j.castSucc
            (internal_edge_not_isDiag hij))
      rw [correlation_vertex_apply_diag, correlation_vertex_apply_diag,
        correlation_vertex_apply_offdiag]
      calc
        (fun W ↦ cutIncidenceVector W) (S.map Fin.castSuccEmb) (internal_edge i j hij)
            = if (i.castSucc ∈ S.map Fin.castSuccEmb) = (j.castSucc ∈ S.map Fin.castSuccEmb) then
                0
              else
                1 := by
                  simpa using hinter
        _ = (if i ∈ S then (1 : ℝ) else 0) + (if j ∈ S then (1 : ℝ) else 0) -
              2 * ((if i ∈ S then (1 : ℝ) else 0) * (if j ∈ S then (1 : ℝ) else 0)) := by
              by_cases hi : i ∈ S
              · by_cases hj : j ∈ S
                · norm_num [hi, hj]
                · simp [hi, hj]
              · by_cases hj : j ∈ S
                · simp [hi, hj]
                · simp [hi, hj]
  · rintro ⟨W, rfl⟩
    let W0 : Finset (Fin (n + 1)) :=
      if Fin.last n ∈ W then Finset.univ \ W else W
    let S : Finset (Fin n) := Finset.univ.filter fun i ↦ i.castSucc ∈ W0
    have hcut : cutIncidenceVector W0 = cutIncidenceVector W := by
      -- Normalizing by complement removes the last vertex without changing the cut.
      by_cases hlast : Fin.last n ∈ W
      · simp [W0, hlast, cutIncidenceVector_compl_eq]
      · simp [W0, hlast]
    have hlast0 : Fin.last n ∉ W0 := by
      -- By construction, the normalized cut does not contain the last vertex.
      by_cases hlast : Fin.last n ∈ W
      · simp [W0, hlast]
      · simp [W0, hlast]
    have hpreimage :
        correlation_cut_inverse n (cutIncidenceVector W0) = correlation_vertex S := by
      -- The inverse formulas reconstruct exactly the rank-one correlation matrix of the normalized
      -- subset `S`.
      apply Subtype.ext
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [correlation_cut_inverse_diag, correlation_vertex_apply_diag]
        rw [edge_to_last]
        rw [cutIncidenceVector_apply_pair W0 i.castSucc (Fin.last n) (edge_to_last_not_isDiag n i)]
        by_cases hi : i.castSucc ∈ W0
        · simp [S, hlast0, hi]
        · simp [S, hlast0, hi]
      · rw [correlation_cut_inverse_offdiag n (cutIncidenceVector W0) i j hij,
            correlation_vertex_apply_offdiag]
        rw [edge_to_last]
        rw [cutIncidenceVector_apply_pair W0 i.castSucc (Fin.last n)
          (edge_to_last_not_isDiag n i)]
        rw [edge_to_last]
        rw [cutIncidenceVector_apply_pair W0 j.castSucc (Fin.last n)
          (edge_to_last_not_isDiag n j)]
        rw [internal_edge]
        rw [cutIncidenceVector_apply_pair W0 i.castSucc j.castSucc
          (internal_edge_not_isDiag hij)]
        by_cases hi : i.castSucc ∈ W0
        · by_cases hj : j.castSucc ∈ W0
          · norm_num [S, hlast0, hi, hj]
          · norm_num [S, hlast0, hi, hj]
        · by_cases hj : j.castSucc ∈ W0
          · norm_num [S, hlast0, hi, hj]
          · norm_num [S, hlast0, hi, hj]
    have himage :
        correlation_cut_linear_equiv n (correlation_vertex S) = cutIncidenceVector W0 := by
      -- After identifying the inverse image, apply the right-inverse identity.
      rw [← hpreimage]
      simpa [correlation_cut_linear_equiv] using
        correlation_cut_right_inv n (cutIncidenceVector W0)
    refine ⟨correlation_vertex S, ⟨S, rfl⟩, ?_⟩
    -- Replacing `W` by the normalized `W0` does not change the cut-incidence vector.
    simpa [hcut] using himage

/-- Helper for Lemma 4.55: the explicit equivalence maps the whole correlation polytope onto the
cut polytope. -/
theorem correlation_cut_linear_equiv_image_correlationPolytope (n : ℕ) :
    correlation_cut_linear_equiv n '' correlationPolytope n = cutPolytope (n + 1) := by
  -- The source and target polytopes are convex hulls of the corresponding vertex sets, and linear
  -- maps commute with convex hulls.
  simpa [correlationPolytope_eq_convexHull, cutPolytope,
    correlation_cut_linear_equiv_image_correlationVertices] using
    (LinearMap.image_convexHull (correlation_cut_linear_equiv n).toLinearMap
      (correlationVertices n))

/-- Lemma 4.55. For every `n`, the correlation polytope `P_n^corr` and `P_{n+1}^cut` are
linearly isomorphic. -/
theorem correlation_polytope_linearly_isomorphic_cut_polytope (n : ℕ) :
    ∃ e : correlationSpace n ≃ₗ[ℝ] (complete_graph_edges (n + 1) → ℝ),
      e '' correlationPolytope n = cutPolytope (n + 1) := by
  -- The explicit coordinate equivalence carries generators of one polytope exactly to generators
  -- of the other.
  exact ⟨correlation_cut_linear_equiv n, correlation_cut_linear_equiv_image_correlationPolytope n⟩

/-- A source-faithful coordinate specification for a linear equivalence from the correlation
polytope to the cut polytope, stated on the symmetric correlation-coordinate space. -/
theorem correlation_polytope_cut_polytope_linear_equiv_spec (n : ℕ) :
    ∃ e : correlationSpace n ≃ₗ[ℝ] (complete_graph_edges (n + 1) → ℝ),
      e '' correlationPolytope n = cutPolytope (n + 1) ∧
      (∀ x : correlationSpace n, ∀ i : Fin n, e x (edge_to_last n i) = x i i) ∧
      (∀ x : correlationSpace n, ∀ i j : Fin n, ∀ hij : i ≠ j,
        e x (internal_edge i j hij) = x i i + x j j - 2 * x i j) := by
  -- Reuse the explicit equivalence together with its two coordinate formulas.
  refine ⟨correlation_cut_linear_equiv n, ?_⟩
  constructor
  · exact correlation_cut_linear_equiv_image_correlationPolytope n
  constructor
  · intro x i
    exact correlation_cut_linear_equiv_apply_edge_to_last n x i
  · intro x i j hij
    exact correlation_cut_linear_equiv_apply_internal_edge x i j hij

/-- The inverse coordinates appearing in Lemma 4.55 recover a correlation-matrix entry from the
cut coordinates of the image point. -/
theorem cut_polytope_correlation_inverse_coordinate_spec (n : ℕ) :
    ∃ e : correlationSpace n ≃ₗ[ℝ] (complete_graph_edges (n + 1) → ℝ),
      e '' correlationPolytope n = cutPolytope (n + 1) ∧
      (∀ y : complete_graph_edges (n + 1) → ℝ, ∀ i : Fin n,
        e.symm y i i = y (edge_to_last n i)) ∧
      (∀ y : complete_graph_edges (n + 1) → ℝ, ∀ i j : Fin n, ∀ hij : i ≠ j,
        e.symm y i j =
          (1 / 2 : ℝ) *
            (y (edge_to_last n i) + y (edge_to_last n j) - y (internal_edge i j hij))) := by
  -- The same explicit equivalence packages the inverse coordinate formulas as well.
  refine ⟨correlation_cut_linear_equiv n, ?_⟩
  constructor
  · exact correlation_cut_linear_equiv_image_correlationPolytope n
  constructor
  · intro y i
    exact correlation_cut_linear_equiv_symm_apply_diag n y i
  · intro y i j hij
    exact correlation_cut_linear_equiv_symm_apply_offdiag n y i j hij
