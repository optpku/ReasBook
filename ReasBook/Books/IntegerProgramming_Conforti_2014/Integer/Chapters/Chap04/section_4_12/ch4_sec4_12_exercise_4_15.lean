import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_theorem_4_18

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: `lean_leansearch` was unavailable in this session, so this file uses
-- mathlib's canonical `SimpleGraph.incMatrix` owner through the chapter bridge
-- `SimpleGraph.edgeIncMatrix`, together with `SimpleGraph.cycleGraph` and `Matrix.det` APIs.

section Exercise_4_15

open Matrix SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Helper for Exercise 4.15: in a graph isomorphism, an edge is incident to a vertex exactly when
its image edge is incident to the image vertex. -/
lemma mapEdgeSet_mem_incidenceSet_iff {W : Type*} [DecidableEq W] {G' : SimpleGraph W}
    [DecidableRel G'.Adj] (f : G ≃g G') {v : V} {e : G.edgeSet} :
    ↑(f.mapEdgeSet e) ∈ G'.incidenceSet (f v) ↔ ↑e ∈ G.incidenceSet v := by
  -- Rewrite incidence against an edge-set element to plain membership in the underlying pair.
  rw [SimpleGraph.edge_mem_incidenceSet_iff, SimpleGraph.edge_mem_incidenceSet_iff]
  change f v ∈ Sym2.map f (↑e : Sym2 V) ↔ v ∈ (↑e : Sym2 V)
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    simpa [f.injective hwv] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- Helper for Exercise 4.15: the edge-indexed incidence matrix is preserved entrywise by a graph
isomorphism after transporting the row and column indices. -/
lemma edgeIncMatrix_apply_iso {W : Type*} [DecidableEq W] {G' : SimpleGraph W}
    [DecidableRel G'.Adj] (f : G ≃g G') (R : Type*) [Zero R] [One R] (v : V) (e : G.edgeSet) :
    G.edgeIncMatrix R v e = G'.edgeIncMatrix R (f v) (f.mapEdgeSet e) := by
  -- Both entries are the same indicator of the corresponding incidence predicate.
  change G.incMatrix R v (↑e : Sym2 V) = G'.incMatrix R (f v) (↑(f.mapEdgeSet e) : Sym2 W)
  rw [SimpleGraph.incMatrix_apply', SimpleGraph.incMatrix_apply']
  by_cases h : ↑e ∈ G.incidenceSet v
  · have h' : ↑(f.mapEdgeSet e) ∈ G'.incidenceSet (f v) :=
      (mapEdgeSet_mem_incidenceSet_iff (G := G) f).2 h
    have hmap : Sym2.map (fun x ↦ f x) (↑e : Sym2 V) ∈ G'.incidenceSet (f v) := by
      simpa using h'
    simp [h, hmap]
  · have h' : ↑(f.mapEdgeSet e) ∉ G'.incidenceSet (f v) := by
      exact mt (mapEdgeSet_mem_incidenceSet_iff (G := G) f).1 h
    have hmap : Sym2.map (fun x ↦ f x) (↑e : Sym2 V) ∉ G'.incidenceSet (f v) := by
      simpa using h'
    simp [h, hmap]

namespace Exercise_4_15

variable {n : ℕ}

/-- Helper for Exercise 4.15: consecutive vertices in a cycle graph are adjacent. -/
lemma cycle_edge_by_index_adj (hcycle_len : 3 ≤ n) (j : Fin n) :
    (cycleGraph n).Adj j (finRotate n j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hcycle_len
  -- Consecutive vertices differ by one in the cycle graph.
  rw [SimpleGraph.cycleGraph_adj']
  right
  rw [finRotate_apply]
  simp [Nat.mod_eq_of_lt (by omega : 1 < 3 + m)]

/-- The canonical edge ordering of `cycleGraph n`: the `j`th edge joins `j` to `j + 1`. -/
def cycle_edge_by_index (hcycle_len : 3 ≤ n) (j : Fin n) : (cycleGraph n).edgeSet :=
  ⟨s(j, finRotate n j), cycle_edge_by_index_adj hcycle_len j⟩

/-- Helper for Exercise 4.15: the canonical cycle edge is incident exactly to its two endpoints. -/
lemma cycle_edge_by_index_mem_incidenceSet_iff (hcycle_len : 3 ≤ n) (i j : Fin n) :
    ↑(cycle_edge_by_index hcycle_len j) ∈ (cycleGraph n).incidenceSet i ↔
      i = j ∨ i = finRotate n j := by
  -- The edge is literally the unordered pair `{j, j + 1}`.
  rw [SimpleGraph.edge_mem_incidenceSet_iff]
  simpa [cycle_edge_by_index] using (Sym2.mem_iff : i ∈ s(j, finRotate n j) ↔ _)

/-- Helper for Exercise 4.15: a two-step rotation on `Fin (m + 3)` has no fixed points. -/
lemma cycle_edge_by_index_two_step_ne {m : ℕ} (j : Fin (m + 3)) :
    finRotate (m + 3) (finRotate (m + 3) j) ≠ j := by
  intro h
  let two : Fin (m + 3) := ⟨2, by omega⟩
  -- Rewrite the double rotation as addition by `2` in the cyclic order.
  have hcycle : j + two = j := by
    change finCycle two j = j
    calc
      finCycle two j = ((finRotate (m + 3))^[2]) j := by
        rw [finCycle_eq_finRotate_iterate]
      _ = finRotate (m + 3) (finRotate (m + 3) j) := rfl
      _ = j := h
  have hval : (j + two).val = j.val := congrArg Fin.val hcycle
  rw [Fin.val_add_eq_ite] at hval
  by_cases hwrap : m + 3 ≤ j.val + two.val
  · simp [hwrap, two] at hval
    omega
  · simp [hwrap, two] at hval

/-- Helper for Exercise 4.15: the canonical edge ordering of a cycle is injective, hence
bijection after counting edges. -/
lemma cycle_edge_by_index_injective (hcycle_len : 3 ≤ n) :
    Function.Injective (cycle_edge_by_index (n := n) hcycle_len) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hcycle_len
  have hn : n = m + 3 := by omega
  subst hn
  intro j k hjk
  -- Route correction: use the source proof's unordered-pair equality and rule out the swapped
  -- branch by the explicit no-2-cycle lemma above.
  have hs : s(j, finRotate (m + 3) j) = s(k, finRotate (m + 3) k) := by
    exact congrArg Subtype.val hjk
  rw [Sym2.eq_iff] at hs
  rcases hs with ⟨hjk', _⟩ | ⟨hjk', hkj'⟩
  · exact hjk'
  · have htwo : finRotate (m + 3) (finRotate (m + 3) j) = j := by
      calc
        finRotate (m + 3) (finRotate (m + 3) j) = finRotate (m + 3) k := by
          rw [hkj']
        _ = j := hjk'.symm
    exfalso
    exact (cycle_edge_by_index_two_step_ne j) htwo

/-- Helper for Exercise 4.15: a cycle with at least three vertices has as many edges as vertices. -/
lemma cycleGraph_card_edgeSet (hcycle_len : 3 ≤ n) :
    Fintype.card ((cycleGraph n).edgeSet) = n := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hcycle_len
  have hn : n = m + 3 := by omega
  subst hn
  have hdeg : ∀ v : Fin (m + 3), (cycleGraph (m + 3)).degree v = 2 := by
    intro v
    simpa using (SimpleGraph.cycleGraph_degree_three_le (n := m) (v := v))
  -- The degree-sum formula identifies the total degree with twice the number of edges.
  have hdouble : 2 * Fintype.card ((cycleGraph (m + 3)).edgeSet) = 2 * (m + 3) := by
    calc
      2 * Fintype.card ((cycleGraph (m + 3)).edgeSet) =
          ∑ v : Fin (m + 3), (cycleGraph (m + 3)).degree v := by
            calc
              _ = 2 * (cycleGraph (m + 3)).edgeFinset.card := by
                rw [(cycleGraph (m + 3)).edgeFinset_card]
              _ = ∑ v : Fin (m + 3), (cycleGraph (m + 3)).degree v := by
                symm
                exact (cycleGraph (m + 3)).sum_degrees_eq_twice_card_edges
      _ = 2 * (m + 3) := by
        simp [hdeg, Fintype.card_fin, two_mul]
        ring
  omega

/-- Helper for Exercise 4.15: the consecutive-edge map is a bijection from `Fin n` to the edge set
of the cycle graph. -/
lemma cycle_edge_by_index_bijective (hcycle_len : 3 ≤ n) :
    Function.Bijective (cycle_edge_by_index (n := n) hcycle_len) := by
  -- Combine injectivity with the edge-count equality from the cycle degree sum.
  exact
    (Fintype.bijective_iff_injective_and_card (cycle_edge_by_index (n := n) hcycle_len)).2
      ⟨cycle_edge_by_index_injective (n := n) hcycle_len,
        by simpa using (cycleGraph_card_edgeSet (n := n) hcycle_len).symm⟩

/-- Helper for Exercise 4.15: the explicit edge ordering of a cycle graph. -/
noncomputable def cycle_edge_equiv (hcycle_len : 3 ≤ n) : Fin n ≃ (cycleGraph n).edgeSet :=
  Equiv.ofBijective _ (cycle_edge_by_index_bijective (n := n) hcycle_len)

/-- Helper for Exercise 4.15: rotating a non-last `Fin` index sends `castSucc i` to `i.succ`. -/
lemma finRotate_castSucc (i : Fin n) : finRotate (n + 1) i.castSucc = i.succ := by
  apply Fin.ext
  have hne_last : i.castSucc ≠ Fin.last n := Fin.ne_last_of_lt i.castSucc_lt_last
  rw [coe_finRotate, if_neg hne_last]
  simp

/-- The standard square cycle-incidence matrix with columns indexed by consecutive edges. -/
def cycle_square_matrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ if i = j ∨ i = finRotate n j then 1 else 0

/-- Helper for Exercise 4.15: under the canonical edge ordering, the cycle incidence matrix is the
standard band matrix with ones on the diagonal and subdiagonal, with the wrap-around entry in the
top-right corner. -/
lemma cycle_incidence_square_eq_cycle_square_matrix (hcycle_len : 3 ≤ n) :
    ((cycleGraph n).edgeIncMatrix ℤ).submatrix id (cycle_edge_equiv (n := n) hcycle_len) =
      cycle_square_matrix n := by
  ext i j
  -- Under the consecutive edge ordering, each column is the incidence indicator of `{j, j + 1}`.
  rw [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply, Matrix.submatrix_apply,
    SimpleGraph.incMatrix_apply']
  simp [cycle_square_matrix, cycle_edge_equiv, cycle_edge_by_index_mem_incidenceSet_iff]

/-- Helper for Exercise 4.15: in the standard cycle matrix, the first row is supported only in the
first and last columns. -/
lemma cycle_square_matrix_first_row_zero_off_endpoints {m : ℕ} {j : Fin (m + 2)}
    (hj0 : j ≠ 0) (hjlast : j ≠ Fin.last (m + 1)) :
    cycle_square_matrix (m + 2) 0 j = 0 := by
  -- Away from the two endpoint columns, neither defining disjunct for a `1` entry can occur.
  rw [cycle_square_matrix]
  apply if_neg
  rintro (hdiag | hrotate)
  · exact hj0 hdiag.symm
  · have hval : (0 : ℕ) = (finRotate (m + 2) j : ℕ) := congrArg Fin.val hrotate
    rw [coe_finRotate] at hval
    simp [hjlast] at hval

/-- Helper for Exercise 4.15: above the diagonal, the first Laplace minor has zero entries. -/
lemma cycle_square_matrix_minor_zero_lower_entry_vanishes_above_diagonal
    {n : ℕ} {i j : Fin n} (hij : i < j) :
    ((cycle_square_matrix (n + 1)).submatrix Fin.succ Fin.succ) i j = 0 := by
  -- Above the diagonal, the lower minor misses both the diagonal and rotated branches.
  rw [Matrix.submatrix_apply, cycle_square_matrix]
  apply if_neg
  rintro (hdiag | hrotate)
  · exact hij.ne ((Fin.succ_injective _) hdiag)
  · have hval : (i.succ : ℕ) = (finRotate (n + 1) j.succ : ℕ) := congrArg Fin.val hrotate
    rw [coe_finRotate] at hval
    by_cases hjlast : j.succ = Fin.last n
    · simp [hjlast] at hval
    · simp [hjlast, Fin.val_succ] at hval
      omega

/-- Helper for Exercise 4.15: below the diagonal, the second Laplace minor has zero entries. -/
lemma cycle_square_matrix_minor_last_upper_entry_vanishes_below_diagonal
    {n : ℕ} {i j : Fin n} (hij : j < i) :
    ((cycle_square_matrix (n + 1)).submatrix Fin.succ Fin.castSucc) i j = 0 := by
  -- Route correction: rewrite the rotated `castSucc` column once, then compare values directly.
  rw [Matrix.submatrix_apply, cycle_square_matrix, finRotate_castSucc]
  apply if_neg
  rintro (hdiag | hrotate)
  · have hval : i.val + 1 = j.val := by
      simpa using congrArg Fin.val hdiag
    omega
  · exact hij.ne (((Fin.succ_injective _) hrotate).symm)

/-- Helper for Exercise 4.15: removing the first row and first column from the standard cycle
matrix leaves a lower triangular matrix with diagonal entries `1`. -/
lemma cycle_square_matrix_minor_zero_lower (n : ℕ) :
    ((cycle_square_matrix (n + 1)).submatrix Fin.succ Fin.succ).BlockTriangular OrderDual.toDual :=
  by
    -- The entrywise vanishing fact above the diagonal is now isolated in a stable helper lemma.
    intro i j hij
    simpa using
      cycle_square_matrix_minor_zero_lower_entry_vanishes_above_diagonal (n := n) hij

/-- Helper for Exercise 4.15: removing the first row and last column from the standard cycle
matrix leaves an upper triangular matrix with diagonal entries `1`. -/
lemma cycle_square_matrix_minor_last_upper (n : ℕ) :
    ((cycle_square_matrix (n + 1)).submatrix Fin.succ Fin.castSucc).BlockTriangular id := by
  -- The second Laplace minor is upper triangular because its below-diagonal entries all vanish.
  intro i j hij
  exact cycle_square_matrix_minor_last_upper_entry_vanishes_below_diagonal (n := n) hij

/-- Helper for Exercise 4.15: both Laplace-expansion minors of the standard cycle matrix have
determinant `1`. -/
lemma cycle_square_matrix_minor_dets (n : ℕ) :
    ((cycle_square_matrix (n + 1)).submatrix Fin.succ Fin.succ).det = 1 ∧
      ((cycle_square_matrix (n + 1)).submatrix Fin.succ Fin.castSucc).det = 1 := by
  constructor
  · -- The first minor is lower triangular, so its determinant is the product of diagonal ones.
    rw [Matrix.det_of_lowerTriangular _ (cycle_square_matrix_minor_zero_lower n)]
    apply Fintype.prod_eq_one
    intro i
    simp [Matrix.submatrix_apply, cycle_square_matrix]
  · -- The second minor is upper triangular, and its diagonal ones come from the rotated branch.
    rw [Matrix.det_of_upperTriangular (cycle_square_matrix_minor_last_upper n)]
    apply Fintype.prod_eq_one
    intro i
    simp [Matrix.submatrix_apply, cycle_square_matrix]

/-- Helper for Exercise 4.15: the standard cycle-incidence matrix has determinant
`1 + (-1)^(n - 1)`. -/
lemma cycle_square_matrix_det (n : ℕ) (htwo : 2 ≤ n) :
    (cycle_square_matrix n).det = 1 + (-1 : ℤ) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le htwo
  have hmain : (cycle_square_matrix (m + 2)).det = 1 + (-1 : ℤ) ^ (m + 1) := by
    have h00 : cycle_square_matrix (m + 2) 0 0 = 1 := by
      -- The `(0,0)` entry is on the diagonal.
      simp [cycle_square_matrix]
    have h0last : cycle_square_matrix (m + 2) 0 (Fin.last (m + 1)) = 1 := by
      -- The top-right corner is the wrap-around edge of the cycle.
      simp [cycle_square_matrix, finRotate_last]
    have hminor_zero :
        (((cycle_square_matrix (m + 2)).submatrix Fin.succ (0 : Fin (m + 2)).succAbove).det) = 1 := by
      -- Deleting row `0` and column `0` gives the lower-triangular minor.
      simpa using (cycle_square_matrix_minor_dets (n := m + 1)).1
    have hminor_last :
        (((cycle_square_matrix (m + 2)).submatrix Fin.succ (Fin.last (m + 1)).succAbove).det) = 1 := by
      -- Deleting row `0` and the last column gives the upper-triangular minor.
      simpa using (cycle_square_matrix_minor_dets (n := m + 1)).2
    have hlastsucc : (Fin.last m).succ = Fin.last (m + 1) := by
      simp [Fin.succ_last]
    have h0tail : cycle_square_matrix (m + 2) 0 (Fin.last m).succ = 1 := by
      simpa [hlastsucc] using h0last
    have hminor_tail :
        (((cycle_square_matrix (m + 2)).submatrix Fin.succ (Fin.last m).succ.succAbove).det) = 1 := by
      simpa [hlastsucc] using hminor_last
    have htail :
        ∑ i : Fin (m + 1),
            (-1 : ℤ) ^ ((i.succ : Fin (m + 2)) : ℕ) * cycle_square_matrix (m + 2) 0 i.succ *
              (((cycle_square_matrix (m + 2)).submatrix Fin.succ i.succ.succAbove).det) =
          (-1 : ℤ) ^ (((Fin.last m).succ : Fin (m + 2)) : ℕ) *
            cycle_square_matrix (m + 2) 0 (Fin.last m).succ *
              (((cycle_square_matrix (m + 2)).submatrix Fin.succ (Fin.last m).succ.succAbove).det) := by
      -- Every summand except the last one vanishes because the first row has no interior support.
      refine Finset.sum_eq_single (Fin.last m) ?_ ?_
      · rintro i - hi
        have hi_last : i.succ ≠ Fin.last (m + 1) := by
          simpa using (Fin.succ_ne_last_iff i).2 hi
        have hrow :
            cycle_square_matrix (m + 2) 0 i.succ = 0 :=
          cycle_square_matrix_first_row_zero_off_endpoints (j := i.succ) (by simp) hi_last
        simp [hrow]
      · intro hnot
        exfalso
        exact hnot (Finset.mem_univ _)
    -- Expand along the first row, then collapse to the two endpoint minors promised by the source.
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, htail, h00, hminor_zero, h0tail, hminor_tail]
    simp [Fin.succ_last]
  have hm2 : m + 2 = 2 + m := by omega
  calc
    (cycle_square_matrix (2 + m)).det = (cycle_square_matrix (m + 2)).det := by
      exact congrArg (fun k ↦ (cycle_square_matrix k).det) hm2.symm
    _ = 1 + (-1 : ℤ) ^ (m + 1) := hmain
    _ = 1 + (-1 : ℤ) ^ (2 + m - 1) := by
          rw [show m + 1 = 2 + m - 1 by omega]

end Exercise_4_15

open Exercise_4_15

/-- Helper for Exercise 4.15: reindexing the edge-indexed incidence matrix along a graph
isomorphism recovers the target graph's edge-indexed incidence matrix. -/
lemma edgeIncMatrix_submatrix_iso_eq {W : Type*} [DecidableEq W] {G' : SimpleGraph W}
    [DecidableRel G'.Adj] (f : G ≃g G') (R : Type*) [Zero R] [One R] :
    ((G.edgeIncMatrix R).submatrix f.toEquiv.symm f.mapEdgeSet.symm) = G'.edgeIncMatrix R := by
  ext v e
  -- Each transported entry is the same incidence indicator after applying the graph isomorphism.
  rw [Matrix.submatrix_apply]
  calc
    G.edgeIncMatrix R (f.toEquiv.symm v) (f.mapEdgeSet.symm e) =
        G'.edgeIncMatrix R (f (f.toEquiv.symm v)) (f.mapEdgeSet (f.mapEdgeSet.symm e)) := by
          exact edgeIncMatrix_apply_iso (G := G) f R (f.toEquiv.symm v) (f.mapEdgeSet.symm e)
    _ = G'.edgeIncMatrix R v e := by
          change
            G'.incMatrix R (f (f.toEquiv.symm v))
                (Sym2.map (fun x ↦ f x) (Sym2.map (fun x ↦ f.toEquiv.symm x) (↑e : Sym2 W))) =
              G'.incMatrix R v (↑e : Sym2 W)
          rw [Sym2.map_map]
          have hmap :
              Sym2.map ((fun x ↦ f x) ∘ fun x ↦ f.toEquiv.symm x) (↑e : Sym2 W) =
                Sym2.map id (↑e : Sym2 W) := by
            refine Sym2.map_congr ?_
            intro x hx
            change f (f.toEquiv.symm x) = x
            exact f.apply_symm_apply x
          rw [hmap, Sym2.map_id]
          change G'.incMatrix R (f (f.toEquiv.symm v)) (↑e : Sym2 W) =
            G'.incMatrix R v (↑e : Sym2 W)
          exact congrArg (fun w : W => G'.incMatrix R w (↑e : Sym2 W)) (f.apply_symm_apply v)

/-- Helper for Exercise 4.15: after transporting a cycle graph along an isomorphism and then
ordering its edges consecutively, the absolute determinant is the one of `cycle_square_matrix`. -/
lemma abs_det_incidence_submatrix_eq_abs_cycle_square
    (σ : V ≃ G.edgeSet) {n : ℕ} (hcycle : G ≃g cycleGraph n) (hcycle_len : 3 ≤ n) :
    |((G.edgeIncMatrix ℤ).submatrix id σ).det| = |(cycle_square_matrix n).det| := by
  let ρ : Fin n ≃ V := hcycle.toEquiv.symm
  let κ : Fin n ≃ V :=
    ((cycle_edge_equiv (n := n) hcycle_len).trans hcycle.mapEdgeSet.symm).trans σ.symm
  -- Reindex rows by the cycle-graph isomorphism and columns by the consecutive edge ordering.
  have habs :
      |((((G.edgeIncMatrix ℤ).submatrix id σ).submatrix ρ κ).det)| =
        |(((G.edgeIncMatrix ℤ).submatrix id σ).det)| := by
    simpa [ρ, κ] using
      Matrix.abs_det_submatrix_equiv_equiv ρ κ ((G.edgeIncMatrix ℤ).submatrix id σ)
  have hsub :
      (((G.edgeIncMatrix ℤ).submatrix id σ).submatrix ρ κ) =
        (((G.edgeIncMatrix ℤ).submatrix ρ hcycle.mapEdgeSet.symm).submatrix id
          (cycle_edge_equiv (n := n) hcycle_len)) := by
    ext i j
    simp [ρ, κ, Matrix.submatrix_apply]
  calc
    |((G.edgeIncMatrix ℤ).submatrix id σ).det| =
        |((((G.edgeIncMatrix ℤ).submatrix id σ).submatrix ρ κ).det)| := habs.symm
    _ =
        |((((G.edgeIncMatrix ℤ).submatrix ρ hcycle.mapEdgeSet.symm).submatrix id
            (cycle_edge_equiv (n := n) hcycle_len)).det)| := by
          rw [hsub]
    _ = |(((cycleGraph n).edgeIncMatrix ℤ).submatrix id
          (cycle_edge_equiv (n := n) hcycle_len)).det| := by
          rw [edgeIncMatrix_submatrix_iso_eq (G := G) (G' := cycleGraph n) hcycle ℤ]
    _ = |(cycle_square_matrix n).det| := by
          rw [cycle_incidence_square_eq_cycle_square_matrix (n := n) hcycle_len]

/-- Exercise 4.15 (1): if the edge set of `G` is an odd cycle of length at least `3`, then the
absolute value of the determinant of any square reindexing of its edge-indexed incidence matrix is
`2`. -/
theorem odd_cycle_abs_det_cycle_incidence_square_matrix
    (σ : V ≃ G.edgeSet) {n : ℕ} (hcycle : G ≃g cycleGraph n) (hcycle_len : 3 ≤ n)
    (hodd : Odd n) :
    |((G.edgeIncMatrix ℤ).submatrix id σ).det| = (2 : ℤ) :=
    by
      have hnm2 : 2 ≤ n := le_trans (by decide) hcycle_len
      have hEven : Even (n - 1) := by
        rcases hodd with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        omega
      -- Transport to the canonical cycle matrix and then evaluate its determinant by parity.
      calc
        |((G.edgeIncMatrix ℤ).submatrix id σ).det| = |(cycle_square_matrix n).det| := by
            exact abs_det_incidence_submatrix_eq_abs_cycle_square (G := G) σ hcycle hcycle_len
        _ = |1 + (-1 : ℤ) ^ (n - 1)| := by rw [cycle_square_matrix_det (n := n) hnm2]
        _ = 2 := by simp [hEven.neg_one_pow]

/-- Exercise 4.15 (2): if the edge set of `G` is an even cycle of length at least `3`, then the
determinant of its square reindexed edge-indexed incidence matrix is `0`. -/
theorem even_cycle_det_cycle_incidence_square_matrix_eq_zero
    (σ : V ≃ G.edgeSet) {n : ℕ} (hcycle : G ≃g cycleGraph n) (hcycle_len : 3 ≤ n)
    (heven : Even n) :
    ((G.edgeIncMatrix ℤ).submatrix id σ).det = 0 := by
  have hnm2 : 2 ≤ n := le_trans (by decide) hcycle_len
  have hOdd : Odd (n - 1) := by
    rcases heven with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    omega
  have habs :
      |((G.edgeIncMatrix ℤ).submatrix id σ).det| = 0 := by
    -- Transport to the canonical cycle matrix and use the odd exponent to cancel the two terms.
    calc
      |((G.edgeIncMatrix ℤ).submatrix id σ).det| = |(cycle_square_matrix n).det| := by
          exact abs_det_incidence_submatrix_eq_abs_cycle_square (G := G) σ hcycle hcycle_len
      _ = |1 + (-1 : ℤ) ^ (n - 1)| := by rw [cycle_square_matrix_det (n := n) hnm2]
      _ = 0 := by simp [hOdd.neg_one_pow]
  exact abs_eq_zero.mp habs

end Exercise_4_15
