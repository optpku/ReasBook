/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_24.HTTB
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_31.GridGraph
public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

namespace Matrix

/-- The five-point stencil kernel of the Chapter 5 negative discrete Laplacian with
homogeneous Dirichlet boundary conditions. -/
def dirichletLaplacianKernel : ℤ → ℤ → ℝ
  | 0, 0 => 4
  | 1, 0 => -1
  | -1, 0 => -1
  | 0, 1 => -1
  | 0, -1 => -1
  | _, _ => 0

/-- The Chapter 5 negative discrete Laplacian with homogeneous Dirichlet boundary conditions on
the `n_y × n_x` interior grid, realized as an HTTB matrix. -/
def dirichletLaplacian (n_x n_y : ℕ) :
    Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ :=
  Matrix.httb n_x n_y dirichletLaplacianKernel

/-- Entrywise formula for `Matrix.dirichletLaplacian`. -/
theorem dirichletLaplacian_apply (n_x n_y : ℕ)
    (j l : Fin n_y) (i k : Fin n_x) :
    Matrix.dirichletLaplacian n_x n_y (j, i) (l, k) =
      Matrix.dirichletLaplacianKernel
        (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ))
        (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) := by
  simp [Matrix.dirichletLaplacian, Matrix.httb_apply]

/-- The diagonal entries of `Matrix.dirichletLaplacian` are `4`. -/
theorem dirichletLaplacian_apply_self (n_x n_y : ℕ) (ji : Fin n_y × Fin n_x) :
    Matrix.dirichletLaplacian n_x n_y ji ji = 4 := by
  rcases ji with ⟨j, i⟩
  simp [Matrix.dirichletLaplacian_apply, Matrix.dirichletLaplacianKernel]

/-- Helper for Exercise 5.31: the boundary-correction diagonal weight `4 - degree` attached to the
interior grid graph. -/
noncomputable def dirichletBoundaryWeight (n_x n_y : ℕ) : Fin n_y × Fin n_x → ℝ :=
  fun ji ↦ 4 - (((gridGraph n_x n_y).degree ji : ℝ))

/-- Helper for Exercise 5.31: every vertex of a finite path graph has degree at most `2`. -/
theorem pathGraphDegree_le_two (n : ℕ) (v : Fin n) :
    (SimpleGraph.pathGraph n).degree v ≤ 2 := by
  classical
  cases n with
  | zero =>
      exact Fin.elim0 v
  | succ n =>
      have hpath :
          (SimpleGraph.pathGraph (n + 1)).degree v ≤ (SimpleGraph.cycleGraph (n + 1)).degree v := by
        exact SimpleGraph.degree_le_of_le
          (G := SimpleGraph.pathGraph (n + 1))
          (H := SimpleGraph.cycleGraph (n + 1))
          (v := v)
          SimpleGraph.pathGraph_le_cycleGraph
      cases n with
      | zero =>
          exact hpath.trans (by simp [SimpleGraph.cycleGraph_one_eq_bot])
      | succ n =>
          refine hpath.trans ?_
          rw [SimpleGraph.cycleGraph_degree_two_le]
          exact Finset.card_le_two

/-- Helper for Exercise 5.31: the origin vertex of a nonempty path graph has at most one
neighbor. -/
theorem pathGraphDegree_zero_le_one {n : ℕ} (hn : 0 < n) :
    (SimpleGraph.pathGraph n).degree ⟨0, hn⟩ ≤ 1 := by
  classical
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  cases m with
  | zero =>
      have hzero : (SimpleGraph.pathGraph 1).degree (0 : Fin 1) = 0 := by
        exact SimpleGraph.degree_eq_zero_of_subsingleton
          (G := SimpleGraph.pathGraph 1)
          (v := (0 : Fin 1))
      have horigin : (⟨0, hn⟩ : Fin 1) = 0 := by
        ext
        simp
      rw [horigin, hzero]
      norm_num
  | succ m =>
      have hdegree : (SimpleGraph.pathGraph (m + 2)).degree (0 : Fin (m + 2)) = 1 := by
        rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
        refine ⟨1, ?_, ?_⟩
        · simp [SimpleGraph.pathGraph_adj]
        · intro w hw
          rw [SimpleGraph.pathGraph_adj] at hw
          rcases hw with hw | hw
          · simpa [Fin.ext_iff] using hw.symm
          · exact (Nat.succ_ne_zero _ hw).elim
      exact hdegree.le

/-- Helper for Exercise 5.31: away from the diagonal, the stencil entry is `-1` exactly on grid
adjacencies and `0` otherwise. -/
theorem dirichletLaplacian_apply_offDiag (n_x n_y : ℕ)
    (j l : Fin n_y) (i k : Fin n_x) (hneq : (j, i) ≠ (l, k)) :
    Matrix.dirichletLaplacian n_x n_y (j, i) (l, k) =
      if (gridGraph n_x n_y).Adj (j, i) (l, k) then -1 else 0 := by
  classical
  by_cases hadj : (gridGraph n_x n_y).Adj (j, i) (l, k)
  · rw [if_pos hadj, dirichletLaplacian_apply]
    rw [gridGraph, SimpleGraph.boxProd_adj] at hadj
    rcases hadj with ⟨hjl, hik⟩ | ⟨hjl, hik⟩
    · rw [SimpleGraph.pathGraph_adj] at hjl
      cases hik
      rcases hjl with hjl | hjl
      · have hdx : (((i : ℕ) : ℤ) - ((i : ℕ) : ℤ)) = 0 := by
          norm_num
        have hdy : (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) = -1 := by
          have hjl' : (((j : ℕ) : ℤ) + 1) = ((l : ℕ) : ℤ) := by
            exact_mod_cast hjl
          linarith
        simp [Matrix.dirichletLaplacianKernel, hdy]
      · have hdx : (((i : ℕ) : ℤ) - ((i : ℕ) : ℤ)) = 0 := by
          norm_num
        have hdy : (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) = 1 := by
          have hjl' : (((l : ℕ) : ℤ) + 1) = ((j : ℕ) : ℤ) := by
            exact_mod_cast hjl
          linarith
        simp [Matrix.dirichletLaplacianKernel, hdy]
    · cases hik
      rw [SimpleGraph.pathGraph_adj] at hjl
      rcases hjl with hik | hik
      · have hdx : (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) = -1 := by
          have hik' : (((i : ℕ) : ℤ) + 1) = ((k : ℕ) : ℤ) := by
            exact_mod_cast hik
          linarith
        have hdy : (((j : ℕ) : ℤ) - ((j : ℕ) : ℤ)) = 0 := by
          norm_num
        simp [Matrix.dirichletLaplacianKernel, hdx]
      · have hdx : (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) = 1 := by
          have hik' : (((k : ℕ) : ℤ) + 1) = ((i : ℕ) : ℤ) := by
            exact_mod_cast hik
          linarith
        have hdy : (((j : ℕ) : ℤ) - ((j : ℕ) : ℤ)) = 0 := by
          norm_num
        simp [Matrix.dirichletLaplacianKernel, hdx]
  · rw [if_neg hadj]
    by_cases hj : j = l
    · by_cases hi : i = k
      · exact (hneq (by cases hj; cases hi; rfl)).elim
      · have hdy : (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) = 0 := by
          omega
        have hdx0 : (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) ≠ 0 := by
          omega
        have hnotx : ¬ (SimpleGraph.pathGraph n_x).Adj i k := by
          intro hik
          apply hadj
          rw [gridGraph, SimpleGraph.boxProd_adj]
          exact Or.inr ⟨hik, hj⟩
        rw [SimpleGraph.pathGraph_adj] at hnotx
        have hdx1 : (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) ≠ 1 := by
          intro hdx
          apply hnotx
          right
          omega
        have hdxm1 : (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) ≠ -1 := by
          intro hdx
          apply hnotx
          left
          omega
        rw [dirichletLaplacian_apply]
        simp [Matrix.dirichletLaplacianKernel, hdy, hdx0, hdx1, hdxm1]
    · by_cases hi : i = k
      · have hdx : (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) = 0 := by
          omega
        have hdy0 : (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) ≠ 0 := by
          omega
        have hnoty : ¬ (SimpleGraph.pathGraph n_y).Adj j l := by
          intro hik
          apply hadj
          rw [gridGraph, SimpleGraph.boxProd_adj]
          exact Or.inl ⟨hik, hi⟩
        rw [SimpleGraph.pathGraph_adj] at hnoty
        have hdy1 : (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) ≠ 1 := by
          intro hdy
          apply hnoty
          right
          omega
        have hdym1 : (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) ≠ -1 := by
          intro hdy
          apply hnoty
          left
          omega
        rw [dirichletLaplacian_apply]
        simp [Matrix.dirichletLaplacianKernel, hdx, hdy0, hdy1, hdym1]
      · have hdx0 : (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) ≠ 0 := by
          omega
        have hdy0 : (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) ≠ 0 := by
          omega
        rw [dirichletLaplacian_apply]
        simp [Matrix.dirichletLaplacianKernel, hdx0, hdy0]

/-- Helper for Exercise 5.31: the boundary weight is `4 - degree` when the degree is expressed
through the interior grid-graph API. -/
theorem dirichletBoundaryWeight_apply (n_x n_y : ℕ) (j : Fin n_y) (i : Fin n_x) :
    dirichletBoundaryWeight n_x n_y (j, i) =
      4 - (((gridGraph n_x n_y).degree (j, i) : ℝ)) := by
  rfl

/-- Helper for Exercise 5.31: the diagonal boundary correction contributes `4 - degree` at each
interior vertex. -/
theorem dirichletBoundaryDiagonal_apply_self (n_x n_y : ℕ) (ji : Fin n_y × Fin n_x) :
    Matrix.diagonal (dirichletBoundaryWeight n_x n_y) ji ji =
      4 - (((gridGraph n_x n_y).degree ji : ℝ)) := by
  rcases ji with ⟨j, i⟩
  -- Reduce the diagonal matrix entry to the already-normalized boundary weight formula.
  rw [Matrix.diagonal_apply_eq]
  simpa using dirichletBoundaryWeight_apply n_x n_y j i

/-- Helper for Exercise 5.31: on the diagonal, the grid Laplacian and boundary correction sum to
the stencil value `4`. -/
theorem gridLapMatrixAddBoundaryDiagonal_apply_self (n_x n_y : ℕ) (ji : Fin n_y × Fin n_x) :
    ((gridGraph n_x n_y).lapMatrix ℝ +
        Matrix.diagonal (dirichletBoundaryWeight n_x n_y)) ji ji = 4 := by
  -- Combine the diagonal Laplacian contribution with the diagonal boundary correction.
  have hself : (gridGraph n_x n_y).lapMatrix ℝ ji ji = (gridGraph n_x n_y).degree ji := by
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply]
    simpa using
      degree_eq_of_neighborFintype
        (G := gridGraph n_x n_y)
        (v := ji)
        (Subtype.fintype (Membership.mem ((gridGraph n_x n_y).neighborSet ji)))
        (SimpleGraph.boxProdFintypeNeighborSet
          (G := SimpleGraph.pathGraph n_y)
          (H := SimpleGraph.pathGraph n_x)
          (x := ji))
  rw [Matrix.add_apply, hself, dirichletBoundaryDiagonal_apply_self]
  nlinarith

/-- Helper for Exercise 5.31: `Matrix.dirichletLaplacian` is the product-grid graph Laplacian
plus the diagonal boundary correction `4 - degree`. -/
theorem dirichletLaplacian_eq_gridLapMatrix_add_boundaryDiagonal (n_x n_y : ℕ) :
    Matrix.dirichletLaplacian n_x n_y =
      (gridGraph n_x n_y).lapMatrix ℝ +
        Matrix.diagonal (dirichletBoundaryWeight n_x n_y) := by
  classical
  -- Normalize the concrete stencil entry-by-entry to the graph Laplacian plus diagonal form.
  ext a b
  rcases a with ⟨j, i⟩
  rcases b with ⟨l, k⟩
  by_cases h : (j, i) = (l, k)
  · cases h
    -- Route correction: keep the diagonal normalization behind helper lemmas instead of
    -- unfolding the box-product degree inside the main extensionality proof.
    rw [dirichletLaplacian_apply_self]
    symm
    -- On the diagonal, both sides are the same `4`-valued stencil entry.
    exact gridLapMatrixAddBoundaryDiagonal_apply_self n_x n_y (j, i)
  · rw [dirichletLaplacian_apply_offDiag n_x n_y j l i k h]
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
      gridGraph, h]
    split_ifs <;> norm_num

/-- Helper for Exercise 5.31: every boundary correction weight is nonnegative. -/
theorem dirichletBoundaryWeight_nonneg (n_x n_y : ℕ) (ji : Fin n_y × Fin n_x) :
    0 ≤ dirichletBoundaryWeight n_x n_y ji := by
  classical
  -- The box-product degree splits into the sum of two path-graph degrees, each bounded by `2`.
  have hdegree : (((SimpleGraph.pathGraph n_y □ SimpleGraph.pathGraph n_x).degree ji : ℝ) ≤ 4) := by
    rw [SimpleGraph.degree_boxProd]
    exact_mod_cast add_le_add
      (pathGraphDegree_le_two n_y ji.1)
      (pathGraphDegree_le_two n_x ji.2)
  have hweight :
      0 ≤ 4 - (((SimpleGraph.pathGraph n_y □ SimpleGraph.pathGraph n_x).degree ji : ℝ)) := by
    linarith
  simpa [dirichletBoundaryWeight] using hweight

/-- Helper for Exercise 5.31: the boundary correction is strictly positive at the origin vertex
once both grid side lengths are positive. -/
theorem dirichletBoundaryWeight_pos_origin {n_x n_y : ℕ} (hx : 0 < n_x) (hy : 0 < n_y) :
    let origin : Fin n_y × Fin n_x := (⟨0, hy⟩, ⟨0, hx⟩)
    0 < dirichletBoundaryWeight n_x n_y origin := by
  classical
  let origin : Fin n_y × Fin n_x := (⟨0, hy⟩, ⟨0, hx⟩)
  have hdegree :
      (((SimpleGraph.pathGraph n_y) □ (SimpleGraph.pathGraph n_x)).degree origin : ℝ) ≤ 2 := by
    -- At the origin, each path-graph factor contributes at most one neighbor.
    rw [SimpleGraph.degree_boxProd]
    exact_mod_cast add_le_add
      (pathGraphDegree_zero_le_one hy)
      (pathGraphDegree_zero_le_one hx)
  -- Convert the degree bound into strict positivity of `4 - degree`.
  have hweight :
      0 < 4 - (((SimpleGraph.pathGraph n_y) □ (SimpleGraph.pathGraph n_x)).degree origin : ℝ) := by
    linarith
  simpa [dirichletBoundaryWeight, origin] using hweight

/-- The Chapter 5 Dirichlet discrete Laplacian is symmetric. -/
theorem dirichletLaplacian_isSymm (n_x n_y : ℕ) :
    Matrix.IsSymm (Matrix.dirichletLaplacian n_x n_y) := by
  -- Route correction: use the graph-Laplacian plus diagonal decomposition instead of
  -- re-matching the stencil kernel under index reversal.
  simpa [dirichletLaplacian_eq_gridLapMatrix_add_boundaryDiagonal] using
    ((gridGraph n_x n_y).isSymm_lapMatrix (R := ℝ)).add (Matrix.isSymm_diagonal _)

/-- The Chapter 5 Dirichlet discrete Laplacian is positive semidefinite. -/
theorem dirichletLaplacian_posSemidef (n_x n_y : ℕ) :
    Matrix.PosSemidef (Matrix.dirichletLaplacian n_x n_y) := by
  classical
  -- Rewrite to the graph-Laplacian plus diagonal boundary correction and show each summand is
  -- positive semidefinite separately.
  have hgrid : Matrix.PosSemidef ((gridGraph n_x n_y).lapMatrix ℝ) :=
    (gridGraph n_x n_y).posSemidef_lapMatrix ℝ
  have hdiag :
      Matrix.PosSemidef (Matrix.diagonal (dirichletBoundaryWeight n_x n_y)) := by
    refine Matrix.PosSemidef.diagonal ?_
    intro ji
    exact dirichletBoundaryWeight_nonneg n_x n_y ji
  simpa [dirichletLaplacian_eq_gridLapMatrix_add_boundaryDiagonal] using hgrid.add hdiag

/-- The Chapter 5 Dirichlet discrete Laplacian is positive definite. -/
theorem dirichletLaplacian_posDef (n_x n_y : ℕ) :
    Matrix.PosDef (Matrix.dirichletLaplacian n_x n_y) := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- Positive definiteness is proved over `ℝ`, so symmetry is the needed Hermitian input.
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial, dirichletLaplacian_isSymm]
  · intro x hx
    let G := gridGraph n_x n_y
    let D := Matrix.diagonal (dirichletBoundaryWeight n_x n_y)
    -- A nonzero vector forces both grid dimensions to be positive, so the origin vertex exists.
    have hxPos : 0 < n_x := by
      by_contra hxPos
      have hxZero : n_x = 0 := Nat.eq_zero_of_not_pos hxPos
      apply hx
      ext ji
      exact Fin.elim0 (hxZero ▸ ji.2)
    have hyPos : 0 < n_y := by
      by_contra hyPos
      have hyZero : n_y = 0 := Nat.eq_zero_of_not_pos hyPos
      apply hx
      ext ji
      exact Fin.elim0 (hyZero ▸ ji.1)
    have hgrid : Matrix.PosSemidef (G.lapMatrix ℝ) := G.posSemidef_lapMatrix ℝ
    have hdiag : Matrix.PosSemidef D := by
      refine Matrix.PosSemidef.diagonal ?_
      intro ji
      simpa [D] using dirichletBoundaryWeight_nonneg n_x n_y ji
    have hnonneg :
        0 ≤ star x ⬝ᵥ (Matrix.dirichletLaplacian n_x n_y *ᵥ x) :=
      (dirichletLaplacian_posSemidef n_x n_y).dotProduct_mulVec_nonneg x
    have hne :
        star x ⬝ᵥ (Matrix.dirichletLaplacian n_x n_y *ᵥ x) ≠ 0 := by
      intro hzero
      have hsplit :
          star x ⬝ᵥ (Matrix.dirichletLaplacian n_x n_y *ᵥ x) =
            star x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) + star x ⬝ᵥ (D *ᵥ x) := by
        -- Expand the decomposition at the quadratic-form level once, then work with the two
        -- nonnegative summands separately.
        have hdecomp :=
          congrArg
            (fun A : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ =>
              star x ⬝ᵥ (A *ᵥ x))
            (dirichletLaplacian_eq_gridLapMatrix_add_boundaryDiagonal n_x n_y)
        simpa [G, D, Matrix.add_mulVec, dotProduct_add] using hdecomp
      let qGrid : ℝ := star x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x)
      let qDiag : ℝ := star x ⬝ᵥ (D *ᵥ x)
      have hqGridNonneg : 0 ≤ qGrid := by
        simpa [qGrid] using hgrid.dotProduct_mulVec_nonneg x
      have hqDiagNonneg : 0 ≤ qDiag := by
        simpa [qDiag] using hdiag.dotProduct_mulVec_nonneg x
      have hsumZero : qGrid + qDiag = 0 := by
        calc
          qGrid + qDiag = star x ⬝ᵥ (Matrix.dirichletLaplacian n_x n_y *ᵥ x) := by
            simpa [qGrid, qDiag] using hsplit.symm
          _ = 0 := hzero
      have hqGrid : qGrid = 0 := by
        linarith
      have hqDiag : qDiag = 0 := by
        linarith
      have hgridMulVecZero : G.lapMatrix ℝ *ᵥ x = 0 := by
        refine (hgrid.toLinearMap₂'_zero_iff x).mp ?_
        simpa [Matrix.toLinearMap₂'_apply', star_trivial, qGrid] using hqGrid
      have hdiagMulVecZero : D *ᵥ x = 0 := by
        refine (hdiag.toLinearMap₂'_zero_iff x).mp ?_
        simpa [Matrix.toLinearMap₂'_apply', star_trivial, qDiag] using hqDiag
      have hreachable :
          ∀ i j : Fin n_y × Fin n_x, G.Reachable i j → x i = x j :=
        (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable (x := x)).mp hgridMulVecZero
      have hconnected : G.Connected := gridGraph_connected hxPos hyPos
      let origin : Fin n_y × Fin n_x := (⟨0, hyPos⟩, ⟨0, hxPos⟩)
      have horigin :
          x origin = 0 := by
        have horiginMul : dirichletBoundaryWeight n_x n_y origin * x origin = 0 := by
          simpa [D, origin, Matrix.mulVec_diagonal] using congrFun hdiagMulVecZero origin
        exact (mul_eq_zero.mp horiginMul).resolve_left
          (ne_of_gt (by simpa [origin] using dirichletBoundaryWeight_pos_origin hxPos hyPos))
      apply hx
      funext ji
      exact (hreachable ji origin (hconnected.preconnected ji origin)).trans horigin
    exact lt_of_le_of_ne hnonneg hne.symm

end Matrix
