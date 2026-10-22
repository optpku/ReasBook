/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_24.HTTB
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Prod

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

/-- Helper for Exercise 5.31: the interior `n_y × n_x` path-product graph whose graph Laplacian
captures the non-boundary part of `Matrix.dirichletLaplacian`. -/
def dirichletGridGraph (n_x n_y : ℕ) : SimpleGraph (Fin n_y × Fin n_x) :=
  SimpleGraph.pathGraph n_y □ SimpleGraph.pathGraph n_x

/-- Helper for Exercise 5.31: adjacency on finite path graphs is decidable. -/
noncomputable instance instDecidableRelPathGraphAdj (n : ℕ) :
    DecidableRel (SimpleGraph.pathGraph n).Adj := by
  classical
  infer_instance

/-- Helper for Exercise 5.31: adjacency on the interior grid graph is decidable. -/
noncomputable instance instDecidableRelDirichletGridGraphAdj (n_x n_y : ℕ) :
    DecidableRel (dirichletGridGraph n_x n_y).Adj := by
  classical
  infer_instance

/-- Helper for Exercise 5.31: the boundary-correction diagonal weight `4 - degree` attached to the
interior grid graph. -/
noncomputable def dirichletBoundaryWeight (n_x n_y : ℕ) : Fin n_y × Fin n_x → ℝ :=
  fun ji ↦ 4 - (((SimpleGraph.pathGraph n_y) □ (SimpleGraph.pathGraph n_x)).degree ji : ℝ)

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
      have hzero : (SimpleGraph.pathGraph 1).degree (⟨0, hn⟩ : Fin 1) = 0 := by
        exact SimpleGraph.degree_eq_zero_of_subsingleton
          (G := SimpleGraph.pathGraph 1)
          (v := (⟨0, hn⟩ : Fin 1))
      rw [hzero]
      omega
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
      if (dirichletGridGraph n_x n_y).Adj (j, i) (l, k) then -1 else 0 := by
  classical
  by_cases hadj : (dirichletGridGraph n_x n_y).Adj (j, i) (l, k)
  · rw [if_pos hadj, dirichletLaplacian_apply]
    rw [dirichletGridGraph, SimpleGraph.boxProd_adj] at hadj
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
          rw [dirichletGridGraph, SimpleGraph.boxProd_adj]
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
          rw [dirichletGridGraph, SimpleGraph.boxProd_adj]
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

/-- Helper for Exercise 5.31: the diagonal entry of the interior grid-graph Laplacian equals the
vertex degree. -/
theorem dirichletGridGraph_lapMatrix_apply_self (n_x n_y : ℕ) (ji : Fin n_y × Fin n_x) :
    (dirichletGridGraph n_x n_y).lapMatrix ℝ ji ji =
      (dirichletGridGraph n_x n_y).degree ji := by
  -- On the diagonal, the adjacency contribution vanishes by irreflexivity.
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply]

/-- Helper for Exercise 5.31: the degree of a fixed vertex is independent of which finitely-many
neighbors witness the same neighbor-set type. -/
theorem degree_eq_of_neighborFintype {V : Type*} (G : SimpleGraph V) (v : V)
    (inst₁ inst₂ : Fintype (G.neighborSet v)) :
    @SimpleGraph.degree V G v inst₁ = @SimpleGraph.degree V G v inst₂ := by
  -- Compare both degree spellings through the cardinality of the same neighbor-set type.
  calc
    @SimpleGraph.degree V G v inst₁ = @Fintype.card (G.neighborSet v) inst₁ := by
      exact (@SimpleGraph.card_neighborSet_eq_degree V G v inst₁).symm
    _ = @Fintype.card (G.neighborSet v) inst₂ := by
      exact @Fintype.card_congr (G.neighborSet v) (G.neighborSet v) inst₁ inst₂ (Equiv.refl _)
    _ = @SimpleGraph.degree V G v inst₂ := by
      exact @SimpleGraph.card_neighborSet_eq_degree V G v inst₂

/-- Helper for Exercise 5.31: the degree of the interior grid graph splits as the sum of the two
path-graph degrees. -/
theorem dirichletGridGraph_degree_boxProd (n_x n_y : ℕ) (j : Fin n_y) (i : Fin n_x) :
    (dirichletGridGraph n_x n_y).degree (j, i) =
      (SimpleGraph.pathGraph n_y).degree j + (SimpleGraph.pathGraph n_x).degree i := by
  classical
  let instDefault : Fintype ((dirichletGridGraph n_x n_y).neighborSet (j, i)) :=
    Subtype.fintype (Membership.mem ((dirichletGridGraph n_x n_y).neighborSet (j, i)))
  let instCanonical : Fintype ((dirichletGridGraph n_x n_y).neighborSet (j, i)) :=
    SimpleGraph.boxProdFintypeNeighborSet
      (G := SimpleGraph.pathGraph n_y)
      (H := SimpleGraph.pathGraph n_x)
      (x := (j, i))
  -- First bridge the default degree spelling to the canonical box-product neighbor-set fintype.
  have hdegree :
      @SimpleGraph.degree (Fin n_y × Fin n_x) (dirichletGridGraph n_x n_y) (j, i)
          instDefault =
        @SimpleGraph.degree (Fin n_y × Fin n_x) (dirichletGridGraph n_x n_y) (j, i)
          instCanonical := by
    exact
      degree_eq_of_neighborFintype
        (G := dirichletGridGraph n_x n_y)
        (v := (j, i))
        instDefault
        instCanonical
  -- With the canonical fintype fixed explicitly, the standard box-product degree formula applies.
  change
    @SimpleGraph.degree (Fin n_y × Fin n_x) (dirichletGridGraph n_x n_y) (j, i) instDefault =
      (SimpleGraph.pathGraph n_y).degree j + (SimpleGraph.pathGraph n_x).degree i
  exact hdegree.trans <| by
    simpa [dirichletGridGraph, instCanonical] using
      (SimpleGraph.degree_boxProd
        (G := SimpleGraph.pathGraph n_y)
        (H := SimpleGraph.pathGraph n_x)
        (x := (j, i)))

/-- Helper for Exercise 5.31: the boundary weight is `4 - degree` when the degree is expressed
through the interior grid-graph API. -/
theorem dirichletBoundaryWeight_apply (n_x n_y : ℕ) (j : Fin n_y) (i : Fin n_x) :
    dirichletBoundaryWeight n_x n_y (j, i) =
      4 - (((dirichletGridGraph n_x n_y).degree (j, i) : ℝ)) := by
  -- Rewrite both degree spellings to the same sum of path-graph degrees.
  rw [dirichletBoundaryWeight]
  have hbox :
      (((SimpleGraph.pathGraph n_y □ SimpleGraph.pathGraph n_x).degree (j, i) : ℕ) : ℝ) =
        ((SimpleGraph.pathGraph n_y).degree j : ℝ) +
          ((SimpleGraph.pathGraph n_x).degree i : ℝ) := by
    exact_mod_cast
      (SimpleGraph.degree_boxProd
        (G := SimpleGraph.pathGraph n_y)
        (H := SimpleGraph.pathGraph n_x)
        (x := (j, i)))
  have hgrid :
      (((dirichletGridGraph n_x n_y).degree (j, i) : ℕ) : ℝ) =
        ((SimpleGraph.pathGraph n_y).degree j : ℝ) +
          ((SimpleGraph.pathGraph n_x).degree i : ℝ) := by
    exact_mod_cast dirichletGridGraph_degree_boxProd n_x n_y j i
  calc
    4 - ↑((SimpleGraph.pathGraph n_y □ SimpleGraph.pathGraph n_x).degree (j, i))
        = 4 -
            (((SimpleGraph.pathGraph n_y).degree j : ℝ) +
              ((SimpleGraph.pathGraph n_x).degree i : ℝ)) := by
          rw [hbox]
    _ = 4 - ↑((dirichletGridGraph n_x n_y).degree (j, i)) := by
          rw [hgrid]

/-- Helper for Exercise 5.31: the diagonal boundary correction contributes `4 - degree` at each
interior vertex. -/
theorem dirichletBoundaryDiagonal_apply_self (n_x n_y : ℕ) (ji : Fin n_y × Fin n_x) :
    Matrix.diagonal (dirichletBoundaryWeight n_x n_y) ji ji =
      4 - (((dirichletGridGraph n_x n_y).degree ji : ℝ)) := by
  rcases ji with ⟨j, i⟩
  -- Reduce the diagonal matrix entry to the already-normalized boundary weight formula.
  rw [Matrix.diagonal_apply_eq]
  simpa using dirichletBoundaryWeight_apply n_x n_y j i

/-- Helper for Exercise 5.31: on the diagonal, the grid Laplacian and boundary correction sum to
the stencil value `4`. -/
theorem gridLapMatrixAddBoundaryDiagonal_apply_self (n_x n_y : ℕ) (ji : Fin n_y × Fin n_x) :
    ((dirichletGridGraph n_x n_y).lapMatrix ℝ +
        Matrix.diagonal (dirichletBoundaryWeight n_x n_y)) ji ji = 4 := by
  -- Combine the diagonal Laplacian contribution with the diagonal boundary correction.
  rw [Matrix.add_apply, dirichletGridGraph_lapMatrix_apply_self,
    dirichletBoundaryDiagonal_apply_self]
  ring

/-- Exercise 5.31: `Matrix.dirichletLaplacian` is the product-grid graph Laplacian plus the
diagonal boundary correction `4 - degree`. -/
theorem dirichletLaplacian_eq_gridLapMatrix_add_boundaryDiagonal (n_x n_y : ℕ) :
    Matrix.dirichletLaplacian n_x n_y =
      (dirichletGridGraph n_x n_y).lapMatrix ℝ +
        Matrix.diagonal (dirichletBoundaryWeight n_x n_y) := by
  classical
  -- Normalize the concrete stencil entry-by-entry to the graph Laplacian plus diagonal form.
  ext a b
  rcases a with ⟨j, i⟩
  rcases b with ⟨l, k⟩
  by_cases h : (j, i) = (l, k)
  · cases h
    -- Keep the diagonal normalization behind helper lemmas instead of unfolding degrees here.
    rw [dirichletLaplacian_apply_self]
    symm
    -- On the diagonal, both sides are the same `4`-valued stencil entry.
    exact gridLapMatrixAddBoundaryDiagonal_apply_self n_x n_y (j, i)
  · rw [dirichletLaplacian_apply_offDiag n_x n_y j l i k h]
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
      dirichletGridGraph, h]
    split_ifs <;> norm_num

end Matrix
