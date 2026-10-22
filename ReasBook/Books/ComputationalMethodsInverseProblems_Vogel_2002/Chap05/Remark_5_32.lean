/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_27.BCCB
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_31.DirichletLaplacian
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Remark_5_32.NeumannLaplacian

public section

/- Remark 5.32 (1). The homogeneous Dirichlet replacement is represented by the
exact Chapter 5 owner `Matrix.dirichletLaplacian`; by construction it is the
nonperiodic HTTB/BTTB operator obtained by removing the periodic wrap-around
couplings. -/
#check Matrix.dirichletLaplacian

/- Remark 5.32 (2). The homogeneous Neumann, or no-flux, replacement is
represented by `Matrix.neumannLaplacian`; the source clause that each row of
`L` sums to zero is recorded by
`Matrix.neumannLaplacian_mulVecOne_eqZero`. The BCCB periodicity surface needed
for the non-BCCB comparison is the canonical Chapter 5 companion theorem
`Matrix.bccb_apply_eq_of_sub_eq_sub`. -/
#check Matrix.neumannLaplacian
#check Matrix.neumannLaplacian_mulVecOne_eqZero
#check Matrix.bccb_apply_eq_of_sub_eq_sub

namespace Matrix

/-- Internal x-direction witness for Remark 5.32 (3): a Dirichlet stencil entry
breaks the BCCB wrap-around periodicity in the `x` direction once `n_x > 2`. -/
private theorem dirichletLaplacian_ne_bccb_of_x {n_x n_y : ℕ}
    (h_x : 2 < n_x) (h_y : 0 < n_y) (c : Matrix (Fin n_x) (Fin n_y) ℝ) :
    Matrix.dirichletLaplacian n_x n_y ≠ Matrix.bccb c := by
  obtain ⟨m, rfl⟩ : ∃ m, n_x = m + 3 := by
    exact ⟨n_x - 3, by omega⟩
  intro h_eq
  let j0 : Fin n_y := ⟨0, h_y⟩
  have h_periodic :
      Matrix.bccb c (j0, (1 : Fin (m + 3))) (j0, 0) =
        Matrix.bccb c (j0, 0) (j0, Fin.last (m + 2)) := by
    apply Matrix.bccb_apply_eq_of_sub_eq_sub c
    · calc
        (1 : Fin (m + 3)) - 0 = (1 : Fin (m + 3)) := by simp
        _ = -Fin.last (m + 2) := by simp
        _ = 0 - Fin.last (m + 2) := by simp
    · rfl
  have h_left : Matrix.dirichletLaplacian (m + 3) n_y (j0, (1 : Fin (m + 3))) (j0, 0) = -1 := by
    have hneq : (j0, (1 : Fin (m + 3))) ≠ (j0, 0) := by
      intro hji
      have : (1 : Fin (m + 3)) = 0 := congrArg Prod.snd hji
      simp at this
    rw [Matrix.dirichletLaplacian_apply_offDiag (m + 3) n_y j0 j0 (1 : Fin (m + 3)) 0 hneq]
    have hadj : (Matrix.gridGraph (m + 3) n_y).Adj (j0, (1 : Fin (m + 3))) (j0, 0) := by
      rw [Matrix.gridGraph, SimpleGraph.boxProd_adj]
      refine Or.inr ⟨?_, rfl⟩
      rw [SimpleGraph.pathGraph_adj]
      right
      rfl
    rw [if_pos hadj]
  have h_right :
      Matrix.dirichletLaplacian (m + 3) n_y (j0, 0) (j0, Fin.last (m + 2)) = 0 := by
    have hneq : (j0, (0 : Fin (m + 3))) ≠ (j0, Fin.last (m + 2)) := by
      intro hji
      have : (0 : Fin (m + 3)) = Fin.last (m + 2) := congrArg Prod.snd hji
      simp at this
    rw [Matrix.dirichletLaplacian_apply_offDiag (m + 3) n_y j0 j0 0 (Fin.last (m + 2)) hneq]
    have hnotadj :
        ¬ (Matrix.gridGraph (m + 3) n_y).Adj (j0, (0 : Fin (m + 3))) (j0, Fin.last (m + 2)) := by
      have hnotadjLast :
          ¬ (SimpleGraph.pathGraph (m + 3)).Adj (0 : Fin (m + 3)) (Fin.last (m + 2)) := by
        rw [SimpleGraph.pathGraph_adj]
        simp [Fin.last]
      intro hadj
      rw [Matrix.gridGraph, SimpleGraph.boxProd_adj] at hadj
      rcases hadj with ⟨hyAdj, _⟩ | ⟨hxAdj, _⟩
      · exact hyAdj.ne rfl
      · exact hnotadjLast hxAdj
    rw [if_neg hnotadj]
  have h_dirichlet :
      Matrix.dirichletLaplacian (m + 3) n_y (j0, (1 : Fin (m + 3))) (j0, 0) =
        Matrix.dirichletLaplacian (m + 3) n_y (j0, 0) (j0, Fin.last (m + 2)) := by
    calc
      Matrix.dirichletLaplacian (m + 3) n_y (j0, (1 : Fin (m + 3))) (j0, 0) =
          Matrix.bccb c (j0, (1 : Fin (m + 3))) (j0, 0) := by
            exact congrArg (fun M ↦ M (j0, (1 : Fin (m + 3))) (j0, 0)) h_eq
      _ = Matrix.bccb c (j0, 0) (j0, Fin.last (m + 2)) := h_periodic
      _ = Matrix.dirichletLaplacian (m + 3) n_y (j0, 0) (j0, Fin.last (m + 2)) := by
            exact congrArg (fun M ↦ M (j0, 0) (j0, Fin.last (m + 2))) h_eq |>.symm
  rw [h_left, h_right] at h_dirichlet
  norm_num at h_dirichlet

/-- Internal y-direction witness for Remark 5.32 (3): a Dirichlet stencil entry
breaks the BCCB wrap-around periodicity in the `y` direction once `n_y > 2`. -/
private theorem dirichletLaplacian_ne_bccb_of_y {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 2 < n_y) (c : Matrix (Fin n_x) (Fin n_y) ℝ) :
    Matrix.dirichletLaplacian n_x n_y ≠ Matrix.bccb c := by
  obtain ⟨m, rfl⟩ : ∃ m, n_y = m + 3 := by
    exact ⟨n_y - 3, by omega⟩
  intro h_eq
  let j0 : Fin (m + 3) := 0
  let i0 : Fin n_x := ⟨0, h_x⟩
  have h_periodic :
      Matrix.bccb c ((1 : Fin (m + 3)), i0) (j0, i0) =
        Matrix.bccb c (j0, i0) (Fin.last (m + 2), i0) := by
    apply Matrix.bccb_apply_eq_of_sub_eq_sub c
    · rfl
    · calc
        (1 : Fin (m + 3)) - 0 = (1 : Fin (m + 3)) := by simp
        _ = -Fin.last (m + 2) := by simp
        _ = 0 - Fin.last (m + 2) := by simp
  have h_left : Matrix.dirichletLaplacian n_x (m + 3) ((1 : Fin (m + 3)), i0) (j0, i0) = -1 := by
    have hneq : ((1 : Fin (m + 3)), i0) ≠ (j0, i0) := by
      intro hji
      have : (1 : Fin (m + 3)) = 0 := congrArg Prod.fst hji
      simp at this
    rw [Matrix.dirichletLaplacian_apply_offDiag n_x (m + 3) (1 : Fin (m + 3)) j0 i0 i0 hneq]
    have hadj : (Matrix.gridGraph n_x (m + 3)).Adj ((1 : Fin (m + 3)), i0) (j0, i0) := by
      rw [Matrix.gridGraph, SimpleGraph.boxProd_adj]
      refine Or.inl ⟨?_, rfl⟩
      dsimp [j0]
      rw [SimpleGraph.pathGraph_adj]
      right
      rfl
    rw [if_pos hadj]
  have h_right :
      Matrix.dirichletLaplacian n_x (m + 3) (j0, i0) (Fin.last (m + 2), i0) = 0 := by
    have hneq : (j0, i0) ≠ (Fin.last (m + 2), i0) := by
      intro hji
      have : (0 : Fin (m + 3)) = Fin.last (m + 2) := congrArg Prod.fst hji
      simp at this
    rw [Matrix.dirichletLaplacian_apply_offDiag n_x (m + 3) j0 (Fin.last (m + 2)) i0 i0 hneq]
    have hnotadj :
        ¬ (Matrix.gridGraph n_x (m + 3)).Adj (j0, i0) (Fin.last (m + 2), i0) := by
      have hnotadjLast :
          ¬ (SimpleGraph.pathGraph (m + 3)).Adj (0 : Fin (m + 3)) (Fin.last (m + 2)) := by
        rw [SimpleGraph.pathGraph_adj]
        simp [Fin.last]
      intro hadj
      rw [Matrix.gridGraph, SimpleGraph.boxProd_adj] at hadj
      rcases hadj with ⟨hyAdj, _⟩ | ⟨hxAdj, _⟩
      · exact hnotadjLast hyAdj
      · exact hxAdj.ne rfl
    rw [if_neg hnotadj]
  have h_dirichlet :
      Matrix.dirichletLaplacian n_x (m + 3) ((1 : Fin (m + 3)), i0) (j0, i0) =
        Matrix.dirichletLaplacian n_x (m + 3) (j0, i0) (Fin.last (m + 2), i0) := by
    calc
      Matrix.dirichletLaplacian n_x (m + 3) ((1 : Fin (m + 3)), i0) (j0, i0) =
          Matrix.bccb c ((1 : Fin (m + 3)), i0) (j0, i0) := by
            exact congrArg (fun M ↦ M ((1 : Fin (m + 3)), i0) (j0, i0)) h_eq
      _ = Matrix.bccb c (j0, i0) (Fin.last (m + 2), i0) := h_periodic
      _ = Matrix.dirichletLaplacian n_x (m + 3) (j0, i0) (Fin.last (m + 2), i0) := by
            exact congrArg (fun M ↦ M (j0, i0) (Fin.last (m + 2), i0)) h_eq |>.symm
  rw [h_left, h_right] at h_dirichlet
  norm_num at h_dirichlet

/-- Internal x-direction witness for Remark 5.32 (4): a Neumann stencil entry
breaks the BCCB wrap-around periodicity in the `x` direction once `n_x > 2`. -/
private theorem neumannLaplacian_ne_bccb_of_x {n_x n_y : ℕ}
    (h_x : 2 < n_x) (h_y : 0 < n_y) (c : Matrix (Fin n_x) (Fin n_y) ℝ) :
    Matrix.neumannLaplacian n_x n_y ≠ Matrix.bccb c := by
  obtain ⟨m, rfl⟩ : ∃ m, n_x = m + 3 := by
    exact ⟨n_x - 3, by omega⟩
  intro h_eq
  let j0 : Fin n_y := ⟨0, h_y⟩
  have h_periodic :
      Matrix.bccb c (j0, (1 : Fin (m + 3))) (j0, 0) =
        Matrix.bccb c (j0, 0) (j0, Fin.last (m + 2)) := by
    apply Matrix.bccb_apply_eq_of_sub_eq_sub c
    · calc
        (1 : Fin (m + 3)) - 0 = (1 : Fin (m + 3)) := by simp
        _ = -Fin.last (m + 2) := by simp
        _ = 0 - Fin.last (m + 2) := by simp
    · rfl
  have h_left : Matrix.neumannLaplacian (m + 3) n_y (j0, (1 : Fin (m + 3))) (j0, 0) = -1 := by
    have hneq : (j0, (1 : Fin (m + 3))) ≠ (j0, 0) := by
      intro hji
      have : (1 : Fin (m + 3)) = 0 := congrArg Prod.snd hji
      simp at this
    have hadj : (Matrix.gridGraph (m + 3) n_y).Adj (j0, (1 : Fin (m + 3))) (j0, 0) := by
      rw [Matrix.gridGraph, SimpleGraph.boxProd_adj]
      refine Or.inr ⟨?_, rfl⟩
      rw [SimpleGraph.pathGraph_adj]
      right
      rfl
    rw [Matrix.neumannLaplacian_eqGridLapMatrix, SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, Matrix.diagonal_apply_ne _ hneq,
      SimpleGraph.adjMatrix_apply, if_pos hadj]
    norm_num
  have h_right :
      Matrix.neumannLaplacian (m + 3) n_y (j0, 0) (j0, Fin.last (m + 2)) = 0 := by
    have hneq : (j0, (0 : Fin (m + 3))) ≠ (j0, Fin.last (m + 2)) := by
      intro hji
      have : (0 : Fin (m + 3)) = Fin.last (m + 2) := congrArg Prod.snd hji
      simp at this
    have hnotadj :
        ¬ (Matrix.gridGraph (m + 3) n_y).Adj (j0, (0 : Fin (m + 3))) (j0, Fin.last (m + 2)) := by
      have hnotadjLast :
          ¬ (SimpleGraph.pathGraph (m + 3)).Adj (0 : Fin (m + 3)) (Fin.last (m + 2)) := by
        rw [SimpleGraph.pathGraph_adj]
        simp [Fin.last]
      intro hadj
      rw [Matrix.gridGraph, SimpleGraph.boxProd_adj] at hadj
      rcases hadj with ⟨hyAdj, _⟩ | ⟨hxAdj, _⟩
      · exact hyAdj.ne rfl
      · exact hnotadjLast hxAdj
    rw [Matrix.neumannLaplacian_eqGridLapMatrix, SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, Matrix.diagonal_apply_ne _ hneq,
      SimpleGraph.adjMatrix_apply, if_neg hnotadj]
    norm_num
  have h_neumann :
      Matrix.neumannLaplacian (m + 3) n_y (j0, (1 : Fin (m + 3))) (j0, 0) =
        Matrix.neumannLaplacian (m + 3) n_y (j0, 0) (j0, Fin.last (m + 2)) := by
    calc
      Matrix.neumannLaplacian (m + 3) n_y (j0, (1 : Fin (m + 3))) (j0, 0) =
          Matrix.bccb c (j0, (1 : Fin (m + 3))) (j0, 0) := by
            exact congrArg (fun M ↦ M (j0, (1 : Fin (m + 3))) (j0, 0)) h_eq
      _ = Matrix.bccb c (j0, 0) (j0, Fin.last (m + 2)) := h_periodic
      _ = Matrix.neumannLaplacian (m + 3) n_y (j0, 0) (j0, Fin.last (m + 2)) := by
            exact congrArg (fun M ↦ M (j0, 0) (j0, Fin.last (m + 2))) h_eq |>.symm
  rw [h_left, h_right] at h_neumann
  norm_num at h_neumann

/-- Internal y-direction witness for Remark 5.32 (4): a Neumann stencil entry
breaks the BCCB wrap-around periodicity in the `y` direction once `n_y > 2`. -/
private theorem neumannLaplacian_ne_bccb_of_y {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 2 < n_y) (c : Matrix (Fin n_x) (Fin n_y) ℝ) :
    Matrix.neumannLaplacian n_x n_y ≠ Matrix.bccb c := by
  obtain ⟨m, rfl⟩ : ∃ m, n_y = m + 3 := by
    exact ⟨n_y - 3, by omega⟩
  intro h_eq
  let j0 : Fin (m + 3) := 0
  let i0 : Fin n_x := ⟨0, h_x⟩
  have h_periodic :
      Matrix.bccb c ((1 : Fin (m + 3)), i0) (j0, i0) =
        Matrix.bccb c (j0, i0) (Fin.last (m + 2), i0) := by
    apply Matrix.bccb_apply_eq_of_sub_eq_sub c
    · rfl
    · calc
        (1 : Fin (m + 3)) - 0 = (1 : Fin (m + 3)) := by simp
        _ = -Fin.last (m + 2) := by simp
        _ = 0 - Fin.last (m + 2) := by simp
  have h_left : Matrix.neumannLaplacian n_x (m + 3) ((1 : Fin (m + 3)), i0) (j0, i0) = -1 := by
    have hneq : ((1 : Fin (m + 3)), i0) ≠ (j0, i0) := by
      intro hji
      have : (1 : Fin (m + 3)) = 0 := congrArg Prod.fst hji
      simp at this
    have hadj : (Matrix.gridGraph n_x (m + 3)).Adj ((1 : Fin (m + 3)), i0) (j0, i0) := by
      rw [Matrix.gridGraph, SimpleGraph.boxProd_adj]
      refine Or.inl ⟨?_, rfl⟩
      dsimp [j0]
      rw [SimpleGraph.pathGraph_adj]
      right
      rfl
    rw [Matrix.neumannLaplacian_eqGridLapMatrix, SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, Matrix.diagonal_apply_ne _ hneq,
      SimpleGraph.adjMatrix_apply, if_pos hadj]
    norm_num
  have h_right :
      Matrix.neumannLaplacian n_x (m + 3) (j0, i0) (Fin.last (m + 2), i0) = 0 := by
    have hneq : (j0, i0) ≠ (Fin.last (m + 2), i0) := by
      intro hji
      have : (0 : Fin (m + 3)) = Fin.last (m + 2) := congrArg Prod.fst hji
      simp at this
    have hnotadj :
        ¬ (Matrix.gridGraph n_x (m + 3)).Adj (j0, i0) (Fin.last (m + 2), i0) := by
      have hnotadjLast :
          ¬ (SimpleGraph.pathGraph (m + 3)).Adj (0 : Fin (m + 3)) (Fin.last (m + 2)) := by
        rw [SimpleGraph.pathGraph_adj]
        simp [Fin.last]
      intro hadj
      rw [Matrix.gridGraph, SimpleGraph.boxProd_adj] at hadj
      rcases hadj with ⟨hyAdj, _⟩ | ⟨hxAdj, _⟩
      · exact hnotadjLast hyAdj
      · exact hxAdj.ne rfl
    rw [Matrix.neumannLaplacian_eqGridLapMatrix, SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, Matrix.diagonal_apply_ne _ hneq,
      SimpleGraph.adjMatrix_apply, if_neg hnotadj]
    norm_num
  have h_neumann :
      Matrix.neumannLaplacian n_x (m + 3) ((1 : Fin (m + 3)), i0) (j0, i0) =
        Matrix.neumannLaplacian n_x (m + 3) (j0, i0) (Fin.last (m + 2), i0) := by
    calc
      Matrix.neumannLaplacian n_x (m + 3) ((1 : Fin (m + 3)), i0) (j0, i0) =
          Matrix.bccb c ((1 : Fin (m + 3)), i0) (j0, i0) := by
            exact congrArg (fun M ↦ M ((1 : Fin (m + 3)), i0) (j0, i0)) h_eq
      _ = Matrix.bccb c (j0, i0) (Fin.last (m + 2), i0) := h_periodic
      _ = Matrix.neumannLaplacian n_x (m + 3) (j0, i0) (Fin.last (m + 2), i0) := by
            exact congrArg (fun M ↦ M (j0, i0) (Fin.last (m + 2), i0)) h_eq |>.symm
  rw [h_left, h_right] at h_neumann
  norm_num at h_neumann

/-- Remark 5.32 (3), fixed-generator form: for a positive grid, if at least one
grid direction has length greater than `2`, then the Dirichlet replacement
cannot equal any BCCB matrix generated by `c`. -/
theorem dirichletLaplacian_ne_bccb {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y) (h_nonperiodic : 2 < n_x ∨ 2 < n_y)
    (c : Matrix (Fin n_x) (Fin n_y) ℝ) :
    Matrix.dirichletLaplacian n_x n_y ≠ Matrix.bccb c := by
  rcases h_nonperiodic with h_nonperiodic | h_nonperiodic
  · exact dirichletLaplacian_ne_bccb_of_x h_nonperiodic h_y c
  · exact dirichletLaplacian_ne_bccb_of_y h_x h_nonperiodic c

/-- Remark 5.32 (3). For a positive grid, if at least one grid direction has
length greater than `2`, then the Dirichlet replacement is no longer BCCB. -/
theorem dirichletLaplacian_not_bccb {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y)
    (h_nonperiodic : 2 < n_x ∨ 2 < n_y) :
    ¬ ∃ c : Matrix (Fin n_x) (Fin n_y) ℝ,
      Matrix.dirichletLaplacian n_x n_y = Matrix.bccb c := by
  intro h_bccb
  rcases h_bccb with ⟨c, hc⟩
  exact dirichletLaplacian_ne_bccb h_x h_y h_nonperiodic c hc

/-- Remark 5.32 (4), fixed-generator form: for a positive grid, if at least one
grid direction has length greater than `2`, then the Neumann replacement
cannot equal any BCCB matrix generated by `c`. -/
theorem neumannLaplacian_ne_bccb {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y) (h_nonperiodic : 2 < n_x ∨ 2 < n_y)
    (c : Matrix (Fin n_x) (Fin n_y) ℝ) :
    Matrix.neumannLaplacian n_x n_y ≠ Matrix.bccb c := by
  rcases h_nonperiodic with h_nonperiodic | h_nonperiodic
  · exact neumannLaplacian_ne_bccb_of_x h_nonperiodic h_y c
  · exact neumannLaplacian_ne_bccb_of_y h_x h_nonperiodic c

/-- Remark 5.32 (4). For a positive grid, if at least one grid direction has
length greater than `2`, then the Neumann replacement is no longer BCCB. -/
theorem neumannLaplacian_not_bccb {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y)
    (h_nonperiodic : 2 < n_x ∨ 2 < n_y) :
    ¬ ∃ c : Matrix (Fin n_x) (Fin n_y) ℝ,
      Matrix.neumannLaplacian n_x n_y = Matrix.bccb c := by
  intro h_bccb
  rcases h_bccb with ⟨c, hc⟩
  exact neumannLaplacian_ne_bccb h_x h_y h_nonperiodic c hc

end Matrix
