/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_31.DirichletLaplacian

public section
namespace Matrix

/-- The interior path-product grid used by the Dirichlet Laplacian. -/
abbrev dirichletGridGraph (n_x n_y : ℕ) : SimpleGraph (Fin n_y × Fin n_x) :=
  gridGraph n_x n_y

/-- The diagonal of the interior grid Laplacian records the vertex degree. -/
theorem dirichletGridGraph_lapMatrix_apply_self (n_x n_y : ℕ) (ji : Fin n_y × Fin n_x) :
    (dirichletGridGraph n_x n_y).lapMatrix ℝ ji ji =
      (dirichletGridGraph n_x n_y).degree ji := by
  simp only [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
    Matrix.diagonal_apply_eq, SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl, if_false, sub_zero]
  exact_mod_cast degree_eq_of_neighborFintype (dirichletGridGraph n_x n_y) ji _ _

/-- The degree of the grid is the sum of the degrees in its two path factors. -/
theorem dirichletGridGraph_degree_boxProd (n_x n_y : ℕ) (j : Fin n_y) (i : Fin n_x) :
    (dirichletGridGraph n_x n_y).degree (j, i) =
      (SimpleGraph.pathGraph n_y).degree j + (SimpleGraph.pathGraph n_x).degree i :=
  gridGraph_degree_boxProd n_x n_y j i

end Matrix
