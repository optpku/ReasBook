/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_5_feasible_set

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n p : ℕ}

/- Definition 12.8 is `source-facing`: it introduces the polyhedral feasible region cut out by
`A x ≤ b` in `ℝ^n` and then reuses the chapter owner `projectionPoint` for orthogonal projection
onto that set.

Domain sampling for this file identifies the relevant owner abstractions as follows.
- `inequality_feasible_set` from Chapter 3 is the canonical owner for finitely many inequality
  constraints;
- orthogonal projection onto a nonempty closed convex set is already owned upstream in Chapter 3
  by `projectionPoint` and its derived API.

Primitive data are therefore only the matrix-induced constraint family
`(i, x) ↦ A.toEuclideanLin x i - b i`; the feasible set is derived from the Chapter 3 owner, and
the projection/minimizer facts stay upstream at that owner level rather than being repackaged as
parallel local theorems here. -/

/-- Definition 12.8. The polyhedral feasible set `S = {x ∈ ℝ^n | A x ≤ b}` associated to the
matrix inequality system `A x ≤ b`. -/
def polyhedral_projection_feasible_set
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  inequality_feasible_set (fun i x ↦ A.toEuclideanLin x i - b i)

/-- Helper for Definition 12.8: membership in the polyhedral feasible set means satisfying each
row inequality `A x ≤ b`. -/
@[simp] theorem mem_polyhedral_projection_feasible_set
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ polyhedral_projection_feasible_set A b ↔
      ∀ i : Fin p, A.toEuclideanLin x i ≤ b i := by
  -- Unfold the Chapter 3 feasible-set owner and translate each residual inequality rowwise.
  constructor
  · intro hx i
    exact sub_nonpos.mp (show A.toEuclideanLin x i - b i ≤ 0 from hx i)
  · intro hx i
    exact sub_nonpos.mpr (hx i)

/-- Helper for Definition 12.8: the polyhedral feasible set is exactly the set of points
satisfying every row inequality `A x ≤ b`. -/
theorem polyhedral_projection_feasible_set_eq_setOf
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) :
    polyhedral_projection_feasible_set A b =
      {x | ∀ i : Fin p, A.toEuclideanLin x i ≤ b i} := by
  -- Extensionality reduces the set equality to the rowwise membership characterization.
  ext x
  simp [mem_polyhedral_projection_feasible_set]

/- Definition 12.8 packages the feasible region `S = {x ∈ ℝ^n | A x ≤ b}` itself. The orthogonal
projection problem onto `S` is then handled by the upstream Chapter 3 owner `projectionPoint`
once nonemptiness, closedness, and convexity of `S` are supplied in later developments. -/

end
