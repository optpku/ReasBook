/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped StandardSimplex

variable {n m : ℕ+}

/-- The data of a simplex saddle-point problem used in Definition 6.12 consists of a matrix
`A : ℝⁿ → ℝᵐ` and linear terms `c ∈ ℝⁿ` and `b ∈ ℝᵐ`. -/
structure SimplexSaddlePointProblem (n m : ℕ+) where
  /-- The matrix `A : ℝⁿ → ℝᵐ` defining the bilinear coupling term. -/
  matrix : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ
  /-- The primal linear term `c ∈ ℝⁿ`. -/
  primalLinearTerm : EuclideanSpace ℝ (Fin (n : ℕ))
  /-- The dual linear term `b ∈ ℝᵐ`. -/
  dualLinearTerm : EuclideanSpace ℝ (Fin (m : ℕ))

namespace SimplexSaddlePointProblem

local notation "Eₙ" => EuclideanSpace ℝ (Fin (n : ℕ))
local notation "Eₘ" => EuclideanSpace ℝ (Fin (m : ℕ))

/-- The canonical Euclidean linear map induced by the matrix `A`. -/
abbrev linearMap (problem : SimplexSaddlePointProblem n m) : Eₙ →ₗ[ℝ] Eₘ :=
  problem.matrix.toEuclideanLin

/-- Helper for Definition 6.12: the Euclidean-coordinate preimage of `stdSimplex ℝ ι` is compact.
-/
private theorem euclideanPreimageStdSimplexIsCompact
    (ι : Type*) [Fintype ι] :
    IsCompact ((EuclideanSpace.equiv ι ℝ) ⁻¹' stdSimplex ℝ ι) := by
  -- Transport compactness across the coordinate homeomorphism to keep the simplex owner canonical.
  simpa using
    (EuclideanSpace.equiv ι ℝ).toHomeomorph.isCompact_preimage.2 (isCompact_stdSimplex ℝ ι)

/-- Helper for Definition 6.12: the Euclidean-coordinate preimage of `stdSimplex ℝ ι` is closed.
-/
private theorem euclideanPreimageStdSimplexIsClosed
    (ι : Type*) [Fintype ι] :
    IsClosed ((EuclideanSpace.equiv ι ℝ) ⁻¹' stdSimplex ℝ ι) := by
  -- Closedness is likewise transported through the coordinate homeomorphism.
  simpa using
    (EuclideanSpace.equiv ι ℝ).toHomeomorph.isClosed_preimage.2 (isClosed_stdSimplex ℝ ι)

/-- Helper for Definition 6.12: the Euclidean-coordinate preimage of `stdSimplex ℝ ι` is convex.
-/
private theorem euclideanPreimageStdSimplexConvex
    (ι : Type*) [Fintype ι] :
    Convex ℝ ((EuclideanSpace.equiv ι ℝ) ⁻¹' stdSimplex ℝ ι) := by
  -- Convexity is preserved under preimage by the coordinate linear equivalence.
  simpa using
    (convex_stdSimplex ℝ ι).linear_preimage (EuclideanSpace.equiv ι ℝ).toLinearEquiv.toLinearMap

/-- Helper for Definition 6.12: the primal linear term is continuous on the Euclidean simplex
preimage. -/
private theorem smoothPartContinuousOn (problem : SimplexSaddlePointProblem n m) :
    ContinuousOn
      (InnerProductSpace.toDualMap ℝ Eₙ problem.primalLinearTerm)
      ((EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) ⁻¹' Δ[n]) := by
  -- A continuous linear functional stays continuous when restricted to the feasible set.
  simpa using
    (InnerProductSpace.toDualMap ℝ Eₙ problem.primalLinearTerm).continuous.continuousOn

/-- Helper for Definition 6.12: the primal linear term is convex on the Euclidean simplex
preimage. -/
private theorem smoothPartConvexOn (problem : SimplexSaddlePointProblem n m) :
    ConvexOn ℝ
      ((EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) ⁻¹' Δ[n])
      (InnerProductSpace.toDualMap ℝ Eₙ problem.primalLinearTerm) := by
  -- Linear functionals are convex on every convex set, so we reuse the simplex preimage geometry.
  simpa using
    (InnerProductSpace.toDualMap ℝ Eₙ problem.primalLinearTerm).toLinearMap.convexOn
      (euclideanPreimageStdSimplexConvex (ι := Fin (n : ℕ)))

/-- Helper for Definition 6.12: the negated dual linear term is continuous on the Euclidean
simplex preimage. -/
private theorem dualPenaltyContinuousOn (problem : SimplexSaddlePointProblem n m) :
    ContinuousOn
      (-InnerProductSpace.toDualMap ℝ Eₘ problem.dualLinearTerm)
      ((EuclideanSpace.equiv (Fin (m : ℕ)) ℝ) ⁻¹' Δ[m]) := by
  -- Negating a continuous linear functional preserves continuity on the feasible set.
  simpa using
    ((InnerProductSpace.toDualMap ℝ Eₘ problem.dualLinearTerm).continuous.continuousOn.neg :
      ContinuousOn
        (fun u : Eₘ ↦ -(InnerProductSpace.toDualMap ℝ Eₘ problem.dualLinearTerm u))
        ((EuclideanSpace.equiv (Fin (m : ℕ)) ℝ) ⁻¹' Δ[m]))

/-- Helper for Definition 6.12: the negated dual linear term is convex on the Euclidean simplex
preimage. -/
private theorem dualPenaltyConvexOn (problem : SimplexSaddlePointProblem n m) :
    ConvexOn ℝ
      ((EuclideanSpace.equiv (Fin (m : ℕ)) ℝ) ⁻¹' Δ[m])
      (-InnerProductSpace.toDualMap ℝ Eₘ problem.dualLinearTerm) := by
  -- The negative of a linear functional is still linear, hence convex on the dual feasible set.
  exact
    (-InnerProductSpace.toDualMap ℝ Eₘ problem.dualLinearTerm).toLinearMap.convexOn
      (euclideanPreimageStdSimplexConvex (ι := Fin (m : ℕ)))

/-- Definition 6.12: [Simplex saddle-point problem and primal--dual nonsmooth forms] the simplex
saddle-point problem determined by `A`, `c`, and `b` induces the corresponding Chapter 6
structured objective model on the Euclidean simplices `Δ_n` and `Δ_m`. -/
def toStructuredObjectiveModel (problem : SimplexSaddlePointProblem n m) :
    StructuredObjectiveModel Eₙ Eₘ where
  primalSet := (EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) ⁻¹' Δ[n]
  primalSet_bounded :=
    (euclideanPreimageStdSimplexIsCompact (ι := Fin (n : ℕ))).isBounded
  primalSet_closed := euclideanPreimageStdSimplexIsClosed (ι := Fin (n : ℕ))
  primalSet_convex := euclideanPreimageStdSimplexConvex (ι := Fin (n : ℕ))
  dualSet := (EuclideanSpace.equiv (Fin (m : ℕ)) ℝ) ⁻¹' Δ[m]
  dualSet_bounded :=
    (euclideanPreimageStdSimplexIsCompact (ι := Fin (m : ℕ))).isBounded
  dualSet_closed := euclideanPreimageStdSimplexIsClosed (ι := Fin (m : ℕ))
  dualSet_convex := euclideanPreimageStdSimplexConvex (ι := Fin (m : ℕ))
  smoothPart := InnerProductSpace.toDualMap ℝ Eₙ problem.primalLinearTerm
  dualPenalty := -InnerProductSpace.toDualMap ℝ Eₘ problem.dualLinearTerm
  linearMap :=
    (InnerProductSpace.toDual ℝ Eₘ).toContinuousLinearMap.comp
      problem.linearMap.toContinuousLinearMap
  smoothPart_continuous := smoothPartContinuousOn problem
  smoothPart_convex := smoothPartConvexOn problem
  dualPenalty_continuous := dualPenaltyContinuousOn problem
  dualPenalty_convex := dualPenaltyConvexOn problem

/-- The simplex saddle-function
`(x, u) ↦ ⟪A x, u⟫ + ⟪c, x⟫ + ⟪b, u⟫` on `Δ_n × Δ_m`. -/
def saddleFunction (problem : SimplexSaddlePointProblem n m) :
    Δ[n] → Δ[m] → ℝ :=
  fun x u ↦
    dotProduct (problem.matrix.mulVec x.1) u.1 +
      dotProduct problem.primalLinearTerm x.1 +
      dotProduct problem.dualLinearTerm u.1

/-- A simplex saddle-point problem can be evaluated as its canonical saddle function on
`Δ_n × Δ_m`. -/
instance : CoeFun (SimplexSaddlePointProblem n m) (fun _ ↦
    Δ[n] → Δ[m] → ℝ) where
  coe problem := problem.saddleFunction

/-- The primal nonsmooth objective
`x ↦ ⟪c, x⟫ + max_j {⟪a_j, x⟫ + b^(j)}` on `Δ_n`. -/
def primalObjective (problem : SimplexSaddlePointProblem n m) :
    Δ[n] → ℝ :=
  fun x ↦
    dotProduct problem.primalLinearTerm x.1 +
      Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (m : ℕ) ↦ dotProduct (problem.matrix j) x.1 + problem.dualLinearTerm j)

/-- The dual nonsmooth objective
`u ↦ ⟪b, u⟫ + min_i {⟪\hat a_i, u⟫ + c^(i)}` on `Δ_m`. -/
def dualObjective (problem : SimplexSaddlePointProblem n m) :
    Δ[m] → ℝ :=
  fun u ↦
    dotProduct problem.dualLinearTerm u.1 +
      Finset.univ.inf' Finset.univ_nonempty
        (fun i : Fin (n : ℕ) ↦
          dotProduct (problem.matrix.transpose i) u.1 + problem.primalLinearTerm i)

/-- Evaluating the simplex saddle function gives the bilinear term `⟪A x, u⟫` together with the
linear contributions `⟪c, x⟫` and `⟪b, u⟫`. -/
theorem saddleFunction_apply (problem : SimplexSaddlePointProblem n m)
    (x : Δ[n]) (u : Δ[m]) :
    problem.saddleFunction x u =
      dotProduct (problem.matrix.mulVec x.1) u.1 +
        dotProduct problem.primalLinearTerm x.1 +
        dotProduct problem.dualLinearTerm u.1 :=
  rfl

/-- The primal nonsmooth objective equals the row-wise maximum
`⟪c, x⟫ + max_j {⟪a_j, x⟫ + b^(j)}`, where `a_j` is the `j`-th row of `A`. -/
theorem primalObjective_eq_max_rows (problem : SimplexSaddlePointProblem n m)
    (x : Δ[n]) :
    problem.primalObjective x =
      dotProduct problem.primalLinearTerm x.1 +
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (m : ℕ) ↦
            dotProduct (problem.matrix j) x.1 + problem.dualLinearTerm j) :=
  rfl

/-- The dual nonsmooth objective equals the column-wise minimum
`⟪b, u⟫ + min_i {⟪\hat a_i, u⟫ + c^(i)}`, where `\hat a_i` is the `i`-th column of `A`. -/
theorem dualObjective_eq_min_columns (problem : SimplexSaddlePointProblem n m)
    (u : Δ[m]) :
    problem.dualObjective u =
      dotProduct problem.dualLinearTerm u.1 +
        Finset.univ.inf' Finset.univ_nonempty
          (fun i : Fin (n : ℕ) ↦
            dotProduct (problem.matrix.transpose i) u.1 + problem.primalLinearTerm i) :=
  rfl

end SimplexSaddlePointProblem

end
