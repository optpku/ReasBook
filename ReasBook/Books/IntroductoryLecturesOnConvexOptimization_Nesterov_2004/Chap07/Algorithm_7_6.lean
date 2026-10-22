/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Algorithm 7.6 lies in the centrally symmetric rounding / finite-family inverse-matrix bridge
domain.

Sampled owner-style declarations:
- `CentralSymmetricRoundingMethod` and `centralSymmetricRoundingUpdatedMatrix` in
  `Algorithm_7_5`, the Chapter 7 owner of the `Gₖ`-matrix rounding process and its rank-one
  update;
- `CentralSymmetricRoundingMethod.radius` in `Algorithm_7_5`, the downstream owner of the
  stopping-radius data;
- mathlib `absConvexHull` together with the bridge theorem
  `convexHull_range_union_neg_eq_absConvexHull_range` in `Proposition_7_12`;
- `centralSymmetryRoundingAlphaStar` in `Proposition_7_8`, the chapter owner of the scalar update
  coefficient as a function of `σ = r² / n - 1`;
- `IsMaxOn` and `isMaxOn_univ_iff` in mathlib, the canonical maximizer owners for a chosen
  maximizing index;
- `Matrix.PosDef.inv`, `Matrix.toEuclideanLin`, and `Matrix.vecMulVec`, the canonical
  positive-definite inverse, matrix-action, and rank-one outer-product owners.

Best owner abstraction:
- source-facing: Algorithm 7.6's finite-family inverse-matrix presentation;
- core/canonical: `CentralSymmetricRoundingMethod`;
- bridge/view: the generating family, the symmetric-hull identification, the inverse matrices
  `Hₖ = Gₖ⁻¹`, and the score/update formulas derived from the core owner.

Primitive data:
- the Chapter 7 owner `toCentralSymmetricRoundingMethod`;
- the input vectors `aᵢ`;
- the identification of the rounded body with `absConvexHull ℝ (Set.range a)`;
- the Gram-matrix initialization `G₀ = (1 / m) ∑ᵢ aᵢ aᵢᵀ`;
- the chosen maximizing indices and the source-facing inverse-matrix update formulas.

Derived API:
- the inverse matrices `Hₖ = Gₖ⁻¹` and their positive-definiteness;
- the initial inverse matrix `H₀ = G₀⁻¹`;
- the score vector, selected radius, update direction, and scalar `α` derived from `Hₖ`;
- the stopping predicate as the source-facing inverse-matrix view of the Chapter 7 threshold.

This refinement removes the second root owner from the previous version. Algorithm 7.6 is kept as
the finite-family inverse-matrix view of `CentralSymmetricRoundingMethod`, rather than as a
parallel process with an unrelated `γ > 0` API.
-/

/-- The matrix `G₀ = (1 / m) ∑_{i=1}^m aᵢ aᵢᵀ` attached to the input vectors. -/
def centralSymmetryGramMatrix (a : Fin m → Eₙ) : Matrix (Fin n) (Fin n) ℝ :=
  (m : ℝ)⁻¹ • ∑ i : Fin m, vecMulVec (a i) (a i)

/-- The initial inverse matrix `H₀ = G₀⁻¹`, defined on the intended positive-definite Gram-matrix
domain of Algorithm 7.6. -/
def centralSymmetryInitialInverseMatrix
    (a : Fin m → Eₙ) (hGram : (centralSymmetryGramMatrix a).PosDef) :
    Matrix (Fin n) (Fin n) ℝ :=
  let _ : (centralSymmetryGramMatrix a).PosDef := hGram
  (centralSymmetryGramMatrix a)⁻¹

/-- The initial inverse matrix is positive definite. -/
theorem centralSymmetryInitialInverseMatrix_posDef
    (a : Fin m → Eₙ) (hGram : (centralSymmetryGramMatrix a).PosDef) :
    (centralSymmetryInitialInverseMatrix a hGram).PosDef := by
  simpa [centralSymmetryInitialInverseMatrix] using hGram.inv

/-- The quadratic score `ν_H^{(i)} = ⟪aᵢ, H aᵢ⟫` attached to the current inverse matrix. -/
def centralSymmetryScore
    (a : Fin m → Eₙ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin m) : ℝ :=
  inner ℝ (a i) (toEuclideanLin H (a i))

/-- The score vector with entries `ν_H^{(i)} = ⟪aᵢ, H aᵢ⟫`. -/
def centralSymmetryScoreVector
    (a : Fin m → Eₙ) (H : Matrix (Fin n) (Fin n) ℝ) : Eₘ :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦
    centralSymmetryScore a H i

/-- The vector `x = H aᵢ` used in the rank-one update. -/
def centralSymmetryUpdateDirection
    (H : Matrix (Fin n) (Fin n) ℝ) (a : Fin m → Eₙ) (i : Fin m) : Eₙ :=
  toEuclideanLin H (a i)

/-- The selected radius `r = √(ν_H^{(i)})` attached to the chosen quadratic score. -/
def centralSymmetrySelectedRadius
    (a : Fin m → Eₙ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin m) : ℝ :=
  Real.sqrt (centralSymmetryScore a H i)

/-- The quantity `σ = (1 / n) r² - 1` used in the rank-one update. -/
def centralSymmetrySigma (n : ℕ) (r : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * r ^ (2 : ℕ) - 1

/-- The coefficient `α = σ / (r² - 1)` from the update rule. -/
def centralSymmetryAlpha (n : ℕ) (r : ℝ) : ℝ :=
  centralSymmetryRoundingAlphaStar n (centralSymmetrySigma n r)

/-- The stopping condition `r ≤ γ √n` from Algorithm 7.6. -/
def centralSymmetryShouldStop (γ : ℝ) (n : ℕ) (r : ℝ) : Prop :=
  r ≤ γ * Real.sqrt n

/-- The updated inverse matrix
`H₊ = (1 / (1 - α)) [H - (α / (1 + α)) x xᵀ]`. -/
def centralSymmetryNextInverseMatrix
    (H : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (x : Eₙ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 - α)⁻¹ • (H - (α / (1 + α)) • vecMulVec x x)

/-- The updated score vector with entries
`v₊^{(i)} = (1 / (1 - α)) [v^{(i)} - (α / (1 + α)) ⟪aᵢ, x⟫²]`. -/
def centralSymmetryNextScoreVector
    (a : Fin m → Eₙ) (v : Eₘ) (α : ℝ) (x : Eₙ) : Eₘ :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦
    (1 - α)⁻¹ * (v i - (α / (1 + α)) * (inner ℝ (a i) x) ^ (2 : ℕ))

-- Proof sketch: unfold `centralSymmetryScoreVector`; evaluation at coordinate `i` is the
-- defining formula for the Euclidean-space vector with components `⟪aᵢ, H aᵢ⟫`.
/-- Evaluating `centralSymmetryScoreVector` recovers the score `⟪aᵢ, H aᵢ⟫` in coordinate `i`. -/
theorem centralSymmetryScoreVector_apply
    (a : Fin m → Eₙ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin m) :
    centralSymmetryScoreVector a H i =
      centralSymmetryScore a H i := by
  simp [centralSymmetryScoreVector]

-- Proof sketch: unfold `centralSymmetryNextScoreVector`; evaluation at coordinate `i` yields
-- exactly the displayed coordinate update formula for `v₊^{(i)}`.
/-- Evaluating `centralSymmetryNextScoreVector` gives the coordinate formula from the textbook
update rule. -/
theorem centralSymmetryNextScoreVector_apply
    (a : Fin m → Eₙ) (v : Eₘ) (α : ℝ) (x : Eₙ) (i : Fin m) :
    centralSymmetryNextScoreVector a v α x i =
      (1 - α)⁻¹ * (v i - (α / (1 + α)) * (inner ℝ (a i) x) ^ (2 : ℕ)) := by
  simp [centralSymmetryNextScoreVector]

/-- Algorithm 7.6: the finite-family inverse-matrix presentation of the centrally symmetric
rounding process. The core owner is the Chapter 7 `Gₖ`-matrix method
`toCentralSymmetricRoundingMethod`; the extra source-facing data are the generating family
`a₁, …, aₘ`, the identification of the body with `conv {±aᵢ}`, the chosen maximizing indices, and
the inverse-side update formulas for `Hₖ = Gₖ⁻¹`. -/
structure CentralSymmetryRoundingAlgorithm (m n : ℕ) where
  /-- The core Chapter 7 centrally symmetric rounding method in `Gₖ`-matrix form. -/
  toCentralSymmetricRoundingMethod : CentralSymmetricRoundingMethod n
  /-- The input vectors `a₁, …, aₘ ∈ ℝⁿ`. -/
  vectors : Fin m → EuclideanSpace ℝ (Fin n)
  /-- The rounded body is the canonical absolutely convex hull `absConvexHull ℝ (Set.range a)`,
  equivalently the textbook symmetric convex hull `conv {±aᵢ}`. -/
  body_eq :
    ((toCentralSymmetricRoundingMethod.body :
        ConvexBody (EuclideanSpace ℝ (Fin n))) :
      Set (EuclideanSpace ℝ (Fin n))) =
      absConvexHull ℝ (Set.range vectors)
  /-- The core method starts from the textbook Gram matrix
  `G₀ = (1 / m) ∑ᵢ aᵢ aᵢᵀ`. -/
  initialMatrix_eq :
    toCentralSymmetricRoundingMethod.initialMatrix = centralSymmetryGramMatrix vectors
  /-- A choice of maximizing index `iₖ` at each iteration. -/
  maximizingIndex : ℕ → Fin m
  /-- The core maximizer `gₖ` is the chosen generator `a_{iₖ}`. -/
  maximizer_eq :
    ∀ k : ℕ,
      toCentralSymmetricRoundingMethod.maximizer k = vectors (maximizingIndex k)
  /-- Each chosen index `iₖ` realizes the maximum of the current score vector `vₖ`. -/
  maximizingIndex_isMaxOn :
    ∀ k : ℕ,
      IsMaxOn
        (fun i ↦ centralSymmetryScore vectors ((toCentralSymmetricRoundingMethod k)⁻¹) i)
        Set.univ (maximizingIndex k)
  /-- If the stopping criterion fails at iteration `k`, then `Hₖ₊₁` is given by the rank-one
  matrix update from Algorithm 7.6. -/
  inverse_succ :
    ∀ k : ℕ,
      ¬ centralSymmetryShouldStop toCentralSymmetricRoundingMethod.gamma n
          (centralSymmetrySelectedRadius
            vectors ((toCentralSymmetricRoundingMethod k)⁻¹) (maximizingIndex k)) →
        (toCentralSymmetricRoundingMethod (k + 1))⁻¹ =
          centralSymmetryNextInverseMatrix
            ((toCentralSymmetricRoundingMethod k)⁻¹)
            (centralSymmetryAlpha n
              (centralSymmetrySelectedRadius
                vectors ((toCentralSymmetricRoundingMethod k)⁻¹) (maximizingIndex k)))
            (centralSymmetryUpdateDirection
              ((toCentralSymmetricRoundingMethod k)⁻¹) vectors (maximizingIndex k))
  /-- If the stopping criterion fails at iteration `k`, then the score vector derived from
  `Hₖ₊₁` is given coordinatewise by the textbook update formula. -/
  score_succ :
    ∀ k : ℕ,
      ¬ centralSymmetryShouldStop toCentralSymmetricRoundingMethod.gamma n
          (centralSymmetrySelectedRadius
            vectors ((toCentralSymmetricRoundingMethod k)⁻¹) (maximizingIndex k)) →
        centralSymmetryScoreVector vectors ((toCentralSymmetricRoundingMethod (k + 1))⁻¹) =
          centralSymmetryNextScoreVector
            vectors
            (centralSymmetryScoreVector vectors ((toCentralSymmetricRoundingMethod k)⁻¹))
            (centralSymmetryAlpha n
              (centralSymmetrySelectedRadius
                vectors ((toCentralSymmetricRoundingMethod k)⁻¹) (maximizingIndex k)))
            (centralSymmetryUpdateDirection
              ((toCentralSymmetricRoundingMethod k)⁻¹) vectors (maximizingIndex k))

namespace CentralSymmetryRoundingAlgorithm

/-- The Gram matrix attached to the generating family is positive definite because it is the
initial positive-definite matrix of the underlying Chapter 7 method. -/
theorem gramMatrix_posDef
    (algorithm : CentralSymmetryRoundingAlgorithm m n) :
    (centralSymmetryGramMatrix algorithm.vectors).PosDef := by
  simpa [algorithm.toCentralSymmetricRoundingMethod.matrix_zero, algorithm.initialMatrix_eq] using
    algorithm.toCentralSymmetricRoundingMethod.matrix_posDef 0

/-- The inverse matrices `Hₖ = Gₖ⁻¹` derived from the underlying Chapter 7 method. -/
def inverseMatrix (algorithm : CentralSymmetryRoundingAlgorithm m n) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (algorithm.toCentralSymmetricRoundingMethod k)⁻¹

/-- Every derived inverse matrix `Hₖ` is positive definite. -/
theorem inverseMatrix_posDef
    (algorithm : CentralSymmetryRoundingAlgorithm m n) (k : ℕ) :
    (algorithm.inverseMatrix k).PosDef := by
  simpa [inverseMatrix] using
    (algorithm.toCentralSymmetricRoundingMethod.matrix_posDef k).inv

/-- The derived inverse history starts from the canonical inverse of the Gram matrix. -/
theorem inverse_zero
    (algorithm : CentralSymmetryRoundingAlgorithm m n) :
    algorithm.inverseMatrix 0 =
      centralSymmetryInitialInverseMatrix algorithm.vectors algorithm.gramMatrix_posDef := by
  simp [inverseMatrix, centralSymmetryInitialInverseMatrix,
    algorithm.toCentralSymmetricRoundingMethod.matrix_zero, algorithm.initialMatrix_eq]

/-- A run of Algorithm 7.6 can be used as its inverse-matrix sequence `H₀, H₁, H₂, ...`. -/
instance : CoeFun (CentralSymmetryRoundingAlgorithm m n)
    (fun _ ↦ ℕ → Matrix (Fin n) (Fin n) ℝ) where
  coe algorithm := algorithm.inverseMatrix

/-- The score vector `vₖ` attached to the current inverse matrix `Hₖ`. -/
def scoreVector (algorithm : CentralSymmetryRoundingAlgorithm m n) (k : ℕ) : Eₘ :=
  centralSymmetryScoreVector algorithm.vectors (algorithm k)

/-- The selected radius `rₖ = √(vₖ^{(iₖ)})` of a run of Algorithm 7.6. -/
def selectedRadius (algorithm : CentralSymmetryRoundingAlgorithm m n) (k : ℕ) : ℝ :=
  centralSymmetrySelectedRadius algorithm.vectors (algorithm k) (algorithm.maximizingIndex k)

/-- The quantity `σₖ = (1 / n) rₖ² - 1` attached to the current selected radius. -/
def sigma (algorithm : CentralSymmetryRoundingAlgorithm m n) (k : ℕ) : ℝ :=
  centralSymmetrySigma n (algorithm.selectedRadius k)

/-- The coefficient `αₖ = σₖ / (rₖ² - 1)` attached to the current selected radius. -/
def alpha (algorithm : CentralSymmetryRoundingAlgorithm m n) (k : ℕ) : ℝ :=
  centralSymmetryAlpha n (algorithm.selectedRadius k)

/-- The vector `xₖ = Hₖ a_{iₖ}` used in the rank-one update. -/
def updateDirection (algorithm : CentralSymmetryRoundingAlgorithm m n) (k : ℕ) : Eₙ :=
  centralSymmetryUpdateDirection (algorithm k) algorithm.vectors (algorithm.maximizingIndex k)

/-- The stopping predicate `rₖ ≤ γ √n` for the current iteration. -/
def shouldStop (algorithm : CentralSymmetryRoundingAlgorithm m n) (k : ℕ) : Prop :=
  centralSymmetryShouldStop
    algorithm.toCentralSymmetricRoundingMethod.gamma n (algorithm.selectedRadius k)

/-- Algorithm 7.6 inherits the same threshold parameter `γ > 1` as the core Chapter 7 owner. -/
theorem one_lt_gamma
    (algorithm : CentralSymmetryRoundingAlgorithm m n) :
    1 < algorithm.toCentralSymmetricRoundingMethod.gamma :=
  algorithm.toCentralSymmetricRoundingMethod.one_lt_gamma

/-- The chosen maximizing index dominates every coordinate of the current score vector. -/
theorem maximizingIndex_spec
    (algorithm : CentralSymmetryRoundingAlgorithm m n) (k : ℕ) (i : Fin m) :
    algorithm.scoreVector k i ≤ algorithm.scoreVector k (algorithm.maximizingIndex k) :=
  by
    simpa [scoreVector] using
      (isMaxOn_univ_iff.mp (algorithm.maximizingIndex_isMaxOn k)) i

-- Proof sketch: unfold `CentralSymmetryRoundingAlgorithm.shouldStop` and
-- `centralSymmetryShouldStop`; the predicate is definitionally the displayed inequality.
/-- The stopping predicate is exactly the textbook inequality `rₖ ≤ γ √n`. -/
theorem shouldStop_iff
    (algorithm : CentralSymmetryRoundingAlgorithm m n) (k : ℕ) :
    algorithm.shouldStop k ↔
      algorithm.selectedRadius k ≤
        algorithm.toCentralSymmetricRoundingMethod.gamma * Real.sqrt (n : ℝ) :=
  Iff.rfl

end CentralSymmetryRoundingAlgorithm

end
