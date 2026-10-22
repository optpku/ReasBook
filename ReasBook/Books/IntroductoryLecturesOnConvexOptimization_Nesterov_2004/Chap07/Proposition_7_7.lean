/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_8_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_9_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Corollary_3_1_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_12

open scoped BigOperators Matrix
open scoped WeightedGramMatrix

noncomputable section

variable {ι : Type} [Fintype ι]

section PsiStar

/-- The feasible strict-simplex weights for `ψ*` are exactly those whose weighted Gram matrix is
invertible, so the inverse-defined objective is evaluated only on its intended domain. -/
def psiStarFeasibleSet {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) :
    Set (StdSimplex.Strict ℝ ι) :=
  {t | IsUnit (B[a](t.1.weights))}

/-- The source-facing objective `⟪B(t)⁻¹ f, f⟫` for `ψ*`, viewed as a function on the feasible
strict-simplex subtype. -/
def psiStarObjective {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    psiStarFeasibleSet a → ℝ :=
  fun ⟨t, _⟩ ↦ dotProduct ((B[a](t.1.weights))⁻¹ *ᵥ f) f

/-- The constrained minimization problem defining `ψ*` on the strict simplex of weights. -/
def psiStarProblem {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    SetConstrainedMinimizationProblem (StdSimplex.Strict ℝ ι) where
  feasibleSet := psiStarFeasibleSet a
  objective :=
    let _ : DecidablePred (· ∈ psiStarFeasibleSet a) := Classical.decPred (· ∈ psiStarFeasibleSet a)
    fun t ↦ if ht : t ∈ psiStarFeasibleSet a then psiStarObjective a f ⟨t, ht⟩ else 0

/-- On a feasible strict-simplex point, the constrained-problem objective recovers the source-facing
`ψ*` objective. -/
@[simp] theorem psiStarProblem_apply_of_mem_feasibleSet {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (t : StdSimplex.Strict ℝ ι) (ht : t ∈ psiStarFeasibleSet a) :
    psiStarProblem a f t = psiStarObjective a f ⟨t, ht⟩ := by
  classical
  simp [psiStarProblem, ht]

/-- The value `ψ*`, recorded as the canonical constrained optimal value on strict simplex
combinations. Using `EReal` keeps the infimum faithful even when the displayed real minimum is not
attained. -/
def psiStar {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) : EReal :=
  (psiStarProblem a f).optimalValue

end PsiStar

section MaxAbsoluteInner

variable [Nonempty ι]

/-- The unconstrained minimization problem whose negated optimal value is the quadratic max
formulation `maxₓ [2⟪f, x⟫ - maxᵢ ⟪aᵢ, x⟫²]`. -/
def maxQuadraticProblem {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  feasibleSet := Set.univ
  objective := fun x ↦
    -(2 * dotProduct f x -
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2)

/-- The quadratic max value, defined through the constrained-optimization owner so that
unbounded-above cases are represented faithfully in `EReal`. -/
def maxQuadraticValue {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) : EReal :=
  -(maxQuadraticProblem a f).optimalValue

/-- The feasible set for the ratio formulation consists of points where the denominator
`maxᵢ ⟪aᵢ, x⟫²` is strictly positive. -/
def maxRatioFeasibleSet {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | 0 < (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2}

/-- The constrained minimization problem whose negated optimal value is the ratio max formulation.
The feasible set explicitly excludes the non-mathematical totalization of division by zero. -/
def maxRatioProblem {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  feasibleSet := maxRatioFeasibleSet a
  objective := fun x ↦
    -((dotProduct f x) ^ 2 /
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2)

/-- The ratio max value, defined on the faithful feasible set `0 < maxᵢ ⟪aᵢ, x⟫²`. -/
def maxRatioValue {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) : EReal :=
  -(maxRatioProblem a f).optimalValue

section SupportAbsMin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The constrained minimization problem defining
`f* = min {maxᵢ |⟪aᵢ, x⟫| | ⟪f, x⟫ = 1}` on a real inner-product space. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` presentation. -/
def supportAbsMinProblem (a : ι → E) (f : E) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := nesterovHyperplane f 1
  objective := maxTypeObjective (fun i x ↦ |inner ℝ (a i) x|)

/-- The constrained support minimum `f*`, recorded as the canonical optimal value of the affine
slice problem. Using `EReal` keeps empty or non-attained cases faithful. -/
def supportAbsMin (a : ι → E) (f : E) : EReal :=
  (supportAbsMinProblem a f).optimalValue

/-- The objective of the constrained support-minimum problem is the finite max
`x ↦ maxᵢ |⟪aᵢ, x⟫|`. -/
@[simp] theorem supportAbsMinProblem_apply (a : ι → E) (f x : E) :
    supportAbsMinProblem a f x =
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  rfl

/-- The feasible set of the constrained support-minimum problem is the affine nesterovHyperplane
`nesterovHyperplane f 1`. -/
@[simp] theorem supportAbsMinProblem_feasibleSet (a : ι → E) (f : E) :
    (supportAbsMinProblem a f).feasibleSet = nesterovHyperplane f 1 :=
  rfl

/-- Membership in the feasible set of the constrained support-minimum problem is exactly the
normalization constraint `⟪f, x⟫ = 1`. -/
@[simp] theorem mem_supportAbsMinProblem_feasibleSet_iff (a : ι → E) {f x : E} :
    x ∈ (supportAbsMinProblem a f).feasibleSet ↔ inner ℝ f x = 1 := by
  rfl

end SupportAbsMin

end MaxAbsoluteInner

section PsiStarTheorems

variable [Nonempty ι]

/-- Helper for Proposition 7.7: applying the weighted Gram matrix to a vector collects the rank-one
summands into the expected weighted linear combination `∑ᵢ wᵢ ⟪aᵢ, x⟫ aᵢ`. -/
private theorem weightedGram_toEuclideanLin_eq_sum_weights_smul
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (w : ι → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (B[a](w)).toEuclideanLin x = ∑ i, (w i * inner ℝ (a i) x) • a i := by
  -- Route correction: the coordinate proof is stable once `vecMulVec_mulVec` collapses each
  -- rank-one summand before the remaining real-scalar commutativity cleanup.
  ext p
  -- Expand the weighted Gram action into rank-one matrix-vector products.
  simp [Matrix.toEuclideanLin_apply, weightedGramMatrix, Matrix.vecMulVec_mulVec, inner,
    dotProduct, mul_assoc]
  -- Over `ℝ`, the only remaining mismatch is the order of scalar factors inside each summand.
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [mul_comm, mul_assoc]

/-- Helper for Proposition 7.7: the quadratic form of the weighted Gram matrix is the weighted sum
of squared inner products `∑ᵢ wᵢ ⟪aᵢ, x⟫²`. -/
private theorem weightedGram_quadratic_eq_sum_weights_mul_sq_inner
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (w : ι → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((B[a](w)).toEuclideanLin x) x =
      ∑ i, w i * (inner ℝ (a i) x) ^ 2 := by
  -- First rewrite the operator action as the weighted linear combination from the source formula.
  rw [weightedGram_toEuclideanLin_eq_sum_weights_smul]
  -- Then distribute the inner product over the finite sum and each scalar multiple.
  rw [sum_inner]
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Each summand is `wᵢ * ⟪aᵢ, x⟫ * ⟪aᵢ, x⟫`, i.e. `wᵢ * ⟪aᵢ, x⟫²`.
  rw [real_inner_smul_left]
  ring_nf

/-- Helper for Proposition 7.7: every simplex-weighted Gram quadratic form is bounded above by the
source-side extremal square `maxᵢ |⟪aᵢ, x⟫|²`. -/
private theorem weightedGram_quadratic_le_max_abs_sq_of_simplex
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (t : StdSimplex ℝ ι)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((B[a](t.weights)).toEuclideanLin x) x ≤
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 := by
  -- Rewrite the quadratic form into the source weighted sum of squared pairings.
  rw [weightedGram_quadratic_eq_sum_weights_mul_sq_inner]
  let M : ℝ := maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x
  have hterm_le : ∀ i : ι, (inner ℝ (a i) x) ^ 2 ≤ M ^ 2 := by
    intro i
    have hle : |inner ℝ (a i) x| ≤ M := by
      rw [show M = maxTypeObjective (fun j y ↦ |inner ℝ (a j) y|) x by rfl, maxTypeObjective_apply]
      exact Finset.le_sup' (fun j : ι ↦ |inner ℝ (a j) x|) (Finset.mem_univ i)
    have hnonneg : 0 ≤ M := le_trans (abs_nonneg _) hle
    -- Squaring preserves the order because both sides are nonnegative.
    calc
      (inner ℝ (a i) x) ^ 2 = |inner ℝ (a i) x| ^ 2 := by rw [sq_abs]
      _ ≤ M ^ 2 := by
            have hsq : |inner ℝ (a i) x| ^ 2 ≤ M ^ 2 := by
              exact sq_le_sq.mpr <| by simpa [abs_of_nonneg hnonneg] using hle
            simpa using hsq
  have hsum_le :
      ∑ i, t.weights i * (inner ℝ (a i) x) ^ 2 ≤ ∑ i, t.weights i * M ^ 2 := by
    -- Each summand is controlled by the same extremal square, and simplex weights are nonnegative.
    refine Finset.sum_le_sum fun i _ ↦ ?_
    exact mul_le_mul_of_nonneg_left (hterm_le i) (t.nonneg i)
  have hweights_sum : ∑ i, t.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using t.total
  calc
    ∑ i, t.weights i * (inner ℝ (a i) x) ^ 2
        ≤ ∑ i, t.weights i * M ^ 2 := hsum_le
    _ = (∑ i, t.weights i) * M ^ 2 := by
          rw [Finset.sum_mul]
    _ = M ^ 2 := by simp [hweights_sum]

/-- Helper for Proposition 7.7: the strict-simplex quadratic slice is bounded above by the source
extremal square `maxᵢ |⟪aᵢ, x⟫|²`. -/
private theorem weightedGram_quadratic_le_max_abs_sq_of_strict
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (t : StdSimplex.Strict ℝ ι)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((B[a](t.1.weights)).toEuclideanLin x) x ≤
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 := by
  -- The strict case is the simplex case with the positivity witness forgotten.
  simpa using weightedGram_quadratic_le_max_abs_sq_of_simplex a t.1 x

/-- Helper for Proposition 7.7: an invertible weighted Gram matrix coming from strict simplex
weights has strictly positive quadratic form on every nonzero vector. -/
private theorem weightedGram_quadratic_pos_of_strict_isUnit
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (t : StdSimplex.Strict ℝ ι)
    (hinv : IsUnit (B[a](t.1.weights))) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    0 < inner ℝ ((B[a](t.1.weights)).toEuclideanLin x) x := by
  have hnonneg : 0 ≤ inner ℝ ((B[a](t.1.weights)).toEuclideanLin x) x := by
    -- The quadratic form is a sum of nonnegative weighted squares.
    rw [weightedGram_quadratic_eq_sum_weights_mul_sq_inner]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (le_of_lt (t.2 i)) (sq_nonneg _)
  by_contra hnot
  have hzero : inner ℝ ((B[a](t.1.weights)).toEuclideanLin x) x = 0 := by
    exact le_antisymm (le_of_not_gt hnot) hnonneg
  have hterm_zero : ∀ i : ι, t.1.weights i * (inner ℝ (a i) x) ^ 2 = 0 := by
    -- Since every summand is nonnegative, vanishing of the total sum forces termwise vanishing.
    have hsum_zero : ∑ i, t.1.weights i * (inner ℝ (a i) x) ^ 2 = 0 := by
      simpa [weightedGram_quadratic_eq_sum_weights_mul_sq_inner] using hzero
    intro i
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ mul_nonneg (le_of_lt (t.2 j)) (sq_nonneg _))).mp hsum_zero i
        (Finset.mem_univ i)
  have hinner_zero : ∀ i : ι, inner ℝ (a i) x = 0 := by
    intro i
    have hw_ne : t.1.weights i ≠ 0 := ne_of_gt (t.2 i)
    have hsq_zero : (inner ℝ (a i) x) ^ 2 = 0 := by
      rcases mul_eq_zero.mp (hterm_zero i) with hweight | hsquare
      · exact False.elim (hw_ne hweight)
      · exact hsquare
    exact sq_eq_zero_iff.mp hsq_zero
  have hBx : (B[a](t.1.weights)).toEuclideanLin x = 0 := by
    -- The action formula collapses because each coefficient `⟪aᵢ, x⟫` vanishes.
    rw [weightedGram_toEuclideanLin_eq_sum_weights_smul]
    apply Finset.sum_eq_zero
    intro i hi
    simp [hinner_zero i]
  have hdet : IsUnit (B[a](t.1.weights)).det :=
    (B[a](t.1.weights)).isUnit_iff_isUnit_det.mp hinv
  letI : Invertible (B[a](t.1.weights)) := Matrix.invertibleOfIsUnitDet _ hdet
  have hcoord : B[a](t.1.weights) *ᵥ x.ofLp = 0 := by
    ext i
    simpa [Matrix.toEuclideanLin_apply] using congrArg (fun v ↦ v i) hBx
  have hcoord' := congrArg (fun v ↦ (B[a](t.1.weights))⁻¹ *ᵥ v) hcoord
  have hx_zero : x.ofLp = 0 := by
    simpa [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec] using hcoord'
  apply hx
  ext i
  simpa using congrArg (fun v : Fin n → ℝ ↦ v i) hx_zero

/-- Helper for Proposition 7.7: a strict feasible weighted Gram matrix is positive definite in the
matrix sense, so the Chapter 1 quadratic-minimization API applies to it. -/
private theorem weightedGram_posDef_of_strict_isUnit
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (t : StdSimplex.Strict ℝ ι)
    (hinv : IsUnit (B[a](t.1.weights))) :
    (B[a](t.1.weights)).PosDef := by
  -- Convert the intrinsic quadratic positivity already proved above into the matrix owner API.
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- The weighted Gram matrix is symmetric because each rank-one summand is symmetric.
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using
      (show (B[a](t.1.weights))ᵀ = B[a](t.1.weights) by
        ext i j
        rw [Matrix.transpose_apply, weightedGramMatrix_apply, weightedGramMatrix_apply]
        refine Finset.sum_congr rfl ?_
        intro k hk
        ring)
  · intro x hx
    let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
    have hy : y ≠ 0 := by
      -- The coordinate representative is nonzero exactly when the Euclidean vector is nonzero.
      dsimp [y]
      simpa using hx
    have hpos :
        0 < inner ℝ ((B[a](t.1.weights)).toEuclideanLin y) y :=
      weightedGram_quadratic_pos_of_strict_isUnit a t hinv hy
    -- Rewrite the Euclidean quadratic form as the matrix quadratic form `xᵀ B x`.
    calc
      0 < inner ℝ y ((B[a](t.1.weights)).toEuclideanLin y) := by
            simpa [real_inner_comm] using hpos
      _ = x ⬝ᵥ B[a](t.1.weights) *ᵥ x := by
            simpa [y] using inner_toEuclideanLin_eq_dotProduct_mulVec (B[a](t.1.weights)) y

/-- Helper for Proposition 7.7: for an invertible weighted Gram matrix, applying the inverse after
the Euclidean linear action recovers the original vector. -/
private theorem weightedGram_nonsing_inv_toEuclideanLin_comp
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M)
    (x : EuclideanSpace ℝ (Fin n)) :
    (M⁻¹).toEuclideanLin (M.toEuclideanLin x) = x := by
  -- Move to coordinates so that `M⁻¹ * M = 1` cancels directly.
  have hdet : IsUnit M.det := M.isUnit_iff_isUnit_det.mp hM
  letI : Invertible M := Matrix.invertibleOfIsUnitDet _ hdet
  ext i
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible]

/-- Helper for Proposition 7.7: scaling the quadratic owner by `2` does not change the canonical
minimizer after the linear term is simultaneously scaled by `-2`. -/
private theorem scaled_quadratic_minimizer_eq_inverse_action
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M)
    (f : EuclideanSpace ℝ (Fin n)) :
    -((((2 : ℝ) • M)⁻¹).toEuclideanLin (-((2 : ℝ) • f))) = (M⁻¹).toEuclideanLin f := by
  have hdet : IsUnit M.det := M.isUnit_iff_isUnit_det.mp hM
  -- Rewrite the scaled inverse once, then the simultaneous `2` / `2⁻¹` cancellation is scalar.
  rw [Matrix.inv_smul (A := M) (k := (2 : ℝ)) hdet]
  simp [smul_smul]

/-- Helper for Proposition 7.7: for an invertible matrix, applying the matrix after its inverse
Euclidean action recovers the original vector. -/
private theorem nonsing_toEuclideanLin_inv_comp
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M)
    (x : EuclideanSpace ℝ (Fin n)) :
    M.toEuclideanLin ((M⁻¹).toEuclideanLin x) = x := by
  -- Move to coordinates so that `M * M⁻¹ = 1` cancels directly.
  have hdet : IsUnit M.det := M.isUnit_iff_isUnit_det.mp hM
  letI : Invertible M := Matrix.invertibleOfIsUnitDet _ hdet
  ext i
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]

/-- Helper for Proposition 7.7: evaluating the scaled Chapter 1 quadratic owner at the canonical
inverse-action point gives the source value `-⟪M⁻¹ f, f⟫`. -/
private theorem scaled_quadratic_objective_at_inverse_eq_neg_dotProduct
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M)
    (f : EuclideanSpace ℝ (Fin n)) :
    quadraticObjective 0 (-((2 : ℝ) • f)) ((2 : ℝ) • M) ((M⁻¹).toEuclideanLin f) =
      -(dotProduct (M⁻¹ *ᵥ f) f) := by
  let y : EuclideanSpace ℝ (Fin n) := (M⁻¹).toEuclideanLin f
  have hy : M.toEuclideanLin y = f := by
    -- The inverse-action point is sent back to `f` by the original matrix.
    simpa [y] using nonsing_toEuclideanLin_inv_comp M hM f
  have hinner : inner ℝ f y = dotProduct (M⁻¹ *ᵥ f) f := by
    -- On Euclidean space, the coordinate and intrinsic inner-product views agree.
    simpa [y, Matrix.toEuclideanLin_apply, dotProduct_comm] using
      (EuclideanSpace.inner_eq_star_dotProduct f y)
  -- Expand the scaled quadratic owner and collapse the remaining inverse-action term.
  calc
    quadraticObjective 0 (-((2 : ℝ) • f)) ((2 : ℝ) • M) y
        = inner ℝ (-((2 : ℝ) • f)) y +
            (1 / 2 : ℝ) * inner ℝ (((2 : ℝ) • M).toEuclideanLin y) y := by
              simp [quadraticObjective]
    _ = -(2 * inner ℝ f y) + inner ℝ (M.toEuclideanLin y) y := by
          have hlin : inner ℝ (-((2 : ℝ) • f)) y = -(2 * inner ℝ f y) := by
            rw [inner_neg_left, real_inner_smul_left]
          have hquad :
              (1 / 2 : ℝ) * inner ℝ (((2 : ℝ) • M).toEuclideanLin y) y =
                inner ℝ (M.toEuclideanLin y) y := by
            have hquad2 :
                inner ℝ (((2 : ℝ) • M.toEuclideanLin y)) y =
                  2 * inner ℝ (M.toEuclideanLin y) y := by
              simpa using real_inner_smul_left (M.toEuclideanLin y) y (2 : ℝ)
            have htoLin : (((2 : ℝ) • M).toEuclideanLin y) = (2 : ℝ) • M.toEuclideanLin y := by
              simp
            rw [htoLin]
            rw [hquad2]
            ring
          rw [hlin, hquad]
    _ = -2 * inner ℝ f y + inner ℝ f y := by
          rw [hy]
          ring
    _ = -(dotProduct (M⁻¹ *ᵥ f) f) := by
          rw [hinner]
          ring

/-- Helper for Proposition 7.7: the strict weighted slice objective is exactly the Chapter 1
quadratic owner with Hessian `2 • B(t)` and linear term `-2f`. -/
private theorem weighted_quadratic_slice_eq_scaled_quadraticObjective
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (t : StdSimplex.Strict ℝ ι) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((B[a](t.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x =
      quadraticObjective 0 (-((2 : ℝ) • f)) ((2 : ℝ) • B[a](t.1.weights)) x := by
  -- Expand the quadratic owner and rewrite the simultaneous factor-`2` scaling explicitly.
  rw [quadraticObjective]
  have hlin : inner ℝ (-((2 : ℝ) • f)) x = -(2 * inner ℝ f x) := by
    rw [inner_neg_left, real_inner_smul_left]
  have hquad :
      (1 / 2 : ℝ) * inner ℝ ((((2 : ℝ) • B[a](t.1.weights))).toEuclideanLin x) x =
        inner ℝ ((B[a](t.1.weights)).toEuclideanLin x) x := by
    rw [show (((2 : ℝ) • B[a](t.1.weights)).toEuclideanLin x) =
        (2 : ℝ) • ((B[a](t.1.weights)).toEuclideanLin x) by simp]
    rw [real_inner_smul_left]
    ring
  rw [hlin, hquad]
  ring

/-- Helper for Proposition 7.7: pointwise-equal unconstrained objectives have the same global
minimizers on `Set.univ`. -/
private theorem isMinOn_unconstrained_congr_of_pointwise_eq
    {X : Type*} {g h : X → ℝ} {x : X} (hpointwise : ∀ y, g y = h y) :
    IsMinOn g Set.univ x ↔ IsMinOn h Set.univ x := by
  -- On the whole space, `IsMinOn` is just the pointwise order inequality.
  rw [isMinOn_univ_iff, isMinOn_univ_iff]
  constructor <;> intro hmin y
  · simpa [hpointwise x, hpointwise y] using hmin y
  · simpa [hpointwise x, hpointwise y] using hmin y

/-- Helper for Proposition 7.7: fixing a strict feasible weight turns the source quadratic slice
into an unconstrained positive-definite quadratic minimization problem whose optimal value is
`-⟪B(t)⁻¹ f, f⟫`. -/
private theorem weighted_quadratic_optimalValue_eq_neg_psiStarObjective
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (t : StdSimplex.Strict ℝ ι) (hinv : IsUnit (B[a](t.1.weights))) :
    (SetConstrainedMinimizationProblem.unconstrained
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        inner ℝ ((B[a](t.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x)).optimalValue =
      -(psiStarObjective a f ⟨t, hinv⟩) := by
  let M : Matrix (Fin n) (Fin n) ℝ := B[a](t.1.weights)
  let problem : UnconstrainedQuadraticMinimizationProblem n :=
    { α := 0
      a := -((2 : ℝ) • f)
      A := (2 : ℝ) • M
      posDef := by
        -- The fixed strict slice is exactly the positive-definite quadratic owner from Chapter 1.
        simpa [M] using (weightedGram_posDef_of_strict_isUnit a t hinv).smul
          (show 0 < (2 : ℝ) by norm_num) }
  have hslice :
      ∀ x : EuclideanSpace ℝ (Fin n),
        inner ℝ (M.toEuclideanLin x) x - 2 * inner ℝ f x =
          quadraticObjective 0 (-((2 : ℝ) • f)) ((2 : ℝ) • M) x := by
    intro x
    simpa [M] using weighted_quadratic_slice_eq_scaled_quadraticObjective a f t x
  have hmin_owner :
      IsMinOn (quadraticObjective 0 (-((2 : ℝ) • f)) ((2 : ℝ) • M))
        Set.univ problem.minimizer := by
    -- The Chapter 1 owner already knows that its canonical minimizer is globally optimal.
    simpa [problem, UnconstrainedQuadraticMinimizationProblem.objective] using
      (UnconstrainedQuadraticMinimizationProblem.minimizer_isMinOn problem)
  have hmin_slice :
      IsMinOn
        (fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ (M.toEuclideanLin x) x - 2 * inner ℝ f x)
        Set.univ problem.minimizer := by
    -- Route correction: transport the minimizer through pointwise equality of objectives instead
    -- of comparing optimization owners directly.
    exact (isMinOn_unconstrained_congr_of_pointwise_eq hslice).2 hmin_owner
  have hopt :
      SetConstrainedMinimizationProblem.optimalValue
        (SetConstrainedMinimizationProblem.unconstrained
          (fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ (M.toEuclideanLin x) x - 2 * inner ℝ f x)) =
        ((fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ (M.toEuclideanLin x) x - 2 * inner ℝ f x)
          problem.minimizer : EReal) :=
    -- Evaluate the unconstrained owner at the transported minimizer.
    SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
      (problem := SetConstrainedMinimizationProblem.unconstrained
        (fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ (M.toEuclideanLin x) x - 2 * inner ℝ f x))
      (x := problem.minimizer) (by simp) hmin_slice
  have hminimizer :
      problem.minimizer = (M⁻¹).toEuclideanLin f := by
    -- The simultaneous scaling of the Hessian and linear term leaves the inverse-action minimizer
    -- unchanged.
    simpa [problem, UnconstrainedQuadraticMinimizationProblem.minimizer] using
      scaled_quadratic_minimizer_eq_inverse_action M hinv f
  calc
    (SetConstrainedMinimizationProblem.unconstrained
      (fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ ((B[a](t.1.weights)).toEuclideanLin x) x -
        2 * inner ℝ f x)).optimalValue
        = ((fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ (M.toEuclideanLin x) x -
            2 * inner ℝ f x) problem.minimizer : EReal) := by
              simpa [M] using hopt
    _ = (quadraticObjective 0 (-((2 : ℝ) • f)) ((2 : ℝ) • M) problem.minimizer : EReal) := by
          exact_mod_cast hslice problem.minimizer
    _ = (quadraticObjective 0 (-((2 : ℝ) • f)) ((2 : ℝ) • M) ((M⁻¹).toEuclideanLin f) : EReal) := by
          rw [hminimizer]
    _ = (-(dotProduct (M⁻¹ *ᵥ f) f) : ℝ) := by
          exact_mod_cast scaled_quadratic_objective_at_inverse_eq_neg_dotProduct M hinv f
    _ = -(psiStarObjective a f ⟨t, hinv⟩) := by
          simp [psiStarObjective, M]

/-- Helper for Proposition 7.7: the quadratic max formulation is bounded above by every strict
weighted Gram slice, hence by `ψ*`. -/
private theorem maxQuadraticValue_le_psiStar
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    maxQuadraticValue a f ≤ psiStar a f := by
  rw [psiStar, SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  refine le_sInf ?_
  rintro _ ⟨t, ht, rfl⟩
  have ht_unit : IsUnit (B[a](t.1.weights)) := by
    simpa [psiStarFeasibleSet] using ht
  let slice : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    inner ℝ ((B[a](t.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x
  have hslice_le :
      (SetConstrainedMinimizationProblem.unconstrained slice).optimalValue ≤
        (maxQuadraticProblem a f).optimalValue := by
    -- Every strict weighted quadratic slice is pointwise dominated by the source max objective.
    refine SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      (problem₁ := SetConstrainedMinimizationProblem.unconstrained slice)
      (problem₂ := maxQuadraticProblem a f) rfl ?_
    intro x hx
    have hdot : inner ℝ f x = dotProduct f x := by
      simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct f x)
    have hquad := weightedGram_quadratic_le_max_abs_sq_of_strict a t x
    simp only [SetConstrainedMinimizationProblem.unconstrained_apply, slice, maxQuadraticProblem]
    rw [← hdot]
    linarith
  have hneg :
      maxQuadraticValue a f ≤ -(SetConstrainedMinimizationProblem.unconstrained slice).optimalValue := by
    rw [maxQuadraticValue, EReal.neg_le, neg_neg]
    exact hslice_le
  calc
    maxQuadraticValue a f
        ≤ -(SetConstrainedMinimizationProblem.unconstrained slice).optimalValue := hneg
    _ = psiStarObjective a f ⟨t, ht_unit⟩ := by
          rw [weighted_quadratic_optimalValue_eq_neg_psiStarObjective a f t ht_unit]
          simp
    _ = psiStarProblem a f t := by
          rw [psiStarProblem_apply_of_mem_feasibleSet a f t ht]

/-- Helper for Proposition 7.7: the source family
`x ↦ |⟪aᵢ, x⟫|² - 2⟪f, x⟫` linearizes exactly to the weighted Gram slice attached to `coeffs`. -/
private theorem weighted_family_linearization_eq_slice
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (coeffs : StdSimplex ℝ ι) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, coeffs.weights i * (|inner ℝ (a i) x| ^ 2 - 2 * inner ℝ f x) =
      inner ℝ ((B[a](coeffs.weights)).toEuclideanLin x) x - 2 * inner ℝ f x := by
  have hweights_sum : ∑ i, coeffs.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using coeffs.total
  -- Expand the weighted family sum into its quadratic part and its common affine part.
  calc
    ∑ i, coeffs.weights i * (|inner ℝ (a i) x| ^ 2 - 2 * inner ℝ f x)
        = ∑ i, (coeffs.weights i * |inner ℝ (a i) x| ^ 2 -
            coeffs.weights i * (2 * inner ℝ f x)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_sub]
    _ = ∑ i, coeffs.weights i * (inner ℝ (a i) x) ^ 2 -
          ∑ i, coeffs.weights i * (2 * inner ℝ f x) := by
            rw [Finset.sum_sub_distrib]
            refine congrArg (fun z : ℝ => z - ∑ i, coeffs.weights i * (2 * inner ℝ f x)) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [sq_abs]
    _ = inner ℝ ((B[a](coeffs.weights)).toEuclideanLin x) x -
          (∑ i, coeffs.weights i) * (2 * inner ℝ f x) := by
            rw [weightedGram_quadratic_eq_sum_weights_mul_sq_inner, ← Finset.sum_mul]
    _ = inner ℝ ((B[a](coeffs.weights)).toEuclideanLin x) x - 2 * inner ℝ f x := by
          simp [hweights_sum]

/-- Helper for Proposition 7.7: every simplex-weighted average of the source family is bounded
above by the pointwise quadratic max objective. -/
private theorem weighted_family_linearization_le_max_slice
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (coeffs : StdSimplex ℝ ι) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, coeffs.weights i * (|inner ℝ (a i) x| ^ 2 - 2 * inner ℝ f x) ≤
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 - 2 * inner ℝ f x := by
  -- Rewrite the weighted family through the Gram slice and compare its quadratic part to the max.
  rw [weighted_family_linearization_eq_slice]
  have hquad := weightedGram_quadratic_le_max_abs_sq_of_simplex a coeffs x
  linarith

/-- Helper for Proposition 7.7: the family maximum of
`x ↦ |⟪aᵢ, x⟫|² - 2⟪f, x⟫` is exactly the quadratic max objective. -/
private theorem familyMaximum_eq_maxQuadraticProblem_apply
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y| ^ 2 - 2 * inner ℝ f y) x =
      maxQuadraticProblem a f x := by
  let M : ℝ := maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x
  have hupper :
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y| ^ 2 - 2 * inner ℝ f y) x ≤
        M ^ 2 - 2 * inner ℝ f x := by
    -- Each member of the family is bounded by the square of the extremal absolute pairing.
    rw [maxTypeObjective_le_iff]
    intro i
    have hle : |inner ℝ (a i) x| ≤ M := by
      rw [show M = maxTypeObjective (fun j y ↦ |inner ℝ (a j) y|) x by rfl]
      exact Finset.le_sup' (fun j : ι ↦ |inner ℝ (a j) x|) (Finset.mem_univ i)
    have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) hle
    have hsq : |inner ℝ (a i) x| ^ 2 ≤ M ^ 2 := by
      exact sq_le_sq.mpr <| by simpa [abs_of_nonneg hM_nonneg] using hle
    linarith
  have hlower :
      M ^ 2 - 2 * inner ℝ f x ≤
        maxTypeObjective (fun i y ↦ |inner ℝ (a i) y| ^ 2 - 2 * inner ℝ f y) x := by
    -- An index attaining the absolute maximum also attains the shifted square maximum.
    obtain ⟨i, hi, hmax⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x|)
    rw [show M = |inner ℝ (a i) x| by simpa [maxTypeObjective_apply] using hmax]
    exact Finset.le_sup' (fun j : ι ↦ |inner ℝ (a j) x| ^ 2 - 2 * inner ℝ f x) hi
  -- Both surfaces are the same scalar quantity `M² - 2⟪f, x⟫`.
  have hdot : dotProduct f x = inner ℝ f x := by
    simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct f x).symm
  calc
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y| ^ 2 - 2 * inner ℝ f y) x
        = M ^ 2 - 2 * inner ℝ f x := le_antisymm hupper hlower
    _ = maxQuadraticProblem a f x := by
          simp [maxQuadraticProblem, M, hdot]

/-- Helper for Proposition 7.7: the uniform weights yield a canonical strict simplex witness, which
serves as the source-faithful interior anchor for later perturbation arguments. -/
private theorem uniform_strict_simplex_point_exists :
    Nonempty (StdSimplex.Strict ℝ ι) := by
  classical
  let c : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hcard_pos_nat : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast hcard_pos_nat
  let w : StdSimplex ℝ ι :=
    ⟨Finsupp.equivFunOnFinite.symm (fun _ : ι ↦ c),
      by
        intro i
        exact le_of_lt (by simpa [c] using inv_pos.mpr hcard_pos),
      by
        have hsum_fun : ∑ i : ι, c = 1 := by
          have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
          simpa [c, hcard_ne] using
            (show (∑ _ : ι, c) = (Fintype.card ι : ℝ) * c by simp [c])
        simpa [c] using (Finsupp.equivFunOnFinite_symm_sum (fun _ : ι ↦ c)).trans hsum_fun⟩
  refine ⟨⟨w, ?_⟩⟩
  intro i
  exact by simpa [w, c] using inv_pos.mpr hcard_pos

/-- Helper for Proposition 7.7: a strict feasible simplex weight supplies a quantitative coercive
lower bound for its weighted Gram quadratic form. -/
private theorem strict_anchor_quadratic_lower_bound
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (u0 : StdSimplex.Strict ℝ ι)
    (hu0 : IsUnit (B[a](u0.1.weights))) :
    ∃ m > 0, ∀ x : EuclideanSpace ℝ (Fin n),
      m * ‖x‖ ^ 2 ≤ inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x := by
  obtain ⟨m, hm_pos, _, _, hbound⟩ :=
    posDef_exists_quadraticForm_bounds (B[a](u0.1.weights))
      (weightedGram_posDef_of_strict_isUnit a u0 hu0)
  refine ⟨m, hm_pos, ?_⟩
  -- Keep only the coercive lower estimate from the positive-definite quadratic-form bounds.
  intro x
  exact (hbound x).1

/-- Helper for Proposition 7.7: one strict interior slice controls every sublevel set of the
family maximum `x ↦ maxᵢ (|⟪aᵢ, x⟫|² - 2⟪f, x⟫)`. -/
private theorem familyMaximumSublevels_bounded_of_strictAnchor
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    ∀ α : ℝ,
      Bornology.IsBounded
        (constrainedSublevelSet Set.univ
          (fun x ↦
            ((maxTypeObjective
              (fun i y ↦ |inner ℝ (a i) y| ^ 2 - 2 * inner ℝ f y) x : ℝ) : WithTop ℝ)) α) := by
  let u0 : StdSimplex.Strict ℝ ι := Classical.choice uniform_strict_simplex_point_exists
  obtain ⟨m, hm_pos, hm⟩ := strict_anchor_quadratic_lower_bound a u0 (hinv u0)
  intro α
  let R : ℝ := max 1 ((|α| + 2 * ‖f‖) / m)
  refine (Metric.isBounded_closedBall : Bornology.IsBounded
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)).subset ?_
  intro x hx
  rcases mem_constrainedSublevelSet_iff.mp hx with ⟨_, hxα⟩
  have hmaxα :
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y| ^ 2 - 2 * inner ℝ f y) x ≤ α := by
    exact_mod_cast hxα
  have hfamily_upper :
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y| ^ 2 - 2 * inner ℝ f y) x ≤
        (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 - 2 * inner ℝ f x := by
    rw [maxTypeObjective_le_iff]
    intro i
    have hle :
        |inner ℝ (a i) x| ≤ maxTypeObjective (fun j y ↦ |inner ℝ (a j) y|) x := by
      exact (maxTypeObjective_le_iff (fun j y ↦ |inner ℝ (a j) y|) x
        (maxTypeObjective (fun j y ↦ |inner ℝ (a j) y|) x)).mp le_rfl i
    have hsq :
        |inner ℝ (a i) x| ^ 2 ≤
          (maxTypeObjective (fun j y ↦ |inner ℝ (a j) y|) x) ^ 2 := by
      have hM_nonneg :
          0 ≤ maxTypeObjective (fun j y ↦ |inner ℝ (a j) y|) x :=
        le_trans (abs_nonneg _) hle
      exact sq_le_sq.mpr <| by
        simpa [abs_of_nonneg hM_nonneg] using hle
    linarith
  have hfamily_lower :
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 - 2 * inner ℝ f x ≤
        maxTypeObjective (fun i y ↦ |inner ℝ (a i) y| ^ 2 - 2 * inner ℝ f y) x := by
    obtain ⟨i, hi, hmax⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x|)
    rw [show maxTypeObjective (fun j y ↦ |inner ℝ (a j) y|) x =
        |inner ℝ (a i) x| by
          simpa [maxTypeObjective_apply] using hmax]
    exact Finset.le_sup' (fun j : ι ↦ |inner ℝ (a j) x| ^ 2 - 2 * inner ℝ f x) hi
  have hslice_le :
      inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x ≤ α := by
    calc
      inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x
          = ∑ i, u0.1.weights i * (|inner ℝ (a i) x| ^ 2 - 2 * inner ℝ f x) := by
              symm
              exact weighted_family_linearization_eq_slice a f u0.1 x
      _ ≤ (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 - 2 * inner ℝ f x :=
            weighted_family_linearization_le_max_slice a f u0.1 x
      _ ≤ maxTypeObjective (fun i y ↦ |inner ℝ (a i) y| ^ 2 - 2 * inner ℝ f y) x :=
            hfamily_lower
      _ ≤ α := hmaxα
  have hquad :
      m * ‖x‖ ^ 2 ≤ |α| + 2 * ‖f‖ * ‖x‖ := by
    calc
      m * ‖x‖ ^ 2 ≤ inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x := hm x
      _ ≤ α + 2 * inner ℝ f x := by linarith
      _ ≤ |α| + 2 * |inner ℝ f x| := by
            have hα : α ≤ |α| := le_abs_self α
            have hinner : inner ℝ f x ≤ |inner ℝ f x| := le_abs_self _
            linarith
      _ ≤ |α| + 2 * (‖f‖ * ‖x‖) := by
            have hnorm_inner : ‖inner ℝ f x‖ ≤ ‖f‖ * ‖x‖ := norm_inner_le_norm f x
            have habs : |inner ℝ f x| ≤ ‖f‖ * ‖x‖ := by
              simpa using hnorm_inner
            nlinarith
      _ = |α| + 2 * ‖f‖ * ‖x‖ := by ring
  have hnorm : ‖x‖ ≤ R := by
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hx1.trans (le_max_left _ _)
    · have h1 : 1 ≤ ‖x‖ := le_of_not_ge hx1
      have hlinear : m * ‖x‖ ≤ |α| + 2 * ‖f‖ := by
        nlinarith [hquad, h1, hm_pos, abs_nonneg α, norm_nonneg f]
      have hdiv : ‖x‖ ≤ (|α| + 2 * ‖f‖) / m := by
        refine (le_div_iff₀ hm_pos).2 ?_
        simpa [mul_comm, mul_left_comm, mul_assoc] using hlinear
      exact hdiv.trans (le_max_right _ _)
  simpa [Metric.mem_closedBall, dist_eq_norm, R] using hnorm

/-- Helper for Proposition 7.7: every nonzero direction has strictly positive source denominator
`(maxᵢ |⟪aᵢ, x⟫|)^2`. -/
private theorem max_abs_inner_sq_pos_of_ne_zero
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    0 < (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 := by
  let u0 : StdSimplex.Strict ℝ ι := Classical.choice uniform_strict_simplex_point_exists
  have hquad_pos :
      0 < inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x :=
    weightedGram_quadratic_pos_of_strict_isUnit a u0 (hinv u0) hx
  have hquad_le :
      inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x ≤
        (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 :=
    weightedGram_quadratic_le_max_abs_sq_of_strict a u0 x
  -- One strict interior slice is already enough to force positivity of the extremal square.
  exact lt_of_lt_of_le hquad_pos hquad_le

/-- Helper for Proposition 7.7: the source denominator `maxᵢ |⟪aᵢ, x⟫|` is positively homogeneous
under real scaling. -/
private theorem max_abs_inner_smul
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) (c • x) =
      |c| * maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  rw [maxTypeObjective_apply, maxTypeObjective_apply]
  apply le_antisymm
  · -- Each scaled pairing is bounded by the scaled maximum of the unscaled pairings.
    rw [Finset.sup'_le_iff]
    intro i hi
    calc
      |inner ℝ (a i) (c • x)| = |c| * |inner ℝ (a i) x| := by
        rw [inner_smul_right, abs_mul]
      _ ≤ |c| * Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x|) := by
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun j : ι ↦ |inner ℝ (a j) x|) (Finset.mem_univ i))
          (abs_nonneg c)
  · -- Realize the unscaled maximum at an actual index and scale that witness.
    obtain ⟨i, hi, hmax⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x|)
    calc
      |c| * Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) x|)
          = |inner ℝ (a i) (c • x)| := by
              rw [hmax, inner_smul_right, abs_mul, mul_comm]
      _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ |inner ℝ (a j) (c • x)|) := by
            exact Finset.le_sup' (fun j : ι ↦ |inner ℝ (a j) (c • x)|) hi

/-- Helper for Proposition 7.7: the squared source denominator scales by the square of the real
factor along each ray. -/
private theorem max_abs_inner_sq_smul
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) (c • x)) ^ 2 =
      c ^ 2 * (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 := by
  -- First rewrite the denominator by positive homogeneity, then replace `|c|²` by `c²`.
  rw [max_abs_inner_smul]
  calc
    (|c| * maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2
        = |c| ^ 2 * (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 := by
            ring
    _ = c ^ 2 * (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2 := by
          rw [sq_abs]

/-- Helper for Proposition 7.7: mixing any simplex weights with a strict anchor by a coefficient
`ε ∈ (0, 1)` stays in the strict simplex and has the expected affine-coordinate formula. -/
private theorem strictSimplexMixWithAnchor
    (coeffs : StdSimplex ℝ ι) (u0 : StdSimplex.Strict ℝ ι)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ tε : StdSimplex.Strict ℝ ι, ∀ i,
      tε.1.weights i = (1 - ε) * coeffs.weights i + ε * u0.1.weights i := by
  let updatedWeights : ι →₀ ℝ := (1 - ε) • coeffs.weights + ε • u0.1.weights
  have hupdated_nonneg : ∀ i : ι, 0 ≤ updatedWeights i := by
    intro i
    have h_one_sub_nonneg : 0 ≤ 1 - ε := sub_nonneg.mpr hε1.le
    have hleft : 0 ≤ (1 - ε) * coeffs.weights i :=
      mul_nonneg h_one_sub_nonneg (coeffs.nonneg i)
    have hright : 0 ≤ ε * u0.1.weights i :=
      mul_nonneg hε0.le (u0.1.nonneg i)
    simpa [updatedWeights, mul_comm, mul_left_comm, mul_assoc] using add_nonneg hleft hright
  have hupdated_strict : ∀ i : ι, 0 < updatedWeights i := by
    intro i
    have h_one_sub_nonneg : 0 ≤ 1 - ε := sub_nonneg.mpr hε1.le
    have hleft : 0 ≤ (1 - ε) * coeffs.weights i :=
      mul_nonneg h_one_sub_nonneg (coeffs.nonneg i)
    have hright : 0 < ε * u0.1.weights i :=
      mul_pos hε0 (u0.2 i)
    simpa [updatedWeights, mul_comm, mul_left_comm, mul_assoc] using
      add_pos_of_nonneg_of_pos hleft hright
  have hcoeffs_sum : ∑ i, coeffs.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using coeffs.total
  have hu0_sum : ∑ i, u0.1.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using u0.1.total
  have hupdated_total_fn : ∑ i, updatedWeights i = 1 := by
    calc
      ∑ i, updatedWeights i
          = (1 - ε) * ∑ i, coeffs.weights i + ε * ∑ i, u0.1.weights i := by
              simp [updatedWeights, Finset.sum_add_distrib, Finset.mul_sum]
      _ = (1 - ε) * 1 + ε * 1 := by rw [hcoeffs_sum, hu0_sum]
      _ = 1 := by ring
  let tε : StdSimplex ℝ ι :=
    ⟨updatedWeights,
      hupdated_nonneg,
      by simpa [Finsupp.sum_fintype] using hupdated_total_fn⟩
  refine ⟨⟨tε, hupdated_strict⟩, ?_⟩
  intro i
  simp [tε, updatedWeights, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Proposition 7.7: the strict mixture of the supporting coefficients and the strict
anchor satisfies the source pointwise lower bound needed for the perturbative minimax step. -/
private theorem mixedStrictSlice_pointwise_lower_bound
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (coeffs : StdSimplex ℝ ι) (u0 : StdSimplex.Strict ℝ ι) (fStar : ℝ)
    (hlower :
      ∀ x : EuclideanSpace ℝ (Fin n),
        fStar ≤
          ∑ i, coeffs.weights i * (|inner ℝ (a i) x| ^ 2 - 2 * inner ℝ f x))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ tε : StdSimplex.Strict ℝ ι,
      (∀ i, tε.1.weights i = (1 - ε) * coeffs.weights i + ε * u0.1.weights i) ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        (1 - ε) * fStar +
            ε * (inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x)
          ≤ inner ℝ ((B[a](tε.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x := by
  obtain ⟨tε, htε⟩ := strictSimplexMixWithAnchor coeffs u0 hε0 hε1
  refine ⟨tε, htε, ?_⟩
  intro x
  let sx : ι → ℝ := fun i ↦ |inner ℝ (a i) x| ^ 2 - 2 * inner ℝ f x
  have hweighted :
      (1 - ε) * fStar ≤ (1 - ε) * ∑ i, coeffs.weights i * sx i := by
    exact mul_le_mul_of_nonneg_left (hlower x) (sub_nonneg.mpr hε1.le)
  have hu0slice :
      inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x =
        ∑ i, u0.1.weights i * sx i := by
    symm
    simpa [sx] using weighted_family_linearization_eq_slice a f u0.1 x
  have htεslice :
      inner ℝ ((B[a](tε.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x =
        ∑ i, tε.1.weights i * sx i := by
    symm
    simpa [sx] using weighted_family_linearization_eq_slice a f tε.1 x
  rw [hu0slice, htεslice]
  calc
    (1 - ε) * fStar + ε * ∑ i, u0.1.weights i * sx i
        ≤ (1 - ε) * ∑ i, coeffs.weights i * sx i + ε * ∑ i, u0.1.weights i * sx i := by
              linarith
    _ = ∑ i, (((1 - ε) * coeffs.weights i + ε * u0.1.weights i) * sx i) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = ∑ i, tε.1.weights i * sx i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [htε i]

/-- Helper for Proposition 7.7: each family member
`x ↦ |⟪aᵢ, x⟫|² - 2⟪f, x⟫` is a closed convex real-valued function on the whole space. -/
private theorem quadraticFamilyMember_closedConvexOn
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n)) (i : ι) :
    ClosedConvexOn Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        ((|inner ℝ (a i) x| ^ 2 - 2 * inner ℝ f x : ℝ) : WithTop ℝ)) := by
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ (inner ℝ (a i) x) ^ (2 : ℕ)
  let ℓ : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ -2 * inner ℝ f x
  have hq_convex : ConvexOn ℝ Set.univ q := by
    let L : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] ℝ := ((innerSL ℝ (a i)).toLinearMap).toAffineMap
    -- Compose the scalar square with the affine inner-product functional.
    simpa [q, L, innerSL_apply_apply, Function.comp] using
      ((show Even 2 by decide).convexOn_pow.comp_affineMap L)
  have hℓ_convex : ConvexOn ℝ Set.univ ℓ := by
    let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
      { toFun := fun x ↦ -2 * inner ℝ f x
        map_add' := by
          intro x y
          rw [inner_add_right]
          ring_nf
        map_smul' := by
          intro c x
          rw [inner_smul_right]
          simpa [mul_assoc, mul_left_comm, mul_comm] }
    -- Linear functionals are convex on the whole space.
    simpa [ℓ, L] using L.convexOn convex_univ
  have hcont_q : Continuous q := by
    -- The squared inner-product functional is continuous as a polynomial of a continuous linear map.
    simpa [q, innerSL_apply_apply] using
      (((innerSL ℝ (a i)).continuous).pow 2)
  have hcont_ℓ : Continuous ℓ := by
    -- The affine linear term is continuous by continuity of the inner-product map.
    simpa [ℓ, innerSL_apply_apply, real_inner_smul_left] using
      ((innerSL ℝ ((-2 : ℝ) • f)).continuous)
  have hclosed :
      ClosedConvexFunction
        (fun x : EuclideanSpace ℝ (Fin n) ↦ ((q x + ℓ x : ℝ) : WithTop ℝ)) := by
    exact closedConvexFunction_coe_of_convexOn_continuous
      (hq_convex.add hℓ_convex) (hcont_q.add hcont_ℓ)
  -- Package the real-valued convexity and continuity into the chapter closed-convex owner.
  simpa [q, ℓ, sq_abs, sub_eq_add_neg] using
    hclosed.restrict isClosed_univ convex_univ (by intro x hx; simpa using hx)

/-- Helper for Proposition 7.7: if a real-valued constrained problem has a nonempty feasible image
bounded below in `ℝ`, then its owner optimal value is the corresponding real infimum. -/
private theorem optimalValue_eq_coe_sInf_of_nonempty_bddBelow_local
    {X : Type*} (Q : Set X) (g : X → ℝ) (hQ : Q.Nonempty) (hbounded : BddBelow (g '' Q)) :
    (.mk Q g : SetConstrainedMinimizationProblem X).optimalValue =
      ((sInf (g '' Q) : ℝ) : EReal) := by
  -- Transport the real greatest-lower-bound characterization across the coercion `ℝ → EReal`.
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  have hs :
      IsGLB ((fun x : ℝ ↦ (x : EReal)) '' (g '' Q)) (((sInf (g '' Q) : ℝ) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact EReal.coe_le_coe (csInf_le hbounded hy)
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          intro hz_eq_top
          rcases hQ with ⟨x, hx⟩
          have hz_mem : z ≤ (g x : EReal) := hz ⟨g x, ⟨x, hx, rfl⟩, rfl⟩
          simp [hz_eq_top] at hz_mem
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : r ≤ sInf (g '' Q) := by
          refine le_csInf (hQ.image g) ?_
          intro y hy
          have hzy : (r : EReal) ≤ (y : EReal) := hz ⟨y, hy, rfl⟩
          exact_mod_cast hzy
        exact_mod_cast hr
  have hs' : ((fun x : ℝ ↦ (x : EReal)) '' (g '' Q)).Nonempty := by
    rcases hQ with ⟨x, hx⟩
    exact ⟨g x, ⟨g x, ⟨x, hx, rfl⟩, rfl⟩⟩
  simpa [Set.image_image] using hs.csInf_eq hs'

/-- Helper for Proposition 7.7: every strict feasible slice objective is nonnegative. -/
private theorem psiStarObjective_nonneg
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights)))
    (t : StdSimplex.Strict ℝ ι) :
    0 ≤ psiStarObjective a f ⟨t, hinv t⟩ := by
  let slice : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    inner ℝ ((B[a](t.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x
  have hopt_le_zero :
      (SetConstrainedMinimizationProblem.unconstrained slice).optimalValue ≤ 0 := by
    -- Evaluating the slice at `x = 0` bounds its optimal value above by `0`.
    refine ((SetConstrainedMinimizationProblem.unconstrained slice).optimalValue_le_of_mem_feasibleSet
      (x := 0) (by simp)).trans ?_
    simp [slice]
  rw [weighted_quadratic_optimalValue_eq_neg_psiStarObjective a f t (hinv t)] at hopt_le_zero
  have hnonnegE : (0 : EReal) ≤ psiStarObjective a f ⟨t, hinv t⟩ := by
    exact (EReal.neg_le_zero).1 hopt_le_zero
  exact_mod_cast hnonnegE

/-- Helper for Proposition 7.7: under strict invertibility, `ψ*` is the coercion of the real
infimum of the strict-simplex objective values. -/
private theorem psiStar_eq_coe_sInf_strictObjective
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    psiStar a f =
      ((sInf ((fun t : StdSimplex.Strict ℝ ι ↦ psiStarObjective a f ⟨t, hinv t⟩) '' Set.univ) :
        ℝ) : EReal) := by
  let g : StdSimplex.Strict ℝ ι → ℝ := fun t ↦ psiStarObjective a f ⟨t, hinv t⟩
  have hQ : (Set.univ : Set (StdSimplex.Strict ℝ ι)).Nonempty := by
    exact ⟨Classical.choice uniform_strict_simplex_point_exists, by simp⟩
  have hbounded : BddBelow (g '' Set.univ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, -, rfl⟩
    exact psiStarObjective_nonneg a f hinv t
  -- Every strict-simplex point is feasible under `hinv`, so the owner problem is exactly the
  -- unconstrained real objective `g`.
  simpa [psiStar, psiStarProblem, psiStarFeasibleSet, g, hinv] using
    optimalValue_eq_coe_sInf_of_nonempty_bddBelow_local
      (Set.univ : Set (StdSimplex.Strict ℝ ι)) g hQ hbounded

/-- Helper for Proposition 7.7: in positive dimension the ratio-feasible set is nonempty, since
any nonzero vector has strictly positive denominator under the strict invertibility hypothesis. -/
private theorem exists_maxRatio_feasible
    {n : ℕ} (hn : 0 < n) (a : ι → EuclideanSpace ℝ (Fin n))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    ∃ x : EuclideanSpace ℝ (Fin n), x ∈ maxRatioFeasibleSet a := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  obtain ⟨x, hx⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  refine ⟨x, ?_⟩
  simpa [maxRatioFeasibleSet] using max_abs_inner_sq_pos_of_ne_zero a hinv hx

/-- Helper for Proposition 7.7: the reverse inequality `ψ* ≤ maxQuadraticValue` is the source
minimax step once the bounded-sublevel and strict-approximation bridges are supplied. -/
private theorem psiStar_le_maxQuadraticValue
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    psiStar a f ≤ maxQuadraticValue a f := by
  classical
  let fs : ι → EuclideanSpace ℝ (Fin n) → ℝ := fun i x ↦
    |inner ℝ (a i) x| ^ 2 - 2 * inner ℝ f x
  have hfs : ∀ i, ClosedConvexOn Set.univ (fun x ↦ ((fs i x : ℝ) : WithTop ℝ)) := by
    intro i
    simpa [fs] using quadraticFamilyMember_closedConvexOn a f i
  have hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet Set.univ
            (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α) := by
    simpa [fs] using familyMaximumSublevels_bounded_of_strictAnchor a f hinv
  obtain ⟨xStar, hxStarMin⟩ :=
    exists_isMinOn_familyMaximum_of_bounded_sublevels hfs hbounded Set.univ_nonempty
  obtain ⟨coeffs, hweighted_lower, _hweighted_xStar_eq⟩ :=
    supporting_coeffs_of_familyMaximum_minimizer xStar hfs hxStarMin
  let fStar : ℝ := maxTypeObjective fs ↑xStar
  have hmin_problem : IsMinOn (maxQuadraticProblem a f) Set.univ ↑xStar := by
    -- The family-maximum minimizer is exactly a minimizer of the quadratic owner.
    rw [isMinOn_univ_iff] at hxStarMin ⊢
    intro x
    change (maxQuadraticProblem a f).objective ↑xStar ≤ (maxQuadraticProblem a f).objective x
    rw [← familyMaximum_eq_maxQuadraticProblem_apply a f ↑xStar]
    rw [← familyMaximum_eq_maxQuadraticProblem_apply a f x]
    simpa [fStar, fs] using hxStarMin ⟨x, by simp⟩
  have hmax_opt :
      (maxQuadraticProblem a f).optimalValue = (fStar : EReal) := by
    simpa [fStar, fs, familyMaximum_eq_maxQuadraticProblem_apply] using
      (maxQuadraticProblem a f).optimalValue_eq_of_isMinOn (x := ↑xStar) (by simp) hmin_problem
  have hmax_value : maxQuadraticValue a f = (-fStar : EReal) := by
    simp [maxQuadraticValue, hmax_opt]
  have hlower :
      ∀ x : EuclideanSpace ℝ (Fin n),
        fStar ≤ ∑ i, coeffs.weights i * fs i x := by
    intro x
    simpa [fStar, fs] using hweighted_lower ⟨x, by simp⟩
  let u0 : StdSimplex.Strict ℝ ι := Classical.choice uniform_strict_simplex_point_exists
  let ψ0 : ℝ := psiStarObjective a f ⟨u0, hinv u0⟩
  let g : StdSimplex.Strict ℝ ι → ℝ := fun t ↦ psiStarObjective a f ⟨t, hinv t⟩
  have hg_bdd : BddBelow (g '' Set.univ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, -, rfl⟩
    exact psiStarObjective_nonneg a f hinv t
  have hanchor_lb :
      ∀ x : EuclideanSpace ℝ (Fin n),
        -ψ0 ≤
          inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x := by
    intro x
    have hopt_le :
        (SetConstrainedMinimizationProblem.unconstrained
          (fun y : EuclideanSpace ℝ (Fin n) ↦
            inner ℝ ((B[a](u0.1.weights)).toEuclideanLin y) y - 2 * inner ℝ f y)).optimalValue
          ≤
            inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x := by
      let problem : SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) :=
        SetConstrainedMinimizationProblem.unconstrained
          (fun y : EuclideanSpace ℝ (Fin n) ↦
            inner ℝ ((B[a](u0.1.weights)).toEuclideanLin y) y - 2 * inner ℝ f y)
      have hx : x ∈ problem.feasibleSet := by
        simp [problem]
      simpa [problem] using problem.optimalValue_le_of_mem_feasibleSet hx
    rw [weighted_quadratic_optimalValue_eq_neg_psiStarObjective a f u0 (hinv u0)] at hopt_le
    have hopt_le_real :
        -psiStarObjective a f ⟨u0, hinv u0⟩ ≤
          inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x := by
      refine EReal.coe_le_coe_iff.mp ?_
      simpa using hopt_le
    simpa [ψ0] using hopt_le_real
  rw [psiStar_eq_coe_sInf_strictObjective a f hinv, hmax_value]
  exact_mod_cast
    le_of_forall_pos_le_add fun δ hδ ↦ by
      let C : ℝ := |fStar| + ψ0 + 1
      have hψ0_nonneg : 0 ≤ ψ0 := by
        simpa [ψ0] using psiStarObjective_nonneg a f hinv u0
      have hC_pos : 0 < C := by
        dsimp [C]
        linarith [abs_nonneg fStar, hψ0_nonneg]
      let ε : ℝ := min (1 / 2 : ℝ) (δ / C)
      have hε0 : 0 < ε := by
        dsimp [ε]
        refine lt_min (by norm_num) ?_
        exact div_pos hδ hC_pos
      have hε1 : ε < 1 := by
        have hε_half : ε ≤ (1 / 2 : ℝ) := by
          dsimp [ε]
          exact min_le_left _ _
        linarith
      have hε_nonneg : 0 ≤ ε := hε0.le
      have hεC : ε * C ≤ δ := by
        have hε_le : ε ≤ δ / C := by
          dsimp [ε]
          exact min_le_right _ _
        have hmul := mul_le_mul_of_nonneg_right hε_le hC_pos.le
        have hdiv : (δ / C) * C = δ := by
          field_simp [hC_pos.ne']
        linarith
      obtain ⟨tε, _, hmix⟩ :=
        mixedStrictSlice_pointwise_lower_bound a f coeffs u0 fStar hlower hε0 hε1
      let sliceε : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
        inner ℝ ((B[a](tε.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x
      have hconst_lb :
          ∀ x : EuclideanSpace ℝ (Fin n), (1 - ε) * fStar - ε * ψ0 ≤ sliceε x := by
        intro x
        have hmix_x := hmix x
        have hanchor_x := hanchor_lb x
        have hscaled_anchor :
            ε * (-ψ0) ≤
              ε *
                (inner ℝ ((B[a](u0.1.weights)).toEuclideanLin x) x - 2 * inner ℝ f x) := by
          exact mul_le_mul_of_nonneg_left hanchor_x hε_nonneg
        dsimp [sliceε] at hmix_x hscaled_anchor ⊢
        linarith
      have hslice_opt :
          (((1 - ε) * fStar - ε * ψ0 : ℝ) : EReal) ≤
            (SetConstrainedMinimizationProblem.unconstrained sliceε).optimalValue := by
        rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
        refine le_csInf ?_ ?_
        · exact ⟨sliceε 0, ⟨0, by simp, rfl⟩⟩
        · rintro _ ⟨x, -, rfl⟩
          change (((1 - ε) * fStar - ε * ψ0 : ℝ) : EReal) ≤ ((sliceε x : ℝ) : EReal)
          exact_mod_cast hconst_lb x
      have hψε_le :
          g tε ≤ -fStar + ε * C := by
        have hslice_opt' :
            (((1 - ε) * fStar - ε * ψ0 : ℝ) : EReal) ≤ -(g tε) := by
          simpa [g, sliceε] using
            hslice_opt.trans_eq (weighted_quadratic_optimalValue_eq_neg_psiStarObjective a f tε
              (hinv tε))
        have hslice_opt_real : (1 - ε) * fStar - ε * ψ0 ≤ -(g tε) := by
          exact_mod_cast hslice_opt'
        have hcoeff_le : fStar + ψ0 ≤ C := by
          dsimp [C]
          nlinarith [le_abs_self fStar]
        have hscaled_le : ε * (fStar + ψ0) ≤ ε * C := by
          exact mul_le_mul_of_nonneg_left hcoeff_le hε_nonneg
        linarith
      have hsInf_le_tε :
          sInf (g '' Set.univ) ≤ g tε := by
        exact csInf_le hg_bdd (Set.mem_image_of_mem g (by simp))
      calc
        sInf (g '' Set.univ) ≤ g tε := hsInf_le_tε
        _ ≤ -fStar + ε * C := hψε_le
        _ ≤ -fStar + δ := by linarith [hεC]

/-- Helper for Proposition 7.7: on every ratio-feasible point, the quadratic objective is bounded
above by the ratio objective through the scalar inequality `(β - γ)^2 ≥ 0`. -/
private theorem maxRatioProblem_apply_le_maxQuadraticProblem_apply
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ maxRatioFeasibleSet a) :
    maxRatioProblem a f x ≤ maxQuadraticProblem a f x := by
  let β : ℝ := dotProduct f x
  let γ : ℝ := (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2
  have hγ_pos : 0 < γ := by
    simpa [γ, maxRatioFeasibleSet] using hx
  have hscalar :
      2 * β - γ ≤ β ^ 2 / γ := by
    refine (le_div_iff₀ hγ_pos).2 ?_
    have hsq : 0 ≤ (β - γ) ^ 2 := sq_nonneg (β - γ)
    nlinarith
  -- Rewrite both owner objectives to the same scalar inequality.
  simp only [maxRatioProblem, maxQuadraticProblem]
  dsimp [β, γ] at hscalar
  linarith

/-- Helper for Proposition 7.7: evaluating the quadratic objective on the ray
`((⟪f, x⟫ / γ) • x)` realizes the ratio objective value, where
`γ = (maxᵢ |⟪aᵢ, x⟫|)^2`. -/
private theorem maxQuadraticProblem_apply_optimalRay_eq_maxRatioProblem_apply
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ maxRatioFeasibleSet a) :
    let β : ℝ := dotProduct f x
    let γ : ℝ := (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2
    maxQuadraticProblem a f ((β / γ) • x) = maxRatioProblem a f x := by
  let β : ℝ := dotProduct f x
  let γ : ℝ := (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2
  have hγ_pos : 0 < γ := by
    simpa [γ, maxRatioFeasibleSet] using hx
  have hdot :
      dotProduct f ((β / γ) • x) = β ^ 2 / γ := by
    -- The ray parameter `β / γ` is chosen so that the linear term and denominator coincide.
    calc
      dotProduct f ((β / γ) • x) = (β / γ) * dotProduct f x := by
        rw [dotProduct_smul]
        simp [smul_eq_mul]
      _ = (β / γ) * β := by simp [β]
      _ = β ^ 2 / γ := by
            field_simp [hγ_pos.ne']
  have hden :
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) ((β / γ) • x)) ^ 2 = β ^ 2 / γ := by
    -- Positive homogeneity of the denominator reduces the ray computation to scalar arithmetic.
    rw [max_abs_inner_sq_smul]
    calc
      (β / γ) ^ 2 * (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2
          = (β / γ) ^ 2 * γ := by simp [γ]
      _ = β ^ 2 / γ := by
            field_simp [hγ_pos.ne']
  -- Both objectives now reduce to the same scalar `-β² / γ`.
  simp only [maxQuadraticProblem, maxRatioProblem]
  dsimp [β, γ]
  rw [hdot, hden]
  ring

/-- Helper for Proposition 7.7: after the first minimax equality is established, ray scaling along
each nonzero direction identifies the quadratic max value with the ratio max value. -/
private theorem maxQuadraticValue_eq_maxRatioValue
    {n : ℕ} (hn : 0 < n) (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    maxQuadraticValue a f = maxRatioValue a f := by
  -- Route correction: the ray-scaling step should compare the quadratic objective and the ratio
  -- objective by optimizing the scalar parameter along each nonzero ray and then normalizing by
  -- the denominator `maxᵢ |⟪aᵢ, x⟫|²`.
  apply le_antisymm
  · rw [maxQuadraticValue, maxRatioValue, EReal.neg_le_neg_iff]
    rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_csInf ?_ ?_
    · refine ⟨((maxQuadraticProblem a f) 0 : EReal), ?_⟩
      refine ⟨0, by simp [maxQuadraticProblem], rfl⟩
    · rintro _ ⟨x, -, rfl⟩
      by_cases hx0 : x = 0
      · obtain ⟨z, hz⟩ := exists_maxRatio_feasible hn a hinv
        have hratio_nonpos : (maxRatioProblem a f).optimalValue ≤ 0 := by
          refine ((maxRatioProblem a f).optimalValue_le_of_mem_feasibleSet hz).trans ?_
          have hnonneg :
              0 ≤ (dotProduct f z) ^ 2 /
                (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) z) ^ 2 := by
            exact div_nonneg (sq_nonneg _) (le_of_lt hz)
          change (((-((dotProduct f z) ^ 2 /
            (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) z) ^ 2) : ℝ) : EReal) ≤ 0)
          exact_mod_cast neg_nonpos.mpr hnonneg
        have hmax_zero :
            maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|)
              (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
          simp [maxTypeObjective_apply]
        calc
          (maxRatioProblem a f).optimalValue ≤ 0 := hratio_nonpos
          _ = ((maxQuadraticProblem a f) x : EReal) := by
                simp [maxQuadraticProblem, hx0, hmax_zero]
      · have hx : x ∈ maxRatioFeasibleSet a := by
          simpa [maxRatioFeasibleSet] using max_abs_inner_sq_pos_of_ne_zero a hinv hx0
        calc
          (maxRatioProblem a f).optimalValue
              ≤ ((maxRatioProblem a f) x : EReal) :=
                (maxRatioProblem a f).optimalValue_le_of_mem_feasibleSet hx
          _ ≤ ((maxQuadraticProblem a f) x : EReal) := by
                exact_mod_cast
                  maxRatioProblem_apply_le_maxQuadraticProblem_apply a f hx
  · rw [maxRatioValue, maxQuadraticValue, EReal.neg_le_neg_iff]
    rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_csInf ?_ ?_
    · obtain ⟨x, hx⟩ := exists_maxRatio_feasible hn a hinv
      refine ⟨((maxRatioProblem a f) x : EReal), ?_⟩
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      let β : ℝ := dotProduct f x
      let γ : ℝ := (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2
      let y : EuclideanSpace ℝ (Fin n) := (β / γ) • x
      calc
        (maxQuadraticProblem a f).optimalValue
            ≤ ((maxQuadraticProblem a f) y : EReal) :=
              (maxQuadraticProblem a f).optimalValue_le_of_mem_feasibleSet (by
                simp [maxQuadraticProblem, y])
        _ = ((maxRatioProblem a f) x : EReal) := by
              simpa [β, γ, y] using
                maxQuadraticProblem_apply_optimalRay_eq_maxRatioProblem_apply a f hx

/-- Helper for Proposition 7.7: if a real-valued constrained problem has a nonempty feasible image
bounded below in `ℝ`, then its owner optimal value is the corresponding real infimum. -/
private theorem optimalValue_eq_coe_sInf_of_nonempty_bddBelow
    {X : Type*} (Q : Set X) (g : X → ℝ) (hQ : Q.Nonempty) (hbounded : BddBelow (g '' Q)) :
    (.mk Q g : SetConstrainedMinimizationProblem X).optimalValue =
      ((sInf (g '' Q) : ℝ) : EReal) := by
  -- Transport the real greatest-lower-bound characterization across the coercion `ℝ → EReal`.
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  have hs :
      IsGLB ((fun x : ℝ ↦ (x : EReal)) '' (g '' Q)) (((sInf (g '' Q) : ℝ) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact EReal.coe_le_coe (csInf_le hbounded hy)
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          intro hz_eq_top
          rcases hQ with ⟨x, hx⟩
          have hz_mem : z ≤ (g x : EReal) := hz ⟨g x, ⟨x, hx, rfl⟩, rfl⟩
          simp [hz_eq_top] at hz_mem
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : r ≤ sInf (g '' Q) := by
          refine le_csInf (hQ.image g) ?_
          intro y hy
          have hzy : (r : EReal) ≤ (y : EReal) := hz ⟨y, hy, rfl⟩
          exact_mod_cast hzy
        exact_mod_cast hr
  have hs' : ((fun x : ℝ ↦ (x : EReal)) '' (g '' Q)).Nonempty := by
    rcases hQ with ⟨x, hx⟩
    exact ⟨g x, ⟨g x, ⟨x, hx, rfl⟩, rfl⟩⟩
  simpa [Set.image_image] using hs.csInf_eq hs'

/-- Helper for Proposition 7.7: under nonemptiness and a real lower bound, the owner optimal value
projects back to the corresponding real infimum via `.toReal`. -/
private theorem optimalValue_toReal_eq_sInf_of_nonempty_bddBelow
    {X : Type*} (Q : Set X) (g : X → ℝ) (hQ : Q.Nonempty) (hbounded : BddBelow (g '' Q)) :
    ((.mk Q g : SetConstrainedMinimizationProblem X).optimalValue).toReal = sInf (g '' Q) := by
  -- First rewrite the owner value as a finite `EReal`, then remove the coercion.
  rw [optimalValue_eq_coe_sInf_of_nonempty_bddBelow Q g hQ hbounded]
  simp

/-- Helper for Proposition 7.7: on a nonnegative feasible image, squaring commutes with taking the
real infimum. -/
private theorem sInf_sq_image_eq_sq_sInf_image_of_nonneg
    {X : Type*} (Q : Set X) (φ : X → ℝ) (hQ : Q.Nonempty) (hφ_nonneg : ∀ y ∈ Q, 0 ≤ φ y) :
    sInf ((fun y ↦ φ y ^ (2 : ℕ)) '' Q) = (sInf (φ '' Q)) ^ (2 : ℕ) := by
  let A : Set ℝ := φ '' Q
  have hA_nonempty : A.Nonempty := by
    simpa [A] using hQ.image φ
  have hA_bddBelow : BddBelow A := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hφ_nonneg y hy
  have hA_subset : A ⊆ Set.Ici 0 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hφ_nonneg y hy
  have hmono : MonotoneOn (fun x : ℝ ↦ x * x) A := by
    exact (strictMonoOn_mul_self.monotoneOn).mono hA_subset
  have hsq :
      (sInf A) * sInf A = sInf ((fun x : ℝ ↦ x * x) '' A) := by
    -- The square map is continuous and monotone on the nonnegative feasible image.
    simpa [pow_two] using
      (MonotoneOn.map_csInf_of_continuousWithinAt
        (A := A) (f := fun x : ℝ ↦ x * x)
        (continuous_id.mul continuous_id).continuousWithinAt
        hmono hA_nonempty hA_bddBelow)
  have himage :
      ((fun x : ℝ ↦ x * x) '' A) = ((fun y ↦ φ y ^ (2 : ℕ)) '' Q) := by
    ext z
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp [pow_two]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨φ y, ⟨y, hy, rfl⟩, by simp [pow_two]⟩
  -- Rewrite the squared image back from the intermediate feasible-value set `A`.
  simpa [A, himage, pow_two] using hsq.symm

/-- Helper for Proposition 7.7: the finite maximum of absolute pairings is always nonnegative. -/
private theorem maxTypeObjective_absInner_nonneg
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact le_trans (abs_nonneg _) <|
    Finset.le_sup' (fun j : ι ↦ |inner ℝ (a j) x|) (Finset.mem_univ i)

/-- Helper for Proposition 7.7: if `f ≠ 0`, then the affine slice `⟪f, y⟫ = 1` is nonempty. -/
private theorem hyperplane_one_nonempty
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n)} (hf : f ≠ 0) :
    (nesterovHyperplane f 1).Nonempty := by
  let y : EuclideanSpace ℝ (Fin n) := (‖f‖ ^ 2)⁻¹ • f
  refine ⟨y, ?_⟩
  have hnorm_pos : 0 < ‖f‖ ^ 2 := by
    positivity
  rw [mem_nesterovHyperplane_iff]
  calc
    inner ℝ f y = (‖f‖ ^ 2)⁻¹ * inner ℝ f f := by
          dsimp [y]
          rw [inner_smul_right]
    _ = (‖f‖ ^ 2)⁻¹ * (‖f‖ ^ 2) := by rw [real_inner_self_eq_norm_sq]
    _ = 1 := by field_simp [hnorm_pos.ne']

/-- Helper for Proposition 7.7: on `f ≠ 0`, the support minimum is the coercion of the real
infimum of `y ↦ maxᵢ |⟪aᵢ, y⟫|` over the affine slice `⟪f, y⟫ = 1`. -/
private theorem supportAbsMin_eq_coe_sInf_on_hyperplane
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (hf : f ≠ 0) :
    supportAbsMin a f =
      ((sInf
        ((fun y : EuclideanSpace ℝ (Fin n) ↦
          maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) y) '' nesterovHyperplane f 1) : ℝ) : EReal) := by
  let φ : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦
    maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) y
  have hQ : (nesterovHyperplane f 1).Nonempty := hyperplane_one_nonempty hf
  have hbounded : BddBelow (φ '' nesterovHyperplane f 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact maxTypeObjective_absInner_nonneg a y
  -- Rewrite the support-minimum owner directly as the real infimum over the affine slice.
  simpa [supportAbsMin, supportAbsMinProblem, φ] using
    optimalValue_eq_coe_sInf_of_nonempty_bddBelow (nesterovHyperplane f 1) φ hQ hbounded

/-- Helper for Proposition 7.7: on `f ≠ 0`, the affine-slice support infimum is strictly positive. -/
private theorem supportAbsMin_hyperplane_inf_pos
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) (hf : f ≠ 0) :
    0 <
      sInf
        ((fun y : EuclideanSpace ℝ (Fin n) ↦
          maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) y) '' nesterovHyperplane f 1) := by
  let Q : Set (EuclideanSpace ℝ (Fin n)) := nesterovHyperplane f 1
  let φ : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦
    maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) y
  let u0 : StdSimplex.Strict ℝ ι := Classical.choice uniform_strict_simplex_point_exists
  obtain ⟨μ, hμ_pos, hμ⟩ := strict_anchor_quadratic_lower_bound a u0 (hinv u0)
  have hQ : Q.Nonempty := hyperplane_one_nonempty hf
  have hφ_nonneg : ∀ y ∈ Q, 0 ≤ φ y := by
    intro y hy
    exact maxTypeObjective_absInner_nonneg a y
  have hQ_bddBelow : BddBelow (φ '' Q) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hφ_nonneg y hy
  have hlower_sq : ∀ y ∈ Q, μ * (‖f‖ ^ 2)⁻¹ ≤ (φ y) ^ 2 := by
    intro y hy
    have hy_pair : inner ℝ f y = 1 := by simpa [Q] using hy
    have hpair_norm : 1 ≤ ‖f‖ * ‖y‖ := by
      calc
        1 = |inner ℝ f y| := by rw [hy_pair]; norm_num
        _ ≤ ‖f‖ * ‖y‖ := by simpa using abs_real_inner_le_norm f y
    have hy_norm_sq : (‖f‖ ^ 2)⁻¹ ≤ ‖y‖ ^ 2 := by
      have hsq_pos : 0 < ‖f‖ ^ 2 := by positivity
      have hsq_le : 1 ≤ ‖f‖ ^ 2 * ‖y‖ ^ 2 := by
        nlinarith [hpair_norm, norm_nonneg f, norm_nonneg y]
      exact (inv_le_iff_one_le_mul₀ hsq_pos).2 <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hsq_le
    have hgram :
        μ * ‖y‖ ^ 2 ≤ inner ℝ ((B[a](u0.1.weights)).toEuclideanLin y) y := hμ y
    have hmax :
        inner ℝ ((B[a](u0.1.weights)).toEuclideanLin y) y ≤ (φ y) ^ 2 := by
      simpa [φ] using weightedGram_quadratic_le_max_abs_sq_of_strict a u0 y
    exact (mul_le_mul_of_nonneg_left hy_norm_sq hμ_pos.le).trans (hgram.trans hmax)
  have hsq_inf :
      μ * (‖f‖ ^ 2)⁻¹ ≤ sInf ((fun y ↦ (φ y) ^ 2) '' Q) := by
    refine le_csInf (hQ.image fun y ↦ (φ y) ^ 2) ?_
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact hlower_sq y hy
  have hsq_eq :
      sInf ((fun y ↦ (φ y) ^ 2) '' Q) = (sInf (φ '' Q)) ^ 2 :=
    sInf_sq_image_eq_sq_sInf_image_of_nonneg Q φ hQ hφ_nonneg
  have hsq_pos : 0 < (sInf (φ '' Q)) ^ 2 := by
    have hleft_pos : 0 < μ * (‖f‖ ^ 2)⁻¹ := by positivity
    calc
      0 < μ * (‖f‖ ^ 2)⁻¹ := hleft_pos
      _ ≤ sInf ((fun y ↦ (φ y) ^ 2) '' Q) := hsq_inf
      _ = (sInf (φ '' Q)) ^ 2 := hsq_eq
  have hsInf_nonneg : 0 ≤ sInf (φ '' Q) := by
    refine le_csInf (hQ.image φ) ?_
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact hφ_nonneg y hy
  have hsInf_ne_zero : sInf (φ '' Q) ≠ 0 := by
    intro hs0
    simpa [hs0] using hsq_pos.ne'
  exact lt_of_le_of_ne hsInf_nonneg (by symm; exact hsInf_ne_zero)

/-- Helper for Proposition 7.7: normalizing ratio-feasible vectors to the nesterovHyperplane
`⟪f, x⟫ = 1` rewrites the ratio optimum as `(f*)⁻²`. -/
private theorem normalizeRatioFeasible_eq_invSq
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ maxRatioFeasibleSet a)
    (hβ : dotProduct f x ≠ 0) :
    let y : EuclideanSpace ℝ (Fin n) := (dotProduct f x)⁻¹ • x
    y ∈ nesterovHyperplane f 1 ∧
      (dotProduct f x) ^ 2 /
          (maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) x) ^ 2 =
        1 / (maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) y) ^ 2 := by
  let β : ℝ := dotProduct f x
  let γ : ℝ := (maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) x) ^ 2
  let y : EuclideanSpace ℝ (Fin n) := β⁻¹ • x
  have hγ_pos : 0 < γ := by
    simpa [γ, maxRatioFeasibleSet] using hx
  have hβ' : β ≠ 0 := by
    simpa [β] using hβ
  have hinner : inner ℝ f x = β := by
    simpa [β, dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct f x)
  have hy_mem : y ∈ nesterovHyperplane f 1 := by
    rw [mem_nesterovHyperplane_iff]
    calc
      inner ℝ f y = β⁻¹ * inner ℝ f x := by
            rw [show y = β⁻¹ • x by rfl, inner_smul_right]
      _ = β⁻¹ * β := by rw [hinner]
      _ = 1 := by
            field_simp [hβ']
  have hy_den :
      (maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) y) ^ 2 = β⁻¹ ^ 2 * γ := by
    simpa [β, γ, y] using max_abs_inner_sq_smul a β⁻¹ x
  refine ⟨hy_mem, ?_⟩
  calc
    (dotProduct f x) ^ 2 / (maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) x) ^ 2
        = β ^ 2 / γ := by simp [β, γ]
    _ = 1 / (β⁻¹ ^ 2 * γ) := by
          field_simp [hβ', hγ_pos.ne']
    _ = 1 / (maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) y) ^ 2 := by
          rw [hy_den]

/-- Helper for Proposition 7.7: negating the infimum of the negated image of an `EReal` set
recovers the supremum of the original set. -/
private theorem neg_sInf_neg_image_eq_sSup (s : Set EReal) :
    -sInf ((fun z : EReal ↦ -z) '' s) = sSup s := by
  -- Negation exchanges upper bounds on `s` with lower bounds on the negated image.
  apply le_antisymm
  · rw [EReal.neg_le]
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rw [EReal.neg_le, neg_neg]
    exact le_sSup hy
  · refine sSup_le ?_
    intro y hy
    rw [EReal.le_neg]
    exact sInf_le (Set.mem_image_of_mem (fun z : EReal ↦ -z) hy)

/-- Helper for Proposition 7.7: the ratio owner is the `EReal` supremum of the feasible ratio
image. -/
private theorem maxRatioValue_eq_sSup_ratioImage
    {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n)) :
    maxRatioValue a f =
      sSup (((fun x : EuclideanSpace ℝ (Fin n) ↦
        (((dotProduct f x) ^ 2 /
          (maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) x) ^ 2 : ℝ) : EReal)) ''
        maxRatioFeasibleSet a)) := by
  -- Rewrite the minimization owner as the negated infimum of the negated feasible ratio values.
  rw [maxRatioValue, SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  -- Then use the order anti-isomorphism `z ↦ -z` on `EReal`.
  simpa [maxRatioProblem, Set.image_image] using
    neg_sInf_neg_image_eq_sSup
      (((fun x : EuclideanSpace ℝ (Fin n) ↦
          (((dotProduct f x) ^ 2 /
            (maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) x) ^ 2 : ℝ) : EReal)) ''
        maxRatioFeasibleSet a))

private theorem maxRatioValue_eq_supportAbsMin_inv_sq_aux
    {n : ℕ} (hn : 0 < n) (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    maxRatioValue a f = (supportAbsMin a f)⁻¹ ^ 2 := by
  -- Route correction: the support-normalization step should proceed by rewriting the ratio value as
  -- the reciprocal square of the slice denominator and then comparing the resulting infimum on the
  -- nesterovHyperplane `⟪f, y⟫ = 1` with `supportAbsMin`.
  by_cases hf : f = 0
  · obtain ⟨x, hx⟩ := exists_maxRatio_feasible hn a hinv
    have hratio_zero :
        maxRatioValue a f = 0 := by
      have hmin :
          IsMinOn (maxRatioProblem a f) (maxRatioFeasibleSet a) x := by
        rw [isMinOn_iff]
        intro y hy
        simp [maxRatioProblem, hf, hy]
      have hopt :
          (maxRatioProblem a f).optimalValue = 0 := by
        simpa [maxRatioProblem, hf, hx] using
          (maxRatioProblem a f).optimalValue_eq_of_isMinOn hx hmin
      simp [maxRatioValue, hopt]
    have hsupport_top : supportAbsMin a f = ⊤ := by
      rw [supportAbsMin, SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
      simp [supportAbsMinProblem, hf, nesterovHyperplane]
    rw [hratio_zero, hsupport_top]
    simp
  · let Q : Set (EuclideanSpace ℝ (Fin n)) := nesterovHyperplane f 1
    let φ : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦
      maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) y
    let m : ℝ := sInf (φ '' Q)
    let ρ : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
      (dotProduct f x) ^ 2 / (φ x) ^ 2
    let R : Set ℝ := ρ '' maxRatioFeasibleSet a
    let g : ℝ → ℝ := fun r ↦ 1 / r ^ 2
    have hsupport :
        supportAbsMin a f = (m : EReal) := by
      simpa [Q, φ, m] using supportAbsMin_eq_coe_sInf_on_hyperplane a f hf
    have hm_pos : 0 < m := by
      simpa [Q, φ, m] using supportAbsMin_hyperplane_inf_pos a f hinv hf
    have hQ_nonempty : Q.Nonempty := hyperplane_one_nonempty hf
    have hQ_bddBelow : BddBelow (φ '' Q) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact maxTypeObjective_absInner_nonneg a y
    have hR_nonempty : R.Nonempty := by
      obtain ⟨x, hx⟩ := exists_maxRatio_feasible hn a hinv
      exact ⟨ρ x, ⟨x, hx, rfl⟩⟩
    have hratio_pointwise_le : ∀ x ∈ maxRatioFeasibleSet a, ρ x ≤ g m := by
      intro x hx
      by_cases hβ : dotProduct f x = 0
      · -- The zero-numerator branch contributes only the value `0`.
        simp [ρ, g, hβ, hm_pos.le]
      · let y : EuclideanSpace ℝ (Fin n) := (dotProduct f x)⁻¹ • x
        obtain ⟨hyQ, hnorm⟩ := normalizeRatioFeasible_eq_invSq a f hx hβ
        have hm_le : m ≤ φ y := csInf_le hQ_bddBelow ⟨y, hyQ, rfl⟩
        have hy_pos : 0 < φ y := lt_of_lt_of_le hm_pos hm_le
        have hsq : m ^ 2 ≤ (φ y) ^ 2 := by
          nlinarith [hm_le, hm_pos, hy_pos]
        have hinv_le : g (φ y) ≤ g m := by
          simpa [g] using one_div_le_one_div_of_le (show 0 < m ^ 2 by positivity) hsq
        simpa [ρ, g, y] using hnorm.trans_le hinv_le
    have hR_bddAbove : BddAbove R := by
      refine ⟨g m, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hratio_pointwise_le x hx
    have hA_nonempty : (φ '' Q).Nonempty := hQ_nonempty.image φ
    have hg_antitone : AntitoneOn g (φ '' Q) := by
      intro r hr s hs hrs
      rcases hr with ⟨y, hyQ, rfl⟩
      rcases hs with ⟨z, hzQ, rfl⟩
      have hy_le : m ≤ φ y := csInf_le hQ_bddBelow ⟨y, hyQ, rfl⟩
      have hz_le : m ≤ φ z := csInf_le hQ_bddBelow ⟨z, hzQ, rfl⟩
      have hy_pos : 0 < φ y := lt_of_lt_of_le hm_pos hy_le
      have hz_pos : 0 < φ z := lt_of_lt_of_le hm_pos hz_le
      have hsq : (φ y) ^ 2 ≤ (φ z) ^ 2 := by
        nlinarith [hrs, hy_pos, hz_pos]
      simpa [g] using
        one_div_le_one_div_of_le (show 0 < (φ y) ^ 2 by positivity) hsq
    have hcont_g : ContinuousWithinAt g (φ '' Q) m := by
      have hm_sq_ne : m ^ 2 ≠ 0 := by positivity
      exact (((continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (1 : ℝ)) m).div
        (continuousAt_id.pow 2) hm_sq_ne)).continuousWithinAt
    have himage_subset : g '' (φ '' Q) ⊆ R := by
      rintro _ ⟨r, ⟨y, hyQ, rfl⟩, rfl⟩
      have hy_le : m ≤ φ y := csInf_le hQ_bddBelow ⟨y, hyQ, rfl⟩
      have hy_pos : 0 < φ y := lt_of_lt_of_le hm_pos hy_le
      have hy_feasible : y ∈ maxRatioFeasibleSet a := by
        simpa [Q, φ, maxRatioFeasibleSet] using sq_pos_of_pos hy_pos
      have hy_inner : inner ℝ f y = 1 := by
        simpa [Q] using hyQ
      have hy_dot : dotProduct f y = 1 := by
        have hinner_dot : inner ℝ f y = dotProduct f y := by
          simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct f y)
        linarith
      refine ⟨y, hy_feasible, ?_⟩
      simp [ρ, g, hy_dot]
    have hlower_real : g m ≤ sSup R := by
      calc
        g m = sSup (g '' (φ '' Q) : Set ℝ) :=
          AntitoneOn.map_csInf_of_continuousWithinAt hcont_g hg_antitone hA_nonempty hQ_bddBelow
        _ ≤ sSup R := by
          refine csSup_le (hA_nonempty.image g) ?_
          intro z hz
          exact le_csSup hR_bddAbove (himage_subset hz)
    have hratio_value :
        maxRatioValue a f = sSup (Real.toEReal '' R) := by
      simpa [R, ρ, Set.image_image, Function.comp] using maxRatioValue_eq_sSup_ratioImage a f
    have hupper :
        maxRatioValue a f ≤ ((g m : ℝ) : EReal) := by
      rw [hratio_value]
      refine sSup_le ?_
      rintro _ ⟨r, ⟨x, hx, rfl⟩, rfl⟩
      exact_mod_cast hratio_pointwise_le x hx
    have hlower :
        ((g m : ℝ) : EReal) ≤ maxRatioValue a f := by
      rw [hratio_value]
      calc
        ((g m : ℝ) : EReal) ≤ ((sSup R : ℝ) : EReal) := by
          exact_mod_cast hlower_real
        _ = sSup (Real.toEReal '' R) := by
          have hR_lub : IsLUB (Real.toEReal '' R) ((sSup R : ℝ) : EReal) := by
            refine ⟨?_, ?_⟩
            · rintro _ ⟨r, hr, rfl⟩
              exact_mod_cast le_csSup hR_bddAbove hr
            · intro z hz
              by_cases hz_top : z = ⊤
              · simp [hz_top]
              · by_cases hz_bot : z = ⊥
                · rcases hR_nonempty with ⟨r, hr⟩
                  have hz_le : (r : EReal) ≤ z := hz ⟨r, hr, rfl⟩
                  simp [hz_bot] at hz_le
                · lift z to ℝ using ⟨hz_top, hz_bot⟩ with z'
                  have hz' : ∀ r ∈ R, r ≤ z' := by
                    intro r hr
                    exact_mod_cast hz ⟨r, hr, rfl⟩
                  exact_mod_cast csSup_le hR_nonempty hz'
          simpa using hR_lub.sSup_eq.symm
    have hg_support :
        ((g m : ℝ) : EReal) = (supportAbsMin a f)⁻¹ ^ 2 := by
      rw [hsupport]
      dsimp [g]
      rw [one_div]
      change (((m ^ 2)⁻¹ : ℝ) : EReal) = ((m⁻¹ ^ 2 : ℝ) : EReal)
      exact_mod_cast (inv_pow m 2).symm
    -- The ratio `sSup` equals the reciprocal square of the nesterovHyperplane support infimum.
    calc
      maxRatioValue a f = ((g m : ℝ) : EReal) := le_antisymm hupper hlower
      _ = (supportAbsMin a f)⁻¹ ^ 2 := hg_support

-- Proof sketch: for each interior simplex point `t`, identify `⟪B(t)⁻¹ f, f⟫` with the
-- optimum of the quadratic form `2⟪f, x⟫ - ⟪B(t)x, x⟫`, compare `⟪B(t)x, x⟫` with
-- `maxᵢ ⟪aᵢ, x⟫²`, and then optimize over `t` and `x`; the ratio identity follows by rescaling
-- along each nonzero ray.
/-- Proposition 7.7: if every interior simplex combination `B(t)` is invertible, then `ψ*`
coincides with both the quadratic max formulation and the ratio max formulation, provided the
index family is nonempty and the ambient space has positive dimension. -/
theorem psiStar_eq_max_formulations
    (n : ℕ) (hn : 0 < n) (a : ι → EuclideanSpace ℝ (Fin (2 * n)))
    (f : EuclideanSpace ℝ (Fin (2 * n)))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    psiStar a f = maxQuadraticValue a f ∧ maxQuadraticValue a f = maxRatioValue a f :=
  by
  have hψ_le : maxQuadraticValue a f ≤ psiStar a f := maxQuadraticValue_le_psiStar a f hinv
  have hψ_ge : psiStar a f ≤ maxQuadraticValue a f := psiStar_le_maxQuadraticValue a f hinv
  constructor
  · -- The first equality is exactly the two-sided minimax comparison.
    exact le_antisymm hψ_ge hψ_le
  · -- The second equality is the ray-scaling normalization of the same source objective.
    exact maxQuadraticValue_eq_maxRatioValue (show 0 < 2 * n by omega) a f hinv

-- Proof sketch: normalize vectors by the constraint `⟪f, x⟫ = 1` and rewrite the ratio
-- formulation in terms of the minimum of `maxᵢ |⟪aᵢ, x⟫|`.
/-- Under the same nondegeneracy hypotheses as Proposition 7.7, the constrained support minimum
`f*` satisfies the identity `ψ* = (f*)⁻²`. -/
theorem psiStar_eq_supportAbsMin_inv_sq
    (n : ℕ) (hn : 0 < n) (a : ι → EuclideanSpace ℝ (Fin (2 * n)))
    (f : EuclideanSpace ℝ (Fin (2 * n)))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    psiStar a f = (supportAbsMin a f)⁻¹ ^ 2 :=
  by
  rcases psiStar_eq_max_formulations n hn a f hinv with ⟨hψ, hratio⟩
  calc
    psiStar a f = maxQuadraticValue a f := hψ
    _ = maxRatioValue a f := hratio
    _ = (supportAbsMin a f)⁻¹ ^ 2 := maxRatioValue_eq_supportAbsMin_inv_sq_aux
      (show 0 < 2 * n by omega) a f hinv

end PsiStarTheorems
