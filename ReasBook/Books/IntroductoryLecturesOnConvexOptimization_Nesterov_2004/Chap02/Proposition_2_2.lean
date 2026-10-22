/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient SmoothConvex

noncomputable section

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "p" => normSeminorm ℝ E

/- Primary domain: Euclidean `C²` smooth-convex objectives controlled by Hessian quadratic-form
bounds.

Owner-style declarations sampled before refining this file:
* `ConvexC1SeminormSmooth` in `Theorem_2_5`
* `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded` in `Theorem_2_6`
* `Seminorm.dualNorm_normSeminorm_eq_norm` in `Lemma_2_3`
* `smoothLowerBoundFunction_hessian_eq_tridiagonal` in `Definition_2_11`

Best owner abstraction:
`f ∈ 𝓕[L, p]¹¹` for the canonical smoothness constant `L : NNReal`.

Primitive data:
- the textbook chain quadratic form `nesterovChainQuadraticForm k`;
- the explicit Hessian quadratic-form identity for `f`.

Derived API:
- membership in the chapter owner class `𝓕[L, p]¹¹`;
- the textbook convexity and Euclidean gradient-Lipschitz consequences.

Accordingly, this file keeps the explicit chain formula but routes its consequences through the
chapter's source-facing owner notation instead of a parallel wrapper predicate and intermediate
Hessian-bounds API.
-/

/-- Restrict a vector in `ℝⁿ` to its first `k.1 + 1` coordinates. This keeps the chain
quadratic form source-facing while avoiding repeated index-transport bookkeeping. -/
private def nesterovChainPrefix (k : Fin n) (h : E) :
    EuclideanSpace ℝ (Fin (k.1 + 1)) :=
  (EuclideanSpace.equiv (Fin (k.1 + 1)) ℝ).symm
    (fun i ↦ h (Fin.castLE (Nat.succ_le_of_lt k.2) i))

/-- Helper for Proposition 2.2: the prefix restriction reads off the corresponding coordinate of
the original vector. -/
private theorem nesterovChainPrefix_apply (k : Fin n) (h : E) (i : Fin (k.1 + 1)) :
    nesterovChainPrefix k h i = h (Fin.castLE (Nat.succ_le_of_lt k.2) i) := by
  -- The restricted vector was defined by transporting exactly these first coordinates.
  simp [nesterovChainPrefix]

/-- The chain quadratic form appearing in the Hessian identity for Nesterov's function `f_k`. -/
def nesterovChainQuadraticForm (k : Fin n) (h : E) : ℝ :=
  let h' := nesterovChainPrefix k h
  h' 0 ^ 2 +
    (∑ i : Fin k.1,
      (h' (Fin.castLE (Nat.le_succ k.1) i) - h' i.succ) ^ 2) +
    h' (Fin.last k.1) ^ 2

/-- The chain quadratic form is nonnegative because it is a sum of squares. -/
-- Proof sketch: expand `nesterovChainQuadraticForm`; each summand is a square, hence nonnegative,
-- and finite sums of nonnegative terms remain nonnegative.
theorem nesterovChainQuadraticForm_nonneg (k : Fin n) (h : E) :
    0 ≤ nesterovChainQuadraticForm k h := by
  -- Expand the quadratic form so positivity can read off the square terms directly.
  simp only [nesterovChainQuadraticForm]
  positivity

/-- The chain quadratic form is bounded by four times the Euclidean squared norm. -/
-- Proof sketch: bound each difference square by `2 a^2 + 2 b^2`, sum over the chain
-- `0, …, k`, and compare the resulting coordinate sum with `‖h‖^2`.
theorem nesterovChainQuadraticForm_le_four_mul_norm_sq (k : Fin n) (h : E) :
    nesterovChainQuadraticForm k h ≤ 4 * ‖h‖ ^ 2 := by
  let h' := nesterovChainPrefix k h
  -- Each chain edge satisfies the textbook estimate `(a - b)^2 ≤ 2 a^2 + 2 b^2`.
  have hedge :
      ∀ i : Fin k.1,
        (h' (Fin.castLE (Nat.le_succ k.1) i) - h' i.succ) ^ 2
          ≤ 2 * (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 + 2 * (h' i.succ) ^ 2 := by
    intro i
    nlinarith [sq_nonneg (h' (Fin.castLE (Nat.le_succ k.1) i) + h' i.succ)]
  have hsum_edges :
      (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i) - h' i.succ) ^ 2)
        ≤ ∑ i : Fin k.1,
            (2 * (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 + 2 * (h' i.succ) ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hedge i
  have hsum_expand :
      (∑ i : Fin k.1,
          (2 * (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 + 2 * (h' i.succ) ^ 2)) =
        2 * (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) +
          2 * (∑ i : Fin k.1, (h' i.succ) ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- The endpoint and shifted-prefix sums are each controlled by the full prefix square sum.
  have hfirst_le :
      (h' 0) ^ 2 ≤ ∑ i : Fin (k.1 + 1), (h' i) ^ 2 := by
    rw [Fin.sum_univ_succ]
    have htail_nonneg : 0 ≤ ∑ i : Fin k.1, (h' i.succ) ^ 2 := by positivity
    exact le_add_of_nonneg_right htail_nonneg
  have hlast_le :
      (h' (Fin.last k.1)) ^ 2 ≤ ∑ i : Fin (k.1 + 1), (h' i) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    have hcast_nonneg :
        0 ≤ ∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 := by
      positivity
    exact le_add_of_nonneg_left hcast_nonneg
  have hcast_le :
      (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2)
        ≤ ∑ i : Fin (k.1 + 1), (h' i) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sq_nonneg (h' (Fin.last k.1)))
  have hsucc_le :
      (∑ i : Fin k.1, (h' i.succ) ^ 2)
        ≤ ∑ i : Fin (k.1 + 1), (h' i) ^ 2 := by
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (sq_nonneg (h' 0))
  -- The prefix square sum is a partial coordinate sum of `‖h‖^2`.
  have hprefix_le :
      (∑ i : Fin (k.1 + 1), (h' i) ^ 2) ≤ ‖h‖ ^ 2 := by
    let g : ℕ → ℝ := fun i ↦ if hi : i < n then h ⟨i, hi⟩ ^ 2 else 0
    have hprefix_eq :
        (∑ i : Fin (k.1 + 1), (h' i) ^ 2) = ∑ i ∈ Finset.range (k.1 + 1), g i := by
      calc
        (∑ i : Fin (k.1 + 1), (h' i) ^ 2) = ∑ i : Fin (k.1 + 1), g i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt_n : (i : ℕ) < n := lt_of_lt_of_le i.2 (Nat.succ_le_of_lt k.2)
            have hindex : Fin.castLE (Nat.succ_le_of_lt k.2) i = ⟨(i : ℕ), hi_lt_n⟩ := by
              apply Fin.ext
              rfl
            rw [show g i = h ⟨(i : ℕ), hi_lt_n⟩ ^ 2 by simp [g, hi_lt_n]]
            rw [nesterovChainPrefix_apply]
            rw [hindex]
        _ = ∑ i ∈ Finset.range (k.1 + 1), g i := Fin.sum_univ_eq_sum_range g (k.1 + 1)
    have hnorm_eq :
        ‖h‖ ^ 2 = ∑ i ∈ Finset.range n, g i := by
      calc
        ‖h‖ ^ 2 = ∑ i : Fin n, (h i) ^ 2 := by
            simpa using EuclideanSpace.real_norm_sq_eq h
        _ = ∑ i : Fin n, g i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [g, i.2]
        _ = ∑ i ∈ Finset.range n, g i := Fin.sum_univ_eq_sum_range g n
    rw [hprefix_eq, hnorm_eq]
    have hk1 : k.1 + 1 ≤ n := Nat.succ_le_of_lt k.2
    rw [← Finset.sum_range_add_sum_Ico g hk1]
    have htail_nonneg : 0 ≤ ∑ i ∈ Finset.Ico (k.1 + 1) n, g i := by
      refine Finset.sum_nonneg ?_
      intro i hi
      have hi_lt_n : i < n := (Finset.mem_Ico.mp hi).2
      simpa [g, hi_lt_n] using sq_nonneg (h ⟨i, hi_lt_n⟩)
    exact le_add_of_nonneg_right htail_nonneg
  have hcast_eq :
      (∑ i : Fin (k.1 + 1), (h' i) ^ 2) =
        (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) + (h' (Fin.last k.1)) ^ 2 := by
    calc
      (∑ i : Fin (k.1 + 1), (h' i) ^ 2)
          = (∑ i : Fin k.1, (h' i.castSucc) ^ 2) + (h' (Fin.last k.1)) ^ 2 := by
              rw [Fin.sum_univ_castSucc]
      _ = (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) + (h' (Fin.last k.1)) ^ 2 := by
            congr 1
  have hsucc_eq :
      (∑ i : Fin (k.1 + 1), (h' i) ^ 2) =
        (h' 0) ^ 2 + (∑ i : Fin k.1, (h' i.succ) ^ 2) := by
    rw [Fin.sum_univ_succ]
  -- Combine the edge estimate with the prefix/full norm comparison.
  calc
    nesterovChainQuadraticForm k h
        = h' 0 ^ 2 +
            (∑ i : Fin k.1, (h' (Fin.castLE (Nat.le_succ k.1) i) - h' i.succ) ^ 2) +
            h' (Fin.last k.1) ^ 2 := by
              simp [nesterovChainQuadraticForm, h']
    _ ≤ 4 * ∑ i : Fin (k.1 + 1), (h' i) ^ 2 := by
      nlinarith [hsum_edges, hsum_expand, hcast_eq, hsucc_eq, hcast_le, hsucc_le]
    _ ≤ 4 * ‖h‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left hprefix_le (by positivity)

section

variable (L : NNReal) (k : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)

/-- Proposition 2.2 in owner form: the explicit chain Hessian formula places `f` in the chapter's
smooth-convex owner class `𝓕[L, p]¹¹`. -/
-- Proof sketch: apply
-- `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded` for the Euclidean norm seminorm.
-- The lower and upper Hessian quadratic-form bounds come directly from the chain identity together
-- with `nesterovChainQuadraticForm_nonneg` and
-- `nesterovChainQuadraticForm_le_four_mul_norm_sq`.
theorem chain_hessian_formula_mem_smooth_convex_objective
    (hf_C2 : ContDiff ℝ 2 f)
    (hH : ∀ x h : E, inner ℝ (hessian f x h) h = ((L : ℝ) / 4) * nesterovChainQuadraticForm k h)
    : ConvexC1SeminormSmooth (normSeminorm ℝ (EuclideanSpace ℝ (Fin n))) L f := by
  -- Package the chain lower and upper bounds into the chapter's Hessian criterion.
  have hquad :
      ∀ x h : E,
        0 ≤ inner ℝ (hessian f x h) h ∧
          inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2 := by
    intro x h
    constructor
    · have hEq := hH x h
      nlinarith [L.2, hEq, nesterovChainQuadraticForm_nonneg k h]
    · have hEq := hH x h
      have hupper : inner ℝ (hessian f x h) h ≤ (L : ℝ) * ‖h‖ ^ 2 := by
        nlinarith [L.2, hEq, nesterovChainQuadraticForm_le_four_mul_norm_sq k h]
      simpa using hupper
  simpa using
    (@convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded
      (EuclideanSpace ℝ (Fin n)) _ _ _ _
      (normSeminorm ℝ (EuclideanSpace ℝ (Fin n))) _ L f hf_C2).2 hquad

/-- Proposition 2.2: the explicit chain formula for the Hessian quadratic form implies that `f`
is convex and that its gradient is `L`-Lipschitz in the Euclidean norm. -/
-- Proof sketch: first pass from the chain formula to the owner predicate `f ∈ 𝓕[L, p]¹¹` via
-- `chain_hessian_formula_mem_smooth_convex_objective`. Convexity is then `hf.convexOn`, while
-- the Euclidean `L`-Lipschitz bound for `∇ f` is the owner-derived theorem
-- `hf.gradient_lipschitz`.
theorem chain_hessian_formula_convexLipschitzGradient
    (hf_C2 : ContDiff ℝ 2 f)
    (hH : ∀ x h : E, inner ℝ (hessian f x h) h = ((L : ℝ) / 4) * nesterovChainQuadraticForm k h)
    : ConvexOn ℝ Set.univ f ∧ LipschitzWith L (∇ f) := by
  have hf : ConvexC1SeminormSmooth (normSeminorm ℝ (EuclideanSpace ℝ (Fin n))) L f :=
    chain_hessian_formula_mem_smooth_convex_objective L k f hf_C2 hH
  exact ⟨hf.convexOn, hf.gradient_lipschitz⟩

end
