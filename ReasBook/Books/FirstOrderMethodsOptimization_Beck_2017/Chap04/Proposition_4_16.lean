/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_35

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

noncomputable section

/- Proposition 4.16 is `source-facing`: its primitive data are the simplex-constrained negative
entropy and the associated finite Fenchel objective, while the canonical softmax owner declaration
is already `softmax_point` from Proposition 3.35. The Chapter 4 `core/canonical` owner
abstraction for Fenchel conjugates is `conjugate_function` from Definition 4.1, so this file
reuses both upstream owners directly instead of keeping parallel local copies. -/

section

variable {n : ℕ}

/- Classical decidability for membership in the standard simplex, used to define the extended
negative entropy by cases. -/
local instance stdSimplex_mem_decidable :
    DecidablePred (fun x : Fin n → ℝ ↦ x ∈ stdSimplex ℝ (Fin n)) :=
  Classical.decPred _

/-- The negative entropy on the standard simplex, extended by `∞` outside `stdSimplex ℝ (Fin n)`.
This is the function `x ↦ ∑ i, x i * log (x i)` from the source proposition. -/
def negative_entropy_on_stdSimplex (n : ℕ) : (Fin n → ℝ) → EReal :=
  fun x ↦
    if x ∈ stdSimplex ℝ (Fin n) then
      ((∑ i, x i * Real.log (x i) : ℝ) : EReal)
    else
      ⊤

/-- On simplex points, `negative_entropy_on_stdSimplex` is the finite negative-entropy sum. -/
@[simp] theorem negative_entropy_on_stdSimplex_of_mem
    {x : Fin n → ℝ} (hx : x ∈ stdSimplex ℝ (Fin n)) :
    negative_entropy_on_stdSimplex n x = ((∑ i, x i * Real.log (x i) : ℝ) : EReal) := by
  simp [negative_entropy_on_stdSimplex, hx]

/-- Outside the simplex, `negative_entropy_on_stdSimplex` is `∞`. -/
@[simp] theorem negative_entropy_on_stdSimplex_of_not_mem
    {x : Fin n → ℝ} (hx : x ∉ stdSimplex ℝ (Fin n)) :
    negative_entropy_on_stdSimplex n x = ⊤ := by
  simp [negative_entropy_on_stdSimplex, hx]

/-- The finite-dimensional Fenchel objective associated with the negative entropy on the simplex.
It is the negative of `entropy_linear_objective` from Proposition 3.35. -/
def negative_entropy_fenchel_objective
    (y x : Fin n → ℝ) : ℝ :=
  -entropy_linear_objective y x

/-- `negative_entropy_fenchel_objective` is the negated Chapter 3 entropy-linear objective. -/
@[simp] theorem negative_entropy_fenchel_objective_eq_neg_entropy_linear_objective
    (y x : Fin n → ℝ) :
    negative_entropy_fenchel_objective y x = -entropy_linear_objective y x :=
  rfl

/-- Helper for Proposition 4.16: on simplex points, the conjugate integrand agrees with the
finite Fenchel objective. -/
private theorem negativeEntropyConjugateIntegrand_eq_fenchelObjective_of_mem
    (y : Fin n → ℝ) {x : Fin n → ℝ} (hx : x ∈ stdSimplex ℝ (Fin n)) :
    ((dotProductEquiv ℝ (Fin n) y x : EReal) - negative_entropy_on_stdSimplex n x) =
      ((negative_entropy_fenchel_objective y x : ℝ) : EReal) := by
  -- Rewrite the extended entropy to its finite simplex branch and combine the finite `EReal`
  -- terms into one real expression.
  rw [negative_entropy_on_stdSimplex_of_mem (n := n) hx, ← EReal.coe_sub]
  congr 1
  simp [negative_entropy_fenchel_objective, entropy_linear_objective, dotProduct, sub_eq_add_neg]

/-- Helper for Proposition 4.16: outside the simplex, the conjugate integrand collapses to
`⊥`. -/
private theorem negativeEntropyConjugateIntegrand_eq_bot_of_not_mem
    (y : Fin n → ℝ) {x : Fin n → ℝ} (hx : x ∉ stdSimplex ℝ (Fin n)) :
    ((dotProductEquiv ℝ (Fin n) y x : EReal) - negative_entropy_on_stdSimplex n x) = ⊥ := by
  -- Outside the domain, the entropy extension is `⊤`, so subtracting it gives `⊥`.
  rw [negative_entropy_on_stdSimplex_of_not_mem (n := n) hx, EReal.sub_top]

-- Proof sketch: unfold the canonical Chapter 4 `conjugate_function` and
-- `negative_entropy_on_stdSimplex`. For `x` outside the simplex, the term
-- `(dotProductEquiv ℝ (Fin n) y x : EReal) - ⊤` is `⊥`, so those points do not affect the
-- supremum. On the simplex, the affine-minus-entropy term is exactly the coercion of
-- `negative_entropy_fenchel_objective y x`, leaving the supremum over the simplex image.
/-- Evaluating the conjugate of the simplex negative entropy at `y` is the supremum of the finite
Fenchel objective over the standard simplex. -/
theorem negative_entropy_on_stdSimplex_conjugate_eq_sSup
    (y : Fin n → ℝ) :
    conjugate_function (negative_entropy_on_stdSimplex n)
        (dotProductEquiv ℝ (Fin n) y) =
      sSup
        ((fun x : Fin n → ℝ ↦
            ((negative_entropy_fenchel_objective y x : ℝ) : EReal)) ''
          stdSimplex ℝ (Fin n)) := by
  rw [conjugate_function_apply]
  apply le_antisymm
  · -- Restrict the ambient supremum to simplex points by collapsing the outside branch to `⊥`.
    refine sSup_le ?_
    rintro r ⟨x, rfl⟩
    by_cases hx : x ∈ stdSimplex ℝ (Fin n)
    · have himage :
          (((negative_entropy_fenchel_objective y x : ℝ) : EReal)) ∈
            ((fun x : Fin n → ℝ ↦ ((negative_entropy_fenchel_objective y x : ℝ) : EReal)) ''
              stdSimplex ℝ (Fin n)) :=
        Set.mem_image_of_mem _ hx
      exact
        (negativeEntropyConjugateIntegrand_eq_fenchelObjective_of_mem (n := n) (y := y) hx).le.trans
          (le_sSup himage)
    · simpa using
        (negativeEntropyConjugateIntegrand_eq_bot_of_not_mem (n := n) (y := y) hx).le.trans bot_le
  · -- Every simplex value already appears in the original conjugate range.
    refine sSup_le ?_
    rintro r ⟨x, hx, rfl⟩
    have hrange :
        (((negative_entropy_fenchel_objective y x : ℝ) : EReal)) ∈
          Set.range
            (fun x : Fin n → ℝ ↦
              ((dotProductEquiv ℝ (Fin n) y x : EReal) - negative_entropy_on_stdSimplex n x)) := by
      refine ⟨x, ?_⟩
      simpa using
        (negativeEntropyConjugateIntegrand_eq_fenchelObjective_of_mem (n := n) (y := y) hx)
    exact le_sSup hrange

-- Proof sketch: optimize `negative_entropy_fenchel_objective y` on the simplex using a Lagrange
-- multiplier for the constraint `∑ i, x i = 1`. The stationarity equations
-- `log (x i) = y i + λ - 1` yield `x i = c * exp (y i)`, and the simplex constraint forces
-- `c = (∑ j, exp (y j))⁻¹`, so the optimizer is exactly `softmax_point y`.
/-- The softmax point is a maximizer of the Fenchel objective of the negative entropy over the
standard simplex. -/
theorem softmax_point_isMaxOn_negative_entropy_fenchel_objective
    (y : Fin n → ℝ) :
    IsMaxOn (negative_entropy_fenchel_objective y) (stdSimplex ℝ (Fin n)) (softmax_point y) := by
  rw [isMaxOn_iff]
  intro x hx
  simpa using neg_le_neg (entropyLinearObjective_softmax_le y x hx)

-- Proof sketch: expand `negative_entropy_fenchel_objective` at `softmax_point y`, use
-- `log (softmax_point y i) = y i - log (∑ j, exp (y j))`, and then sum over the simplex identity
-- `∑ i, softmax_point y i = 1` to collapse the entropy terms. No nonemptiness assumption is
-- needed here: when `n = 0`, both sides reduce to `Real.log 0 = 0` by the empty-sum convention.
/-- The Fenchel objective at the softmax point equals the log-sum-exp of `y`. -/
theorem negative_entropy_fenchel_objective_softmax_eq_log_sum_exp
    (y : Fin n → ℝ) :
    negative_entropy_fenchel_objective y (softmax_point y) =
      Real.log (∑ j, Real.exp (y j)) := by
  cases n with
  | zero =>
      simp [negative_entropy_fenchel_objective, entropy_linear_objective, softmax_point]
  | succ n =>
      calc
        negative_entropy_fenchel_objective y (softmax_point y)
            = -entropy_linear_objective y (softmax_point y) := rfl
        _ = -(-Real.log (∑ j, Real.exp (y j))) := by
              rw [entropyLinearObjective_softmax_eq_negLogSumExp y]
        _ = Real.log (∑ j, Real.exp (y j)) := by simp

section

variable [NeZero n]

/-- Helper for Proposition 4.16: the simplex image of the finite Fenchel objective attains its
greatest value at the softmax point. -/
private theorem negativeEntropyFenchelObjectiveImageIsGreatestAtSoftmax
    (y : Fin n → ℝ) :
    IsGreatest
      ((fun x : Fin n → ℝ ↦ ((negative_entropy_fenchel_objective y x : ℝ) : EReal)) ''
        stdSimplex ℝ (Fin n))
      (((negative_entropy_fenchel_objective y (softmax_point y) : ℝ) : EReal)) := by
  -- First record that the softmax value lies in the image set.
  refine ⟨?_, ?_⟩
  · exact ⟨softmax_point y, softmax_point_mem_stdSimplex y, rfl⟩
  · -- Then transport the real-valued `IsMaxOn` statement to the coerced `EReal` image.
    have hmax := softmax_point_isMaxOn_negative_entropy_fenchel_objective (n := n) (y := y)
    rw [isMaxOn_iff] at hmax
    rintro _ ⟨x, hx, rfl⟩
    simpa using hmax x hx

-- Proof sketch: rewrite the conjugate with `negative_entropy_on_stdSimplex_conjugate_eq_sSup`,
-- use `softmax_point_isMaxOn_negative_entropy_fenchel_objective` to identify that supremum with
-- the value at `softmax_point y`, and then apply
-- `negative_entropy_fenchel_objective_softmax_eq_log_sum_exp`.
/-- Proposition 4.16: the Fenchel conjugate of the negative entropy on the unit simplex is the
log-sum-exp function. -/
theorem negative_entropy_on_stdSimplex_conjugate_eq_log_sum_exp
    (y : Fin n → ℝ) :
    conjugate_function (negative_entropy_on_stdSimplex n)
        (dotProductEquiv ℝ (Fin n) y) =
      ((Real.log (∑ j, Real.exp (y j)) : ℝ) : EReal) := by
  -- Rewrite the conjugate as the supremum of the finite simplex image.
  rw [negative_entropy_on_stdSimplex_conjugate_eq_sSup]
  -- Replace the supremum by the softmax value using the attained-maximum package.
  rw [(negativeEntropyFenchelObjectiveImageIsGreatestAtSoftmax (n := n) y).csSup_eq]
  -- Evaluate the finite objective at the softmax point.
  simpa using congrArg (fun t : ℝ ↦ (t : EReal))
    (negative_entropy_fenchel_objective_softmax_eq_log_sum_exp (y := y))

end

end
