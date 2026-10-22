/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_2_1

open Matrix

section

variable {n : ℕ}

local notation "Point" => ConjugateGradientPoint n

-- Domain-style sampling summary:
-- * primary domain: finite-dimensional linear algebra for the linear conjugate-gradient method
--   on quadratic objectives;
-- * inspected owner declarations in the chapter domain:
--   `ConjugateGradientIterativeScheme`,
--   `LinearConjugateGradientMethod`,
--   `LinearConjugateGradientMethod.nonterminalStep`,
--   `posDefDistinctEigenvalueCount_le`;
-- * owner choice: `LinearConjugateGradientMethod` is the source-facing quadratic specialization,
--   built on top of the chapter owner `ConjugateGradientIterativeScheme`; the exercise formulas
--   below are thin bridge/view consequences of that owner;
-- * primitive data vs derived API: the run sequences and Fletcher-Reeves recurrence are
--   primitive in the imported owner, while exact line search, nonterminal-step identities,
--   conjugacy, and residual-direction relations are derived API and should not be duplicated
--   locally.

/-- A nonterminal stage of a positive-definite linear conjugate-gradient run occurs no later than
the distinct-eigenvalue termination bound from Theorem 4.2.1. -/
theorem linearConjugateGradient_nonterminalIndex_le_distinctEigenvalueCount
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point)
    (A : LinearConjugateGradientMethod G (-b)) {k : ℕ} (hk : A.g k ≠ 0) :
    k ≤ posDefDistinctEigenvalueCount hG := by
  obtain ⟨t, ht, ht_first⟩ :=
    linearConjugateGradient_terminatesBy_distinctEigenvalueCount G hG (-b) A
  by_cases hkt : k < t
  · exact le_trans hkt.le ht
  · have hk_term : A.terminatedAt k := by
      apply A.terminatedAt_mono ht_first.1
      exact Nat.le_of_not_gt hkt
    exact False.elim <| hk <| by
      simpa [ConjugateGradientIterativeScheme.terminatedAt] using hk_term

/-- Chapter04 Exercise 4.6 (1): for the quadratic objective
`x ↦ (1 / 2) * xᵀ G x - bᵀ x` with positive-definite Hessian `G`, the exact line-search
steplength at a nonterminal stage has the textbook form
`α_k = -(r_kᵀ d_k) / (d_kᵀ G d_k)`. The chapter owner uses the equivalent linear term `-b`
for the same objective. -/
theorem chapter04Exercise46_linearConjugateGradientStepSizeFormula
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point)
    (A : LinearConjugateGradientMethod G (-b)) {k : ℕ} (h_nonterminal : A.g k ≠ 0) :
    A.α k =
      -dotProduct (A.g k) (A.d k) /
        dotProduct (A.d k) (Matrix.toEuclideanLin G (A.d k)) := by
  have hk :
      k ≤ posDefDistinctEigenvalueCount hG :=
    linearConjugateGradient_nonterminalIndex_le_distinctEigenvalueCount G hG b A h_nonterminal
  rcases A.nonterminalStep h_nonterminal with ⟨_, _, _, hα, _, _, _, _, _⟩
  have hrd :
      dotProduct (A.g k) (A.d k) = -dotProduct (A.g k) (A.g k) := by
    simpa [dotProduct_comm] using
      linearConjugateGradient_direction_dot_residual G hG (-b) A hk
  have hgg :
      dotProduct (A.g k) (A.g k) = -dotProduct (A.g k) (A.d k) := by
    simpa using (congrArg Neg.neg hrd).symm
  calc
    A.α k =
        dotProduct (A.g k) (A.g k) /
          dotProduct (A.d k) (Matrix.toEuclideanLin G (A.d k)) := hα
    _ =
        -dotProduct (A.g k) (A.d k) /
          dotProduct (A.d k) (Matrix.toEuclideanLin G (A.d k)) := by rw [hgg]

/-- Adjacent search directions in a positive-definite linear conjugate-gradient run are
`G`-conjugate. This is the direct Exercise 4.6 companion to Theorem 4.2.1(3). -/
theorem linearConjugateGradient_adjacentDirectionConjugate
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point)
    (A : LinearConjugateGradientMethod G (-b)) {k : ℕ} (hk : 0 < k)
    (h_prev_nonterminal : A.g (k - 1) ≠ 0) :
    dotProduct (A.d k) (Matrix.toEuclideanLin G (A.d (k - 1))) = 0 := by
  have hk_pred : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk)
  obtain ⟨t, ht, ht_first⟩ :=
    linearConjugateGradient_terminatesBy_distinctEigenvalueCount G hG (-b) A
  have hprev_lt_t : k - 1 < t := by
    by_contra hnot
    have hprev_term : A.terminatedAt (k - 1) := by
      apply A.terminatedAt_mono ht_first.1
      exact Nat.le_of_not_gt hnot
    exact h_prev_nonterminal <| by
      simpa [ConjugateGradientIterativeScheme.terminatedAt] using hprev_term
  have hk_le_t : k ≤ t := by
    simpa [Nat.succ_eq_add_one, hk_pred] using Nat.succ_le_of_lt hprev_lt_t
  have hk_le :
      k ≤ posDefDistinctEigenvalueCount hG :=
    le_trans hk_le_t ht
  have hpred : k - 1 < k := by
    simpa [Nat.succ_eq_add_one, hk_pred] using Nat.lt_succ_self (k - 1)
  simpa using linearConjugateGradient_direction_conjugate G hG (-b) A hk_le hpred

/-- Chapter04 Exercise 4.6 (2): for the same quadratic objective and `k > 0`, the textbook
recurrence `d_k = -r_k + β_k d_(k - 1)` yields
`β_k = (r_kᵀ G d_(k - 1)) / (d_(k - 1)ᵀ G d_(k - 1))`. In the chapter owner,
`β (k - 1)` is the coefficient appearing in the update
`d k = -r k + β (k - 1) • d (k - 1)`. -/
theorem chapter04Exercise46_linearConjugateGradientBetaFormula
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point)
    (A : LinearConjugateGradientMethod G (-b)) {k : ℕ} (hk : 0 < k)
    (h_prev_nonterminal : A.g (k - 1) ≠ 0) :
    A.β (k - 1) =
      dotProduct (A.g k) (Matrix.toEuclideanLin G (A.d (k - 1))) /
        dotProduct (A.d (k - 1)) (Matrix.toEuclideanLin G (A.d (k - 1))) := by
  have hk_pred : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk)
  rcases A.nonterminalStep h_prev_nonterminal with ⟨_, _, hdenom_ne, _, _, _, _, _, hdir_raw⟩
  have hconj :=
    linearConjugateGradient_adjacentDirectionConjugate G hG b A hk h_prev_nonterminal
  have hdir :
      A.d k = -A.g k + A.β (k - 1) • A.d (k - 1) := by
    simpa [hk_pred] using hdir_raw
  have hmul :
      A.β (k - 1) *
          dotProduct (A.d (k - 1)) (Matrix.toEuclideanLin G (A.d (k - 1))) =
        dotProduct (A.g k) (Matrix.toEuclideanLin G (A.d (k - 1))) := by
    have hcalc :
        0 =
          -dotProduct (A.g k) (Matrix.toEuclideanLin G (A.d (k - 1))) +
            A.β (k - 1) *
              dotProduct (A.d (k - 1)) (Matrix.toEuclideanLin G (A.d (k - 1))) := by
      calc
        0 = dotProduct (A.d k) (Matrix.toEuclideanLin G (A.d (k - 1))) := by
          simpa using hconj.symm
        _ = dotProduct (-A.g k + A.β (k - 1) • A.d (k - 1))
              (Matrix.toEuclideanLin G (A.d (k - 1))) := by
          rw [hdir]
        _ =
            -dotProduct (A.g k) (Matrix.toEuclideanLin G (A.d (k - 1))) +
              A.β (k - 1) *
                dotProduct (A.d (k - 1)) (Matrix.toEuclideanLin G (A.d (k - 1))) := by
          simp [add_dotProduct, smul_dotProduct]
    linarith
  exact (eq_div_iff hdenom_ne).2 <| by simpa [mul_comm] using hmul

end
