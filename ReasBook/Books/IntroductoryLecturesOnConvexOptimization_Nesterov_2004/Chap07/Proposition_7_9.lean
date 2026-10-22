/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators Matrix

universe u

variable {ι : Type u} [Fintype ι]
variable {m : ℕ}
variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- This file keeps the finite-family weighted Gram-matrix owner used downstream in Chapter 7 and
adds the convex-combination invariant behind the rank-one update rule of Algorithm 7.6.

Relevant owner-style declarations sampled before refinement:
- `Matrix.vecMulVec`, the canonical rank-one outer-product owner in mathlib;
- `Matrix.vecMulVec_apply`, the canonical entrywise bridge for that owner;
- `centralSymmetricRoundingUpdatedMatrix` in `Algorithm_7_5`, the Chapter 7 owner of the
  Algorithm 7.6 rank-one matrix update;
- `TrussTopologyDesignProblem.stiffnessMatrix` in `Definition_7_22`, the chapter's specialized
  weighted-sum-of-rank-one-matrices owner for truss data.

Best owner abstraction:
- source-facing: `weightedGramMatrix` and the convex-combination invariant for repeated rank-one
  updates from a fixed finite family;
- core/canonical: `vecMulVec` for the rank-one summands;
- bridge/view: the entrywise evaluation lemma and the simplex-weight statements below.

Primitive data:
- a finite family `a : ι → ℝⁿ` or `a : Fin m → ℝⁿ`;
- a weight function `w : ι → ℝ`;
- the update coefficients `αₖ ∈ [0, 1]` and the chosen generators `a_{jₖ}`.

Derived API:
- the textbook notation `B[a](w)`;
- the entrywise formula for `B[a](w)`;
- the one-step and iterated preservation of the simplex-weighted Gram-matrix form.

The right public owner here is the general weighted Gram matrix itself. `Definition_7_22`
specializes the same pattern to truss geometry, and `Proposition_7_7` already depends on this
general owner. The current item is therefore expressed as a theorem on repeated
`centralSymmetricRoundingUpdatedMatrix` steps rather than by introducing a second wrapper around
Algorithm 7.6. -/

/-- The weighted Gram matrix `∑ᵢ wᵢ aᵢ aᵢᵀ` associated to a finite family of vectors in `ℝⁿ`. -/
def weightedGramMatrix (a : ι → Eₙ) (w : ι → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, w i • Matrix.vecMulVec (a i) (a i)

namespace WeightedGramMatrix

/- Source-facing Lean notation for the textbook operator `B(w)` attached to the family `a`. -/
scoped notation:max "B[" a:arg "](" w:arg ")" => weightedGramMatrix a w

end WeightedGramMatrix

open scoped WeightedGramMatrix

-- Proof sketch: expand the `(p, q)` entry of each rank-one matrix `aᵢ aᵢᵀ` and distribute the
-- finite sum over the matrix entries.
/-- Evaluating the weighted Gram matrix entrywise gives the coefficient-weighted sum
`∑ᵢ wᵢ aᵢ(p) aᵢ(q)`. -/
theorem weightedGramMatrix_apply (a : ι → Eₙ) (w : ι → ℝ)
    (p q : Fin n) :
    B[a](w) p q = ∑ i, w i * a i p * a i q := by
  -- Evaluate the matrix sum entrywise and rewrite each rank-one summand.
  simp [weightedGramMatrix, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    mul_assoc]

section ConvexCombinationStructure

-- Proof sketch: expand
-- `centralSymmetricRoundingUpdatedMatrix (B[a](λ.weights)) (a j) α` as
-- `(1 - α) ∑ i, λᵢ aᵢ aᵢᵀ + α aⱼ aⱼᵀ`, then absorb the last term into the updated simplex weights
-- whose `j`-th coordinate becomes `(1 - α) λⱼ + α` and whose other coordinates become
-- `(1 - α) λᵢ`.
/-- A single rank-one update with coefficient `α ∈ [0, 1]` preserves the simplex-weighted Gram
matrix form attached to the family `a₁, …, aₘ`. -/
theorem exists_simplex_weights_of_weightedGramMatrix_update
    (a : Fin m → Eₙ) (weights : StdSimplex ℝ (Fin m)) (j : Fin m) {α : ℝ}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) :
    ∃ weights' : StdSimplex ℝ (Fin m),
      centralSymmetricRoundingUpdatedMatrix (B[a](weights.weights)) (a j) α =
        B[a](weights'.weights) := by
  let updatedWeights : Fin m →₀ ℝ :=
    (1 - α) • weights.weights + Finsupp.single j α
  have hupdated_nonneg : ∀ i : Fin m, 0 ≤ updatedWeights i := by
    -- The update keeps every coefficient nonnegative because it is a convex combination.
    intro i
    have h_one_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα_le_one
    by_cases hij : i = j
    · subst hij
      simpa [updatedWeights] using
        add_nonneg (mul_nonneg h_one_sub_nonneg (weights.nonneg i)) hα_nonneg
    · have hmul_nonneg : 0 ≤ (1 - α) * weights.weights i :=
          mul_nonneg h_one_sub_nonneg (weights.nonneg i)
      simpa [updatedWeights, hij] using hmul_nonneg
  have hweights_total : ∑ i : Fin m, weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using weights.total
  have hupdated_total_fn : ∑ i : Fin m, updatedWeights i = 1 := by
    -- The updated coefficients still have total mass `1`.
    calc
      ∑ i : Fin m, updatedWeights i
          = ∑ i : Fin m, ((1 - α) * weights.weights i + (Finsupp.single j α) i) := by
              simp [updatedWeights]
      _ = (1 - α) * ∑ i : Fin m, weights.weights i +
            ∑ i : Fin m, (Finsupp.single j α) i := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (1 - α) * 1 + α := by
              simp [hweights_total, Finsupp.single_apply]
      _ = 1 := by ring
  have hupdated_total : updatedWeights.sum (fun i w ↦ w) = 1 := by
    simpa [Finsupp.sum_fintype] using hupdated_total_fn
  let weights' : StdSimplex ℝ (Fin m) :=
    ⟨updatedWeights, hupdated_nonneg, hupdated_total⟩
  refine ⟨weights', ?_⟩
  ext p q
  -- Compare the two matrices entrywise and expand the updated coefficients explicitly.
  calc
    centralSymmetricRoundingUpdatedMatrix (B[a](weights.weights)) (a j) α p q
        = (1 - α) * (∑ i : Fin m, weights.weights i * a i p * a i q) +
            α * (a j p * a j q) := by
              rw [centralSymmetricRoundingUpdatedMatrix_eq]
              simp [weightedGramMatrix_apply, Matrix.add_apply, Matrix.smul_apply,
                Matrix.vecMulVec_apply]
    _ = (1 - α) * (∑ i : Fin m, weights.weights i * a i p * a i q) +
          ∑ i : Fin m, (Finsupp.single j α) i * a i p * a i q := by
            congr 1
            calc
              α * (a j p * a j q) = α * a j p * a j q := by ring
              _ = ∑ i : Fin m, (Finsupp.single j α) i * a i p * a i q := by
                    simp [Finsupp.single_apply]
    _ = ∑ i : Fin m,
          ((1 - α) * (weights.weights i * a i p * a i q) +
            (Finsupp.single j α) i * a i p * a i q) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = ∑ i : Fin m,
          (((1 - α) * weights.weights i + (Finsupp.single j α) i) * a i p * a i q) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = ∑ i : Fin m, weights'.weights i * a i p * a i q := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [weights', updatedWeights]
    _ = B[a](weights'.weights) p q := by
            rw [weightedGramMatrix_apply]

-- Proof sketch: start from the initial simplex weights `λ₀`; apply the previous one-step
-- preservation theorem inductively along the update sequence
-- `Gₖ₊₁ = centralSymmetricRoundingUpdatedMatrix Gₖ a_{jₖ} αₖ`.
/-- Proposition 7.9 [Chapter7_1.json:55]: if a matrix sequence starts from a convex combination of
the rank-one matrices `aᵢ aᵢᵀ` and each step applies the Algorithm 7.6 rank-one update with some
coefficient `αₖ ∈ [0, 1]` and some chosen generator `a_{jₖ}`, then every `Gₖ` is again a convex
combination of the same rank-one matrices. -/
theorem exists_simplex_weights_for_rank_one_update_sequence
    (a : Fin m → Eₙ) (G : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (choice : ℕ → Fin m) (α : ℕ → ℝ) (weights0 : StdSimplex ℝ (Fin m))
    (hG0 : G 0 = B[a](weights0.weights))
    (hα : ∀ k : ℕ, 0 ≤ α k ∧ α k ≤ 1)
    (hGsucc :
      ∀ k : ℕ,
        G (k + 1) =
          centralSymmetricRoundingUpdatedMatrix (G k) (a (choice k)) (α k)) :
    ∀ k : ℕ, ∃ weightsk : StdSimplex ℝ (Fin m), G k = B[a](weightsk.weights) := by
  intro k
  induction k with
  | zero =>
      -- The initial matrix already comes from the given simplex weights.
      exact ⟨weights0, hG0⟩
  | succ k ih =>
      rcases ih with ⟨weightsk, hweightsk⟩
      rcases
          exists_simplex_weights_of_weightedGramMatrix_update a weightsk (choice k)
            (hα k).1 (hα k).2 with
        ⟨weightsNext, hweightsNext⟩
      -- One application of the update theorem advances the invariant to time `k + 1`.
      refine ⟨weightsNext, ?_⟩
      rw [hGsucc k, hweightsk]
      exact hweightsNext

end ConvexCombinationStructure
